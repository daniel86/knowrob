:- module(mongolog,
	[ mongolog_call/1,
	  mongolog_call/2,
	  mongolog_expand/2,
	  mongolog_add_clause/3,
	  mongolog_assert_rule/2,
	  mongolog_drop_rule/1,
	  is_mongolog_term/1
	]).
/** <module> Compiling goals into aggregation pipelines.

@author Daniel Beßler
@license BSD
*/

% TODO: support for recursion
%		- cycles in views are not allowed
%		- but graphLookup can be used for transitive relations
%       - unwind can be used to iterate over a list
% TODO: support for variable aliasing
% TODO: come up with a program transformation that organizes
%       a program into different segments where each segment
%       is individually evaluated and bulk operations are performed
%       in between to support programs such as `..,assert(a(x)),..,a(x),..`

:- use_module(library('semweb/rdf_db'),
	    [ rdf_meta/1, rdf_global_term/2 ]).
:- use_module(library('db/mongo/client')).

:- use_module('variables').
:- use_module('stages/aggregation', [ aggregate/4 ]).
:- use_module('stages/bulk_operation', [ bulk_operation/1 ]).

% Stores list of terminal terms for each clause. 
:- dynamic mongolog_rule/4.
% set of registered query commands.
:- dynamic step_command/1.
% implemented by query commands to compile query documents
:- multifile step_compile/3, step_compile1/3.
% optionally implemented by query commands.
:- multifile step_expand/2.

:- rdf_meta(step_compile(t,t,t)).
:- rdf_meta(step_compile1(t,t,t)).
:- rdf_meta(mongolog_call(t)).
:- rdf_meta(mongolog_call(t,t)).

%% is_mongolog_term(+PredicateIndicator) is semidet.
%
% True if PredicateIndicator corresponds to a known mongolog predicate.
%
% TODO: rules are fine too!
%
is_mongolog_term((/(Functor,_Arity))) :-
	!, step_command(Functor).
	
is_mongolog_term(Goal) :-
	compound(Goal),!,
	Goal =.. [Functor|_Args],
	step_command(Functor).
	
is_mongolog_term(Functor) :-
	atom(Functor),!,
	step_command(Functor).


%% add_command(+Command) is det.
%
% register a command that can be used in KnowRob
% language expressions and which is implemented
% in a mongo query.
% NOTE: to implement a command several multifile predicates in
% mongolog must be implemented by a command. 
%
% @param Command a command term.
%
add_command(Command) :- step_command(Command),!.
add_command(Command) :- assertz(step_command(Command)).


%% mongolog_add_clause(+Module, +Head, +Body) is semidet.
%
% Register a rule that translates into an aggregation pipeline.
% Any non-terminal predicate in Body must have a previously asserted
% rule it can expand into.
% After being asserted, the Head predicate can be referred to in
% calls of kb_call/1.
%
% @param Module module name
% @param Head The head of a rule.
% @param Body The body of a rule.
%
mongolog_add_clause(Module, Head, Body) :-
	% get the functor of the predicate
	Head =.. [Functor|Args],
	% expand goals into terminal symbols
	(	mongolog_expand(Body, Expanded) -> true
	;	log_error_and_fail(lang(assertion_failed(Body), Functor))
	),
	% assert the clause
	assertz(mongolog_rule(Module, Functor, Args, Expanded)).

%% mongolog_drop_rule(+Head) is semidet.
%
% Drop a previously added `mongolog` rule.
% That is, erase its database record such that it can
% not be referred to anymore in rules added after removal.
%
% @param Term A mongolog rule.
%
mongolog_drop_rule(Head) :-
	compound(Head),
	Head =.. [Functor|_],
	retractall(mongolog_rule(_,Functor, _, _)).

%%
% TODO: rather integrate mongolog_add_clause in this one, and remove mongolog_add_clause
%
mongolog_assert_rule(Head, Module) :-
	Head =.. [Functor|Args],
	expand_rule(Head, Clauses),
	% wrap different clauses into ';'
	semicolon_list(Zs, Clauses),
	mongolog_idb:idb_assert(Module, Functor, Args, Zs).

%% mongolog_call(+Goal) is nondet.
%
% Same as mongolog_call/2 with empty options list.
%
% @param Goal A compound term expanding into an aggregation pipeline
%
mongolog_call(Goal) :-
	current_scope(QScope),
	mongolog_call(Goal,[scope(QScope)]).

%% mongolog_call(+Goal, +Options) is nondet.
%
% Call Goal by translating it into an aggregation pipeline.
%
% @param Goal A compound term expanding into an aggregation pipeline
% @param Options Additional options
%
mongolog_call(Goal, Context) :-
	% get the pipeline document
	mongolog_compile(Goal, CompilerOutput, Vars,
		[head_vars([])|Context]),
	compiled_document(CompilerOutput, Doc),
	% get name of collection on which the aggregate operation
	% should be performed. This is basically the first collection
	% which is explicitely used in a step of the goal.
	ignore(memberchk(input_collection(Coll), CompilerOutput)),
	once((ground(Coll);Coll=one)),
	% TODO: below really needed?
	option(global_vars(GlobalVars), Context, []),
	merge_substitutions(Vars, GlobalVars, Vars2),
	% run the pipeline
	% TODO: split goal at assert's such that they are available in the rest of the query
	aggregate(Coll, Doc, Vars2, Result),
	bulk_operation(Result).


%% mongolog_compile(+Term, -CompilerOutput, -Variables, +Context) is semidet.
%
% Translate a goal into an aggregation pipeline.
% Goal may be a compound term using the various predicates
% supported by mongolog.
% The goal must not but can be expanded before (see mongolog_expand/2).
% An error is thrown in case of compilation failure.
% One failure case is to refer to an unknown predicate
% (it is thus necessary to assert all referred predicates before
% compiling a new predicate).
% Such an error will also be thrown for recursive rules
% (i.e. when a predicate refers to itself).
%
% @param Term A compound term, or a list of terms.
% @param Pipeline a term pipeline(Document,Variables)
% @param Context the query context
%
mongolog_compile(Terminals, Output, Vars, Context) :-
	catch(
		query_compile1(Terminals, Output, Vars, Context),
		% catch error's, add context, and throw again
		error(Formal),
		throw(error(Formal,Terminals))
	).

%%
query_compile1(Terminals, Output, Vars, Context) :-
	% get global variables supplied by the call context and add it
	% to the compile context
	option(global_vars(GlobalVars), Context, []),
	% compile an aggregation pipeline.
	compile_terms(Terminals,
		GlobalVars->Vars,
		Output, Context).

%%
compile_terms([], V0->V0, [document([]),variables([])], _) :-
	!.

compile_terms([X|Xs], V0->Vn, Output, Context) :-
	!,
	% compile first
	compile_term(X,  V0->V1, Output0, Context),
	% compile rest
	compile_terms(Xs, V1->Vn, Output1, Context),
	% merge both compiler outputs
	merge_outputs(Output0, Output1, Output).

compile_terms(Goal, Vars, Output, Context) :-
	\+ is_list(Goal),!,
	compile_terms([Goal], Vars, Output, Context).

%% Compile a single command (Term) into an aggregate pipeline (Doc).
compile_term(Term, V0->V1, Output, Context) :-
	mongolog_expand(Term, Expanded),
	compile_expanded_terms(Expanded, V0->V1, Output, Context).

%%
compile_expanded_terms([], V0->V0, [document([]),variables([])], _) :-
	!.

compile_expanded_terms([Expanded|Rest], V0->Vn, Output, Context) :-
	!,
	% compile first
	compile_expanded_term(Expanded, V0->V1, Output0, Context),
	% toggle on input_assigned flag in compile context to indicate that
	% a previoud step has assigned the input collection of the operation
	option(input_collection(InCollection), Output0, _),
	(	(ground(InCollection), \+ option(input_assigned,Context))
	->	merge_options([input_assigned],Context,Context1)
	;	Context1=Context
	),
	% compile rest
	compile_expanded_terms(Rest, V1->Vn, Output1, Context1),
	% finally merge both compilation outputs
	merge_outputs(Output0, Output1, Output).

compile_expanded_terms(Goal, Vars, Output, Context) :-
	\+ is_list(Goal), !,
	compile_expanded_terms([Goal], Vars, Output, Context).

%
compile_expanded_term(List, Vars, Output, Context) :-
	is_list(List),!,
	compile_expanded_terms(List, Vars, Output, Context).
	
compile_expanded_term(Expanded, V0->V1, Output0, Context) :-
	% create inner context
	merge_options([outer_vars(V0)], Context, InnerContext),
	% and finall compile expanded terms
	once(step_compile1(Expanded, InnerContext, Output)),
	compiled_document(Output, Pipeline),
	compiled_substitution(Output, StepVars),
	list_to_set(StepVars, StepVars_unique),
	% merge StepVars with variables in previous steps (V0)
	merge_substitutions(StepVars_unique, V0, V1),
	merge_options(
		[ document(Pipeline),
		  variables(StepVars_unique)
		],
		Output, Output0).

% combine outputs of two compilations
merge_outputs(Output0,Output1,
	[ document(Doc),
	  variables(StepVars),
	  input_collection(InCollection)
	]) :-
	% concat pipelines
	compiled_document(Output0, Doc0),
	compiled_document(Output1, Doc1),
	append(Doc0, Doc1, Doc),
	% merge substitutions
	compiled_substitution(Output0, StepVars0),
	compiled_substitution(Output1, StepVars1),
	merge_substitutions(StepVars0, StepVars1, StepVars),
	% use first input collection
	option(input_collection(InCollection0), Output0, _),
	(	ground(InCollection0) -> InCollection = InCollection0
	;	option(input_collection(InCollection), Output1, _)
	).

%
compiled_document(CompilerOutput, Doc) :-
	memberchk(document(Doc), CompilerOutput).
compiled_substitution(CompilerOutput, Substitution) :-
	memberchk(variables(Substitution), CompilerOutput).

%
unassign_input(Ctx_in, Ctx_out) :-
	once((
		select_option(input_assigned, Ctx_in, Ctx_x)
	;	Ctx_x=Ctx_in
	)),
	select_option(input_collection(_), Ctx_x, Ctx_out, _).

%%
step_compile1(Step, Ctx, [document(Doc), variables(StepVars)]) :-
	% first compute stepvars and extend context.
	% this is to avoid that different keys are assigned
	% to the same variable
	goal_vars(Step, Ctx, StepVars),
	merge_options([step_vars(StepVars)], Ctx, Ctx0),
	step_compile(Step, Ctx0, Doc).

%% ask(:Goal)
% Call Goal in ask mode.
%
step_compile1(ask(Goal), Ctx, Output) :-
	mongolog:step_compile1(call(Goal), Ctx, Output).

step_command(ask).

%% mongolog_expand(+Term, -Expanded) is det.
%
% Translate a goal into a sequence of terminal commands.
% Terminal commands are the core predicates supported in queries
% such as arithmetic and comparison predicates.
% Rules, on the other hand, are "flattened" during term expansion,
% and translated to a sequence of these terminal commands.
%
% @param Term A compound term, or a list of terms.
% @param Expanded Sequence of terminal commands
%
mongolog_expand(Goal, Goal) :-
	% goals maybe not known during expansion, i.e. in case of
	% higher-level predicates receiving a goal as an argument.
	% these var goals need to be expanded compile-time
	% (call-time is not possible)
	var(Goal), !.

mongolog_expand(Goal, Expanded) :-
	% NOTE: do not use is_list/1 here, it cannot handle list that have not
	%       been completely resolved as in `[a|_]`.
	%       Here we check just the head of the list.
	\+ has_list_head(Goal), !,
	comma_list(Goal, Terms),
	mongolog_expand(Terms, Expanded).

mongolog_expand(Goal, Expanded) :-
	% special handling for cut
	has_cut(Goal),!,
	expand_cut(Goal, [], Expanded).

mongolog_expand(Terms, Expanded) :-
	catch(
		expand_term_0(Terms, Expanded0),
		Exc,
		log_error_and_fail(mongolog(Exc, Terms))
	),
	comma_list(Buf,Expanded0),
	comma_list(Buf,Expanded1),
	%%
	(	Expanded1=[One]
	->	Expanded=One
	;	Expanded=Expanded1
	).

%%
expand_term_0([], []) :- !.
expand_term_0([X|Xs], [X_expanded|Xs_expanded]) :-
	once(expand_term_1(X, X_expanded)),
	% could be that expand-time the list is not fully resolved
	(	var(Xs) -> Xs_expanded=Xs
	;	expand_term_0(Xs, Xs_expanded)
	).

expand_term_1(Goal, Expanded) :-
	% TODO: seems nested terms sometimes not properly flattened, how does it happen?
	is_list(Goal),!,
	expand_term_0(Goal, Expanded).

expand_term_1(Goal, Expanded) :-
	once((compound(Goal);atomic(Goal))),
	Goal =.. [Functor|Args],
	length(Args,Arity),
	once((
		% FIXME: do not use lang_query
		lang_query:expanding_term(Functor, Arity, _, _)
	;	is_callable_with(_,Goal)
	)),
%	once(is_callable_with(_,Goal)),
	% allow the goal to recursively expand
	(	step_expand(Goal, Expanded) -> true
	;	Expanded = Goal
	).

expand_term_1(Goal, Expanded) :-
	% expand the rule head (Goal) into terminal symbols (the rule body)
	(	expand_rule(Goal, Clauses) -> true
	% handle the case that a predicate is referred to that wasn't asserted before
	;	throw(expansion_failed(Goal))
	),
	% wrap different clauses into ';'
	semicolon_list(Disjunction, Clauses),
	mongolog_expand(Disjunction, Expanded).

%%
expand_rule(Goal, Terminals) :-
	% ground goals do not require special handling for variables
	% as done in the clause below. So this clause here is simpler.
	ground(Goal),!,
	% unwrap goal term into functor and arguments.
	Goal =.. [Functor|Args],
	% findall rules with matching functor and arguments
	findall(X, mongolog_rule(_,Functor, Args, X), TerminalClauses),
	(	TerminalClauses \== []
	->	Terminals = TerminalClauses
	% if TerminalClauses==[] it means that either there is no such rule
	% in which case expand_rule fails, or there is a matching rule, but
	% the arguments cannot be unified with the ones provided in which
	% case expand_rule succeeds with a pipeline [fail] that allways fails.
	;	(	once(mongolog_rule(_,Functor,_,_)),
			Terminals=[fail]
		)
	).

expand_rule(Goal, Terminals) :-
	% unwrap goal term into functor and arguments.
	Goal =.. [Functor|Args],
	% find all asserted rules matching the functor
	findall([Args0,Terminals0],
			(	mongolog_rule(_, Functor, Args0, Terminals0),
				unifiable(Args0, Args, _)
			),
			Clauses),
	Clauses \== [],
	expand_rule(Args, Clauses, Terminals).

% prepend pragma call that unifies "child" and "parent" arguments
expand_rule(_, [], []) :- !.
expand_rule(ParentArgs,
		[[ChildArgs,Terminals]|Xs],
		[Expanded|Ys]) :-
	Expanded=[
		% "touch" variables in ParentArgs
		touch(ParentArgs),
		% unify ChildArgs and ParentArgs
		pragma(=(ChildArgs,ParentArgs)),
		Terminals
	],
	expand_rule(ParentArgs, Xs, Ys),
	!.

%
step_expand(ask(Goal), ask(Expanded)) :-
	mongolog_expand(Goal, Expanded).

% 
has_list_head([]) :- !.
has_list_head([_|_]).


