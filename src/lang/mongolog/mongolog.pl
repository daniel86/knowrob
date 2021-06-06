:- module(mongolog,
	[ mongolog_call(t),
	  mongolog_call(t,+),
	  is_mongolog_term/1
	]).
/** <module> Compiling goals into aggregation pipelines.

@author Daniel Beßler
@license BSD
*/

% TODO: better support for recursion
%		- cycles in views are not allowed
%		- but graphLookup can be used for transitive relations
%       - unwind can be used to iterate over a list

:- use_module(library('semweb/rdf_db'),
	    [ rdf_meta/1, rdf_global_term/2 ]).
:- use_module(library('db/mongo/client')).

:- use_module('variables').
:- use_module('stages/aggregation', [ aggregate/4 ]).
:- use_module('stages/bulk_operation', [ bulk_operation/1 ]).

%% set of registered query commands.
:- dynamic step_command/1.
%% implemented by query commands to compile query documents
:- multifile step_compile/3, step_compile1/3.

:- rdf_meta(step_compile(t,t,t)).
:- rdf_meta(step_compile1(t,t,t)).

%% is_mongolog_term(+PredicateIndicator) is semidet.
%
% True if PredicateIndicator corresponds to a known mongolog predicate.
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
	mongolog_compile(Goal, CompilerOutput, Vars, Context),
	memberchk(document(Doc), CompilerOutput),
	% get name of collection on which the aggregate operation
	% should be performed. This is basically the first collection
	% which is explicitely used in a step of the goal.
	ignore(memberchk(input_collection(Coll), CompilerOutput)),
	once((ground(Coll);Coll=one)),
	% TODO: below really needed?
	option(global_vars(GlobalVars), Context, []),
	append(Vars, GlobalVars, Vars1),
	list_to_set(Vars1,Vars2),
	% run the pipeline
	% TODO: split goal at assert's such that they are available in the rest of the query
	aggregate(Coll, Doc, Vars2, Result),
	bulk_operation(Result).


%% mongolog_compile(+Term, -CompilerOutput, -Variables, +Context) is semidet.
%
% Translate a goal into an aggregation pipeline.
% Goal may be a compound term using the various predicates
% supported by mongolog.
% The goal must not but can be expanded before (see kb_expand/3).
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
query_compile1(Terminals, Output0, Vars, Context) :-
	% get global variables supplied by the call context and add it
	% to the compile context
	option(global_vars(GlobalVars), Context, []),
	%
	DocVars=[['g_assertions',_]|GlobalVars],
	compile_terms(Terminals, DocVars->Vars, Output, Context),
	memberchk(document(Doc0), Output),
	%memberchk(variables(StepVars), Output),
	Doc=[['$set',['g_assertions',array([])]] | Doc0],
	merge_options([document(Doc)],Output,Output0).

%%
compile_terms(Goal, Vars, Output, Context) :-
	\+ is_list(Goal), !,
	compile_terms([Goal], Vars, Output, Context).

% FIXME: redundant with compile_expanded_terms
compile_terms([], V0->V0, [document([]),variables([])], _) :- !.
compile_terms([X|Xs], V0->Vn, Output, Context) :-
	%
	compile_term(X,  V0->V1, Output0, Context),
	memberchk(document(Pipeline_x), Output0),
	memberchk(variables(StepVars0), Output0),
	option(input_collection(InCollection0), Output0, _),
	%
	compile_terms(Xs, V1->Vn, Output1, Context),
	memberchk(document(Pipeline_xs), Output1),
	memberchk(variables(StepVars1), Output1),
	%
	append(Pipeline_x, Pipeline_xs, Pipeline),
	append(StepVars0, StepVars1, StepVars),
	(	ground(InCollection0) -> InCollection = InCollection0
	;	ignore(option(input_collection(InCollection), Output1))
	),
	Output=[
		document(Pipeline),
		variables(StepVars),
		input_collection(InCollection)
	].

%% Compile a single command (Term) into an aggregate pipeline (Doc).
compile_term(Term, V0->V1, Output, Context) :-
	% TODO: do not depend on lang_query
	lang_query:kb_expand(Term, Expanded),
	compile_expanded_terms(Expanded, V0->V1, Output, Context).

%%
compile_expanded_terms(Goal, Vars, Output, Context) :-
	\+ is_list(Goal), !,
	compile_expanded_terms([Goal], Vars, Output, Context).

compile_expanded_terms([], V0->V0, [document([]),variables([])], _) :- !.
compile_expanded_terms([Expanded|Rest], V0->Vn, Output, Context) :-
	compile_expanded_term(Expanded, V0->V1, Output0, Context),
	memberchk(document(Doc0), Output0),
	memberchk(variables(StepVars0), Output0),
	ignore(option(input_collection(InCollection0), Output0)),
	% toggle on input_assigned flag in compile context
	(	(ground(InCollection0), \+ option(input_assigned,Context))
	->	merge_options([input_assigned],Context,Context1)
	;	Context1=Context
	),
	compile_expanded_terms(Rest, V1->Vn, Output1, Context1),
	memberchk(document(Doc1), Output1),
	memberchk(variables(StepVars1), Output1),
	%
	append(Doc0, Doc1, Doc),
	append(StepVars0, StepVars1, StepVars),
	(	ground(InCollection0) -> InCollection = InCollection0
	;	ignore(option(input_collection(InCollection), Output1))
	),
	Output=[
		document(Doc),
		variables(StepVars),
		input_collection(InCollection)
	].
	
compile_expanded_term(List, Vars, Output, Context) :-
	is_list(List),!,
	compile_expanded_terms(List, Vars, Output, Context).
	
compile_expanded_term(Expanded, V0->V1, Output0, Context) :-
	% create inner context
	merge_options([outer_vars(V0)], Context, InnerContext),
	% and finall compile expanded terms
	once(step_compile1(Expanded, InnerContext, Output)),
	memberchk(document(Doc), Output),
	memberchk(variables(StepVars), Output),
	list_to_set(StepVars, StepVars_unique),
	% merge StepVars with variables in previous steps (V0)
	merge_substitutions(StepVars_unique, V0, V1),
	% create a field for each variable that was not referred to before
	% TODO: do not do this if the variable is assigned anyway
	findall([VarKey,[['type',string('var')], ['value',string(VarKey)]]],
		(	(	option(input_assigned,Context)
			->	InputKeys=[]
			;	option(input_keys(InputKeys), Output, [])
			),
			member([VarKey,_], StepVars_unique),
			\+ memberchk([VarKey,_], V0),
			% also skip any keys marked as input as these are coming from the
			% input collection
			\+ memberchk(VarKey, InputKeys)
		),
		VarDocs0
	),
	% make sure there are no duplicate entries as these would cause
	% compilation failure in a single $set!
	list_to_set(VarDocs0,VarDocs),
	(	VarDocs==[]
	->	Pipeline=Doc
	;	Pipeline=[['$set', VarDocs]|Doc]
	),
	merge_options(
		[ document(Pipeline),
		  variables(StepVars_unique)
		],
		Output, Output0).

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

step_compile(stepvars(_), _, []) :- true.

step_command(ask).
step_command(stepvars).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- rdf_meta(test_call(t,?,t)).

%%
test_call(Goal, Var, Value) :-
	WithSet=(','(assign(Var,Value), Goal)),
	mongolog_call(WithSet).

