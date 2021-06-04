:- module(mongolog,
	[ mongolog_call(t),
	  mongolog_call(t,+),
	  mongolog_rule_assert(+,+,+,+),
	  is_mongolog_predicate(+)
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

:- use_module('stages/aggregation', [ aggregate/4 ]).
:- use_module('stages/bulk_operation', [ bulk_operation/1 ]).

%% set of registered query commands.
:- dynamic step_command/1.
%% implemented by query commands to compile query documents
:- multifile step_compile/3, step_compile1/3.

:- rdf_meta(step_compile(t,t,t)).
:- rdf_meta(step_compile1(t,t,t)).


%% mongolog_rule_assert(+Module, +Functor, +Args, +Pipeline) is det.
%
mongolog_rule_assert(_Module, Functor, Args, Zs) :-
	Goal =.. [Functor|Args],
%	writeln(compile_view(Goal)),
	length(Args, Arity),
	atomic_list_concat([Functor, Arity], '_', ViewName),
	% compile an aggregation pipeline
	current_scope(QScope),
%once(( Functor==is_resource -> gtrace ; true )),
	mongolog:mongolog_compile(Zs,
		CompilerOutput,
		Vars,
		[ scope(QScope)
		%, prune_unreferenced(false)
		, compile_mode(view)
		]),
	memberchk(document(Pipeline), CompilerOutput),
%	memberchk(variables(Vars), CompilerOutput),
	option(input_collection(ViewOnCollection), CompilerOutput, _),
	once((ground(ViewOnCollection);ViewOnCollection=one)),
	% lookup variable keys used by the predicate and re-use
	% the same keys.
	findall(K,
		(	member(Arg,Args),
			once((
				member([K,X],Vars),
				X == Arg
			))
		),
		Fields),
	% lookup fields with rdfs values
	findall(K,
		(	member(K,Fields),
			atom_concat(K,'_s',K0),
			memberchk([K0,_],Vars)
		),
		RDFSFields),
	!,
	findall([K,Condition],
		(	(	member(K,Fields), Condition=integer(1)	)
		;	(	member(K0,RDFSFields),
				atom_concat(K0,'_s',K),
				atom_concat('$',K,Kv),
				atom_concat(Kv,'.type',Kt),
				Condition=['$cond',[
					[if,   ['$eq', array([string(Kt), string('var')])]],
					[then, string('$$REMOVE')],
					[else, string(Kv)]
				]]
			)
		;	(	K='v_scope', Condition=integer(1)	)
		),
		Projection),
	append(Pipeline, [['$project',Projection]], Pipeline0),
	% create a view for the head predicate
%	mng_one_db(DBName, CollectionName),
%	mng_view_create(DBName, CollectionName, ViewName, array(Pipeline0)),
	mng_db_name(DBName),
	mng_view_create(DBName, ViewOnCollection, ViewName, array(Pipeline0)),
	% add head as an IDB predicate in mongolog
	(	mongolog_database:mongolog_predicate(Goal, _, _)
	->	true
	;	mongolog_add_predicate(Functor, Fields,
			[ type(idb),
			  collection(ViewName),
			  indices([]),
			  rdfs_fields(RDFSFields)
			])
	).

mongolog_rule_assert(Module, Functor, Args, _Zs) :-
	writeln(mongolog_rule_assert_failed(Module, Functor, Args)).


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


%% is_mongolog_predicate(+PredicateIndicator) is semidet.
%
% True if PredicateIndicator corresponds to a known mongolog predicate.
%
is_mongolog_predicate((/(Functor,_Arity))) :-
	!, step_command(Functor).
	
is_mongolog_predicate(Goal) :-
	compound(Goal),!,
	Goal =.. [Functor|_Args],
	step_command(Functor).
	
is_mongolog_predicate(Functor) :-
	atom(Functor),!,
	step_command(Functor).


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
	%
	option(user_vars(UserVars), Context, []),
	option(global_vars(GlobalVars), Context, []),
	append(Vars, UserVars, Vars1),
	append(Vars1, GlobalVars, Vars2),
	list_to_set(Vars2,Vars3),
	% run the pipeline
	% TODO: split goal at assert's such that they are available in the rest of the query
	aggregate(Coll, Doc, Vars3, Result),
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
	DocVars=[['g_assertions',_]],
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
	%option(input_collection(InputCollection), Output, _),
	% merge StepVars with variables in previous steps (V0)
	list_to_set(StepVars, StepVars_unique),
	append(V0, StepVars_unique, V11),
	list_to_set(V11, V1),
	% create a field for each variable that was not referred to before
	(	option(input_assigned,Context) -> InputKeys=[]
	;	option(input_keys(InputKeys), Output, [])
	),
	findall([VarKey,[['type',string('var')], ['value',string(VarKey)]]],
		(	member([VarKey,_], StepVars_unique),
			\+ member([VarKey,_], V0),
			% also skip any keys marked as input as these are coming from the
			% input collection
			\+ member(VarKey, InputKeys)
		),
		VarDocs0
	),
	% make sure there are no duplicate entries as these would cause
	% compilation failure in a single $set!
	list_to_set(VarDocs0,VarDocs),
	(	VarDocs=[] -> Pipeline=Doc
	;	Pipeline=[['$set', VarDocs]|Doc]
	),
	merge_options(
		[ document(Pipeline), variables(StepVars_unique) ],
		Output, Output0).

%%
step_compile1(Step, Ctx, [document(Doc), variables(StepVars)]) :-
	% first compute stepvars and extend context.
	% this is to avoid that different keys are assigned
	% to the same variable
	step_vars(Step, Ctx, StepVars),
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

%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% VARIABLES in queries
%%%%%%%%%%%%%%%%%%%%%%%

% read all variables referred to in Step into list StepVars
step_vars(Step, Ctx, StepVars) :-
	(	bagof(Vs, goal_var(Step, Ctx, Vs), StepVars)
	;	StepVars=[]
	),!.

%%
goal_var(Var, Ctx, [Key,Var]) :-
	var(Var),!,
	var_key(Var, Ctx, Key).

goal_var(List, Ctx, Var) :-
	is_list(List),!,
	member(X,List),
	goal_var(X, Ctx, Var).

goal_var(Dict, Ctx, Var) :-
	is_dict(Dict),!,
	get_dict(Key, Dict, Value),
	(	goal_var(Key,Ctx,Var)
	;	goal_var(Value,Ctx,Var)
	).

goal_var(Compound, Ctx, Var) :-
	compound(Compound),!,
	Compound =.. [_Functor|Args],
	member(Arg,Args),
	goal_var(Arg, Ctx, Var).

%%
context_var(Ctx, [Key,ReferredVar]) :-
	option(scope(Scope), Ctx),
	% NOTE: vars are resolved to keys in scope already!
	%       e.g. `Since == =<(string($v_235472))`
	time_scope(Since, Until, Scope),
	member(X, [Since, Until]),
	mng_strip(X, _, string, Stripped),
	atom(Stripped),
	atom_concat('$', Key, Stripped),
	once((
		(	option(outer_vars(Vars), Ctx)
		;	option(disj_vars(Vars), Ctx)
		),
		member([Key,ReferredVar],Vars)
	)).

%%
get_var(Term, Ctx, [Key,Var]) :-
	term_variables(Term,Vars),
	member(Var,Vars),
	var_key(Var, Ctx, Key).

%%
% Map a Prolog variable to the key that used to
% refer to this variable in mongo queries.
%
var_key(Var, Ctx, Key) :-
	var(Var),
	% TODO: can this be done better then iterating over all variables?
	%		- i.e. by testing if some variable is element of a list
	%		- member/2 cannot be used as it would unify each array element
	(	option(global_vars(Vars), Ctx, [])
	;	option(outer_vars(Vars), Ctx, [])
	;	option(step_vars(Vars), Ctx, [])
	;	option(disj_vars(Vars), Ctx, [])
	),
	member([Key,ReferredVar],Vars),
	ReferredVar == Var,
	!.
var_key(Var, _Ctx, Key) :-
	var(Var),
	%term_to_atom(Var,Atom),
	%atom_concat('v',Atom,Key).
	gensym('v_', Key).

%%
% yield either the key of a variable in mongo,
% or a typed term for some constant value provided
% in the query.
%
var_key_or_val(In, Ctx, Out) :-
	mng_strip_operator(In, '=', In0),
	var_key_or_val0(In0, Ctx, Out).
	
var_key_or_val0(In, Ctx, string(Key)) :-
	mng_strip_type(In, _, In0),
	var_key(In0, Ctx, Out),
	atom_concat('$',Out,Key),
	!.

var_key_or_val0(In, _Ctx, Out) :-
	atomic(In),!,
	once(get_constant(In,Out)).

var_key_or_val0(In, Ctx, array(L)) :-
	is_list(In),!,
	findall(X,
		(	member(Y,In),
			var_key_or_val0(Y, Ctx, X)
		),
		L).

var_key_or_val0(:(NS,Atom), _, _) :-
	throw(unexpanded_namespace(NS,Atom)).

var_key_or_val0(TypedValue, _Ctx, TypedValue) :-
	compound(TypedValue),
	TypedValue =.. [Type|_],
	mng_client:type_mapping(Type,_),
	!.

var_key_or_val0(Term, Ctx, [
		['type', string('compound')],
		['value', [
			['functor', string(Functor)],
			['args', array(Vals)]
		]]
	]) :-
	mng_strip_type(Term, term, Stripped),
	compound(Stripped),
	Stripped =.. [Functor|Args],
	findall(X,
		(	member(Y,Args),
			var_key_or_val0(Y, Ctx, X)
		),
		Vals).

var_key_or_val1(In, Ctx, Out) :-
	var_key_or_val(In, Ctx, X),
	(	(X=string(Str), atom(Str), atom_concat('$',_,Str))
	->	(X=string(Str), atom_concat('$',Str,Y), Out=string(Y))
	;	Out=X
	).

%% in case of atomic in query
get_constant(Value, double(Value)) :- number(Value).
get_constant(true,  bool(true)).
get_constant(false, bool(false)).
get_constant(Value, string(Value)) :- atom(Value).
get_constant(Value, string(Value)) :- string(Value).


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- rdf_meta(test_call(t,?,t)).

%%
test_call(Goal, Var, Value) :-
	WithSet=(','(assign(Var,Value), Goal)),
	mongolog_call(WithSet).

