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

% TODO: some clauses must be inline and cannot be views
%		- findall: findall in views is problematic as the list content depends on instantiations
%         of variables in Goal. findall can only be used in views if non of the variables
%         in Goal are arguments of the rule head.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% - RDFS generalizations can only be used under some circumstances
%    - e.g. same_as does not apply to super classes
%    - so what is the criterion?
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library('semweb/rdf_db'),
	    [ rdf_meta/1, rdf_global_term/2 ]).
:- use_module(library('db/mongo/client')).

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
	query_1(Coll, Doc, Vars3).

query_1(Coll, Pipeline, Vars) :-
	% get DB for cursor creation. use collection with just a
	% single document as starting point.
	%mng_one_db(DB, Coll),
	mng_db_name(DB),
	% run the query
	setup_call_cleanup(
		% setup: create a query cursor
		mng_cursor_create(DB, Coll, Cursor),
		% call: find matching document
		(	mng_cursor_aggregate(Cursor, ['pipeline',array(Pipeline)]),
			query_2(Cursor, Vars)
		),
		% cleanup: destroy cursor again
		mng_cursor_destroy(Cursor)
	).

%%
query_2(Cursor, Vars) :-
	mng_cursor_materialize(Cursor, Result),
	unify_(Result, Vars),
	assert_documents(Result).

%%
assert_documents(Result) :-
	mng_get_dict('g_assertions', Result, array(Assertions)),
	once((setof(X,
		(	member(A,Assertions),
			member(collection-string(X),A)
		),
		Collections
	);Collections=[])),
	assert_documents0(Collections, Assertions).

assert_documents0([],_) :- !.
assert_documents0([Coll|Next], Assertions) :-
	findall(Doc,
		(	member(A,Assertions),
			memberchk(collection-string(Coll),A),
			memberchk(documents-array(Docs),A),
			member(Doc,Docs)
		),
		Docs),
	assert_documents1(array(Docs), Coll),
	assert_documents0(Next, Assertions).

assert_documents1(array([]), _) :- !.
assert_documents1([], _) :- !.
assert_documents1(array(Docs), Key) :-
	% NOTE: the mongo client currently returns documents as pairs A-B instead of
	%       [A,B] which is required as input.
	% TODO: make the client return docs in a format that it accepts as input.
	maplist(format_doc, Docs, Docs0),
	maplist(bulk_operation, Docs0, BulkOperations),
	mng_get_db(DB, Coll, Key),
	mng_bulk_write(DB, Coll, BulkOperations).

%%
format_doc([], []) :- !.
format_doc([X-Y0|Rest0], [[X,Y1]|Rest1]) :-
	!,
	format_doc(Y0,Y1),
	format_doc(Rest0,Rest1).
format_doc(X, X).

%%
bulk_operation(Doc, remove([['_id',id(ID)]])) :-
	memberchk(['delete',bool(Val)],Doc),!,
	memberchk(['_id',id(ID)],Doc),
	once((Val==true ; Val==1)).

bulk_operation(Doc0, update(Selector,['$set', Update])) :-
	select(['_id',id(ID)],Doc0,Update),!,
	Selector=[['_id',id(ID)]].

bulk_operation(Doc, insert(Doc)).

%%
% unify variables.
%
unify_(Result, Vars) :-
	unify_0(Result, Vars, Vars).

unify_0(_, _, []) :- !.
unify_0(Doc, Vars, [[VarKey, Term]|Xs]) :-
	% it is ignored here if some variables referred
	% to are not properly grounded.
	% this can happen e.g. in expressions such as (A=a;B=b)
	% where the first solution has grounded A but not B.
	(	ground(Term)
	->	once(unify_grounded(Doc, [VarKey, Term]))
	;	ignore(unify_1(Doc, Vars, [VarKey, Term]))
	),
	unify_0(Doc, Vars, Xs).

unify_grounded(Doc, [VarKey, Term]) :-
	% variable was unified in pragma command
	% make sure it did not get another grounding in the query
	mng_get_dict(VarKey, Doc, TypedValue),
	!,
	mng_strip_type(TypedValue, _, Value),
	% ignore if value in the document is a variable
	(	Value=_{ type: string(var), value: _ }
	% try to unify
	;	Term=Value
	% special case for number comparison, e.g. `5.0 =:= 5`
	;	(	number(Term),
			number(Value),
			Term=:=Value
		)
	).
unify_grounded(_, [_, _]) :- !.

unify_1(_, _, ['_id', _]).

unify_1(Doc, Vars, [VarKey, Val]) :-
	mng_get_dict(VarKey, Doc, TypedValue),
	unify_2(TypedValue, Vars, Val).

%%
unify_2(string(In), _Vars, X) :-
	% handle case that variable is wrapped in term/1.
	% if this is the case then convert input string to term.
	nonvar(X),
	X=term(Out),!,
	atom_to_term_(In, Out).

unify_2(array(In), Vars, Out) :-
	% a variable was instantiated to a list
	!,
	unify_array(In, Vars, Out).

unify_2([K-V|Rest], Vars, Out) :-
	!,
	dict_pairs(Dict,_,[K-V|Rest]),
	unify_2(Dict, Vars, Out).

unify_2(_{
		type: string(var),
		value: string(VarKey)
	}, Vars, Out) :-
	% a variable was not instantiated
	!,
	memberchk([VarKey, VarVal], Vars),
	Out = VarVal. 

unify_2(_{
		type: string(compound),
		value: Val
	}, Vars, Out) :-
	% a variable was instantiated to a compound term
	!,
	unify_2(Val, Vars, Out).

unify_2(_{
		functor: string(Functor),
		args: Args
	}, Vars, Out) :-
	!,
	unify_2(Args, Vars, Args0),
	Out =.. [Functor|Args0].

unify_2(TypedValue, _, Value) :-
	% a variable was instantiated to an atomic value
	mng_strip_type(TypedValue, _, Value).

%%
unify_array([], _, []) :- !.
unify_array([X|Xs], Vars, [Y|Ys]) :-
	unify_2(X, Vars, Y),
	unify_array(Xs, Vars, Ys).

%%
atom_to_term_(Atom, Term) :-
	% try converting atom stored in DB to a Prolog term
	catch(term_to_atom(Term,Atom), _, fail),
	!.

atom_to_term_(Atom, Term) :-
	% vectors maybe stored space-separated.
	% @deprecated
	atomic_list_concat(Elems, ' ', Atom),
	maplist(atom_number, Elems, Term),
	!.

atom_to_term_(Atom, _) :-
	throw(error(conversion_error(atom_to_term(Atom)))).


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

%%
% pragma(Goal) is evaluated compile-time by calling
% the Goal. This is usually done to unify variables
% used in the aggregation pipeline from the compile context.
%
%step_compile(pragma(Goal), _, []) :-
%	call(Goal).

step_compile1(pragma(Goal), _, [document([]), variables(StepVars)]) :-
	% ignore vars referred to in pragma as these are handled compile-time.
	% only the ones also referred to in parts of the query are added to the document.
	StepVars=[],
	call(Goal).

step_compile(stepvars(_), _, []) :- true.

step_command(ask).
step_command(pragma).
step_command(stepvars).

%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% QUERY DOCUMENTS
%%%%%%%%%%%%%%%%%%%%%%%

%%
add_assertions(Docs, Coll,
	['$set', ['g_assertions',['$concatArrays', array([
		string('$g_assertions'),
		array([[
			['collection', string(Coll)],
			['documents', Docs]
		]])
	])]]]).

add_assertion(Doc, Coll, Step) :-
	add_assertions(array([Doc]), Coll, Step).

%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% VARIABLES in queries
%%%%%%%%%%%%%%%%%%%%%%%

%%
add_assertion_var(StepVars, [['g_assertions',_]|StepVars]).

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

%%
% True iff Arg has been referred to in the query before.
% That is, Arg has been added to the "outer variables"
% of the compile context.
%
is_referenced(Arg, Ctx) :-
	option(outer_vars(OuterVars),Ctx),
	var_key(Arg, Ctx, Key),
	memberchk([Key,_], OuterVars).

%%
all_ground(Args, Ctx) :-
	forall(
		member(Arg,Args),
		(	is_instantiated(Arg, Ctx) -> true
		;	throw(error(instantiation_error))
		)
	).

is_instantiated(Arg, Ctx) :-
	mng_strip_variable(Arg, Arg0),
	term_variables(Arg0, Vars),
	forall(
		member(Var, Vars),
		is_referenced(Var, Ctx)
	).


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- rdf_meta(test_call(t,?,t)).

%%
test_call(Goal, Var, Value) :-
	WithSet=(','(assign(Var,Value), Goal)),
	mongolog_call(WithSet).

