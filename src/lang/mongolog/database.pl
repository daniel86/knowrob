:- module(mongolog_database,
		[ mongolog_add_predicate(+,+,+),
		  mongolog_drop_predicate(+)
		]).
/** <module> Storage of predicates in mongolog programs.

The following predicates are supported:

| Predicate    | Arguments |
| ---          | ---       |
| assert/1     | +Head |
| retractall/1 | +Head |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=dynpreds
@license BSD
*/

:- use_module('mongolog').
:- use_module('aggregation/lookup').
:- use_module('stages/bulk_operation').


%% Predicates that are stored in a mongo collection
:- dynamic mongolog_predicate/3.


%% query commands
:- mongolog:add_command(assert).
:- mongolog:add_command(retractall).


%% mongolog_predicate(+Term, -Fields, -Options) is semidet.
%
%
mongolog_predicate(Term, Fields, Options) :-
	compound(Term),
	Term =.. [Functor|Args],
	mongolog_predicate(Functor, Fields, Options),
	length(Args,Arity),
	length(Fields,Arity),
	!.


%% mongolog_add_predicate(+Functor, +Fields, +Options) is semidet.
%
% Register a predicate that stores facts in the database.
% Functor is the functor of a n-ary predicate, and Fields is
% a n-elemental list of keys associated to the different
% arguments of the predicate.
% Options is a list of optional paramers:
%
% | indices(List) | a list of indices passed to setup_collection/2 |
% | collection(Collection) | name of the collection where predicate is stored, default is to use the functor of the predicate |
%
% Current limitation: there cannot be predicates with the same functor,
% but different arity.
%
% @param Functor functor of the predicate
% @param Fields field names of predicate arguments
% @param Options option list
%
mongolog_add_predicate(Functor, Fields, _) :-
	mongolog_predicate(Functor, Args, _),
	length(Fields,Arity),
	length(Args,Arity),
	!,
	throw(permission_error(modify,database_predicate,Functor)).

mongolog_add_predicate(Functor, Fields, Options) :-
	setup_predicate_collection(Functor, Fields, Options),
	assertz(mongolog_predicate(Functor, Fields, Options)),
	mongolog:add_command(Functor).

%%
setup_predicate_collection(Functor, [FirstField|_], Options) :-
	% TODO support fields marked with -/+ here
	option(indices(Indices), Options, [[FirstField]]),
	(	Indices==[] -> true
	;	setup_collection(Functor, Indices)
	).


%% mongolog_drop_predicate(+Functor) is det.
%
% Delete all facts associated to predicate with
% given functor.
%
% @param Functor functor of the predicate
%
mongolog_drop_predicate(Functor) :-
	mng_get_db(DB, Collection, Functor),
	mng_drop(DB, Collection).

%%
lang_query:step_expand(project(Term), assert(Term)) :-
	mongolog_predicate(Term, _, Opts),
	option(type(edb), Opts, edb),
	!.

%%
mongolog:step_compile1(assert(Term), Ctx,
		[ document(Pipeline),
		  variables(StepVars)
		]) :-
	mongolog_predicate(Term, _, Opts),
	option(type(edb), Opts, edb),
	!,
	mongolog_predicate_assert(Term, Ctx, Pipeline, StepVars).

mongolog:step_compile1(retractall(Term), Ctx,
		[ document(Pipeline),
		  variables(StepVars)
		]) :-
	mongolog_predicate(Term, _, Opts),
	option(type(edb), Opts, edb),
	!,
	mongolog_predicate_retractall(Term, Ctx, Pipeline, StepVars).

mongolog:step_compile1(Term, Ctx,
		[ document(Pipeline),
		  variables(StepVars0),
		  input_collection(Collection),
		  input_keys(Fields)
		]) :-
	mongolog_predicate(Term, Fields, Opts),!,
	mongolog_predicate_call(Term, Ctx, Pipeline, StepVars, Collection),
	%
	add_array_vars(Term, Opts, Ctx, StepVars, StepVars0).

%
add_array_vars(Term, Opts, Ctx, StepVars, StepVars0) :-
	option(rdfs_fields(RDFSFields), Opts, []),
	RDFSFields \== [],
	bagof([K0,_],
		(	mongolog:goal_var(Term, Ctx, [K,_]),
			memberchk(K,RDFSFields),
			atom_concat(K,'_s',K0)
		),
		ArrayVars),
	!,
	append(StepVars, ArrayVars, StepVars0).
add_array_vars(_, _, _, StepVars, StepVars).

%%
mongolog_predicate_call(Term, Ctx, Pipeline, StepVars, Collection) :-
	mongolog_predicate_zip(Term, Ctx, Zipped, Ctx_pred, read),
	option(collection(Collection), Ctx_pred),
	option(step_vars(StepVars), Ctx_pred),
	unpack_compound(Zipped, Unpacked),
	%
	findall(InnerStep,
		match_predicate(Unpacked, Ctx, Ctx_pred, InnerStep),
		InnerPipeline),
	mongolog_predicate_call1(Unpacked, InnerPipeline, Ctx_pred, Pipeline).

%%
mongolog_predicate_call1(Unpacked, Matches, Ctx, Pipeline) :-
	% no need to perform a $lookup if input collection was assigned before
	\+ option(input_assigned,Ctx),!,
	findall(Step,
		(	member(Step,Matches)
		;	project_predicate1(Unpacked, Ctx, Step)
		),
		Pipeline).
	
mongolog_predicate_call1(Unpacked, InnerPipeline, Ctx, Pipeline) :-
	% option(input_assigned,Ctx),!,
	findall(Step,
		% look-up documents into 't_pred' array field
		(	lookup_predicate('t_pred', InnerPipeline, Ctx, Step)
		% unwind lookup results and assign variables
		;	Step=['$unwind', string('$t_pred')]
		;	project_predicate(Unpacked, Ctx, Step)
		;	Step=['$unset', string('t_pred')]
		),
		Pipeline).

%%
mongolog_predicate_retractall(Term, Ctx, Pipeline, StepVars) :-
	mongolog_predicate_zip(Term, Ctx, Zipped, Ctx_pred, write),
	option(collection(Collection), Ctx_pred),
	option(step_vars(StepVars), Ctx_pred),
	unpack_compound(Zipped, Unpacked),
	findall(InnerStep,
		(	match_predicate(Unpacked, Ctx, Ctx_pred, InnerStep)
		% retractall first performs match, then only projects the id of the document
		;	project_retract(InnerStep)
		),
		InnerPipeline),
	%
	findall(Step,
		% look-up documents into 't_pred' array field
		(	lookup_predicate('t_pred', InnerPipeline, Ctx_pred, Step)
		% add removed facts to assertions list
		;	add_assertions(string('$t_pred'), Collection, Step)
		;	Step=['$unset', string('t_pred')]
		),
		Pipeline
	).

%%
mongolog_predicate_assert(Term, Ctx, Pipeline, StepVars) :-
	mongolog_predicate_zip(Term, Ctx, Zipped, Ctx_pred, write),
	option(collection(Collection), Ctx_pred),
	option(step_vars(StepVars), Ctx_pred),
	% create a document
	findall([Field,Val],
		(	member([Field,Arg],Zipped),
			mongolog:var_key_or_val(Arg, Ctx_pred, Val)
		),
		PredicateDoc),
	% and add it to the list of asserted documents
	findall(Step,
		add_assertion(PredicateDoc, Collection, Step),
		Pipeline).

%%
%
mongolog_predicate_zip(Term, Ctx, Zipped, Ctx_zipped, ReadOrWrite) :-
	% get predicate fields and options
	mongolog_predicate(Term, ArgFields, Options),
	length(ArgFields,Arity),
	% get predicate functor and arguments
	Term =.. [Functor|Args],
	length(Args,Arity),
	% get the database collection of the predicate
	(	(option(collection(Collection), Options), ground(Collection))
	;	mng_get_db(_DB, Collection, Functor)
	),
	!,
	% try to re-use field name if a field in the document refers to a variable
	% in Term
%	predicate_vars(ArgFields, Args, PredVars),
%	merge_options([step_vars(PredVars)], Ctx, Ctx_tmp),
	% read variable in Term
	mongolog:step_vars(Term, Ctx, StepVars0),
	(	ReadOrWrite==read -> StepVars=StepVars0
	;	add_assertion_var(StepVars0, StepVars)
	),
	% add predicate options to compile context
	merge_options([
		step_vars(StepVars),
		collection(Collection)
	], Ctx, Ctx0),
	merge_options(Ctx0, Options, Ctx_zipped),
	% zip field names with predicate arguments
	zip(ArgFields, Args, Zipped).

%%
predicate_vars([], [], []) :- !.
predicate_vars([Key|Xs], [Arg|Ys], [[Key,Var]|Zs]) :-
	mng_strip_variable(Arg, Arg0),
	term_variables(Arg0, [Var]),!,
	predicate_vars(Xs, Ys, Zs).
predicate_vars([_|Xs], [_|Ys], Zs) :-
	predicate_vars(Xs, Ys, Zs).

%%
unpack_compound([], []) :- !.

unpack_compound([X|Xs], Unpacked) :-
	unpack_compound1(X, Unpacked0),
	unpack_compound(Xs, Unpacked1),
	append(Unpacked0, Unpacked1, Unpacked).

unpack_compound1([Field,Arg], Unpacked) :-
	!, unpack_compound1([Field,Arg,[]], Unpacked).

unpack_compound1([Field,Arg,Is], [[Field,Arg,Is]]) :-
	(ground(Arg);var(Arg)),!.

unpack_compound1([Field,Term,Is], [[FunctorField,Functor,Is]|ArgsUnpacked]) :-
	compound(Term),!,
	% compound term with free variables
	Term =.. [Functor|Args],
	atom_concat(Field,'.value.functor',FunctorField),
	arg_fields_(Field, Args, Is, 0, ArgFields),
	unpack_compound(ArgFields, ArgsUnpacked).

%%
arg_fields_(_, [], _, []) :- !.
arg_fields_(Field, [X|Xs], Is, Index, [[Field,X,[Index|Is]]|Rest]) :-
	Index1 is Index+1,
	arg_fields_(Field, Xs, Index1, Rest).

%%
set_nested_args(Unpacked, ['$set', NestedArgs]) :-
	findall(X,
		(	member([Key,_,Is], Unpacked),
			set_nested_arg(Key,Is,X)
		),
		NestedArgs0),
	NestedArgs0 \== [],
	list_to_set(NestedArgs0, NestedArgs).

set_nested_arg(Key, [I|Is], Arg) :-
	atomic_list_concat(['$',Key,'.value.args'], '', ThisVal),
	atomic_list_concat([Key,I],'_',Y),
	(	Arg=[Y, ['$arrayElemAt', array([string(ThisVal),integer(I)])]]
	;	set_nested_arg(Y, Is, Y)
	).

%% $lookup
%
lookup_predicate(Field, InnerPipeline, Ctx, ['$lookup', [
		['from', string(Collection)],
		['as', string(Field)],
		['let', LetDoc],
		['pipeline', array(InnerPipeline)]
	]]) :-
	option(collection(Collection), Ctx),
	option(step_vars(StepVars), Ctx),
	lookup_let_doc(StepVars, LetDoc).

%% $set
%
project_predicate(Unpacked, Ctx, Step) :-
	member([FieldPath0,Var,Is], Unpacked),
	mongolog:var_key(Var,Ctx,VarKey),
	atomic_list_concat([FieldPath0|Is],'_',FieldPath),
	atom_concat('$t_pred.', FieldPath, FieldQuery),
	% FIXME: some unneeded set's here. can we skip if not one of the predicate variable fields?
	Step=['$set', [VarKey, string(FieldQuery)]].

project_predicate1(Unpacked, Ctx, Step) :-
	member([FieldPath0,Var,Is], Unpacked),
	mongolog:var_key(Var,Ctx,VarKey),
	atomic_list_concat([FieldPath0|Is],'_',FieldPath),
	atom_concat('$', FieldPath, FieldQuery),
	% FIXME: some unneeded set's here. can we skip if not one of the predicate variable fields?
	Step=['$set', [VarKey, string(FieldQuery)]].

%%
project_retract(Step) :-
	(	Step=['$project',[['_id',int(1)]]]
	;	Step=['$set',['delete',bool(true)]]
	).

%% $match
%
match_predicate(Unpacked, OuterCtx, Ctx, Match) :-
	option(rdfs_fields(RDFSFields), Ctx, []),
	findall(MatchQuery,
		% first match what is grounded compile-time
		% TODO: conditional match can be avoided in case we know the variable
		%       is associated to a input document field!
		(	(	findall([DocKey, ValueQuery],
					(	member([DocKey0,Value,[]], Unpacked),
						(	memberchk(DocKey0, RDFSFields)
						->	atom_concat(DocKey0,'_s',DocKey)
						;	DocKey=DocKey0
						),
						mng_query_value(Value, ValueQuery)
					),
					MatchQuery),
				MatchQuery \== []
			)
		% next match variables grounded in call context
		;	(	member([DocKey,Var,[]], Unpacked),
				match_conditional(DocKey, Var, OuterCtx, Ctx, MatchQuery)
			)
		),
		MatchQueries
	),
	MatchQueries \== [],
	(	MatchQueries=[FirstMatch]
	->	Match=['$match', FirstMatch]
	;	Match=['$match', ['$and', array(MatchQueries)]]
	).

match_predicate(Unpacked, OuterCtx, Ctx, Match) :-
	% compound arguments with free variables need to be handled
	% separately because we cannot write path queries that
	% access array elements.
	set_nested_args(Unpacked,SetArgs),
	(	Match = SetArgs
	;	match_nested(Unpacked, OuterCtx, Ctx, Match)
	).

%%
match_nested(Unpacked, OuterCtx, Ctx, Match) :-
	nested_args(Unpacked, NestedArgs),
	match_predicate(NestedArgs, OuterCtx, Ctx, Match).

%%
nested_args([], []) :- !.

nested_args([[Key,Val,Is]|Xs], [[Key1,Val,[]]|Ys]) :-
	Is \== [],!,
	atomic_list_concat([Key|Is], '_', Key1),
	nested_args(Xs,Ys).

nested_args([_|Xs], Ys) :-
	nested_args(Xs,Ys).

%%
match_conditional(FieldKey, Arg, OuterCtx, Ctx, ['$expr', ['$or', array([
			% pass through if var is not grounded
			['$eq',       array([string(ArgType),   string('var')])],
			% else perform a match
			[ArgOperator, array([string(ArgValue), string(FieldQuery)])]
		])]]) :-
	option(rdfs_fields(RDFSFields), Ctx, []),
	% get the variable in Arg term
	mng_strip_variable(Arg, Arg0),
	term_variables(Arg0, [ArgVar]),!,
	% do not perform conditional match if variable was not referred to before
	mongolog:is_referenced(ArgVar, OuterCtx),
	mongolog:var_key(ArgVar, Ctx, ArgKey),
	% TODO: need to set let variables or use $ vs $$ conditional
	(	option(input_assigned,Ctx)
	->	atom_concat('$$',ArgKey,ArgValue)
	;	atom_concat('$',ArgKey,ArgValue)
	),
	atom_concat(ArgValue,'.type',ArgType),
	% get the operator
	mng_strip_operator(Arg0, Operator1, _Arg1),
	atom_concat('$',FieldKey,FieldQuery0),
	(	memberchk(FieldKey, RDFSFields)
	->	(
		% FIXME handle Operator1
		ArgOperator='$in',
		atom_concat(FieldQuery0,'_s',FieldQuery)
	);(
		mng_operator(Operator1, ArgOperator),
		FieldQuery=FieldQuery0
	)).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_database').

test('add_predicate') :-
	assert_true(mongolog_add_predicate(woman, [name], [[name]])),
	assert_true(mongolog_add_predicate(loves, [a,b], [[a],[b],[a,b]])).

test('assert(woman)') :-
	assert_true(mongolog_call(assert(woman(mia)))),
	assert_true(mongolog_call(assert(woman(jody)))).

test('woman(+)') :-
	assert_true(mongolog_call(woman(mia))),
	assert_true(mongolog_call(woman(jody))),
	assert_false(mongolog_call(woman(vincent))).

test('woman(-)') :-
	findall(X, mongolog_call(woman(X)), Xs),
	assert_unifies([_,_],Xs),
	assert_true(ground(Xs)),
	assert_true(memberchk(mia,Xs)),
	assert_true(memberchk(jody,Xs)).

test('retract(woman)') :-
	assert_true(mongolog_call(woman(jody))),
	assert_true(mongolog_call(retractall(woman(jody)))),
	assert_false(mongolog_call(woman(jody))).

test('assert(loves)') :-
	assert_true(mongolog_call(assert(loves(vincent,mia)))),
	assert_true(mongolog_call(assert(loves(marsellus,jody)))),
	assert_true(mongolog_call(assert(loves(pumpkin,honey_bunny)))).

test('loves(+,+)') :-
	assert_true(mongolog_call(loves(vincent,mia))),
	assert_true(mongolog_call(loves(marsellus,jody))),
	assert_false(mongolog_call(loves(mia,vincent))).

test('loves(+,-)') :-
	findall(X, mongolog_call(loves(vincent,X)), Xs),
	assert_unifies([_],Xs),
	assert_true(ground(Xs)),
	assert_true(memberchk(mia,Xs)).

test('loves(-,+)') :-
	findall(X, mongolog_call(loves(X,mia)), Xs),
	assert_unifies([_],Xs),
	assert_true(ground(Xs)),
	assert_true(memberchk(vincent,Xs)).

test('assert(shape)') :-
	assert_true(mongolog_add_predicate(shape, [name,term], [[name]])),
	assert_true(mongolog_call(assert(shape(obj1,sphere(1.0))))),
	assert_true(mongolog_call(assert(shape(obj3,sphere(2.0))))),
	assert_true(mongolog_call(assert(shape(obj2,box(1.0,2.0,3.0))))).

test('shape(+,+)') :-
	assert_true(mongolog_call(shape(obj1,sphere(1.0)))),
	assert_true(mongolog_call(shape(obj2,box(1.0,2.0,3.0)))),
	assert_false(mongolog_call(shape(obj1,cylinder(1.0)))),
	assert_false(mongolog_call(shape(obj2,sphere(1.0)))).

test('shape(+,-)') :-
	mongolog_call(shape(obj1,Term)),
	assert_equals(Term, sphere(1.0)).

test('shape(-,+)') :-
	findall(X, mongolog_call(shape(X,sphere(1.0))), Xs),
	assert_unifies([_],Xs),
	assert_true(ground(Xs)),
	assert_true(memberchk(obj1,Xs)).

test('shape(+,sphere(-))') :-
	findall(X, mongolog_call(shape(obj1,sphere(X))), Xs),
	assert_unifies([_],Xs),
	assert_true(ground(Xs)),
	assert_true(memberchk(1.0,Xs)).

test('edb_rule') :-
	lang_query:expand_ask_rule(loved_woman(A), (woman(A), loves(_,A)), _),
	lang_query:flush_predicate(user),
	%%
	findall(X, mongolog_call(loved_woman(X)), Xs),
	assert_equals(Xs, [mia]),
	assert_true(mongolog_drop_predicate(loved_woman_1)).

test('+Cond->assert(woman);assert(woman)') :-
	% TODO: move into disjunction test
	assert_false(mongolog_call(woman(bar))),
	assert_true(mongolog:test_call(
		(	Num > 5
		->	assert(woman(foo))
		;	assert(woman(bar))
		),
		Num, 4.5)),
	assert_true(mongolog_call(woman(bar))),
	assert_false(mongolog_call(woman(foo))).

test('findall_rule') :-
	% TODO: move into findall test
	lang_query:expand_ask_rule(findall_test(As), findall(A, woman(A), As), _),
	lang_query:flush_predicate(user),
	%%
	findall(As, mongolog_call(findall_test(As)), X),
	assert_equals(X, [[mia,bar]]),
	assert_true(mongolog_drop_predicate(findall_test_1)).

test('drop_database_predicate') :-
	assert_true(mongolog_drop_predicate(shape)),
	assert_true(mongolog_drop_predicate(woman)),
	assert_true(mongolog_drop_predicate(loves)).

:- end_tests('mongolog_database').
