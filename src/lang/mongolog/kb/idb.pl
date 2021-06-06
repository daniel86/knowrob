:- module(mongolog_idb,
		[ is_idb_predicate/1,
		  idb_create/3,
		  idb_drop/1,
		  idb_assert/4
		]).

:- use_module('../mongolog').
:- use_module('../aggregation/lookup').
:- use_module('db_predicate').


%% is_idb_predicate(+Indicator) is semidet.
%
%
is_idb_predicate(Predicate) :-
	db_predicate(Predicate, _, Opts),
	option(type(idb), Opts).

%% idb_create(+Functor, +Fields, +Opts) is det.
%
% Same as db_predicate_create/3 with idb-specific options.
%
idb_create(Functor, Fields, Opts) :-
	select_option(type(_),Opts,Opts0,_),
	select_option(indices(_),Opts0,Opts1,_),
	db_predicate_create(Functor, Fields,
		[ type(idb),
		  indices([])
		| Opts1
		]).

%% idb_drop(+Indicator) is det.
%
% Same as db_predicate_drop/1.
%
idb_drop(Indicator) :-
	db_predicate_drop(Indicator).


%% idb_assert(+Module, +Functor, +Args, +Clauses) is semidet.
%
%
idb_assert(_Module, Functor, Args, Clauses) :-
	Goal =.. [Functor|Args],
%	writeln(compile_view(Goal)),
	length(Args, Arity),
	atomic_list_concat([Functor, Arity], '_', ViewName),
	% compile an aggregation pipeline
	current_scope(QScope),
%once(( Functor==findall_test2 -> gtrace ; true )),
	head_vars(Args, HeadVars),
	mongolog:mongolog_compile(
		Clauses,
		CompilerOutput,
		Vars,
		[ scope(QScope)
		, compile_mode(view)
		, head_functor(Functor)
		, head_vars(HeadVars)
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
	mng_db_name(DBName),
	mng_view_create(DBName, ViewOnCollection, ViewName, array(Pipeline0)),
	% add head as an IDB predicate in mongolog
	(	is_db_predicate(Goal) -> true
	;	idb_create(Functor, Fields,
			[ collection(ViewName),
			  rdfs_fields(RDFSFields)
			])
	).

idb_assert(Module, Functor, Args, _Zs) :-
	length(Args, Arity),
	writeln(not_viewable(('/'((:(Module, Functor)), Arity)))).

%%
mongolog:step_compile1(Term, Ctx, Output) :-
	is_idb_predicate(Term),!,
	db_predicate_compile(Term, Ctx, Output).

%%
head_vars([], []) :- !.
head_vars([V|Xs],[[K,V]|Ys]) :-
	gensym('v_', K),
	head_vars(Xs,Ys).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- use_module('../mongolog_tests').

:- begin_mongolog_tests('mongolog_idb',
		[ % EDB facts
		  woman(mia), woman(jola),
		  loves(fred,mia), loves(jola,fred),
		  % IDB clauses
		  ( findall_test(X1)       :- findall(Y1, woman(Y1), X1) ),
		  ( loved_woman(X2)        :- woman(X2), loves(_,X2) ),
		  ( test_nested_rule1(X3)  :- assign(X3,2) ),
		  ( test_nested_rule1(X4)  :- assign(X4,3) ),
		  ( test_nested_rule(X5)   :- test_nested_rule1(Y5), X5 is Y5 + 2 ),
		  % not viewable because X1 appears in findall goal
		  ( findall_test1(X6,Y6)   :- findall(Z6, loves(Z6,X6), Y6) ),
		  % viewable because call context instantiates X1 in above clause
		  ( findall_test2(Y7)      :- findall_test1(mia, Y7) ),
		  % ask-rule with partially instantiated arg and multiple clauses
		  ( test_shape1(mesh(X8))   :- =(X8,foo) ),
		  ( test_shape1(sphere(X9)) :- =(X9,5.0) ),
		  ( test_shape2(X10)        :- ( =(X10,mesh(foo)) ; =(X10,sphere(5.0)) ) ),
		  ( test_shape3(X11)        :- ( test_shape1(X11) ; =(X11,mesh(bar)) ) )
		]).

test('edb-conjunction') :-
	findall(X, mongolog_call(loved_woman(X)), Xs),
	assert_equals(Xs, [mia]).

test('findall(edb)') :-
	findall(As, mongolog_call(findall_test(As)), X),
	assert_equals(X, [[mia,jola]]).

test('idb-body') :-
	findall(X, mongolog_call(test_nested_rule(X)), Xs),
	assert_equals(Xs, [4.0,5.0]).

test('viewable-findall') :-
	% findall_test1 is not viewable because head var appears in findall goal
	% findall_test2 is viewable as it instantiates this var
	assert_true(is_mongolog_term(findall_test2/1)),
	assert_false(is_mongolog_term(findall_test1/2)).

test('test_shape1(mesh(foo))') :-
	assert_true(mongolog_call(test_shape1(mesh(foo)))).

test('test_shape1(mesh(X))') :-
	findall(X, mongolog_call(test_shape1(mesh(X))), Xs),
	assert_true(length(Xs,1)),
	assert_true(ground(Xs)),
	assert_true(memberchk(foo, Xs)).

test('test_shape1(X)') :-
	findall(X, mongolog_call(test_shape1(X)), Xs),
	assert_true(length(Xs,2)),
	assert_true(ground(Xs)),
	assert_true(memberchk(mesh(foo), Xs)),
	assert_true(memberchk(sphere(5.0), Xs)).

test('test_shape2(mesh(foo))') :-
	assert_true(mongolog_call(test_shape2(mesh(foo)))).

test('test_shape2(mesh(X))') :-
	findall(X, mongolog_call(test_shape2(mesh(X))), Xs),
	assert_true(length(Xs,1)),
	assert_true(ground(Xs)),
	assert_true(memberchk(foo, Xs)).

test('test_shape2(X)') :-
	findall(X, mongolog_call(test_shape2(X)), Xs),
	assert_true(length(Xs,2)),
	assert_true(ground(Xs)),
	assert_true(memberchk(mesh(foo), Xs)),
	assert_true(memberchk(sphere(5.0), Xs)).

test('test_shape3(mesh(foo))') :-
	assert_true(mongolog_call(test_shape3(mesh(foo)))).

test('test_shape3(mesh(X))') :-
	findall(X, mongolog_call(test_shape3(mesh(X))), Xs),
	assert_true(length(Xs,2)),
	assert_true(ground(Xs)),
	assert_true(memberchk(foo, Xs)),
	assert_true(memberchk(bar, Xs)).

test('test_shape3(X)') :-
	findall(X, mongolog_call(test_shape3(X)), Xs),
	assert_true(length(Xs,3)),
	assert_true(ground(Xs)),
	assert_true(memberchk(mesh(bar), Xs)),
	assert_true(memberchk(mesh(foo), Xs)),
	assert_true(memberchk(sphere(5.0), Xs)).

%
%test_recursive_rule(Left,Right) ?>
%	(	(Left=a,assign(X,b))
%	;	(Left=b,assign(X,c))
%	;	(Left=d,assign(X,c))
%	),
%	(	assign(Right,X)
%	;	test_recursive_rule(X,Right)
%	).
%
%test('test_recursive_rule(+,-)') :-
%	lang_query:flush_predicate(mongolog_unification),
%	findall(X, kb_call(test_recursive_rule(a,X)), Xs),
%	assert_equals(Xs, [b,c]).

:- end_mongolog_tests('mongolog_idb').

