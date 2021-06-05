:- module(mongolog_edb,
		[ is_edb_predicate/1,
		  edb_create/3,
		  edb_drop/1
		]).

:- use_module('../mongolog').
:- use_module('db_predicate').

%% is_edb_predicate(+Indicator) is semidet.
%
%
is_edb_predicate(Predicate) :-
	db_predicate(Predicate, _, Opts),
	option(type(edb), Opts).

%% edb_create(+Functor, +Fields, +Opts) is det.
%
% Same as db_predicate_create/3 with edb-specific options.
%
edb_create(Functor, Fields, Opts) :-
	select_option(type(_),Opts,Opts0,_),
	db_predicate_create(Functor, Fields,
		[ type(edb)
		| Opts0
		]).

%% edb_drop(+Indicator) is det.
%
% Same as db_predicate_drop/1.
%
edb_drop(Indicator) :-
	db_predicate_drop(Indicator).

%%
mongolog:step_compile1(Term, Ctx, Output) :-
	is_edb_predicate(Term),!,
	db_predicate_compile(Term, Ctx, Output).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_edb').

test('add_predicate') :-
	assert_true(edb_create(woman, [name], [[name]])),
	assert_true(edb_create(loves, [a,b], [[a],[b],[a,b]])).

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
	assert_true(edb_create(shape, [name,term], [[name]])),
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
	assert_true(idb_drop(loved_woman/1)).

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
	assert_true(idb_drop(findall_test/1)).

test('drop_database_predicate') :-
	assert_true(edb_drop(shape/2)),
	assert_true(edb_drop(woman/1)),
	assert_true(edb_drop(loves/2)).

:- end_tests('mongolog_edb').
