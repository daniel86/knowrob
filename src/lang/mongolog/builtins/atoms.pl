:- module(mongolog_atoms, []).
/** <module> Analysing and constructing atoms in mongolog programs.

The following predicates are supported:

| Predicate             | Arguments |
| ---                   | ---       |
| atom_number/2         | ?Atom, ?Number |
| atom_length/2         | +Atom, ?Length |
| atom_prefix/2         | +Atom, +Prefix |
| atom_concat/3         | ?Atom1, ?Atom2, ?Atom3 |
| atomic_list_concat/2  | +List, ?Atom |
| atomic_list_concat/3  | +List, +Separator, ?Atom |
| upcase_atom/2         | +AnyCase, ?UpperCase |
| downcase_atom/2       | +AnyCase, ?LowerCase |
| random_atom/2         | +Length, -Atom |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=manipatom
@license BSD
*/

:- use_module('../mongolog').
:- use_module('../variables').
:- use_module('../aggregation/match').
:- use_module('../aggregation/set').

%% query commands
:- mongolog:add_command(atom_number).
:- mongolog:add_command(atom_length).
:- mongolog:add_command(atom_prefix).
:- mongolog:add_command(atom_concat).
:- mongolog:add_command(atomic_list_concat).
:- mongolog:add_command(upcase_atom).
:- mongolog:add_command(downcase_atom).
% TODO: support term_to_atom
% - atom parsing is a bit difficult
% - $split can be used, but then e.g. string "7" would need to be mapped to number 7 somehow.
%:- mongolog:add_command(term_to_atom).
:- mongolog:add_command(random_atom).

%% query compilation
mongolog:step_compile(
		atom_number(Atom,Number), _, []) :-
	(ground(Atom);ground(Number)),!,
	atom_number(Atom,Number).

mongolog:step_compile(
		atom_number(Atom,Number),
		Ctx, Pipeline) :-
	arg_val(Atom,Ctx,Atom0),
	arg_val(Number,Ctx,Number0),
	findall(Step,
		(	set_if_var(Atom,    ['$toString', Number0], Ctx, Step)
		;	set_if_var(Number,  ['$toDouble', Atom0],   Ctx, Step)
		;	match_equals(Atom0, ['$toString', Number0], Step)
		),
		Pipeline).

mongolog:step_compile(atom_length(Atom,Length), _, []) :-
	ground(Atom),!,
	atom_length(Atom,Length).

mongolog:step_compile(
		atom_length(Atom,Length),
		Ctx, Pipeline) :-
	arg_val(Atom,Ctx,Atom0),
	arg_val(Length,Ctx,Length0),
	findall(Step,
		(	set_if_var(Length,    ['$strLenCP', Atom0], Ctx, Step)
		;	match_equals(Length0, ['$strLenCP', Atom0], Step)
		),
		Pipeline).

mongolog:step_compile(upcase_atom(Atom,UpperCase), _, []) :-
	ground(Atom),!,
	upcase_atom(Atom,UpperCase).

mongolog:step_compile(
		upcase_atom(Atom,UpperCase),
		Ctx, Pipeline) :-
	arg_val(Atom,Ctx,Atom0),
	arg_val(UpperCase,Ctx,UpperCase0),
	findall(Step,
		(	set_if_var(UpperCase,    ['$toUpper', Atom0], Ctx, Step)
		;	match_equals(UpperCase0, ['$toUpper', Atom0], Step)
		),
		Pipeline).

mongolog:step_compile(downcase_atom(Atom,UpperCase), _, []) :-
	ground(Atom),!,
	downcase_atom(Atom,UpperCase).

mongolog:step_compile(
		downcase_atom(Atom,LowerCase),
		Ctx, Pipeline) :-
	arg_val(Atom,Ctx,Atom0),
	arg_val(LowerCase,Ctx,LowerCase0),
	findall(Step,
		(	set_if_var(LowerCase,    ['$toLower', Atom0], Ctx, Step)
		;	match_equals(LowerCase0, ['$toLower', Atom0], Step)
		),
		Pipeline).

mongolog:step_compile(atom_prefix(Atom,Prefix), _, []) :-
	ground([Atom,Prefix]),!,
	atom_prefix(Atom,Prefix).

mongolog:step_compile(
		atom_prefix(Atom,Prefix),
		Ctx, Pipeline) :-
	arg_val(Atom,Ctx,Atom0),
	arg_val(Prefix,Ctx,Prefix0),
	findall(Step,
		match_equals(Prefix0,
			['$substr', array([
				Atom0, int(0), ['$strLenCP', Prefix0]
			])],
			Step
		),
		Pipeline).

mongolog:step_compile(atom_concat(Left,Right,Atom), _, []) :-
	ground(Left),
	ground(Right),!,
	atom_concat(Left,Right,Atom).

mongolog:step_compile(
		atom_concat(Left,Right,Atom),
		Ctx, Pipeline) :-
	% FIXME: SWI Prolog allows var(Left), var(Right), atom(Atom), and then
	%         yields all possible concatenations.
	arg_val(Left,Ctx,Left0),
	arg_val(Right,Ctx,Right0),
	arg_val(Atom,Ctx,Atom0),
	findall(Step,
		(	set_if_var(Left, ['$substr', array([Atom0,
				int(0),
				['$subtract', array([ ['$strLenCP',Atom0], ['$strLenCP',Right0] ])]
			])], Ctx, Step)
		;	set_if_var(Right, ['$substr', array([Atom0,
				['$strLenCP',Left0],
				['$strLenCP',Atom0]
			])], Ctx, Step)
		;	set_if_var(Atom,    ['$concat', array([Left0,Right0])], Ctx, Step)
		;	match_equals(Atom0, ['$concat', array([Left0,Right0])], Step)
		),
		Pipeline).

mongolog:step_compile(atomic_list_concat(List, Atom), _, []) :-
	ground(List),!,
	atomic_list_concat(List, Atom).

mongolog:step_compile(
		atomic_list_concat(List, Atom),
		Ctx, Pipeline) :-
	findall(Resolved,
		(	member(Unresolved,List),
			arg_val(Unresolved,Ctx,Resolved)
		),
		List0),
	arg_val(Atom,Ctx,Atom0),
	findall(Step,
		(	set_if_var(Atom,    ['$concat', array(List0)], Ctx, Step)
		;	match_equals(Atom0, ['$concat', array(List0)], Step)
		),
		Pipeline).

mongolog:step_compile(atomic_list_concat(List, Sep, Atom), _, []) :-
	ground(Sep),
	(ground(List);ground(Atom)),!,
	atomic_list_concat(List, Sep, Atom).

mongolog:step_compile(
		atomic_list_concat(List, Sep, Atom),
		Ctx, Pipeline) :-
	findall(Resolved,
		(	member(Unresolved,List),
			arg_val(Unresolved,Ctx,Resolved)
		),
		List0),
	arg_val(Sep, Ctx, Sep0),
	arg_val(Atom, Ctx, Atom0),
	add_separator(List0, Sep0, List1),
	findall(Step,
		(	set_if_var(Atom,    ['$concat', array(List1)], Ctx, Step)
		;	match_equals(Atom0, ['$concat', array(List1)], Step)
		),
		Pipeline).

mongolog:step_compile(
		random_atom(Length,Atom),
		Ctx, [Set]) :-
	var_key(Atom,Ctx,AtomKey),
	arg_val(Length,Ctx,Length0),
	maplist([X,string(X)]>>true, [
		'0','1','2','3','4','5','6','7','8','9',
		'A','B','E','F','G','H','I','J','K','L',
		'M','N','O','P','Q','R','S','T','U','V',
		'W','X','Y'
	], CharacterArray),
	Set=[ '$set', [AtomKey, [ '$reduce', [
		[ input, [ '$map', [
			[ input, [ '$range', array([ integer(0), Length0 ]) ] ],
			[ in, [ '$arrayElemAt', array([
				array(CharacterArray),
				[ '$ceil', [ '$multiply', array([
					integer(32),
					[ '$rand', [] ]
				]) ] ]
			]) ] ]
		] ] ],
		[ initialValue, string('') ],
		[ in, [ '$concat', array([string('$$value'), string('$$this')]) ]]
	] ] ] ].

%%
add_separator([], _, []) :- !.
add_separator([X], _, [X]) :- !.
add_separator([X0,X1|Xs], Sep, [X0,Sep,X1|Ys]) :-
	add_separator(Xs, Sep, Ys).


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_atoms').

test('atom_number(+Atom,-Num)'):-
	mongolog_tests:test_call(
		atom_number(Atom, Num), Atom, '4.5'),
	assert_equals(Num, 4.5).

test('atom_number(+Atom,+Num)'):-
	assert_true(mongolog_tests:test_call(
		atom_number(Atom, 4.5), Atom, '4.5')),
	assert_true(mongolog_tests:test_call(
		atom_number(Atom, -2.25), Atom, '-2.25')).

test('atom_number(NaN,_)', [throws(mng_error(_))]):-
	mongolog_tests:test_call(
		atom_number(Atom,_), Atom, 'not a number').

test('atom_length(+Atom,-Length)'):-
	mongolog_tests:test_call(
		atom_length(Atom, Len), Atom, '4.5'),
	assert_equals(Len, 3).

test('upcase_atom(+Atom,+Uppercase)'):-
	assert_true(mongolog_tests:test_call(
		upcase_atom(Atom, 'FOO 3'), Atom, 'foo 3')),
	assert_true(mongolog_tests:test_call(
		upcase_atom(Atom, 'FOO BAR'), Atom, 'foo BAR')),
	assert_true(mongolog_tests:test_call(
		upcase_atom(Atom, ''), Atom, '')),
	assert_false(mongolog_tests:test_call(
		upcase_atom(Atom, 'Foo Bar'), Atom, 'foo BAR')).

test('upcase_atom(+Atom,-Uppercase)'):-
	mongolog_tests:test_call(
		upcase_atom(Atom, Uppercase), Atom, 'foo Bar'),
	assert_equals(Uppercase, 'FOO BAR').

test('downcase_atom(+Atom,+Uppercase)'):-
	assert_true(mongolog_tests:test_call(
		downcase_atom(Atom, 'foo 3'), Atom, 'foo 3')),
	assert_true(mongolog_tests:test_call(
		downcase_atom(Atom, 'foo bar'), Atom, 'foo BAR')),
	assert_true(mongolog_tests:test_call(
		downcase_atom(Atom, ''), Atom, '')),
	assert_false(mongolog_tests:test_call(
		downcase_atom(Atom, 'Foo Bar'), Atom, 'foo BAR')).

test('atom_length(+Atom,+Length)'):-
	assert_true(mongolog_tests:test_call(
		atom_length(Atom, 3), Atom, 'foo')),
	assert_false(mongolog_tests:test_call(
		atom_length(Atom, 2), Atom, 'foo')),
	assert_true(mongolog_tests:test_call(
		atom_length(Atom, 0), Atom, '')).

test('atom_prefix(+Atom,+Prefix)'):-
	assert_true(mongolog_tests:test_call(
		atom_prefix(Atom, 'f'), Atom, 'foo')),
	assert_true(mongolog_tests:test_call(
		atom_prefix(Atom, 'fo'), Atom, 'foo')),
	assert_true(mongolog_tests:test_call(
		atom_prefix(Atom, 'foo'), Atom, 'foo')),
	assert_false(mongolog_tests:test_call(
		atom_prefix(Atom, 'bar'), Atom, 'foo')).

test('atom_concat(+A1,+A2,+A3)'):-
	assert_true(mongolog_tests:test_call(
		atom_concat('foo', 'bar', Atom),
		Atom, 'foobar')).

test('atom_concat(+A1,+A2,-A3)'):-
	mongolog_tests:test_call(
		atom_concat(A1, 'bar', A3),
		A1, 'foo'),
	assert_equals(A3, 'foobar').

test('atom_concat(+A1,-A2,+A3)'):-
	mongolog_tests:test_call(
		atom_concat(A1, A2, 'foobar'),
		A1, 'foo'),
	assert_equals(A2, 'bar').

test('atom_concat(-A1,+A2,+A3)'):-
	mongolog_tests:test_call(
		atom_concat(A1, A2, 'foobar'),
		A2, 'bar'),
	assert_equals(A1, 'foo').

test('atomic_list_concat(+List,+Atom)'):-
	assert_true(mongolog_tests:test_call(
		atomic_list_concat(['foo', 'bar'], Atom),
		Atom, 'foobar')).

test('atomic_list_concat(+List,-Atom)'):-
	mongolog_tests:test_call(
		atomic_list_concat([X1, 'bar'], Atom),
		X1, 'foo'),
	assert_equals(Atom, 'foobar').

test('atomic_list_concat(+List,+Sep,-Atom)'):-
	mongolog_tests:test_call(
		atomic_list_concat([X1, 'bar'], '-', Atom),
		X1, 'foo'),
	assert_equals(Atom, 'foo-bar').

test('random_atom(+Length,-Atom)'):-
	mongolog_tests:test_call(random_atom(Length, Atom), Length, 5),
	assert_true(atom(Atom)),
	(	\+atom(Atom)->true
	;	(
		atom_length(Atom,AtomLength),
		assert_equals(AtomLength,5)
	)).

:- end_tests('mongolog_atoms').
