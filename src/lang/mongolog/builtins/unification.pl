:- module(mongolog_unification,
		[ unify_arg_field/4
		]).
/** <module> Unification of terms in mongolog programs.

The following predicates are supported:

| Predicate  | Arguments |
| ---        | ---       |
| =/2        | ?Term1, ?Term2 |
| \=/2       | ?Term1, ?Term2 |
| assign/2   | -Term1, +Term2 |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=compare
@license BSD
*/

:- use_module('../mongolog').
:- use_module('../variables').
:- use_module('../aggregation/match').
:- use_module('../aggregation/set').

%% mongolog:add_command
:- mongolog:add_command(=).
:- mongolog:add_command(\=).
:- mongolog:add_command(assign).

%% @Term1 \= @Term2
%
% Equivalent to \+Term1 = Term2.
%
% This predicate is logically sound if its arguments are sufficiently instantiated.
% In other cases, such as ?- X \= Y., the predicate fails although there are solutions.
% This is due to the incomplete nature of \+/1. 
%
lang_query:step_expand((A \= B), Expanded) :-
	lang_query:step_expand(\+(A = B), Expanded).

%%
mongolog:step_compile(
		assign(Var,Value), Ctx,
		[['$set', [[Key,Value0]]]]) :-
	arg_val(Value,Ctx,Value0),
	var_key(Var,Ctx,Key).

%% ?Term1 = ?Term2
% Unify Term1 with Term2. True if the unification succeeds.
%
mongolog:step_compile((Term1 = Term2), _, _) :-
	\+ unifiable(Term1, Term2, _), !,
	fail.

mongolog:step_compile((Term1 = Term2), Ctx, Pipeline) :-
	arg_val(Term1,Ctx,Term1_val),
	arg_val(Term2,Ctx,Term2_val),
	findall(Step,
		(	set_if_var(Term1, Term2_val, Ctx, Step)
		;	set_if_var(Term2, Term1_val, Ctx, Step)
		% make both terms accessible via fields
		;	Step=['$set', ['t_term1', Term1_val]]
		;	Step=['$set', ['t_term2', Term2_val]]
		% assign vars in term1 to values of arguments in term2
		;	set_term_arguments(Term1, Term2, 't_term1', 't_term2', Step)
		% assign vars in term2 to values of arguments in term1
		;	set_term_arguments(Term2, Term1, 't_term2', 't_term1', Step)
		% perform equality test
		;	match_equals(string('$t_term1'), string('$t_term2'), Step)
		% project new variable groundings
		;	set_term_vars(Term1, 't_term1', Ctx, Step)
		;	set_term_vars(Term2, 't_term2', Ctx, Step)
		% and cleanup
		;	Step=['$unset', array([string('t_term1'),string('t_term2')])]
		),
		Pipeline).

%%
unify_arg_field(Argument, Field, Ctx, Step) :-
	arg_val(Argument,Ctx,Argument0),
	atom_concat('$',Field,Field0),
	(	set_if_var(Argument, string(Field0), Ctx, Step)
	% make Argument accessible via field
	;	Step=['$set', ['t_arg', Argument0]]
	% assign vars in t_arg to values of arguments in Field
	;	set_term_arguments('t_arg', Field, Step)
	% perform equality test
	;	match_equals(string(Field0), string('$t_arg'), Step)
	% project new variable groundings
	;	set_term_vars(Argument, 't_arg', Ctx, Step)
	% and cleanup
	;	Step=['$unset', string('t_arg')]
	).

%%
% this operation replaces all variable arguments in Term1 with
% arguments in Term2.
% NOTE: variables are also replaced if the argument in Term2 is also a variable.
%       this is important for later equality test! 
%
set_term_arguments(List1, List2, List1Key, List2Key,
		['$set', [List1Key, MapList]]) :-
	% TODO: remove this clause/rule
	(is_list(List1);is_list(List2)),!,
	atom_concat('$',List1Key,List1Val),
	atom_concat('$',List2Key,List2Val),
writeln(fixme(set_list_args(List1, List2))),
	MapList=['$map', [
		['input', string(List1Val)],
		['in', ['$cond', [
			% if not a variable
			['if', ['$eq', array([string('$$this'), constant(undefined)])]],
			% then use argument of other term
			% FIXME: $indexOfArray only return first occurence, we need to call $range to
			%        iterate over every index!!
			%        TODO: Is there a way to get index from $map context?
			['then', ['$arrayElemAt', array([
				string(List2Val),
				['$indexOfArray', array([string(List1Val),string('$$this')])]
			])]],
			% else use $$this
			['else', string('$$this')]
		]]]
	]].

set_term_arguments(_Term1, _Term2, Term1Key, Term2Key, Set) :-
	set_term_arguments(Term1Key, Term2Key, Set).

%%
% assign vars in term1 to values of arguments in term2
%
set_term_arguments(Term1Key, Term2Key,
	['$set', [Term1Key, ['$cond', [
		% if term1 is atomic (no field term.value exists)
		['if', ['$eq', array([string(Term1Args0), constant(undefined)])]],
		% then assign self if not a variable, and use term2 as value else
		['then', ['$ifNull', array([string(Term1Value), string(Term2Value)])]],
		% if term is non atomic...
		['else', [
			['type', string('compound')],
			['arity', string(Term1Arity)],
			% NOTE: toplevel $reduce is used to flatten the lists created by $map below
			['value', ['$reduce', [
				[initialValue, array([])],
				[in, ['$concatArrays', array([string('$$value'), string('$$this')]) ]],
				% map each element in term1 to a list of elements where variables
				% have been replaced with values from term2.
				% NOTE: variable aliasing is not supported here!
				[input, ['$map', [
					[input, string(Term1Args0)],
					[as, string('t1')],
					[in, ['$cond', [
						% if t1 is a variable
						[if, ['$eq', array([string('$$t1.v'), constant(undefined)])]],
						% select each t2 where t1.i is a prefix of t2.i
						[then, ['$filter', [
							[input, string(Term2Args0)],
							[as, string('t2')],
							% test that t1.i is a prefix of t2.i
							[cond, ['$eq', array([
								string('$$t1.i'),
								['$substr', array([
									string('$$t2.i'),
									integer(0),
									['$strLenCP', string('$$t1.i')]
								])]
							])]]
						]]],
						% else keep the value
						[else, array([string('$$t1')])]
					]]]
				]]]
			]]]
		]]
	]]]]) :-
	atom_concat('$',Term1Key,Term1Value),
	atom_concat('$',Term2Key,Term2Value),
	atomic_list_concat(['$',Term1Key,'.arity'],Term1Arity),
	atomic_list_concat(['$',Term1Key,'.value'],Term1Args0),
	atomic_list_concat(['$',Term2Key,'.value'],Term2Args0).

%%
% =/2 builds up two fields 't_term1' and 't_term2'.
% at this point both of them are equal.
% here we analyze the compile-time argument of the predicate
% and project variables with new groundings as separate fields
% in the document.
%
set_term_vars(Term, _, _, _) :-
	% no projection needed if term is already ground
	ground(Term),!,
	fail.

set_term_vars(Term, Field, Ctx, ['$set', [TermField, string(FieldValue)]]) :-
	% the term itself is a var -> $set var field
	var(Term),!,
	var_key(Term, Ctx, TermField),
	atom_concat('$', Field, FieldValue).

set_term_vars(Args, Field, Ctx, SetVars) :-
	is_list(Args),!,
	atomic_list_concat(['$',Field], ArrayField),
	set_term_vars1(Args, ArrayField, Ctx, SetVars).

set_term_vars(Term, Field, Ctx, SetVars) :-
	% nonvar(Term),
	atomic_list_concat(['$',Field,'.value'], Input),
	set_term_vars0(Term, string(Input), Ctx, SetVars).

%%
set_term_vars0(Term, Input, Ctx, Step) :-
	% iterate over variables and their index string in flattened form
	mongolog_terms:mng_flatten_term1(
		Term,
		[keep_vars|Ctx],
		[[var,Arg],[i,IndexString]|_]),
	% get the field key for Arg
	var_key(Arg, Ctx, ArgField),
	% finally generate $set operation
	mongolog_terms:set_term_argument(
		Input, IndexString, ArgField, Step).

%%
set_term_vars1(Args, ArrayField, Ctx, Step) :-
	% TODO: remove this clause
	% iterate over arguments
	length(Args, NumArgs),
	NumArgs0 is NumArgs - 1,
	between(0, NumArgs0, Index0),
	nth0(Index0, Args, Arg),
	% get the varkey or fail if it is not a var
	var_key(Arg, Ctx, ArgField),
	%
	(	(	% access argument with given index
			% FIXME: argument could be a term, or? then there would be a set of entries in the
			%        array that start with index prefix "1.Index", and a term must be constructed!
			%        in the new term the prefix is changed from "1.Index" to "1."
			Index is Index0+1,
			Step=['$set', [ArgField, ['$arrayElemAt', array([string(ArrayField),integer(Index)])]]]
		)
	;	(	% the argument is stored as a document {i:_,v:_}
			% the i field is removed in this step.
			atomic_list_concat(['$', ArgField, '.v'], '', FieldValue),
			Step=['$set', [ArgField, string(FieldValue)]]
		)
	).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_unification').

test('atom unification'):-
	assert_true(mongolog_tests:test_call(=(X,a), X, a)),
	assert_true(mongolog_tests:test_call(=(a,X), X, a)),
	assert_true(mongolog_tests:test_call(=(_,X), X, a)),
	assert_false(mongolog_tests:test_call(=(b,X), X, a)),
	assert_false(mongolog_tests:test_call(=(a(b),X), X, a)).

test('number unification'):-
	assert_true(mongolog_tests:test_call(=(X,7), X, 7)),
	assert_true(mongolog_tests:test_call(=(7,X), X, 7)),
	assert_true(mongolog_tests:test_call(=(_,X), X, 7)),
	assert_false(mongolog_tests:test_call(=(8,X), X, 7)),
	assert_false(mongolog_tests:test_call(=(a(7),X), X, 7)).

test('compound unification'):-
	assert_true(mongolog_tests:test_call(=(X,foo(a,b)), X, foo(a,b))),
	assert_true(mongolog_tests:test_call(=(foo(a,b),X), X, foo(a,b))),
	assert_true(mongolog_tests:test_call(=(foo(a,_),X), X, foo(a,b))),
	assert_true(mongolog_tests:test_call(=(_,X), X, foo(a,b))),
	assert_false(mongolog_tests:test_call(=(foo(a,c),X), X, foo(a,b))).

test('list unification'):-
	assert_true(mongolog_tests:test_call(=(X,[a]), X, [a])),
	assert_true(mongolog_tests:test_call(=(X,[a,b]), X, [a,b])),
	assert_true(mongolog_tests:test_call(=(X,[_,_]), X, [a,b])),
	assert_true(mongolog_tests:test_call(=(X,[a,_]), X, [a,b])),
	(	mongolog_tests:test_call(=(X,[A,B]), X, [a,b])
	->	assert_equals([A,B],[a,b])
	;	true
	),
	(	mongolog_tests:test_call(=(X,Y), X, [a,b])
	->	assert_equals(Y,[a,b])
	;	true
	).

test('compound+list unification'):-
	assert_true(mongolog_tests:test_call(=(X,foo([a1,b1])), X, foo([a1,b1]))),
	assert_true(mongolog_tests:test_call(=(foo([a2,b2]),X), X, foo([a2,b2]))),
	assert_true(mongolog_tests:test_call(=(_,X), X, foo([a4,b4]))),
	assert_false(mongolog_tests:test_call(=(foo([a5,c5]),X), X, foo([a5,b5]))),
	(	mongolog_tests:test_call(=(X,foo([A,B])), X, foo([a6,b6]))
	->	assert_equals([A,B],[a6,b6])
	;	true
	).

test('compound+list partially grounded',
		fixme('unification of lists does not work if some list elements are variables')):-
	assert_true(mongolog_tests:test_call(=(foo([a3,_]),X), X, foo([a3,b3]))).

test('unification 1-ary term with var'):-
	mongolog_tests:test_call(=(foo(Y),X), X, foo(a)),
	assert_equals(Y,a).

test('unification 2-ary term with var'):-
	mongolog_tests:test_call(=(foo(a,Y),X), X, foo(a,b)),
	assert_equals(Y,b).

test('variables may appear multiple times in terms'):-
	mongolog_tests:test_call(=(f(g(X),X),f(Y,Z)), Z, a),
	assert_equals(X,a),
	assert_equals(Y,g(a)).

test('unified vars are equivalent',
		fixme('support variable aliasing')):-
	mongolog_tests:test_call(=(X,Y), X, _),
	assert_equals(X,Y).

test('unified vars can be implicitly instantiated',
		fixme('support variable aliasing')):-
	mongolog_tests:test_call((=(X,Y), X is 4), X, _),
	assert_equals(X,4),
	assert_equals(Y,4).

:- end_tests('mongolog_unification').

