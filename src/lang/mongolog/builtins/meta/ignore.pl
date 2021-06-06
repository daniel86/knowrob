:- module(mongolog_ignore, []).
/** <module> Meta predicates in mongolog programs.

The following predicates are supported:

| Predicate    | Arguments |
| ---          | ---       |
| ignore/1     | :Goal |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=metacall
@license BSD
*/

:- use_module('../../mongolog').

%%%% query commands
:- mongolog:add_command(ignore).


%% ignore(:Goal)
% Calls Goal as once/1, but succeeds, regardless of whether Goal succeeded or not.
%
lang_query:step_expand(ignore(Goal), Expanded) :-
	lang_query:kb_expand((once(Goal) ; true), Expanded).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_ignore').

test('ignore(+Failing)'):-
	mongolog_tests:test_call(
		ignore(((Num < 3), (X is (Num * 2)))),
		Num, 4.5),
	assert_unifies(X,_).

test('ignore(+Failing), +Goal'):-
	mongolog_tests:test_call(
		(ignore(Num < 3), (X is (Num * 2))),
		Num, 4.5),
	assert_equals(X,9.0).

test('ignore(+FailingWithVar), +Goal'):-
	% test with variable Z being assigned only in failing ignored
	% goal. Then no grounding will be part of result set and Z still a variable
	% after the call.
	mongolog_tests:test_call(
		(	ignore((Num < 3, Z is Num + 2)),
			X is (Num * 2)
		),
		Num, 4.5),
	assert_equals(X,9.0),
	assert_unifies(Z,_).

:- end_tests('mongolog_ignore').
