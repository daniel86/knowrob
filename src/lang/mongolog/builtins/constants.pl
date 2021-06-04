:- module(mongolog_constants, []).
/** <module> Constants in mongolog programs.

Constants are null-ary predicates with special meaning.
The following predicates are supported:

| Predicate   | Arguments |
| ---         | ---       |
| fail/0      | |
| false/0     | |
| true/0      | |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=control
@license BSD
*/

:- use_module('../mongolog').

%% query commands
:- mongolog:add_command(fail).
:- mongolog:add_command(false).
:- mongolog:add_command(true).

%% false
%
% Same as fail, but the name has a more declarative connotation.
%
lang_query:step_expand(false, fail).

%% true
%
% Always succeed. 
%
mongolog:step_compile1(true,  _,
	[ document([]),
	  variables([])
	]).

%% fail
%
% Always fail. 
%
mongolog:step_compile1(fail,  _,
	[ document([['$match', ['$expr', bool(false)]]]),
	  variables([])
	]).


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_constants').

test('fail'):-
	assert_false(mongolog_call(fail)).

test('true'):-
	assert_true(mongolog_call(true)).

:- end_tests('mongolog_constants').
