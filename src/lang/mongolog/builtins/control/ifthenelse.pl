:- module(mongolog_ifthenelse, []).
/** <module> Control structures in mongolog programs.

The following predicates are supported:

| Predicate   | Arguments |
| ---         | ---       |
| ->/2        | :Condition, :Action |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=control
@license BSD
*/

:- use_module('../../mongolog').

%% query commands
:- mongolog:add_command(->).
%:- mongolog:add_command(*->).

%% :Condition -> :Action
% If-then and If-Then-Else.
% The ->/2 construct commits to the choices made at its left-hand side,
% destroying choice points created inside the clause (by ;/2),
% or by goals called by this clause. Unlike !/0,
% the choice point of the predicate as a whole (due to multiple clauses)
% is not destroyed.
%
% Please note that (If -> Then) acts as (If -> Then ; fail),
% making the construct fail if the condition fails.
% This unusual semantics is part of the ISO and all de-facto Prolog standards. 
%
%mongolog:step_expand((If -> Then ; Else), (X;Y)) :-
%	% (If -> Then) ; Else -> (If, !, Then) ; Else
%	mongolog_expand([If, !, Then], X),
%	mongolog_expand(Else,          Y).

mongolog:step_expand((If -> Then ; Else), Expanded) :-
	mongolog_expand((
		once(
			(If,assign(X,1))
		;	assign(X,0)
		),
		(	(X==1,Then)
		;	(X==0,Else)
		)
	),Expanded).

mongolog:step_expand((If -> Then), Epanded) :-
	mongolog:step_expand((If -> Then ; fail), Epanded).

%% TODO: :Condition *-> :Action ; :Else
% This construct implements the so-called‘soft-cut'.
% The control is defined as follows: If Condition succeeds at least once,
% the semantics is the same as (call(Condition), Action).
% If Condition does not succeed, the semantics is that of (\+ Condition, Else).
% In other words, if Condition succeeds at least once, simply behave as the
% conjunction of call(Condition) and Action, otherwise execute Else.
% The construct is known under the name if/3 in some other Prolog implementations. 
%
%mongolog:step_expand(
%		';'('*->'(Condition,Action),Else),
%		';'(X,Y)) :-
%	fail.


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_ifthenelse').

test('((+If -> +Then) ; +Else)::Then') :-
	mongolog_tests:test_call(
		(	Num > 5 -> X is Num * 2
		;	X is Num + 2
		),
		Num, 5.5),
	assert_equals(X,11.0).

test('((+If -> +Then) ; +Else)::Else'):-
	mongolog_tests:test_call(
		(	Num > 5 -> X is Num * 2
		;	X is Num + 2
		),
		Num, 4.5),
	assert_equals(X,6.5).

:- end_tests('mongolog_ifthenelse').
