:- module(mongolog_cut, []).
/** <module> Control structures in mongolog programs.

The following predicates are supported:

| Predicate   | Arguments |
| ---         | ---       |
| !/0         | |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=control
@license BSD
*/

:- use_module('../../mongolog').

%% query commands
:- mongolog:add_command(!).

%% !
% Cut. Discard all choice points created since entering the predicate in which
% the cut appears. In other words, commit to the clause in which the cut appears
% and discard choice points that have been created by goals to the left of the cut
% in the current clause. Meta calling is opaque to the cut. This implies that cuts that
% appear in a term that is subject to meta-calling (call/1) only affect choice points
% created by the meta-called term.
%
% To realize cut, every clause [X0,...,Xn,!|_] is rewritten as [limit(1, [X0,....,Xn])|_]
% NOTE: the rewriting is currently a special case in compiler.pl and cannot be handled
%         through existing interfaces for commands in this file.
% NOTE: but disjunction below handles cut in disjunction goals
%
%mongolog:step_compile('!', _, [['$limit',int(1)]]).

% TODO: replace cut with unary limit


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_cut').

test('((+Goal ; +Goal), !)'):-
	mongolog_tests:test_call(
		(	(	(X is (Num + 5))
			;	(X is (Num * 2))
			), !
		),
		Num, 4.5),
	assert_equals(X,9.5).

:- end_tests('mongolog_cut').
