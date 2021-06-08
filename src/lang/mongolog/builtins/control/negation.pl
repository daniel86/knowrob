:- module(mongolog_negation, []).
/** <module> Control structures in mongolog programs.

The following predicates are supported:

| Predicate   | Arguments |
| ---         | ---       |
| \+/1        | :Goal |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=control
@license BSD
*/

:- use_module('../../mongolog').
:- use_module('../../aggregation/lookup').

%% query commands
:- mongolog:add_command(\+).
:- mongolog:add_command(not).

%% not(:Goal):
%
% True if Goal cannot be proven.
% Retained for compatibility only. New code should use \+/1.
%
lang_query:step_expand(not(Goal), Expanded) :-
	lang_query:step_expand(\+(Goal), Expanded).

%% \+ :Goal:
%
% True if‘Goal' cannot be proven (mnemonic: + refers to provable and
% the backslash (\) is normally used to indicate negation in Prolog).
%
lang_query:step_expand(\+(Goal), Expanded) :-
	lang_query:kb_expand(Goal, GoalExpanded),
%	lang_query:kb_expand((
%		once(
%			(once(Goal),assign(X,0))
%		;	assign(X,1)
%		),
%		X == 1
%	), Expanded).
	% another way to write it:
%	Expanded=((once(GoalExpanded),!,fail) ; true).
	Expanded = (
		findall([], (call(GoalExpanded), limit(1)), L),
		length(L,0)
	).


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_negation').

test('\\+(+Goal)'):-
	assert_true(mongolog_tests:test_call(
		\+(Number > 5), Number, 4.5)),
	assert_false(mongolog_tests:test_call(
		\+(Number > 4), Number, 4.5)).

:- end_tests('mongolog_negation').
