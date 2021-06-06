:- module(mongolog_limit, []).
/** <module> Meta predicates in mongolog programs.

The following predicates are supported:

| Predicate    | Arguments |
| ---          | ---       |
| once/1       | :Goal |
| limit/2      | +Count, :Goal |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=metacall
@license BSD
*/

:- use_module('../../mongolog').
:- use_module('../../variables').
:- use_module('../../aggregation/lookup').

%%%% query commands
:- mongolog:add_command(once).
:- mongolog:add_command(limit).


%% once(:Goal)
% Make a possibly nondet goal semidet, i.e., succeed at most once.
%
lang_query:step_expand(once(Goal), Expanded) :-
	% TODO: but this won't work if embedded into a disjunction or?
	%        - alternative is $lookup with $limit (same as the limit command)
	%           any other way to do scoping for $limit?
	%		 - cut better for views?
	%		 - once(p_edb/p_view) could be optimized if join is performed by including
	%		   $limit into the join $lookup. but it could be optimized in other cases too!
	append_cut(Goal, WithCut),
	lang_query:kb_expand(WithCut, Expanded).

% append cut operator at the end of a goal.
append_cut(Goal, WithCut) :-
	(	is_list(Goal) -> Terms=Goal
	;	comma_list(Goal,Terms)
	),
	append(Terms, ['!'], X),
	comma_list(WithCut, X).


%% limit(+Count, :Goal)
% Limit the number of solutions.
% True if Goal is true, returning at most Count solutions.
%
lang_query:step_expand(
		limit(Count, Goal),
		limit(Count, Expanded)) :-
	lang_query:kb_expand(Goal, Expanded).

mongolog:step_compile1(limit(_, Terminals), Ctx, Output) :-
	% succeed if goal is empty
	Terminals==[],
	mongolog:step_compile1(true,Ctx,Output),
	!.

mongolog:step_compile1(
		limit(Count, Terminals), Ctx,
		[ document(Pipeline), variables(StepVars) ]) :-
	arg_val(Count,Ctx,Count0),
	% appended to inner pipeline of lookup
	Suffix=[['$limit',Count0]],
	% create a lookup and append $limit to inner pipeline,
	% then unwind next and assign variables to the toplevel document.
	lookup_call(Terminals, Suffix, Ctx, Pipeline, StepVars0),
	%
	(	goal_var(Count,Ctx,Count_var)
	->	StepVars=[Count_var|StepVars0]
	;	StepVars=StepVars0
	).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_limit').

test('limit(1, +Goal)'):-
	mongolog_tests:test_call(
		limit(1, (
			(X is (Num + 5))
		;	(X is (Num * 2))
		)),
		Num, 4.5),
	assert_equals(X,9.5).

test('limit(2, +Goal)'):-
	findall(X,
		mongolog_tests:test_call(
			limit(2, (
				(X is (Num + 5))
			;	(X is (Num * 2))
			;	(X is (Num * 2))
			)),
			Num, 4.5),
		Results
	),
	assert_unifies(Results,[_,_]),
	assert_true(ground(Results)),
	assert_true(memberchk(9.5, Results)),
	assert_true(memberchk(9.0, Results)).

test('once(+Goal)'):-
	mongolog_tests:test_call(
		once((
			(X is (Num + 5))
		;	(X is (Num * 2))
		)),
		Num, 4.5),
	assert_equals(X,9.5).

:- end_tests('mongolog_limit').
