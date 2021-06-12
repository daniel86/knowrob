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
:- use_module('../../kb/edb').

%%%% query commands
:- mongolog:add_command(once).
:- mongolog:add_command(limit).


%% once(:Goal)
% Make a possibly nondet goal semidet, i.e., succeed at most once.
%
lang_query:step_expand(once(Goal), Expanded) :-
	lang_query:kb_expand(limit(1,Goal), Expanded).

%% limit(+Count, :Goal)
% Limit the number of solutions.
% True if Goal is true, returning at most Count solutions.
%
lang_query:step_expand(
		limit(Count, Goal),
		limit(Count, GoalExpanded)) :-
	lang_query:kb_expand(Goal, GoalExpanded).

mongolog:step_compile(limit(Count), Ctx, [['$limit',Count0]]) :-
	% simple case: unary limit is mapped to $limit command
	arg_val(Count,Ctx,Count0).

mongolog:step_compile1(limit(_, Goal), Ctx, Output) :-
	% succeed if goal is empty
	Goal==[],
	mongolog:step_compile1(true, Ctx, Output),
	!.

mongolog:step_compile1(limit(_, Goal), Ctx, []) :-
	% limit views cannot be created if
	% the limit-goal shares a variable with the head of the rule that is compiled
	option(compile_mode(view), Ctx),
	goal_var_in_head(Goal, Ctx),
	!,
	fail.

mongolog:step_compile1(limit(Count, Goal), Ctx, Output) :-
	% try to get rid of the Goal argument of limit.
	% this is only possible if limit is the first step that draws
	% input documents, and that generates choicepoints.
	% FIXME: checking input_assigned flag is not sufficient!
	%        e.g. one could have such a statement:
	%		- member(A,[1,2])
	%		- between(...)
	%        thus we need to keep track of nonderministic predicate calls.
	\+ option(input_assigned,Ctx), !,
	option(outer_vars(OV), Ctx, []),
	mongolog:compile_term(Goal, OV->_, Output1, Ctx),
	mongolog:step_compile1(limit(Count), Ctx, Output2),
	mongolog:merge_outputs(Output1, Output2, Output).

mongolog:step_compile1(limit(Count, Goal), Ctx, Output) :-
	% if Goal is an EDB predicate, and the input was assigned before,
	% then the EDB predicate lookup can perform the limit.
	% TODO: also the case for IDB views?
	is_edb_predicate(Goal), !,
	arg_val(Count,Ctx,Count0),
	mongolog:step_compile1(Goal, [limit(Count0)|Ctx], Output).

mongolog:step_compile1(
		limit(Count, Goal), Ctx,
		[ document(Pipeline),
		  variables(StepVars)
		]) :-
	lookup_call(
		(Goal, limit(Count)),
		Ctx, StepVars0, Pipeline),
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
