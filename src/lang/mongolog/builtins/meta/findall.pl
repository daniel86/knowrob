:- module(mongolog_findall, []).
/** <module> Finding all solutions to a goal in mongolog programs.

The following predicates are supported:

| Predicate    | Arguments |
| ---          | ---       |
| findall/3    | +Template, :Goal, -Bag |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=allsolutions
@license BSD
*/

:- use_module(library('db/mongo/client'), [ mng_one_db/2 ]).
:- use_module('../../mongolog').
:- use_module('../../variables').
:- use_module('../../aggregation/lookup').
:- use_module('../../aggregation/match').
:- use_module('../../aggregation/set').

%% register query commands
:- mongolog:add_command(findall).
% TODO: support bagof (then, setof := bagof o sort)
%:- mongolog:add_command(bagof).
%:- mongolog:add_command(setof).

%%
lang_query:step_expand(
		findall(Template, Goal, List),
		findall(Template, Expanded, List)) :-
	lang_query:kb_expand(Goal, Expanded).

lang_query:step_expand(
		findall(Goal, List),
		findall(Expanded, List)) :-
	lang_query:kb_expand(Goal, Expanded).

%% setof(+Template, +Goal, -Set)
% Equivalent to bagof/3, but sorts the result using sort/2 to
% get a sorted list of alternatives without duplicates.
%
%lang_query:step_expand(
%		setof(Template, Goal, Set),
%		','(bagof(Template, Expanded, List), sort(List, Set))) :-
%	lang_query:kb_expand(Goal, Expanded).

%% findall(:Goal, -Bag)
% Create a list of the different documents where Goal is true.
% Succeeds with an empty list if Goal has no solutions.
%
mongolog:step_compile1(findall(Goal, List), Ctx,
		[ document(Pipeline),
		  variables(StepVars),
		  input_collection(GoalCollection)
		]) :-
	findall_compile(
		Goal, List,
		Ctx,
		GoalCollection,
		StepVars,
		_InnerStepVars,
		InnerPipeline),
	merge_options([step_vars(StepVars)], Ctx, Ctx_outer),
	% compile a pipeline
	findall(Step,
		% collect results in 't_next' array
		(	member(Step,InnerPipeline)
		% field(List) = $t_next
		;	set_if_var(List, string('$t_next'), Ctx_outer, Step)
		% field(List) == argval(List)
		;	(	arg_val(List, Ctx_outer, List0),
				match_equals(List0, string('$t_next'), Step)
			)
		% delete(t_next)
		;	Step=['$unset', array([string('t_next')])]
		),
		Pipeline).

%% findall(+Template, :Goal, -Bag)
% Create a list of the instantiations Template gets for different
% cases where Goal is true.
% Succeeds with an empty list if Goal has no solutions.
%
mongolog:step_compile1(findall(Template, Goal, List), Ctx,
		[ document(Pipeline),
		  variables(StepVars),
		  input_collection(GoalCollection)
		]) :-
	% add template variables to goal context
	findall_goal_ctx(Template, Ctx, Ctx_goal),
	% compile the goal
	findall_compile(
		Goal, List,
		Ctx_goal,
		GoalCollection,
		StepVars,
		InnerStepVars,
		InnerPipeline),
	% make sure to use a common key with the inner pipeline when instantiating
	% the template.
	merge_options([step_vars(InnerStepVars)], Ctx_goal, Ctx_inner),
	merge_options([step_vars(StepVars)],      Ctx_goal, Ctx_outer),
	% compile a pipeline
	findall(Step,
		% collect results in 't_next' array
		(	member(Step,InnerPipeline)
		% $map $t_next into field(List)
		;	findall_map(Template, List, Ctx_outer, Ctx_inner, Step)
		),
		Pipeline).
	

%%
findall_compile(Goal, _, Ctx, _, [], [],[]) :-
	% findall views cannot be created if
	% the findall-goal shares a variable with the head of the rule that is compiled
	option(compile_mode(view), Ctx),
	goal_var_in_head(Goal, Ctx),
	!,
	fail.

findall_compile(Goal, List, Ctx, GoalCollection,
		StepVars0, InnerStepVars, Pipeline) :-
	% findall via $group command.
	% this is useful because findall can be evaluated without lookup.
	% this is only possible if no nondet predicate preceeds findall,
	% i.e. there cannot be any choicepoints before the findall.
	% In such a case we can transform findall into a pipeline with $group
	% command that groups all incoming documents into one group which
	% is then used to instantiate the list variable.
	% FIXME: need to check for nondet predicates before findall
	\+ option(input_assigned,Ctx), !,
	% add list to step variables
	goal_vars(List, Ctx, StepVars),
	% compile the goal
	mongolog:step_compile1(Goal, Ctx, Output_goal),
	mongolog:compiled_document(Output_goal, InnerPipeline),
	mongolog:compiled_substitution(Output_goal, InnerStepVars),
	option(input_collection(GoalCollection), Output_goal, _),
	%
	merge_substitutions(StepVars, InnerStepVars, StepVars0),
	% compile a pipeline for grouping results of Goal into an array
	findall(Step,
		(	member(Step, InnerPipeline)
		% group incoming documents into 't_next' array
		;	Step=['$group', [
				% "null" indicates that all documents are added to the same group.
				% thus $group will output exactly one document.
				['_id', constant(null)],
				% the output document of $group has an array field "t_next"
				% where all documents are added
				['t_next', ['$push', string('$$ROOT') ]]
			] ]
		% re-add lost vars
		;	set_grouped_vars(Ctx, StepVars, Step)
		),
		Pipeline).

findall_compile(Goal, List, Ctx, GoalCollection,
		StepVars, InnerStepVars, [Lookup]) :-
	% findall via $lookup command.
	% used in case findall is preceeded by a nondet predicate such that
	% the findall goal must be scoped to create a result for each choice.
	mng_one_db(_,GoalCollection),
	goal_vars(List, Ctx, StepVars),
	% compile a $lookup query
	lookup_findall(
		't_next',        % array field
		Goal,            % lookup goal
		[],[],           % prefix/suffix for inner pipeline
		Ctx,             % compile context
		InnerStepVars,   % variables in Goal
		Lookup           % the $lookup query
	).

%%
findall_goal_ctx(Template, Ctx, [step_vars(SV2)|Ctx0]) :-
	select_option(step_vars(SV), Ctx, Ctx0, []),
	goal_vars(Template, Ctx, TemplateVars),
	merge_substitutions(TemplateVars, SV, SV2).

%%
findall_map(Template, List, Ctx_outer, Ctx_inner, Step) :-
	% Get the $map expression to instantiate the template for each list element.
	% NOTE: it is not allowed due to handling here to construct
	% the pattern in a query, it must be given in the findall command compile-time.
	template_instantiation(Template, Ctx_inner, Instantiation),
	% $set the list variable field from 'next' field
	(	Step=['$set', ['t_list', ['$map',[
				['input',string('$t_next')],
				['in', Instantiation] ]]]]
	;	set_if_var(List, string('$t_list'), Ctx_outer, Step)
	;	(
			arg_val(List, Ctx_outer, List0),
			match_equals(List0, string('$t_list'), Step)
		)
	% array at 'next' field not needed anymore
	;	Step=['$unset', array([string('t_next'), string('t_list')])]
	).

%%
% findall template must be given compile-time to construct the mongo expression
% to map lookup results to be a proper instantiation of the template.
% the currently mapped array element is referred to as "$$this"
%
template_instantiation(Var, Ctx, string(Val)) :-
	% for variables in template, lookup in compile context
	% or create a key used in mongo to refer to the var
	var_key(Var, Ctx, Key),
	atom_concat('$$this.', Key, Val).

template_instantiation(List, Ctx, array(Elems)) :-
	is_list(List),!,
	findall(Y,
		(	member(X,List),
			template_instantiation(X, Ctx, Y)
		),
		Elems).

template_instantiation(Template, Ctx, [
		['type', string('compound')],
		['value', [
			['functor', string(Functor)],
			['args', Args0]
		]]
	]) :-
	compound(Template),!,
	Template =.. [Functor|Args],
	template_instantiation(Args, Ctx, Args0).
	
template_instantiation(Atomic, _Ctx, Constant) :-
	atomic(Atomic),
	mongolog:get_constant(Atomic, Constant).

% re-add fields that were removed by $group
set_grouped_vars(Ctx, StepVars, ['$set', OuterSet]) :-
	option(outer_vars(OV), Ctx, []),
	findall([VarKey,[['type',string('var')], ['value',string(VarKey)]]],
		(	(member([VarKey,Var], OV) ; member([VarKey,Var],StepVars)),
			% FIXME: improve assertion handling
			VarKey \== 'g_assertions',
			var(Var)
		),
		OuterSet0
	),
	list_to_set(OuterSet0,OuterSet).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_findall').

test('findall(+Succeeds)'):-
	mongolog_tests:test_call(
		findall(X,
			X is (Num + 5),
			Results),
		Num, double(4.5)
	),
	assert_true(ground(Results)),
	assert_equals(Results,[9.5]).

test('findall(+Succeeds ; +Succeeds)'):-
	mongolog_tests:test_call(
		(	findall(X,
				(	(X is (Num + 5))
				;	(X is (Num * 2))
				),
				Results)
		),
		Num, double(4.5)
	),
	assert_true(ground(Results)),
	assert_equals(Results,[9.5,9.0]).

test('findall(+,:,+)'):-
	assert_true(mongolog_tests:test_call(
		(	findall(X,
				(	(X is (Num + 5))
				;	(X is (Num * 2))
				),
				[9.5,9.0])
		),
		Num, double(4.5))).

test('findall(+Succeeds ; +Fails)'):-
	mongolog_tests:test_call(
		(	findall(X,
				(	(X is (Num + 5))
				;	(Num > 5, X is (Num * 2))
				),
				Results)
		),
		Num, double(4.5)
	),
	assert_true(ground(Results)),
	assert_equals(Results,[9.5]).

test('findall(+Succeeds ; +Fails ; +Succeeds)'):-
	mongolog_tests:test_call(
		(	findall(X,
				(	(X is (Num + 5))
				;	(Num > 5, X is (Num * 2))
				;	(X is (Num + 6))
				),
				Results)
		),
		Num, double(4.5)
	),
	assert_true(ground(Results)),
	assert_equals(Results,[9.5,10.5]).

test('findall with ungrounded'):-
	mongolog_tests:test_call(
		(	findall(X,
				(	true
				;	(X is (Num * 2))
				),
				Results)
		),
		Num, double(4.5)
	),
	assert_unifies(Results,[_,9.0]),
	( Results=[Var|_] -> assert_true(var(Var)) ; true ).

test('findall 1-element list'):-
	mongolog_tests:test_call(
		(	findall([X],
				(	X is Num + 5
				;	X is Num * 2
				),
				Results)
		),
		Num, double(4.5)
	),
	assert_true(ground(Results)),
	assert_unifies(Results,[[9.5],[9.0]]).

test('findall 2-element list'):-
	mongolog_tests:test_call(
		(	findall([X,Y],
				(	(X is (Num + 5), Y is X + 1)
				;	(X is (Num * 2), Y is X + 2)
				),
				Results)
		),
		Num, double(4.5)
	),
	assert_true(ground(Results)),
	assert_unifies(Results,[[9.5,10.5],[9.0,11.0]]).

test('findall 1-ary term'):-
	mongolog_tests:test_call(
		(	findall(test(X),
				(	X is (Num + 5)
				;	X is (Num * 2)
				),
				Results)
		),
		Num, double(4.5)
	),
	assert_true(ground(Results)),
	assert_unifies(Results,[test(9.5), test(9.0)]).

test('findall 2-ary term'):-
	mongolog_tests:test_call(
		(	findall(test(X,Y),
				(	(X is (Num + 5), Y is X + 1)
				;	(X is (Num * 2), Y is X + 2)
				),
				Results)
		),
		Num, double(4.5)
	),
	assert_true(ground(Results)),
	assert_unifies(Results,[
		test(9.5,10.5), test(9.0,11.0) ]).

test('findall+length'):-
	mongolog_tests:test_call(
		(	findall(X,
				((X is Num + 5);(X is Num * 2)),
				List),
			length(List, Length)
		),
		Num, double(4.5)),
	assert_equals(Length, 2).

test('findall+max_list'):-
	mongolog_tests:test_call(
		(	findall(X,
				X is Num + 5,
				NumberList),
			max_list(NumberList, Max)
		),
		Num, double(4.5)),
	assert_equals(Max, 9.5).

test('findall+member'):-
	findall(Val,
		mongolog_tests:test_call(
			(	findall(X,
					((X is Num + 5);(X is Num * 2)),
					List),
				member(Val, List)
			),
			Num, double(4.5)),
		Results),
	assert_equals(Results,[9.5,9.0]).

test('findall+length'):-
	mongolog_tests:test_call(
		(	findall(X,
				((Num < 4.0, X is Num + 5);(Num > 4.0, X is Num * 2)),
				List),
			length(List, Length)
		),
		Num, double(4.5)),
	assert_equals(Length,1).

test('findall/2+length'):-
	mongolog_tests:test_call(
		(	findall(
				((Num < 4.0, X is Num + 5);(Num > 4.0, X is Num * 2)),
				List),
			length(List, Length)
		),
		Num, double(4.5)),
	assert_equals(Length,1).

test('findall+nth0'):-
	mongolog_tests:test_call(
		(	findall(X,
				((X is Num + 5);(X is Num * 2)),
				List),
			nth0(0, List, Val)
		),
		Num, double(4.5)),
	assert_equals(Val,9.5).

test('(fail;findall)+length'):-
	mongolog_tests:test_call(
		(	( (	( Num < 4.0 )
			;	( Num > 4.0, findall(X,
					((X is Num + 5);(X is Num * 2)),
					InnerList) )
			)),
			assign(List, InnerList)
		),
		Num, double(4.5)),
	assert_equals(InnerList,[9.5,9.0]),
	assert_equals(List,[9.5,9.0]).

:- end_tests('mongolog_findall').
