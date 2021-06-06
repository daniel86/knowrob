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

%% setof(+Template, +Goal, -Set)
% Equivalent to bagof/3, but sorts the result using sort/2 to
% get a sorted list of alternatives without duplicates.
%
%lang_query:step_expand(
%		setof(Template, Goal, Set),
%		','(bagof(Template, Expanded, List), sort(List, Set))) :-
%	lang_query:kb_expand(Goal, Expanded).

%% findall(+Template, :Goal, -Bag)
% Create a list of the instantiations Template gets for different
% cases where Goal is true.
% Succeeds with an empty list if Goal has no solutions.
%
% The Goal is executed within a $lookup operation for every input document.
% TODO: If there is only one incoming document, it would be possible
%       to avoid $lookup and use $group after the Goal has been executed.
%
mongolog:step_compile1(findall(_, Goal, _), Ctx, []) :-
	% findall views cannot be created if
	% the findall-goal shares a variable with the head of the rule that is compiled
	option(compile_mode(view), Ctx),
	goal_var_in_head(Goal, Ctx),
	!,
	fail.

mongolog:step_compile1(
		findall(Template, Terminals, List), Ctx,
		% CompilerOutput:
		[ document(Pipeline),
		  variables(StepVars),
		  % if not assigned otherwise, draw a document from "one" collection
		  input_collection(OneColl)
		]) :-
	mng_one_db(_,OneColl),
	% get field key for list and variables in template
	goal_vars(List, Ctx, StepVars),
	goal_vars(Template, Ctx, TemplateVars),
	% add template vars to compile context.
	% this is important to enforce that vars in Template are referred
	% to with a common key within findall.
	% note that the vars should not be added to the "outer_vars"
	% array as variables in template are _not_ exposed to the outside.
	% TODO: why we cannot add to outer_vars? it is only given to lookup afterall.
	%        or are the vars included in InnerStepVars below for some reason?
	select_option(step_vars(SV), Ctx, Ctx0, []),
	append(TemplateVars, SV, SV0),
	list_to_set(SV0,SV1),
	Ctx1=[step_vars(SV1)|Ctx0],
	% compile a $lookup query
	lookup_findall(
		% lookup collection
		't_next',
		% lookup goal
		Terminals,
		% prefix/suffix for inner pipeline
		[],[],
		% compile context
		Ctx1, InnerStepVars,
		% the $lookup query
		Lookup),
	% make sure to use a common key with the inner pipeline when instantiating
	% the template.
	merge_options([step_vars(InnerStepVars)],Ctx1,Ctx2),
	merge_options([step_vars(StepVars)],Ctx1,Ctx3),
	% Get the $map expression to instantiate the template for each list element.
	% NOTE: it is not allowed due to handling here to construct
	% the pattern in a query, it must be given in the findall command compile-time.
	% if really needed it could be done more dynamic, I think.
	template_instantiation(Template, Ctx2, Instantiation),
	%
	findall(Step,
		% perform lookup, collect results in 'next' array
		(	Step=Lookup
		% $set the list variable field from 'next' field
		;	Step=['$set', ['t_list', ['$map',[
				['input',string('$t_next')],
				['in', Instantiation] ]]]]
		;	set_if_var(List, string('$t_list'), Ctx3, Step)
		;	(
				arg_val(List, Ctx3, List0),
				match_equals(List0, string('$t_list'), Step)
			)
		% array at 'next' field not needed anymore
		;	Step=['$unset', array([string('t_next'), string('t_list')])]
		),
		Pipeline).

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
