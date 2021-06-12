:- module(mongolog_disjunction, []).
/** <module> Control structures in mongolog programs.

The following predicates are supported:

| Predicate   | Arguments |
| ---         | ---       |
| ;/2         | :Goal1, :Goal2 |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=control
@license BSD
*/

:- use_module('../../mongolog').
:- use_module('../../variables').
:- use_module('../../aggregation/lookup').
:- use_module('../../aggregation/set').
:- use_module('cut').

%% query commands
:- mongolog:add_command(;).


% step through goals of a disjunction and expand them.
% special handling is needed for cut-elimination via program
% transformation
lang_query:step_expand((A0;A1), Expanded) :-
	semicolon_list((A0;A1), Goals),
	expand_disunction(Goals, ExpandedGoals),
	semicolon_list(Expanded, ExpandedGoals).

%
expand_disunction([],[]) :- !.
expand_disunction([X|Xs],[Expanded]) :-
	% special handling in case X contains a cut
	has_cut(X),!,
	semicolon_list(Clauses, Xs),
	expand_cut(X, Clauses, Expanded).
expand_disunction([X|Xs],[Y|Ys]) :-
	% else simply expand X
	lang_query:kb_expand(X,Y),
	expand_disunction(Xs,Ys).

%lang_query:step_expand(';'(A0,A1), ';'(B0,B1)) :-
%	lang_query:kb_expand(A0,B0),
%	lang_query:kb_expand(A1,B1).

%% :Goal1 ; :Goal2
% The ‘or' predicate.
% Unfortunately mongo does not support disjunction of aggregate pipelines.
% So we proceed as follows:
% 1. for each goal, use $lookup to store results into some array field
% 2. then concat all these array fields into single array stored in field 'next'
% 3. unwind the next array
%
% TODO: use $unionWith (mongo DB 4.4) to implement disjunction
%				h <- b1, ..., bn, (bn+1 ; ... ; bk)
%       can be written as:
%               h <- b1, ..., bn, bn+1, union(b1, ..., bn, bn+2), ...., union(b1, ..., bn, bk)
%       the duplication is needed because within union it is not possible to access instantiations
%       of b1, ..., bn (i.e. there is no *let* argument for union).
%       - IDEA: create a view if n>0
%				h' <- bn+1, union(bn+2), ..., union(bk)
%				h  <- b1, ..., bn, h'
%          this is fast if h' can use indices for matching against b1...bn
%		- Approach:
%			- compile into unionWith only if disjunction is first goal in body
%				(todo: or if left side of disjunction fulfills some constaints?)
%			- program transformation: create disjunction views where possible
% TODO: $facet command could be used for some simple disjunctions.
%       but it _cannot_ use search indices. so never use $lookup+$match within $facet.
%       this limits its usefulness, but maybe there are some cases where it is superior?
%
mongolog:step_compile1(';'(A,B), Ctx,
		[ document(Pipeline),
		  variables(StepVars),
		  input_collection(one)
		]) :-
	% TODO: support input collections here
	merge_options([input_assigned],Ctx,Ctx0),
	% get disjunction as list
	semicolon_list(';'(A,B), Goals),
	% generate one variable for each goal
	length(Goals,NumGoals),
	length(FindallVars,NumGoals),
	% get a list of tuples (pipeline, list variable key)
	% the result of each pipeline is written to a list,
	% and resulting lists are concatenated later to
	% achieve disjunction.
	compile_disjunction(Goals, FindallVars, Ctx0, FindallStages, StepVars0),
	FindallStages \== [],
	aggregate_disjunction(FindallStages, StepVars0, Pipeline, StepVars).

%%
% each goal in a disjunction compiles into a lookup expression.
%
compile_disjunction([], [], _, [], []) :- !.

compile_disjunction(
		[Goal|RestGoals],
		[FindallVar|RestVars],
		Ctx,
		[[Stage,Key,Goal]|Ys],
		StepVars) :-
	select_option(outer_vars(OuterVarsOrig), Ctx, Ctx0, []),
	select_option(copy_vars(CopiedVars1), Ctx0, Ctx1, []),
	select_option(head_vars(HeadVarsOrig), Ctx1, Ctx2, []),
	% ensure goal is a list
	(	is_list(Goal)
	->	GoalOrig=Goal
	;	comma_list(Goal, GoalOrig)
	),
	% compile-time grounding of variables can be done in goals of a disjunction.
	% however, a variable referred to in different goals of a disjunction cannot
	% be instantiated to the same value compile-time.
	% the workaround is to create a copy of the goal here,
	% and make sure the different variables are accessed in mongo with a common key
	% this is done by copy_vars/4.
	copy_term(GoalOrig, GoalCopy),
	term_variables(GoalOrig, VarsOrig),
	term_variables(GoalCopy, VarsCopy),
	copy_vars(OuterVarsOrig, VarsOrig, VarsCopy, OuterVarsCopy),
	copy_vars(HeadVarsOrig, VarsOrig, VarsCopy, HeadVarsCopy),
	% remember the mapping between original and copy of the variables,
	% This is important as the copies may receive groundings in the compilation
	% process (when lookup_findall is called)
	pairs_keys_values(VV, VarsOrig, VarsCopy),
	copy_vars(CopiedVars1, VarsOrig, VarsCopy, CopiedVars2),
	get_varkeys(Ctx, CopiedVars2, VV, VOs, VCs),
	% compile the step
	merge_options([
		outer_vars(OuterVarsCopy),
		head_vars(HeadVarsCopy),
		orig_vars(VOs),
		copy_vars(VCs)
	], Ctx2, InnerCtx),
	var_key(FindallVar, Ctx, Key),
	lookup_findall(Key, GoalCopy,
		[],
		PipelineSuffix,
		InnerCtx,
		StepVars_copy0,
		Stage),
	!,
	
	merge_substitutions(StepVars_copy0, OuterVarsCopy, OuterVars_x0),
	% get list of variables whose copies have received a grounding
	% in compile_terms, as these need some special handling
	% to avoid that the original remains ungrounded.
	% GroundVars0: key-original variable mapping
	% GroundVars1: key-grounding mapping
	grounded_vars(
		[outer_vars(OuterVars_x0)|Ctx0],
		[VOs,VCs], GroundVars0, GroundVars1),
	(	GroundVars1=[]
	->	PipelineSuffix=[] %Suffix0=Suffix
	;	PipelineSuffix=[['$set', GroundVars1]]
	),
	% add variables that have received a grounding in compile_terms to StepVars
	merge_substitutions(GroundVars0, StepVars_copy0, StepVars_copy),
	% map copied step-vars back to original
	copy_vars(StepVars_copy, VarsCopy, VarsOrig, StepVars_this),
	% then merge step-vars into outer vars of next step such that variables have a common key
	merge_substitutions(StepVars_this, OuterVarsOrig, OuterVarsNext1),
	% compile remaining goals
	compile_disjunction(RestGoals, RestVars,
		[outer_vars(OuterVarsNext1)|Ctx0], Ys, StepVars_rest),
	merge_substitutions(StepVars_this, StepVars_rest, StepVars).

compile_disjunction([_|Goals], [_|Vars], Ctx, Pipelines, StepVars) :-
	% skip goal if compilation was "surpressed" above
	compile_disjunction(Goals, Vars, Ctx, Pipelines, StepVars).


%%
%aggregate_disjunction([[_,_,SingleGoal]], StepVars, Pipeline, StepVars) :-
%	% special handling in case the disjunction compiles into a single goal
%	% no disjunction needed then.
%	!,
%	mongolog:compile_term(SingleGoal, OuterVars->_InnerVars, Output, Context).

aggregate_disjunction(FindallStages, StepVars, Pipeline, StepVars) :-
	% get a list of list variable keys
	findall(string(X),
		member([_,X,_],FindallStages),
		VarKeys),
	% prepend "$" for accessing values
	maplist([string(In),string(Out)]>>
		atom_concat('$',In,Out),
		VarKeys, VarValues),
	%
	findall(Stage,
		% first, compute array of results for each facet
		(	member([Stage,_,_], FindallStages)
		% second, concatenate the results
		;	Stage=['$set', ['next', ['$concatArrays', array(VarValues)]]]
		% third, delete unneeded array
		;	Stage=['$unset', array(VarKeys)]
		% unwind all solutions from disjunction
		;	Stage=['$unwind', string('$next')]
		% finally project the result of a disjunction goal
		;	set_next_vars(StepVars, Stage)
		% and unset the next field
		;	Stage=['$unset', string('next')]
		),
		Pipeline
	).

%%
% Create a copy of a variable map with fresh variables in the copy
% but the same keys.
%
copy_vars(ReferredVars, TermVarsOrig, TermVarsCopy, CopiedVars) :-
	copy_vars1(ReferredVars, TermVarsOrig, TermVarsCopy, CopiedVars0),
	copy_vars2(ReferredVars, CopiedVars0, CopiedVars).
	
copy_vars1(_, [], [], []) :- !.
copy_vars1(ReferredVars, [X|Xs], [Y|Ys], [[Key,Y]|Zs]) :-
	member([Key,Z], ReferredVars),
	Z == X,
	!,
	copy_vars1(ReferredVars, Xs, Ys, Zs).
copy_vars1(ReferredVars, [_|Xs], [_|Ys], Zs) :-
	copy_vars1(ReferredVars, Xs, Ys, Zs).

%%
copy_vars2([], _, []) :- !.
copy_vars2([[Key,X]|Xs], Vars1, [[Key,term(Z)]|Ys]) :-
	compound(X),
	X=term(X1),!,
	copy_vars2([[Key,X1]|Xs], Vars1, [[Key,Z]|Ys]).
copy_vars2([[Key,X]|Xs], Vars1, [[Key,Z]|Ys]) :-
	(	memberchk([Key,Y],Vars1)
	->	Z=Y
	;	Z=X
	),
	copy_vars2(Xs,Vars1,Ys).

%
get_varkeys(_, _, [], [], []) :- !.
get_varkeys(Ctx, ParentVars,
		[VO-VC|VV],
		[[Key,VO]|VOs],
		[[Key,VC]|VCs]) :-
	once((
		( member([Key,X],ParentVars), X == VO )
	;	( var_key(VO, Ctx, Key) )
	)),
	get_varkeys(Ctx,ParentVars,VV,VOs,VCs).


% yield list of variables whose copies have received a grounding
% VO: original variable
% VC: copied variable
grounded_vars(Ctx,[VOs,VCs],Xs,Ys) :-
	grounded_vars(Ctx,VOs,VCs,Xs,Ys).
grounded_vars(_,[],[],[],[]) :- !.
grounded_vars(Ctx,
		[[Key,VO]|VOs],
		[[Key,VC]|VCs],
		[[Key,VO]|Xs],
		[[Key,Val]|Ys]) :-
	nonvar(VC),
	\+ is_dict(VC),
	!,
	arg_val(VC, Ctx, Val),
	grounded_vars(Ctx,VOs,VCs,Xs,Ys).
grounded_vars(Ctx,[_|VOs],[_|VCs],Xs,Ys) :-
	grounded_vars(Ctx,VOs,VCs,Xs,Ys).


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_disjunction').

test('(+Goal ; +Goal)'):-
	findall(X,
		mongolog_tests:test_call(
			(	(X is (Num + 5))
			;	(X is (Num * 2))
			),
			Num, 4.5),
		Results),
	assert_unifies(Results,[_,_]),
	assert_true(ground(Results)),
	assert_true(memberchk(9.5,Results)),
	assert_true(memberchk(9.0,Results)).

test('(+Goal ; fail)'):-
	findall(X,
		mongolog_tests:test_call(
			(	(X is (Num + 5))
			;	fail
			),
			Num, 4.5),
		Results),
	assert_equals(Results,[9.5]).

test('(fail ; fail)'):-
	assert_false(mongolog_tests:test_call(
		((Num > 5) ; fail), Num, 4.5)).

test('(+Goal ; true)'):-
	findall(X,
		mongolog_tests:test_call(
			(	(X is (Num + 5))
			;	true
			),
			Num, 4.5),
		Results),
	assert_unifies(Results,[_,_]),
	assert_true(memberchk(9.5,Results)),
	assert_true(once((member(Var,Results), var(Var)))).

test('(+Goal ; $early_evaluated)'):-
	% `X is 15` is evaluated compile-time, while
	% the other term must be computed at run-time. 
	findall(X,
		mongolog_tests:test_call(
			(	(X is (Num + 5))
			;	(X is 15)
			),
			Num, 4.5),
		Results),
	assert_unifies(Results,[_,_]),
	assert_true(memberchk(9.5,Results)),
	assert_true(memberchk(15.0,Results)).

test('(+Goal ; +PrunedGoal)'):-
	mongolog_tests:test_call(
		(	(X is (Num + 5))
		;	(7 < 5, X is (Num * 2))
		),
		Num, 4.5),
	assert_equals(X,9.5).

test('(((+Goal,+Goal) ; (+Goal,+Goal)))') :-
	findall([X,Y],
		mongolog_tests:test_call(
			(	(X is Num, Y is X + 1)
			;	(X is Num, Y is X + 2)
			),
			Num, 4.5),
		Results),
	assert_equals(Results, [[4.5,5.5], [4.5,6.5]]).

test('(((+G ; +G), +G) ; +G)') :-
	findall([X,Y],
		mongolog_tests:test_call(
			(	(X is Num, ((X < 2.0 ; X > 4.0), Y is X + 1))
			;	(X is Num, Y is X + 2)
			),
			Num, 4.5),
		Results),
	assert_equals(Results, [[4.5,5.5], [4.5,6.5]]).

:- end_tests('mongolog_disjunction').
