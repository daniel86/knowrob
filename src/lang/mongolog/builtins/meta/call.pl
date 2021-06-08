:- module(mongolog_call, []).
/** <module> Meta predicates in mongolog programs.

The following predicates are supported:

| Predicate    | Arguments |
| ---          | ---       |
| call/1       | :Goal |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=metacall
@license BSD
*/

:- use_module('../../mongolog').
:- use_module('../../aggregation/lookup').

%%%% query commands

:- mongolog:add_command(call).
:- mongolog:add_command(call_with_args).

%%%% query expansion

lang_query:step_expand(call(Goal), call(Expanded)) :-
	lang_query:kb_expand(Goal, Expanded).

lang_query:step_expand(call(Goal,Arg1),
		call_with_args(Expanded,[Arg1])) :-
	lang_query:kb_expand(Goal, Expanded).

lang_query:step_expand(call(Goal,Arg1,Arg2),
		call_with_args(Expanded,[Arg1,Arg2])) :-
	lang_query:kb_expand(Goal, Expanded).

lang_query:step_expand(call(Goal,Arg1,Arg2,Arg3),
		call_with_args(Expanded,[Arg1,Arg2,Arg3])) :-
	lang_query:kb_expand(Goal, Expanded).

lang_query:step_expand(call(Goal,Arg1,Arg2,Arg3,Arg4),
		call_with_args(Expanded,[Arg1,Arg2,Arg3,Arg4])) :-
	lang_query:kb_expand(Goal, Expanded).

%% call(:Goal)
% Call Goal. This predicate is normally used for goals that are not known at compile time.
%
mongolog:step_compile1(
		call(Goal), Ctx,
		[ document(Pipeline),
		  variables(StepVars),
		  input_collection(one)
		]) :-
	% TODO: support input collections here
	merge_options([input_assigned],Ctx,Ctx0),
	lookup_call(Goal, [], Ctx0, Pipeline, StepVars).

%% call_with_args(:Goal,:Args)
% Call Goal. This predicate is normally used for goals that are not known at compile time.
%
mongolog:step_compile1(
		call_with_args(Term0,Args), Ctx, Output) :-
	Term0 =.. Buf0,
	append(Buf0, Args, Buf1),
	Term1 =.. Buf1,
	mongolog:step_compile1(call(Term1), Ctx, Output).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_call').

test('call(+Goal)'):-
	mongolog_tests:test_call(
		call(Y is X), X, -3.25),
	assert_equals(Y, -3.25).

test('call(+Functor, -Arg1, +Arg2)'):-
	mongolog_tests:test_call(
		call(is, Arg1, Arg2), Arg2, -3.25),
	assert_equals(Arg1, -3.25).

:- end_tests('mongolog_call').
