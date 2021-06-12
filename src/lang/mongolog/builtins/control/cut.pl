:- module(mongolog_cut,
		[ has_cut/1,
		  expand_cut/3
		]).
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

%% has_cut(+Goal) is semidet.
%
%
has_cut(Goal) :-
	is_list(Goal), !,
	memberchk('!',Goal).

has_cut(Goal) :-
	comma_list(Goal,List),
	has_cut(List).

%% expand_cut(+Goal, +SuccessorClauses, -Expanded) is semidet.
%
%
expand_cut(Goal, SuccessorClauses, Expanded) :-
	% split the goal into part left-of and part right-of first cut
	split_cut(Goal,Before,After),
	( Before==[] -> If=true   ; If=Before ),
	( After==[]  -> Then=true ; Then=After ),
	expand_cut(If, Then, SuccessorClauses, Expanded),
	!.

expand_cut(If, Then, [], Expanded) :-
	% translate into once(if),then
	lang_query:kb_expand((once(If), Then), Expanded).

expand_cut(If, Then, Else, Expanded) :-
	% translate into if-then-else
	lang_query:kb_expand((If -> Then ; Else), Expanded).

%%
split_cut(Goal,Before,After) :-
	is_list(Goal), !,
	split_cut1(Goal,Before,After).
split_cut(Goal,Before,After) :-
	comma_list(Goal,List),
	split_cut1(List,Before,After).

split_cut1([],_,_) :- !, fail.
split_cut1([!|Xs],[],Xs) :- !.
split_cut1([X|Xs],[X|Ys],Zs) :-
	split_cut1(Xs,Ys,Zs).


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
