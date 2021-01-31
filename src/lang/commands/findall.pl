:- module(lang_findall, []).

:- use_module(library('db/mongo/client'),
		[ mng_one_db/2 ]).
:- use_module(library('lang/compiler')).

%% register query commands
:- query_compiler:add_command(findall, [ask]).
% TODO: support bagof (then, setof := bagof o sort)
%:- query_compiler:add_command(bagof,   [ask]).
%:- query_compiler:add_command(setof,   [ask]).

%%
query_compiler:step_expand(
		findall(Template, Goal, List),
		findall(Template, Expanded, List),
		Context) :-
	query_expand(Goal, Expanded, Context).

%% setof(+Template, +Goal, -Set)
% Equivalent to bagof/3, but sorts the result using sort/2 to
% get a sorted list of alternatives without duplicates.
%
%query_compiler:step_expand(
%		setof(Template, Goal, Set),
%		[ bagof(Template, Expanded, List), sort(List, Set) ],
%		Context) :-
%	query_expand(Goal, Expanded, Context).

%%
% findall only exposes the List variable to the outside.
%
query_compiler:step_var(
		findall(Template, _, List),
		[List_var, list(List,Template)]) :-
	query_compiler:var_key(List, List_var).

%% findall(+Template, :Goal, -Bag)
% Create a list of the instantiations Template gets successively on
% backtracking over Goal and unify the result with Bag.
% Succeeds with an empty list if Goal has no solutions.
%
query_compiler:step_compile(
		findall(Template, Terminals, List),
		Context, Pipeline) :-
	% option(mode(ask), Context),
	findall(Step,
		% perform lookup, collect results in 'next' array
		(	query_compiler:lookup_array('next',Terminals,
				[], [], Context, _, Step)
		% $set the list variable field from 'next' field
		;	set_result(Template, List, Step)
		% array at 'next' field not needed anymore
		;	Step=['$unset', string('next')]
		),
		Pipeline).

%%
% findall $set receives a list of matching documents in "next" field.
% $set uses additional $map operation to only keep the fields of
% variables referred to in Template.
%
set_result(Template, List,
	['$set',
		[List_Key, ['$map',[
			['input',string('$next')],
			['in', ElemProjection]
		]]]
	]) :-
	query_compiler:var_key(List, List_Key),
	term_variables(Template, PatternVars),
	%
	findall([Key, string(Val)],
		(	(	Key='v_scope', Val='$$this.v_scope' )
		;	(	member(Var,PatternVars),
				% FIXME: could be that Var is not ground, thus we need conditional
				%           set, then set to fallback value null or $$REMOVE field
				query_compiler:var_key(Var, Key),
				atom_concat('$$this.', Key, Val)
			)
		),
		ElemProjection).