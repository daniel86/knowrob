:- module(mongolog_lookup,
	[ lookup_call/4,
	  lookup_findall/6,
	  lookup_let_doc/2
	]).

:- use_module('set').
:- use_module('../variables').

%% lookup_call(+Goal, +Context, -StepVars, -Pipeline)
%
%
lookup_call(Goal, Context, StepVars, Pipeline) :-
	% compile lookup stage
	lookup_findall(Goal, 'next', [], Context, StepVars, LookupStage),
	% the inner goal is not satisfiable if Pipeline==[]
	LookupStage \== [],
	findall(Stage,
		% lookup solutions to Goal in list at field "next"
		(	Stage=LookupStage
		% unwind "next" field
		;	Stage=['$unwind',string('$next')]
		% set variables from "next" field
		;	set_next_vars(StepVars, Stage)
		% remove "next" field again
		;	Stage=['$unset',string('next')]
		),
		Pipeline).


%%
% find all records matching a query and store them
% in an array.
%
lookup_findall(Goal, ArrayKey, Suffix, Context, StepVars,
		['$lookup', [
			['from',     string(Coll)],
			['as',       string(ArrayKey)],
			['let',      LetDoc],
			['pipeline', array(Pipeline1)]
		]]) :-
	% get variables referred to in query
	option(outer_vars(OuterVars), Context, []),
	% remove input selected flag
	mongolog:unassign_input(Context, Context_inner),
	% generate inner pipeline
	mongolog:compile_terms(
		Goal,
		OuterVars->_,
		CompilerOutput,
		Context_inner),
	% read from compiler output
	option(input_collection(Coll), CompilerOutput, _),
	once((ground(Coll);Coll=one)),
	mongolog:compiled_document(CompilerOutput, Pipeline),
	mongolog:compiled_substitution(CompilerOutput, StepVars),
	% pass variables from outer goal to inner if they are referred to in the inner goal.
	% TODO: only include intersection of OuterVars and StepVars
	lookup_let_doc(OuterVars, LetDoc),
	% set all let variables so that they can be accessed without aggregate operators in Pipeline
	lookup_set_vars(OuterVars, SetVars),
	% compose inner pipeline
	(	SetVars==[] -> Pipeline0=Pipeline
	;	append([['$set', SetVars]], Pipeline, Pipeline0)
	),
	append(Pipeline0,Suffix,Pipeline1).

%%
lookup_let_doc(Vars, LetDoc) :-
	findall([Key,string(Value)],
		(	member([Key,_], Vars),
			atom_concat('$',Key,Value)
		),
		LetDoc0),
	list_to_set(LetDoc0,LetDoc).


%%
% let doc above ensures all vars can be accessed.
% this does also work if the let var was undefined.
% then the set below is basically a no-op.
% e.g. this runs through _without_ assigning "key" field:
%
%       db.one.aggregate([{'$lookup': {
%			from: "one",
%			as: "next",
%			let: { "test": "$test"},
%			pipeline: [{'$set': {"key": "$$test"}}]
%		}}])
%
lookup_set_vars(Vars, SetVars) :-
	findall([Y,string(Y0)],
		(	member([Y,_], Vars),
			atom_concat('$$',Y,Y0)
		),
		SetVars0),
	list_to_set(SetVars0,SetVars).

