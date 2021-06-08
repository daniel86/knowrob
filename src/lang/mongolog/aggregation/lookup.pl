:- module(mongolog_lookup,
	[ lookup_call/5,
	  lookup_findall/7,
	  lookup_let_doc/2
	]).

:- use_module('set').
:- use_module('../variables').

%%
%
%
lookup_call(
		Goal,
		Suffix,
		Context,
		Pipeline,
		StepVars) :-
	lookup_findall(
		'next',
		Goal,
		[], Suffix,
		Context,
		StepVars,
		Lookup),
	% the inner goal is not satisfiable if Pipeline==[]
	Lookup \== [],
	findall(Step,
		% generate steps
		(	Step=Lookup
		% unwind "next" field
		;	Step=['$unwind',string('$next')]
		% set variables from "next" field
		;	set_next_vars(StepVars, Step)
		% remove "next" field again
		;	Step=['$unset',string('next')]
		),
		Pipeline).


%%
% find all records matching a query and store them
% in an array.
%
lookup_findall(
		ArrayKey,
		Goal,
		Prefix, Suffix,
		Context,
		StepVars,
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
	lookup_let_doc(OuterVars, LetDoc),
	% set all let variables so that they can be accessed without aggregate operators in Pipeline
	lookup_set_vars(OuterVars, SetVars),
	% compose inner pipeline
	(	SetVars=[]
	->	Prefix0=Prefix
	;	Prefix0=[['$set', SetVars] | Prefix]
	),
	append(Prefix0,Pipeline,Pipeline0),
	append(Pipeline0,Suffix,Pipeline1).

%%
lookup_let_doc(InnerVars, LetDoc) :-
	findall([Key,string(Value)],
		(	member([Key,_], InnerVars),
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
lookup_set_vars(InnerVars, SetVars) :-
	findall([Y,string(Y0)],
		(	member([Y,_], InnerVars),
			atom_concat('$$',Y,Y0)
		),
		SetVars0),
	list_to_set(SetVars0,SetVars).

