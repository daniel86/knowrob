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
lookup_call(Terminals, Suffix, Ctx, Pipeline, StepVars) :-
	lookup_findall('next', Terminals, [], Suffix, Ctx, StepVars, Lookup),
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
		Pipeline),
	% the inner goal is not satisfiable if Pipeline==[]
	Lookup \== [].


%%
% find all records matching a query and store them
% in an array.
%
lookup_findall(ArrayKey, Terminals,
		Prefix, Suffix,
		Context, StepVars,
		['$lookup', [
			['from', string(Coll)],
			['as', string(ArrayKey)],
			['let', LetDoc],
			['pipeline', array(Pipeline1)]
		]]) :-
	% get variables referred to in query
	option(outer_vars(OuterVars), Context, []),
	% remove input selected flag
	once((select_option(input_assigned, Context, Context0) ; Context0=Context)),
	once((select_option(input_collection(_), Context0, Context1) ; Context1=Context0)),
	% generate inner pipeline
	mongolog:compile_terms(Terminals, OuterVars->_InnerVars, Output0, Context1),
	% find join collection
	option(input_collection(Coll), Output0, _),
	once((ground(Coll);Coll=one)),
	%
	mongolog:compiled_document(Output0, Pipeline),
	mongolog:compiled_substitution(Output0, StepVars),
	% pass variables from outer goal to inner if they are referred to in the inner goal.
	lookup_let_doc(OuterVars, LetDoc),
	% set all let variables so that they can be accessed without aggregate operators in Pipeline
	lookup_set_vars(OuterVars, SetVars),
	% compose inner pipeline
	(	SetVars=[] -> Prefix0=Prefix
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
lookup_set_vars(InnerVars, SetVars) :-
	% NOTE: let doc above ensures all vars can be accessed.
	%       this does also work if the let var was undefined.
	%       then the set below is basically a no-op.
	%       e.g. this runs through _without_ assigning "key" field:
	%
	%       db.one.aggregate([{'$lookup': {
	%			from: "one",
	%			as: "next",
	%			let: { "test": "$test"},
	%			pipeline: [{'$set': {"key": "$$test"}}]
	%		}}])
	%
	findall([Y,string(Y0)],
		(	member([Y,_], InnerVars),
			atom_concat('$$',Y,Y0)
		),
		SetVars0),
	list_to_set(SetVars0,SetVars).

