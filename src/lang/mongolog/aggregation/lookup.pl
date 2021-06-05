:- module(mongolog_lookup,
	[ lookup_call/5,
	  lookup_findall/7,
	  lookup_let_doc/2
	]).

:- use_module('set').

%% FIXME: redundant with call foo
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
	option(outer_vars(OuterVars), Context),
	% within a disjunction VV provides mapping between
	% original and copied variables (see control.pl)
	option(orig_vars(VOs), Context, []),
	option(copy_vars(VCs), Context, []),
	% remove input selected flag
	once((select_option(input_assigned, Context, Context0) ; Context0=Context)),
	once((select_option(input_collection(_), Context0, Context1) ; Context1=Context0)),
	% generate inner pipeline
	mongolog:compile_terms(Terminals, OuterVars->_InnerVars, Output0, Context1),
	% find join collection
	option(input_collection(Coll), Output0, _),
	once((ground(Coll);Coll=one)),
	%
	memberchk(document(Pipeline), Output0),
	memberchk(variables(StepVars0), Output0),
	% get list of variables whose copies have received a grounding
	% in compile_terms, as these need some special handling
	% to avoid that the original remains ungrounded.
	% GroundVars0: key-original variable mapping
	% GroundVars1: key-grounding mapping
	select_option(outer_vars(OuterVars), Context, Context_x0, []),
	append(StepVars0,OuterVars,OuterVars_x0),
	grounded_vars(
		[outer_vars(OuterVars_x0)|Context_x0],
		[VOs,VCs], GroundVars0, GroundVars1),
	% add variables that have received a grounding in compile_terms
	% to StepVars
	append(GroundVars0, StepVars0, StepVars1),
%	append(GroundVars0, OuterVars, StepVars1),
%	append(GroundVars0, [], StepVars1),
	list_to_set(StepVars1, StepVars),
	% finally also add user supplied variables to the list
	(	option(additional_vars(AddVars), Context)
	->	append(AddVars, StepVars, StepVars2)
	;	StepVars2 = StepVars
	),
	% pass variables from outer goal to inner if they are referred to
	% in the inner goal.
%	lookup_let_doc(StepVars2, LetDoc),
	lookup_let_doc(OuterVars, LetDoc),
	% set all let variables so that they can be accessed
	% without aggregate operators in Pipeline
%	lookup_set_vars(StepVars2, SetVars),
	lookup_set_vars(OuterVars, SetVars),
	% compose inner pipeline
	(	SetVars=[] -> Prefix0=Prefix
	;	Prefix0=[['$set', SetVars] | Prefix]
	),
	append(Prefix0,Pipeline,Pipeline0),
	% $set compile-time grounded vars for later unification.
	% this is needed because different branches cannot ground the same
	% variable to different values compile-time.
	% hence the values need to be assigned within the query.
	(	GroundVars1=[] -> Suffix0=Suffix
	;	Suffix0=[['$set', GroundVars1] | Suffix]
	),
	append(Pipeline0,Suffix0,Pipeline1).

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
	mongolog:var_key_or_val(VC, Ctx, Val),
	grounded_vars(Ctx,VOs,VCs,Xs,Ys).
grounded_vars(Ctx,[_|VOs],[_|VCs],Xs,Ys) :-
	grounded_vars(Ctx,VOs,VCs,Xs,Ys).

%grounded_vars([],_,[],[]) :- !.
%grounded_vars([VO-VC|VV],Ctx,[[Key,VO]|Xs],[[Key,Val]|Ys]) :-
%	nonvar(VC),
%	\+ is_dict(VC),
%	!,
%	var_key(VO, Ctx, Key),
%	var_key_or_val(VC, Ctx, Val),
%	grounded_vars(VV,Ctx,Xs,Ys).
%grounded_vars([_|VV],Ctx,Xs,Ys) :-
%	grounded_vars(VV,Ctx,Xs,Ys).
