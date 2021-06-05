:- module(mongolog_db_predicate,
		[ is_db_predicate/1,
		  db_predicate/3,
		  db_predicate_collection/3,
		  db_predicate_zip/5,
		  db_predicate_create/3,
		  db_predicate_drop/1,
		  db_predicate_compile/3
		]).

:- use_module('../mongolog').
:- use_module('../aggregation/lookup').
:- use_module('../stages/bulk_operation').

:- dynamic db_predicate/3.

%% is_db_predicate(+Indicator) is semidet.
%
% True if PredicateIndicator corresponds to a known mongolog predicate.
%
is_db_predicate(Indicator) :-
	db_predicate(Indicator,_,_).


%% db_predicate(+Term, -Fields, -Options) is semidet.
%
%
db_predicate(Term, Fields, Options) :-
	db_predicate(Term, _, Fields, Options).

%%
db_predicate((/(Functor,Arity)), Functor, Fields, Options) :-
	atom(Functor), number(Arity),
	!,
	db_predicate(Functor, Fields, Options),
	length(Fields,Arity).

db_predicate(Term, Functor, Fields, Options) :-
	compound(Term),
	Term =.. [Functor|Args],
	!,
	db_predicate(Functor, Fields, Options),
	length(Args,Arity),
	length(Fields,Arity).


%% db_predicate_collection(+Predicate, ?DB, ?Collection) is semidet.
%
%
db_predicate_collection(Predicate, DB, Collection) :-
	db_predicate(Predicate, Functor, _, Options),
	% get the database collection of the predicate
	(	(option(collection(CollectionName), Options), ground(CollectionName))
	;	CollectionName=Functor
	),
	mng_get_db(DB, Collection, CollectionName).


%% db_predicate_create(+Functor, +Fields, +Options) is semidet.
%
% Register a predicate that stores facts in the database.
% Functor is the functor of a n-ary predicate, and Fields is
% a n-elemental list of keys associated to the different
% arguments of the predicate.
% Options is a list of optional paramers:
%
% | indices(List) | a list of indices passed to setup_collection/2 |
% | collection(Collection) | name of the collection where predicate is stored, default is to use the functor of the predicate |
%
% Current limitation: there cannot be predicates with the same functor,
% but different arity.
%
% @param Functor functor of the predicate
% @param Fields field names of predicate arguments
% @param Options option list
%
db_predicate_create(Functor, Fields, _) :-
	db_predicate(Functor, Args, _),
	length(Fields,Arity),
	length(Args,Arity),
	!,
	throw(permission_error(modify,database_predicate,Functor)).

db_predicate_create(Functor, Fields, Options) :-
	setup_predicate_collection(Functor, Fields, Options),
	assertz(db_predicate(Functor, Fields, Options)),
	mongolog:add_command(Functor).

%%
setup_predicate_collection(Functor, [FirstField|_], Options) :-
	% TODO support fields marked with -/+ here
	option(indices(Indices), Options, [[FirstField]]),
	(	Indices==[] -> true
	;	setup_collection(Functor, Indices)
	).

%% db_predicate_drop(+Predicate) is det.
%
% Delete all facts associated to predicate with
% given functor.
%
% @param Functor functor of the predicate
%
db_predicate_drop(Predicate) :-
	db_predicate_collection(Predicate, DB, Collection),
	mng_drop(DB, Collection).

%%
db_predicate_compile(Term, Ctx,
		[ document(Pipeline),
		  variables(StepVars0),
		  input_collection(Collection),
		  input_keys(Fields)
		]) :-
	db_predicate(Term, Fields, Opts),!,
	db_predicate_call(Term, Ctx, Pipeline, StepVars, Collection),
	%
	add_array_vars(Term, Opts, Ctx, StepVars, StepVars0).

%
add_array_vars(Term, Opts, Ctx, StepVars, StepVars0) :-
	option(rdfs_fields(RDFSFields), Opts, []),
	RDFSFields \== [],
	bagof([K0,_],
		(	mongolog:goal_var(Term, Ctx, [K,_]),
			memberchk(K,RDFSFields),
			atom_concat(K,'_s',K0)
		),
		ArrayVars),
	!,
	append(StepVars, ArrayVars, StepVars0).
add_array_vars(_, _, _, StepVars, StepVars).

%%
db_predicate_call(Term, Ctx, Pipeline, StepVars, Collection) :-
	db_predicate_zip(Term, Ctx, Zipped, Ctx_pred, read),
	option(collection(Collection), Ctx_pred),
	option(step_vars(StepVars), Ctx_pred),
	unpack_compound(Zipped, Unpacked),
	%
	findall(InnerStep,
		match_predicate(Unpacked, Ctx, Ctx_pred, InnerStep),
		InnerPipeline),
	db_predicate_call1(Unpacked, InnerPipeline, Ctx_pred, Pipeline).

%%
db_predicate_call1(Unpacked, Matches, Ctx, Pipeline) :-
	% no need to perform a $lookup if input collection was assigned before
	\+ option(input_assigned,Ctx),!,
	findall(Step,
		(	member(Step,Matches)
		;	project_predicate1(Unpacked, Ctx, Step)
		),
		Pipeline).
	
db_predicate_call1(Unpacked, InnerPipeline, Ctx, Pipeline) :-
	% option(input_assigned,Ctx),!,
	findall(Step,
		% look-up documents into 't_pred' array field
		(	lookup_predicate('t_pred', InnerPipeline, Ctx, Step)
		% unwind lookup results and assign variables
		;	Step=['$unwind', string('$t_pred')]
		;	project_predicate(Unpacked, Ctx, Step)
		;	Step=['$unset', string('t_pred')]
		),
		Pipeline).

%%
%
db_predicate_zip(Term, Ctx, Zipped, Ctx_zipped, ReadOrWrite) :-
	% get predicate fields and options
	db_predicate(Term, ArgFields, Options),
	length(ArgFields,Arity),
	% get predicate functor and arguments
	Term =.. [_Functor|Args],
	length(Args,Arity),
	% get the database collection of the predicate
	db_predicate_collection(Term, _DB, Collection),
	!,
	% read variable in Term
	mongolog:step_vars(Term, Ctx, StepVars0),
	(	ReadOrWrite==read -> StepVars=StepVars0
	;	add_assertion_var(StepVars0, StepVars)
	),
	% add predicate options to compile context
	merge_options([
		step_vars(StepVars),
		collection(Collection)
	], Ctx, Ctx0),
	merge_options(Ctx0, Options, Ctx_zipped),
	% zip field names with predicate arguments
	zip(ArgFields, Args, Zipped).

%%
predicate_vars([], [], []) :- !.
predicate_vars([Key|Xs], [Arg|Ys], [[Key,Var]|Zs]) :-
	mng_strip_variable(Arg, Arg0),
	term_variables(Arg0, [Var]),!,
	predicate_vars(Xs, Ys, Zs).
predicate_vars([_|Xs], [_|Ys], Zs) :-
	predicate_vars(Xs, Ys, Zs).

%%
unpack_compound([], []) :- !.

unpack_compound([X|Xs], Unpacked) :-
	unpack_compound1(X, Unpacked0),
	unpack_compound(Xs, Unpacked1),
	append(Unpacked0, Unpacked1, Unpacked).

unpack_compound1([Field,Arg], Unpacked) :-
	!, unpack_compound1([Field,Arg,[]], Unpacked).

unpack_compound1([Field,Arg,Is], [[Field,Arg,Is]]) :-
	(ground(Arg);var(Arg)),!.

unpack_compound1([Field,Term,Is], [[FunctorField,Functor,Is]|ArgsUnpacked]) :-
	compound(Term),!,
	% compound term with free variables
	Term =.. [Functor|Args],
	atom_concat(Field,'.value.functor',FunctorField),
	arg_fields_(Field, Args, Is, 0, ArgFields),
	unpack_compound(ArgFields, ArgsUnpacked).

%%
arg_fields_(_, [], _, []) :- !.
arg_fields_(Field, [X|Xs], Is, Index, [[Field,X,[Index|Is]]|Rest]) :-
	Index1 is Index+1,
	arg_fields_(Field, Xs, Index1, Rest).

%%
set_nested_args(Unpacked, ['$set', NestedArgs]) :-
	findall(X,
		(	member([Key,_,Is], Unpacked),
			set_nested_arg(Key,Is,X)
		),
		NestedArgs0),
	NestedArgs0 \== [],
	list_to_set(NestedArgs0, NestedArgs).

set_nested_arg(Key, [I|Is], Arg) :-
	atomic_list_concat(['$',Key,'.value.args'], '', ThisVal),
	atomic_list_concat([Key,I],'_',Y),
	(	Arg=[Y, ['$arrayElemAt', array([string(ThisVal),integer(I)])]]
	;	set_nested_arg(Y, Is, Y)
	).

%% $lookup
%
lookup_predicate(Field, InnerPipeline, Ctx, ['$lookup', [
		['from', string(Collection)],
		['as', string(Field)],
		['let', LetDoc],
		['pipeline', array(InnerPipeline)]
	]]) :-
	option(collection(Collection), Ctx),
	option(step_vars(StepVars), Ctx),
	lookup_let_doc(StepVars, LetDoc).

%% $set
%
project_predicate(Unpacked, Ctx, Step) :-
	member([FieldPath0,Var,Is], Unpacked),
	mongolog:var_key(Var,Ctx,VarKey),
	atomic_list_concat([FieldPath0|Is],'_',FieldPath),
	atom_concat('$t_pred.', FieldPath, FieldQuery),
	% FIXME: some unneeded set's here. can we skip if not one of the predicate variable fields?
	Step=['$set', [VarKey, string(FieldQuery)]].

project_predicate1(Unpacked, Ctx, Step) :-
	member([FieldPath0,Var,Is], Unpacked),
	mongolog:var_key(Var,Ctx,VarKey),
	atomic_list_concat([FieldPath0|Is],'_',FieldPath),
	atom_concat('$', FieldPath, FieldQuery),
	% FIXME: some unneeded set's here. can we skip if not one of the predicate variable fields?
	Step=['$set', [VarKey, string(FieldQuery)]].

%% $match
%
match_predicate(Unpacked, OuterCtx, Ctx, Match) :-
	option(rdfs_fields(RDFSFields), Ctx, []),
	findall(MatchQuery,
		% first match what is grounded compile-time
		% TODO: conditional match can be avoided in case we know the variable
		%       is associated to a input document field!
		(	(	findall([DocKey, ValueQuery],
					(	member([DocKey0,Value,[]], Unpacked),
						(	memberchk(DocKey0, RDFSFields)
						->	atom_concat(DocKey0,'_s',DocKey)
						;	DocKey=DocKey0
						),
						mng_query_value(Value, ValueQuery)
					),
					MatchQuery),
				MatchQuery \== []
			)
		% next match variables grounded in call context
		;	(	member([DocKey,Var,[]], Unpacked),
				match_conditional(DocKey, Var, OuterCtx, Ctx, MatchQuery)
			)
		),
		MatchQueries
	),
	MatchQueries \== [],
	(	MatchQueries=[FirstMatch]
	->	Match=['$match', FirstMatch]
	;	Match=['$match', ['$and', array(MatchQueries)]]
	).

match_predicate(Unpacked, OuterCtx, Ctx, Match) :-
	% compound arguments with free variables need to be handled
	% separately because we cannot write path queries that
	% access array elements.
	set_nested_args(Unpacked,SetArgs),
	(	Match = SetArgs
	;	match_nested(Unpacked, OuterCtx, Ctx, Match)
	).

%%
match_nested(Unpacked, OuterCtx, Ctx, Match) :-
	nested_args(Unpacked, NestedArgs),
	match_predicate(NestedArgs, OuterCtx, Ctx, Match).

%%
nested_args([], []) :- !.

nested_args([[Key,Val,Is]|Xs], [[Key1,Val,[]]|Ys]) :-
	Is \== [],!,
	atomic_list_concat([Key|Is], '_', Key1),
	nested_args(Xs,Ys).

nested_args([_|Xs], Ys) :-
	nested_args(Xs,Ys).

%%
match_conditional(FieldKey, Arg, OuterCtx, Ctx, ['$expr', ['$or', array([
			% pass through if var is not grounded
			['$eq',       array([string(ArgType),   string('var')])],
			% else perform a match
			[ArgOperator, array([string(ArgValue), string(FieldQuery)])]
		])]]) :-
	option(rdfs_fields(RDFSFields), Ctx, []),
	% get the variable in Arg term
	mng_strip_variable(Arg, Arg0),
	term_variables(Arg0, [ArgVar]),!,
	% do not perform conditional match if variable was not referred to before
	is_referenced(ArgVar, OuterCtx),
	mongolog:var_key(ArgVar, Ctx, ArgKey),
	% TODO: need to set let variables or use $ vs $$ conditional
	(	option(input_assigned,Ctx)
	->	atom_concat('$$',ArgKey,ArgValue)
	;	atom_concat('$',ArgKey,ArgValue)
	),
	atom_concat(ArgValue,'.type',ArgType),
	% get the operator
	mng_strip_operator(Arg0, Operator1, _Arg1),
	atom_concat('$',FieldKey,FieldQuery0),
	(	memberchk(FieldKey, RDFSFields)
	->	(
		% FIXME handle Operator1
		ArgOperator='$in',
		atom_concat(FieldQuery0,'_s',FieldQuery)
	);(
		mng_operator(Operator1, ArgOperator),
		FieldQuery=FieldQuery0
	)).
