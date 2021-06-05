:- module(mongolog_idb,
		[ is_idb_predicate/1,
		  idb_create/3,
		  idb_drop/1,
		  idb_assert/4
		]).

:- use_module('../mongolog').
:- use_module('../aggregation/lookup').
:- use_module('db_predicate').


%% is_idb_predicate(+Indicator) is semidet.
%
%
is_idb_predicate(Predicate) :-
	db_predicate(Predicate, _, Opts),
	option(type(idb), Opts).

%% idb_create(+Functor, +Fields, +Opts) is det.
%
% Same as db_predicate_create/3 with idb-specific options.
%
idb_create(Functor, Fields, Opts) :-
	select_option(type(_),Opts,Opts0,_),
	select_option(indices(_),Opts0,Opts1,_),
	db_predicate_create(Functor, Fields,
		[ type(idb),
		  indices([])
		| Opts1
		]).

%% idb_drop(+Indicator) is det.
%
% Same as db_predicate_drop/1.
%
idb_drop(Indicator) :-
	db_predicate_drop(Indicator).


%% idb_assert(+Module, +Functor, +Args, +Clauses) is semidet.
%
%
idb_assert(_Module, Functor, Args, Clauses) :-
	Goal =.. [Functor|Args],
%	writeln(compile_view(Goal)),
	length(Args, Arity),
	atomic_list_concat([Functor, Arity], '_', ViewName),
	% compile an aggregation pipeline
	current_scope(QScope),
%once(( Functor==is_resource -> gtrace ; true )),
	mongolog:mongolog_compile(
		Clauses,
		CompilerOutput,
		Vars,
		[ scope(QScope)
		, compile_mode(view)
		]),
	memberchk(document(Pipeline), CompilerOutput),
%	memberchk(variables(Vars), CompilerOutput),
	option(input_collection(ViewOnCollection), CompilerOutput, _),
	once((ground(ViewOnCollection);ViewOnCollection=one)),
	% lookup variable keys used by the predicate and re-use
	% the same keys.
	findall(K,
		(	member(Arg,Args),
			once((
				member([K,X],Vars),
				X == Arg
			))
		),
		Fields),
	% lookup fields with rdfs values
	findall(K,
		(	member(K,Fields),
			atom_concat(K,'_s',K0),
			memberchk([K0,_],Vars)
		),
		RDFSFields),
	!,
	findall([K,Condition],
		(	(	member(K,Fields), Condition=integer(1)	)
		;	(	member(K0,RDFSFields),
				atom_concat(K0,'_s',K),
				atom_concat('$',K,Kv),
				atom_concat(Kv,'.type',Kt),
				Condition=['$cond',[
					[if,   ['$eq', array([string(Kt), string('var')])]],
					[then, string('$$REMOVE')],
					[else, string(Kv)]
				]]
			)
		;	(	K='v_scope', Condition=integer(1)	)
		),
		Projection),
	append(Pipeline, [['$project',Projection]], Pipeline0),
	% create a view for the head predicate
	mng_db_name(DBName),
	mng_view_create(DBName, ViewOnCollection, ViewName, array(Pipeline0)),
	% add head as an IDB predicate in mongolog
	(	is_db_predicate(Goal) -> true
	;	idb_create(Functor, Fields,
			[ collection(ViewName),
			  rdfs_fields(RDFSFields)
			])
	).

idb_assert(Module, Functor, Args, _Zs) :-
	writeln(mongolog_rule_assert_failed(Module, Functor, Args)).

%%
mongolog:step_compile1(Term, Ctx, Output) :-
	is_idb_predicate(Term),!,
	db_predicate_compile(Term, Ctx, Output).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- use_module('../mongolog_tests').

:- begin_mongolog_tests('mongolog_idb',
		[ woman(mia),
		  woman(jola)
		]).

test('woman(+)') :-
	assert_true(mongolog_call(woman(mia))),
	assert_true(mongolog_call(woman(jola))),
	assert_false(mongolog_call(woman(vincent))).

:- end_mongolog_tests('mongolog_idb').

