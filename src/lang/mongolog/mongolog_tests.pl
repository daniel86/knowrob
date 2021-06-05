:- module(mongolog_tests,
	[ begin_mongolog_tests/3,
	  begin_mongolog_tests/2,
	  end_mongolog_tests/1
	]).

%% begin_mongolog_tests(+Name, +KB, +Options) is det.
%
% Begin unit testing code section with RDF data.
% Load the RDF data during setup, and unload all asserted facts
% and RDF file on cleanup.
% Calls internally begin_tests/2.
%
%
begin_mongolog_tests(Name, KB, Options) :-
	%%
	gen_edb_idb(KB,EDB,IDB),
	Setup   = mongolog_tests:setup(EDB,IDB),
	Cleanup = mongolog_tests:cleanup(EDB,IDB),
	add_option_goal(Options, setup(Setup), Options2),
	add_option_goal(Options2, cleanup(Cleanup), Options3),
	%%
	begin_tests(Name,Options3).

%% begin_rdf_tests(+Name, +KB) is det.
%
% Same as begin_mongolog_tests/3 with empty options list.
%
begin_mongolog_tests(Name, KB) :-
	begin_mongolog_tests(Name, KB, []).

%% end_rdf_tests(+Name) is det.
%
% End unit testing code section with RDF data.
%
end_mongolog_tests(Name) :-
	end_tests(Name).

%%
gen_edb_idb([], [[],[]], [[],[]]) :- !.
gen_edb_idb(
		[ ':-'(Head,Body)|Xs ],
		Ys,
		[ Specs, [':-'(Head,Body)|Zr] ]) :-
	gen_edb_idb1(Head,[Functor,Fields,Opts]),!,
	gen_edb_idb(Xs,Ys,[Zl,Zr]),
	(	memberchk([Functor,_,_],Zl) -> Specs=Zl
	;	Specs=[[Functor,Fields,Opts]|Zl]
	).
gen_edb_idb(
		[ Fact|Xs ],
		[ Specs, [Fact|Yr] ],
		Zs) :-
	gen_edb_idb1(Fact,[Functor,Fields,Opts]),!,
	gen_edb_idb(Xs,[Yl,Yr],Zs),
	(	memberchk([Functor,_,_],Yl) -> Specs=Yl
	;	Specs=[[Functor,Fields,Opts]|Yl]
	).

%
gen_edb_idb1(Literal, [Functor,Fields,[]]) :-
	Literal =.. [Functor|Args],!,
	findall(F, (
		member(_,Args),
		gensym('v_', F)
	), Fields).

%%
setup([EDBPredicates,Facts], [IDBPredicates,Clauses]) :-
	% create predicates
	forall(
		member([Functor,Fields,Options],EDBPredicates),
		edb_create(Functor, Fields, Options)
	),
	forall(
		member([Functor,Fields,Options],IDBPredicates),
		idb_create(Functor, Fields, Options)
	),
	% assert facts
	forall(member(Fact,Facts), edb_assert(Fact)),
	% assert clauses
	forall(member((':-'(Head,Body)),Clauses), 
		lang_query:expand_ask_rule(Head, Body, _)),
	lang_query:flush_predicate(user).

%%
cleanup([EDBPredicates,_], [IDBPredicates,_]) :-
	% drop all predicates
	forall(
		member([Functor,Fields,_],EDBPredicates),
		(length(Fields,N), edb_drop(('/'(Functor,N))))
	),
	forall(
		member([Functor,Fields,_],IDBPredicates),
		(length(Fields,N), idb_drop(('/'(Functor,N))))
	).

%%
add_option_goal(OptionsIn,NewOpt,[MergedOpt|Rest]) :-
	NewOpt =.. [Key,NewGoal],
	OldOpt =.. [Key,OtherGoal],
	MergedOpt =.. [Key,Goal],
	(	select_option(OldOpt,OptionsIn,Rest)
	->	( Goal=(','(OtherGoal,NewGoal)) )
	;	( Goal=NewGoal, Rest=OptionsIn )
	).
