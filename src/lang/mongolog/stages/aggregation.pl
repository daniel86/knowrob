:- module(mongolog_aggregation,
	[ aggregate/4
	]).

:- use_module(library('db/mongo/client')).

%%
%
aggregate(Coll, Pipeline, Vars, Result) :-
	mng_db_name(DB),
	% run the query
	setup_call_cleanup(
		% setup: create a query cursor
		mng_cursor_create(DB, Coll, Cursor),
		% call: find matching document
		(	mng_cursor_aggregate(Cursor, ['pipeline',array(Pipeline)]),
			mng_cursor_materialize(Cursor, Result),
			unify_(Result, Vars)
		),
		% cleanup: destroy cursor again
		mng_cursor_destroy(Cursor)
	).

%%
% unify variables.
%
unify_(Result, Vars) :-
	unify_0(Result, Vars, Vars).

unify_0(_, _, []) :- !.
unify_0(Doc, Vars, [[VarKey, Term]|Xs]) :-
	% it is ignored here if some variables referred
	% to are not properly grounded.
	% this can happen e.g. in expressions such as (A=a;B=b)
	% where the first solution has grounded A but not B.
	(	ground(Term)
	->	once(unify_grounded(Doc, [VarKey, Term]))
	;	ignore(unify_1(Doc, Vars, [VarKey, Term]))
	),
	unify_0(Doc, Vars, Xs).

unify_grounded(Doc, [VarKey, Term]) :-
	% variable was unified in pragma command
	% make sure it did not get another grounding in the query
	mng_get_dict(VarKey, Doc, TypedValue),
	!,
	mng_strip_type(TypedValue, _, Value),
	% ignore if value in the document is a variable
	(	Value=constant(undefined)
	% try to unify
	;	Term=Value
	% special case for number comparison, e.g. `5.0 =:= 5`
	;	(	number(Term),
			number(Value),
			Term=:=Value
		)
	).
unify_grounded(_, [_, _]) :- !.

unify_1(_, _, ['_id', _]).

unify_1(Doc, Vars, [VarKey, Val]) :-
	mng_get_dict(VarKey, Doc, TypedValue),
	unify_2(TypedValue, Vars, Val).

%%
unify_2(string(In), _Vars, X) :-
	% handle case that variable is wrapped in term/1.
	% if this is the case then convert input string to term.
	nonvar(X),
	X=term(Out),!,
	atom_to_term_(In, Out).

unify_2(array(In), Vars, Out) :-
	% a variable was instantiated to a list
	!,
	unify_array(In, Vars, Out).

unify_2(List, Vars, Out) :-
	is_list(List),
	memberchk(type-string(compound),  List),
	memberchk(value-array(Flattened), List),
	% a variable was instantiated to a compound term
	!,
	unflatten_term(Flattened, Vars, Out).

unify_2([K-V|Rest], Vars, Out) :-
	!,
	dict_pairs(Dict,_,[K-V|Rest]),
	unify_2(Dict, Vars, Out).

unify_2(constant(null), _Vars, Out) :-
	% a variable was not instantiated
	!,
	Out = _.

unify_2(Dict, Vars, Out) :-
	is_dict(Dict),
	get_dict(type,  Dict, string(compound)),
	get_dict(value, Dict, array(Flattened)),
	% a variable was instantiated to a compound term
	!,
	unflatten_term(Flattened, Vars, Out).

unify_2(TypedValue, _, Value) :-
	% a variable was instantiated to an atomic value
	mng_strip_type(TypedValue, _, Value).

%%
unify_array([], _, []) :- !.
unify_array([X|Xs], Vars, [Y|Ys]) :-
	unify_2(X, Vars, Y),
	unify_array(Xs, Vars, Ys).

%%
unflatten_term([X|Xs], Vars, Term) :-
	term_index_prefix(X, Prefix),
	term_value(X, X0),
	unify_2(X0, Vars, Functor),
	unflatten_with_prefix(Vars, Prefix, Xs, [], Args),
	Term =.. [Functor|Args].

%%
unflatten_with_prefix(Vars, OuterPrefix, [X|Xs], Ys, [Val|Zs]) :-
	% X is an atomic argument
	term_index_prefix(X, OuterPrefix),
	!,
	term_value(X, X0),
	once((var(X0) ; unify_2(X0, Vars, Val))),
	unflatten_with_prefix(Vars, OuterPrefix, Xs, Ys, Zs).

unflatten_with_prefix(Vars, OuterPrefix, [X|Xs], Ys, [Val|Zs]) :-
	% X starts a new compound term
	term_index_prefix(X, InnerPrefix),
	atom_concat(OuterPrefix, _, InnerPrefix),
	!,
	unflatten_with_prefix(Vars, InnerPrefix, [X|Xs], Remainder, InnerTerm),
	Val =.. InnerTerm,
	unflatten_with_prefix(Vars, OuterPrefix, Remainder, Ys, Zs).

unflatten_with_prefix(_, _, Remainder, Remainder, []) :- !.

%%
term_index_prefix([i-string(IndexAtom)|_], Prefix) :-
	atomic_list_concat(X1, '.', IndexAtom),
	reverse(X1, [_|X2]),
	atomic_list_concat(X2, '.', Prefix).

%%
term_value([_,v-Val], Val).
term_value([_], _).

%%
atom_to_term_(Atom, Term) :-
	% try converting atom stored in DB to a Prolog term
	catch(term_to_atom(Term,Atom), _, fail),
	!.

atom_to_term_(Atom, Term) :-
	% vectors maybe stored space-separated.
	% @deprecated
	atomic_list_concat(Elems, ' ', Atom),
	maplist(atom_number, Elems, Term),
	!.

atom_to_term_(Atom, _) :-
	throw(error(conversion_error(atom_to_term(Atom)))).
