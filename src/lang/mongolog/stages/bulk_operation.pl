:- module(mongolog_bulk_operation,
	[ bulk_operation/1,
	  add_assertions/3,
	  add_assertion/3,
	  add_assertion_var/2
	]).

:- use_module(library('db/mongo/client')).

%%
bulk_operation(Result) :-
	once((
		mng_get_dict('g_assertions', Result, array(Assertions))
	;	Assertions=[]
	)),
	once((setof(X,
		(	member(A,Assertions),
			member(collection-string(X),A)
		),
		Collections
	);Collections=[])),
	assert_documents0(Collections, Assertions).

assert_documents0([],_) :- !.
assert_documents0([Coll|Next], Assertions) :-
	findall(Doc,
		(	member(A,Assertions),
			memberchk(collection-string(Coll),A),
			memberchk(documents-array(Docs),A),
			member(Doc,Docs)
		),
		Docs),
	assert_documents1(array(Docs), Coll),
	assert_documents0(Next, Assertions).

assert_documents1(array([]), _) :- !.
assert_documents1([], _) :- !.
assert_documents1(array(Docs), Key) :-
	% NOTE: the mongo client currently returns documents as pairs A-B instead of
	%       [A,B] which is required as input.
	% TODO: make the client return docs in a format that it accepts as input.
	maplist(format_doc, Docs, Docs0),
	maplist(bulk_operation, Docs0, BulkOperations),
	mng_get_db(DB, Coll, Key),
	mng_bulk_write(DB, Coll, BulkOperations).

%%
format_doc([], []) :- !.
format_doc([X-Y0|Rest0], [[X,Y1]|Rest1]) :-
	!,
	format_doc(Y0,Y1),
	format_doc(Rest0,Rest1).
format_doc(X, X).

%%
bulk_operation(Doc, remove([['_id',id(ID)]])) :-
	memberchk(['delete',bool(Val)],Doc),!,
	memberchk(['_id',id(ID)],Doc),
	once((Val==true ; Val==1)).

bulk_operation(Doc0, update(Selector,['$set', Update])) :-
	select(['_id',id(ID)],Doc0,Update),!,
	Selector=[['_id',id(ID)]].

bulk_operation(Doc, insert(Doc)).

%%
add_assertions(Docs, Coll,
	['$set', ['g_assertions',['$concatArrays', array([
		string('$g_assertions'),
		array([[
			['collection', string(Coll)],
			['documents', Docs]
		]])
	])]]]).

add_assertion(Doc, Coll, Step) :-
	add_assertions(array([Doc]), Coll, Step).

%%
add_assertion_var(StepVars, [['g_assertions',_]|StepVars]).
