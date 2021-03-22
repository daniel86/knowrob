:- use_module(library('lang/rdf_tests')).
:- begin_tests(
		'lang_triple',
		[   setup(lang_query:set_default_graph(test)),
		    cleanup(rdf_tests:cleanup)
		]).

:- use_module(library('semweb/rdf_db'),
		[ rdf_global_term/2 ]).
:- use_module(library('rostest.pl')).
:- use_module(library('semweb/rdf_db'),
		[ rdf_register_ns/3 ]).
:- use_module(library('lang/query')).
:- use_module(library('lang/db')).
:- use_module(library('lang/scope')).

% register namespaces for following tests
:- rdf_register_ns(swrl_tests,
		'http://knowrob.org/kb/swrl_test#',
		[keep(true)]).
:- rdf_register_ns(test_datatype,
		'http://knowrob.org/kb/datatype_test#',
		[keep(true)]).

test('tell(assign(C,c), triple(a,b,C))') :-
	assert_true(lang_query:tell((
		ask(assign(C,g)),
		triple(e,f,C)
	))).

test('tell triple(a,b,c)') :-
	assert_true(lang_query:tell(triple(a,b,c))).

test('tell triple(a,b,_)', [throws(error(instantiation_error,project(triple(a,b,_))))]) :-
	lang_query:tell(triple(a,b,_)).

test('ask triple(a,b,c)') :-
	assert_true(lang_query:ask(triple(a,b,c))),
	assert_false(lang_query:ask(triple(x,b,c))),
	assert_false(lang_query:ask(triple(a,x,c))),
	assert_false(lang_query:ask(triple(a,b,x))).

test('ask triple(A,b,c)') :-
	lang_query:ask(triple(A,b,c)),
	assert_equals(A,a),
	assert_false(lang_query:ask(triple(_,x,c))).

test('ask triple(a,B,c)') :-
	lang_query:ask(triple(a,B,c)),
	assert_equals(B,b),
	assert_false(lang_query:ask(triple(x,_,c))).

test('ask triple(a,b,C)') :-
	lang_query:ask(triple(a,b,C)),
	assert_equals(C,c),
	assert_false(lang_query:ask(triple(a,x,_))).

test('ask triple(A,b,C)') :-
	lang_query:ask(triple(A,b,C)),
	assert_equals(A,a),
	assert_equals(C,c),
	assert_false(lang_query:ask(triple(_,x,_))).

% load swrl owl file for tripledb testing
test('load local owl file') :-
	assert_true(load_owl('package://knowrob/owl/test/swrl.owl', [ parent_graph(test) ])),
	assert_true(load_owl('package://knowrob/owl/test/datatype_test.owl', [ parent_graph(test) ])).

% check via tripledb_ask if individual triple exists
test('ask triple') :-
	assert_true( lang_query:ask( triple(
		swrl_tests:'Adult',
		rdfs:'subClassOf',
		swrl_tests:'TestThing'
	))).

% delete individual triple
test('forget triple') :-
	assert_true( forget( triple(
		swrl_tests:'Adult',
		rdfs:'subClassOf',
		swrl_tests:'TestThing'
	))),
	assert_false( ask( triple(
		swrl_tests:'Adult',
		rdfs:'subClassOf',
		swrl_tests:'TestThing'
	))).

% add triple and check if it exists in db
test('tell to triplestore and check if triple exists') :-
	assert_true( tell( triple(
		swrl_tests:'Adult',
		rdfs:'subClassOf',
		swrl_tests:'TestThing'
	))),
	assert_true( ask( triple(
		swrl_tests:'Adult',
		rdfs:'subClassOf',
		swrl_tests:'TestThing'
	))),
	assert_false( ask( triple(
		swrl_tests:'Adult',
		rdfs:'subClassOf',
		swrl_tests:'Car'
	))).

% test for xsd:integer, Str, float
test('tell XSD') :-
	rdf_global_term(test_datatype:'Lecturer3',S),
	assert_true(tell(triple(S, test_datatype:'first_name', 'Johana$'))),
	assert_true(tell(triple(S, test_datatype:'last_name',  'Muller'))),
	assert_true(tell(triple(S, test_datatype:'studentId',  212123))),
	assert_true(tell(triple(S, test_datatype:'height',     5.10))).

% test for xsd:integer, Str, float
test('ask XSD') :-
	assert_true(forall(ask(triple(_, test_datatype:'studentId',  X)), number(X))),
	assert_true(forall(ask(triple(_, test_datatype:'first_name', Y)), atom(Y))),
	assert_true(forall(ask(triple(_, test_datatype:'last_name',  Z)), atom(Z))),
	assert_true(forall(ask(triple(_, test_datatype:'height',     H)), float(H))).

% test for list as an argument
test('tell list', fixme('terms cannot be used as values')) :-
	rdf_global_term(test_datatype:'Lecturer3',S),
	DataTerm=[255,99,71],
	% test asserting list value
	assert_true(tell(triple(S, test_datatype:'hasHairColor', term(DataTerm)))),
	% test ask with ground value
	assert_true( ask(triple(S, test_datatype:'hasHairColor', term(DataTerm)))),
	% test ask with var value
	(	ask(triple(S, test_datatype:'hasHairColor', term(Actual)))
	->	assert_equals(Actual,DataTerm)
	;	true
	).

% test for time scope
test('tell with scope'):-
	rdf_global_term(test_datatype:'Lecturer4',S),
	rdf_global_term(test_datatype:'last_name',P),
	time_scope(=(double(5)), =(double(10)), T_S1),
	time_scope(=(double(5)), =(double(20)), T_S2),
	%%
	tell(triple(S, P, 'Spiendler'), T_S1),
	assert_true( ask(triple(S, P, 'Spiendler'), T_S1, _)),
	assert_false(ask(triple(S, P, 'Spiendler'), T_S2, _)).

% test for time scope extension
test('extend time scope'):-
	rdf_global_term(test_datatype:'Lecturer4',S),
	rdf_global_term(test_datatype:'last_name',P),
	time_scope(=(double(10)), =(double(20)), T_S1),
	time_scope(=(double(5)),  =(double(20)), T_S2),
	%%
	tell(triple(S, P, 'Spiendler'), T_S1),
	assert_true(ask(triple(S, P, 'Spiendler'), T_S2, _)).

test('query value operators') :-
	assert_true(ask(triple(swrl_tests:'RectangleSmall',swrl_tests:'hasHeightInMeters', =(6)))),
	assert_true(ask(triple(swrl_tests:'RectangleSmall',swrl_tests:'hasHeightInMeters', =<(9)))),
	assert_true(ask(triple(swrl_tests:'RectangleSmall',swrl_tests:'hasHeightInMeters', <(7)))),
	assert_true(ask(triple(swrl_tests:'RectangleSmall',swrl_tests:'hasHeightInMeters', >=(5)))),
	assert_true(ask(triple(swrl_tests:'RectangleSmall',swrl_tests:'hasHeightInMeters', >(3.5)))),
	assert_false(ask(triple(swrl_tests:'RectangleSmall',swrl_tests:'hasHeightInMeters', <(3)))).

test('query operator in'):-
	findall(LastName,
		ask(triple(
			in(array([
				string(test_datatype:'Lecturer3'),
				string(test_datatype:'Lecturer4')
			])),
			test_datatype:'last_name',
			LastName)),
		Names
	),
	assert_equals(Names,['Muller']).

test('query operator in + ->'):-
	findall([Lecturer,LastName],
		ask(triple(
			in(array([
				string(test_datatype:'Lecturer3'),
				string(test_datatype:'Lecturer4')
			])) -> Lecturer,
			test_datatype:'last_name',
			LastName)),
		LecturerList
	),
	assert_equals(LecturerList,
		[[test_datatype:'Lecturer3', 'Muller']]).

% test for special characters in iri: @*~!#?
test('non alphabetic character'):-
	assert_true(tell(triple(
		test_datatype:'normal_user_test_new',
		test_datatype:'last@*~!#?_name',
		'umlaut'
	))),
	assert_true(ask(triple(
		test_datatype:'normal_user_test_new',
		test_datatype:'last@*~!#?_name',
		'umlaut'
	))).

test('non utf8 character', fixme('bson_pl has issues reading non-utf8')):-
	tell(triple(
		test_datatype:'Lecturer3',
		test_datatype:'last_name',
		'Müller'
	)),
	assert_true(ask(triple(
		test_datatype:'Lecturer3',
		test_datatype:'last_name',
		'Müller'
	))).

% test for non existent triples
test('ask non existant'):-
	assert_false( ask(
		triple(test_datatype:'xyz', test_datatype:'last_name', _)
	)).

test('triple(+,transitive(+),+') :-
	assert_true(ask(triple(
		swrl_tests:'Rex',
		transitive(swrl_tests:isParentOf),
		swrl_tests:'Ernest'))),
	assert_true(ask(triple(
		swrl_tests:'Rex',
		transitive(swrl_tests:isParentOf),
		swrl_tests:'Lea'))),
	assert_false(ask(triple(
		swrl_tests:'Rex',
		transitive(swrl_tests:isParentOf),
		swrl_tests:'Person'))).

test('triple(-,transitive(+),+') :-
	findall(X,
		ask(triple(X,
			transitive(swrl_tests:isParentOf),
			swrl_tests:'Lea')),
		Ancestors),
	assert_unifies(Ancestors,[_,_]),
	assert_true(member(swrl_tests:'Fred', Ancestors)),
	assert_true(member(swrl_tests:'Rex', Ancestors)),
	%%
	assert_false(member(swrl_tests:'Ernest', Ancestors)).

test('triple(+,reflexive(transitive(+)),-)') :-
	findall(X,
		ask(triple(
			swrl_tests:'Rex',
			transitive(reflexive(swrl_tests:isParentOf)),
			X)),
		Ancestors),
	length(Ancestors,NumAncestors),
	assert_equals(NumAncestors, 4),
	assert_true(member(swrl_tests:'Rex', Ancestors)),
	assert_true(member(swrl_tests:'Ernest', Ancestors)),
	assert_true(member(swrl_tests:'Fred', Ancestors)),
	assert_true(member(swrl_tests:'Lea', Ancestors)).

test('call(+Triple)') :-
	assert_true(lang_query:ask(call(triple(
		swrl_tests:'Rex',
		swrl_tests:isParentOf,
		swrl_tests:'Ernest')))),
	assert_false(lang_query:ask(call(triple(
		swrl_tests:'Rex',
		swrl_tests:isParentOf,
		test_datatype:'Lecturer3')))).

test('call_with_context(+Triple,+Context)') :-
	assert_true(mongolog:test_call(
		call_with_context(
			triple(swrl_tests:'Rex', swrl_tests:isParentOf, swrl_tests:'Ernest'),
			[ scope(_{ time: _{ since: =<(Time), until: >=(Time) } }) ]
		), Time, 999)),
	%
	assert_false(mongolog:test_call(
		call_with_context(
			triple(swrl_tests:'Rex', swrl_tests:isParentOf, swrl_tests:'Rex'),
			[ scope(_{ time: _{ since: =<(Time), until: >=(Time) } }) ]
		), Time, 999)).

:- end_tests('lang_triple').