:- module(mongolog_sgml, []).
/** <module> XML namespaces in mongolog programs.

The following predicates are supported:

| Predicate            | Arguments |
| ---                  | ---       |
| iri_xml_namespace/3  | +IRI, -Namespace, -Localname |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=xmlns
@license BSD
*/

:- use_module(library('semweb/rdf_db'),
		[ rdf_global_term/2 ]).
:- use_module(library('lang/db'),
		[ get_unique_name/2 ]).
:- use_module('../mongolog').
:- use_module('../variables').
:- use_module('../aggregation/match').
:- use_module('../aggregation/set').

%% query commands
:- mongolog:add_command(iri_xml_namespace).

%% query compilation
mongolog:step_compile(
		iri_xml_namespace(IRI,NS,Name),
		Ctx, Pipeline) :-
	arg_val(IRI, Ctx, IRI0),
	arg_val(NS, Ctx, NS0),
	arg_val(Name, Ctx, Name0),
	findall(Step,
		% first extract the name from the IRI and set new field "t_name".
		% here we use the remainder after the last '#' as name.
		% FIXME: this is not entirely accurate, see the documentation of iri_xml_namespace:
		%			https://www.swi-prolog.org/pldoc/man?predicate=iri_xml_namespace/3
		(	Step=['$set', ['t_name', ['$arrayElemAt', array([
						['$split', array([IRI0, string('#')])],
						int(-1)
			])]]]
		% next set field "t_ns" to remaining prefix of IRI
		;	Step=['$set', ['t_ns',   ['$substr', array([IRI0, int(0),
				['$subtract', array([
					['$strLenCP',IRI0],
					['$strLenCP',string('$t_name')]
				])]
			])]]]
		% assign arguments if needed using fields created above
		;	set_if_var(NS,   string('$t_ns'),   Ctx, Step)
		;	set_if_var(Name, string('$t_name'), Ctx, Step)
		% finally match using concat operator
		;	match_equals(IRI0, ['$concat', array([NS0,Name0])], Step)
		% cleanup
		;	Step=['$unset', array([string('t_ns'),string('t_name')])]
		),
		Pipeline).


		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_sgml').

test('iri_xml_namespace(+IRI,-NS,-Name)'):-
	rdf_global_term(rdf:'Resource', Resource),
	mongolog:test_call(
		iri_xml_namespace(X,NS,Name),
		X, Resource),
	assert_true(atom(NS)),
	assert_equals(Name,'Resource'),
	assert_true(atomic_concat(NS,Name,Resource)).

:- end_tests('mongolog_sgml').
