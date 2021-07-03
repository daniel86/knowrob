:- module(mongolog_lists, []).
/** <module> List manipulation in mongolog programs.

The following predicates are supported:

| Predicate     | Arguments |
| ---           | ---       |
| length/2      | +List, ?Length |
| max_list/2    | +List, ?Max |
| min_list/2    | +List, ?Min |
| sum_list/2    | +List, ?Sum |
| member/2      | ?Elem, +List |
| memberchk/2   | ?Elem, +List |
| nth1/3        | ?Index, +List, ?Elem |
| list_to_set/2 | +List, -Set |
| sort/2        | +List, -Sorted |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=allsolutions
@license BSD
*/

:- use_module('../mongolog').
:- use_module('../variables').
:- use_module('../aggregation/match').
:- use_module('../aggregation/set').

%% query commands
:- mongolog:add_command(length).
:- mongolog:add_command(max_list).
:- mongolog:add_command(min_list).
:- mongolog:add_command(sum_list).
:- mongolog:add_command(member).
:- mongolog:add_command(memberchk).
:- mongolog:add_command(nth1).
:- mongolog:add_command(list_to_set).
:- mongolog:add_command(sort).

%% member(?Elem, +List)
% True if Elem is a member of List. 
% NOTE: here list cannot be a variable which is allowed in SWI Prolog.
%       Prolog then generates all possible list with Elem as member.
%
lang_query:step_expand(member(Elem, List), Expanded) :-
	lang_query:kb_expand(nth1(_, List, Elem), Expanded).

%% memberchk(?Elem, +List)
% True when Elem is an element of List. This variant of member/2 is
% semi deterministic and typically used to test membership of a list. 
%
lang_query:step_expand(memberchk(Elem, List), Expanded) :-
	lang_query:kb_expand(
		limit(1, member(Elem,List)),
		Expanded).

%% length(+List, ?Length)
% True if Length represents the number of elements in List.
%
lang_query:step_expand(length(List, Length), Expanded) :-
	lang_query:kb_expand(
		functor(List, _, Length),
		Expanded).

%% nth1(?Index, +List, ?Elem)
% True when Elem is the Index’th element of List. Counting starts at 0. 
%
lang_query:step_expand(nth1(Index, List, Elem), Expanded) :-
	lang_query:kb_expand(
		arg(Index, List, Elem),
		Expanded).

%% max_list(+List:list(number), -Max:number)
% True if Max is the largest number in List. Fails if List is empty. 
%
mongolog:step_compile(max_list(List, Max), _, []) :-
	ground(List),!,
	max_list(List, Max).

mongolog:step_compile(max_list(List, Max), Ctx, Pipeline) :-
	% FIXME: this will give results even if the list has other elements then numbers
	number_list_attribute(List, Max, '$max', Ctx, Pipeline).

%% min_list(+List, ?Min)
% True if Min is the smallest number in List. Fails if List is empty.
%
mongolog:step_compile(min_list(List, Min), _, []) :-
	ground(List),!,
	min_list(List, Min).

mongolog:step_compile(min_list(List, Min), Ctx, Pipeline) :-
	% FIXME: this will give results even if the list has other elements then numbers
	number_list_attribute(List, Min, '$min', Ctx, Pipeline).

%% sum_list(+List, -Sum)
% Sum is the result of adding all numbers in List.
%
mongolog:step_compile(sum_list(List, Sum), _, []) :-
	ground(List),!,
	sum_list(List, Sum).

mongolog:step_compile(sum_list(List, Sum), Ctx, Pipeline) :-
	number_list_attribute(List, Sum, '$sum', Ctx, Pipeline).

%% list_to_set(+List, -Set)
% Removes duplicates from a list.
% List may *not* contain variables when this is evaluated.
%
mongolog:step_compile(list_to_set(List, Set), _, []) :-
	ground(List),!,
	list_to_set(List, Set).

mongolog:step_compile(list_to_set(List, Set), Ctx, Pipeline) :-
	% FIXME: SWI Prolog allows ground(Set)
	% FIXME: Set and List have same ordering in SWI Prolog, but $setUnion does not ensure this.
	arg_val(List,Ctx,List0),
	var_key(Set,Ctx,SetKey),
	% compute steps of the aggregate pipeline
	findall(Step,
		% first convert list term to array of list elements
		(	Step=['$set', ['t_array', List0]]
		;	list_to_array('t_array', 't_array', Step)
		% then remove duplicates
		;	Step=['$set', ['t_array', ['$setUnion', array([string('$t_array')])]]]
		% convert back to list representation
		;	array_to_list('t_array', SetKey, Step)
		% finally remove temporary field again
		;	Step=['$unset', string('t_array')]
		),
		Pipeline).

%% sort(+List, -Sorted)
% True if Sorted can be unified with a list holding the elements of List,
% sorted to the standard order in mongo. Duplicates are removed.
%
mongolog:step_compile(sort(List, Sorted), Ctx, Pipeline) :-
	arg_val(List,Ctx,List0),
	var_key(Sorted,Ctx,SortedKey),
	mng_one_db(_DB, Coll),
	% compute steps of the aggregate pipeline
	findall(Step,
		% first convert list term to array of list elements
		(	Step=['$set', ['t_array', List0]]
		;	list_to_array('t_array', 't_array', Step)
		% then remove duplicates
		;	Step=['$set', ['t_array', ['$setUnion', array([string('$t_array')])]]]
		% use lookup to sort the array by using $unwind+$sort in lookup pipeline
		;	Step=['$lookup', [
				['from', string(Coll)],
				['as', string('t_sorted')],
				['let', [['t_array', string('$t_array')]]],
				['pipeline', array([
					['$set', ['elem', string('$$t_array')]],
					['$unwind', string('$elem')],
					['$sort', ['elem', integer(1)]]
				])]
			]]
		% map from array of documents to array of values
		;	Step=['$set', ['t_sorted', ['$map', [
				['input', string('$t_sorted')],
				['in', string('$$this.elem')]
			]]]]
		% convert back to list representation
		;	array_to_list('t_sorted', SortedKey, Step)
		% finally remove temporary field again
		;	Step=['$unset', array([
				string('t_array'),
				string('t_sorted')
			])]
		),
		Pipeline
	).

%% +List, ?Attribute
% Applies an operator on grounded array (List) and unifies the
% second argument with the result (i.e. Attribute maybe ground or var).
%
number_list_attribute(List, Attribute, Operator, Ctx, Pipeline) :-
	arg_val(List, Ctx, List0),
	arg_val(Attribute, Ctx, Attribute0),
	findall(Step,
		% first convert list term to array of list elements
		(	Step=['$set', ['t_term', List0]]
		;	list_to_array('t_term', 't_array', Step)
		% then compute the value
		;	Step=['$set', ['t_val', [Operator, string('$t_array')]]]
		% then assign the value to the attribute if it is a variable
		;	set_if_var(Attribute, string('$t_val'), Ctx, Step)
		% then ensure that the attribute has the right value
		;	match_equals(Attribute0, string('$t_val'), Step)
		% finally remove temporary field again
		;	Step=['$unset', array([
				string('t_term'),
				string('t_array'),
				string('t_val')
			])]
		),
		Pipeline
	).

%%
list_to_array(ListField, ArrayField,
	['$set', [ArrayField, ['$map', [
		[input, ['$map', [
			% iterate from 1 ... Arity
			[input, ['$range', array([
				integer(1),
				['$add', array([string(ListArity), integer(1)])]
			])]],
			[as, string('index')],
			% and map to index + list of entries
			[in, [
				[index, string('$$index')],
				[value, ['$map', [
					[in, [
						[i, ['$concat', array([
							string('1'),
							['$substr', array([
								string('$$this.i'),
								['$add', array([
									integer(2), % "1."
									['$strLenCP', ['$toString', string('$$index')]]
								])],
								integer(-1)
							])]
						])]],
						[v, string('$$this.v')]
					]],
					[input, ['$filter', [
						[input, string(ListValue)],
						[cond, ['$eq', array([
							['$toString', string('$$index')],
							['$arrayElemAt', array([
								['$split', array([string('$$this.i'), string('.')])],
								integer(1)
							])]
						])]]
					]]]
				]]]
			]]]
		]],
		[as, string('arg')],
		% finally map list of entries to proper datatype format
		[in, ['$cond', [
			% atomic iff the array has only one element
			[if,   ['$eq', array([integer(1), ['$size', string('$$arg.value')]])]],
			[then, ['$arrayElemAt', array([
				['$map', [
					[input, string('$$arg.value')],
					[in, string('$$this.v')]
				]],
				integer(0)
			])]],
			% else create a compound
			[else, [
				[type,string(compound)],
				[arity, ['$max', ['$map', [
					[input,string('$$arg.value')],
					[in, ['$toInt', ['$arrayElemAt', array([
						['$split', array([string('$$this.i'), string('.')])],
						integer(1)
					])]]]
				]]]],
				[value,string('$$arg.value')]
			]]
		]]]
	]]]]) :-
	atomic_list_concat(['$',ListField,'.arity'],'',ListArity),
	atomic_list_concat(['$',ListField,'.value'],'',ListValue).

%%
% create a list term from an array of values.
% values in the array can be lists or other compound terms,
% or atomic values.
% This is a bit nasty because the list-based representation consists
% of indexstring-value tuples in a flat array in the document.
% The indexstring must be generated for each element in the array which
% bloats below code a bit. 
%
array_to_list(ArrayField, ListField,
	['$set', [ListField, [
		% compound terms are documents {type: "compound", arity::int, value::array}
		[type, string(compound)],
		[arity, ['$size', string(ArrayValue)]],
		[value, ['$concatArrays', array([
			% add entry for the list functor
			array([[[i, string('1.0')], [v, string('[|]')]]]),
			% get remaining values from the array
			['$reduce', [
				% $map below creates array of arrays which is flattened through this $reduce
				[initialValue, array([])],
				[in, ['$concatArrays', array([
					string('$$value'),
					string('$$this')
				])]],
				% map each element in the array to an array of indexed entries.
				% this is needed as compound terms are made of several indexed entries.
				[input, ['$map', [
					% zip index + arrayvalues because $map does not allow us to access the index directly
					[input, ['$zip', [[inputs, array([
						% [1, ...., Arity+1]
						['$range', array([
							integer(1),
							['$add', array([integer(1),['$size', string(ArrayValue)]])]
						])],
						% transform values for easier processing:
						% atomic values in the array are simply mapped to the indexstring "1"
						% such that each entry consists of indexstring + value
						['$map', [
							[input, string(ArrayValue)],
							[in, ['$cond', [
								% if the list element is atomic
								[if, ['$eq', array([
									string('$$this.arity'),
									constant(undefined)
								])]],
								% then assign indexstring "1"
								[then, array([[[i, string('1')], [v, string('$$this')]]])],
								% else keep as is
								[else, string('$$this.value')]
							]]]
						]]
					])]]]],
					[as, string('pair')],
					% finally generate appropiate index string for each array element within
					% the list term
					[in, ['$map', [
						% second element in $pair is the list of values associated to the index,
						% first is the argument index (starting at 1)
						[input, ['$arrayElemAt', array([string('$$pair'), integer(1)])]],
						[as, string('elem')],
						[in, [
							% extend the index (add the argument index within the list)
							[i, ['$reduce', [
								[initialValue, ['$concat', array([
									string('1.'),
									['$toString', ['$arrayElemAt', array([string('$$pair'), integer(0)])]]
								])]], 
								[input, ['$slice', array([
									['$split', array([string('$$elem.i'), string('.')])],
									integer(1),
									% TODO use $let
									['$size', ['$split', array([string('$$elem.i'), string('.')])]]
								])]],
								[in, ['$concat', array([
									string('$$value'),
									string('.'),
									string('$$this')
								])]]
							]]],
							% keep the value
							[v, string('$$elem.v')]
						]]
					]]]
				]]]
			]]
		])]]
	]]]) :-
	atom_concat('$',ArrayField,ArrayValue).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_lists').

test('length(+,+)'):-
	assert_true(mongolog_tests:test_call(
		length(List, 2), List, [2,4])),
	assert_true(mongolog_tests:test_call(
		length([2,4], Count), Count, 2)),
	assert_true(mongolog_tests:test_call(
		length([], Count), Count, 0)),
	assert_false(mongolog_tests:test_call(
		length(List, 3), List, [2,4])),
	assert_false(mongolog_tests:test_call(
		length([2,4], Count), Count, 3)).

test('length(+,-)'):-
	mongolog_tests:test_call(
		length(List, Length), List, [2,4]),
	assert_equals(Length, 2).

test('max_list(+Numbers)'):-
	mongolog_tests:test_call(
		(	X is Num + 5,
			Y is Num * 2,
			max_list([X,Y], Max)
		),
		Num, double(4.5)),
	assert_equals(Max, 9.5).

test('min_list(+Numbers,-Min)'):-
	mongolog_tests:test_call(
		(	X is Num + 5,
			Y is Num * 2,
			min_list([X,Y], Min)
		),
		Num, double(4.5)),
	assert_equals(Min, 9.0).

test('sum_list(+Numbers,-Sum)'):-
	mongolog_tests:test_call(
		(	X is Num + 5,
			Y is Num * 2,
			sum_list([X,Y], Sum)
		),
		Num, double(4.5)),
	assert_equals(Sum, 18.5).

test('list_to_set(+Numbers)'):-
	mongolog_tests:test_call(
		(	X is Num + 5,
			list_to_set([X,X], Set)
		),
		Num, double(4.5)),
	assert_equals(Set, [9.5]).

test('sort(+Numbers)'):-
	mongolog_tests:test_call(
		(	X is Num + 5,
			sort([4,X,Num,2], Sorted)
		),
		Num, double(4)),
	assert_equals(Sorted, [2.0, 4.0, 9.0]).

test('sort(+Atoms)'):-
	mongolog_tests:test_call(
		sort([d,a,X,b], Sorted), X, string(s)),
	assert_equals(Sorted, [a,b,d,s]).

test('sort(+AtomsAndNumbers)'):-
	mongolog_tests:test_call(
		sort([9,a,X,7], Sorted), X, string(s)),
	assert_equals(Sorted, [7.0,9.0,a,s]).

test('nth1(+Numbers)'):-
	mongolog_tests:test_call(
		(	X is Num + 5,
			Y is Num * 2,
			nth1(2, [X,Y], Second)
		),
		Num, double(4.5)),
	assert_equals(Second, 9.0).

test('member(+Number)'):-
	findall(Val,
		mongolog_tests:test_call(
			(	X is Num + 5,
				member(Val, [X])
			),
			Num, double(4.5)),
		Results),
	assert_equals(Results,[9.5]).

test('member(+Numbers)'):-
	findall(Val,
		mongolog_tests:test_call(
			(	X is Num + 5,
				Y is Num * 2,
				member(Val, [X,Y])
			),
			Num, double(4.5)),
		Results),
	assert_equals(Results,[9.5,9.0]).

:- end_tests('mongolog_lists').
