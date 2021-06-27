:- module(mongolog_terms, [ mng_flatten_term/3 ]).
/** <module> Analysing and constructing terms in mongolog programs.

The following predicates are supported:

| Predicate    | Arguments |
| ---          | ---       |
| functor/3    | ?Term, ?Name, ?Arity |
| arg/3        | ?Arg, +Term, ?Value |
| copy_term/2  | +In, -Out |
| =../2        | ?Term, ?List |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=manipterm
@license BSD
*/

:- use_module('../mongolog').
:- use_module('../variables').
:- use_module('../builtins/unification', [ unify_arg_field/4 ]).
:- use_module('../aggregation/match').
:- use_module('../aggregation/set').

%% query commands
:- mongolog:add_command(functor).
:- mongolog:add_command(arg).
:- mongolog:add_command(copy_term).
% TODO: support more term commands
%:- mongolog:add_command(same_term).
%:- mongolog:add_command(term_variables).
:- mongolog:add_command(=..).


%%
set_term_argument(Input, IndexString, OutputField, Step) :-
	atom_concat('$',OutputField,OutputField0),
	% - store some temp values to avoid repetitive computation
	(	Step=['$set', ['t_isize', ['$strLenCP', IndexString]]]
	% - retrieve t_index'th argument of term
	;	Step=['$set', [OutputField, ['$map', [
			[in, [
				[v, string('$$this.v')],
				[i, ['$concat', array([
					string('1'),
					['$substr', array([
						string('$$this.i'),
						string('$t_isize'),
						integer(-1)
					])]
				])]]
			]],
			[input, ['$filter', [
				% $filter t_term.value, only keeping entries for the selected
				% argument index
				[input, Input],
				[cond, ['$eq', array([
					IndexString,
					['$substr', array([
						string('$$this.i'),
						integer(0),
						string('$t_isize')
					])]
				])]]
			]]]
		]]]]
	;	Step=['$set', [OutputField, ['$cond', [
			[if,   ['$eq', array([integer(1), ['$size', string(OutputField0)]])]],
			% special handling of atomic values
			[then, ['$arrayElemAt', array([
				['$map', [
					[input, string(OutputField0)],
					[in, string('$$this.v')]
				]],
				integer(0)
			])]],
			% else create a term document
			[else, [
				[type,string(compound)],
				[arity, ['$max', ['$map', [
					[input,string(OutputField0)],
					[in, ['$toInt', ['$arrayElemAt', array([
						['$split', array([string('$$this.i'), string('.')])],
						integer(1)
					])]]]
				]]]],
				[value,string(OutputField0)]
			]]
		]]]]
	;	Step=['$unset', string('t_isize')]
	).

%% mng_flatten_term(+Term, +Ctx, -Flattened) is det.
%
%     a(b)    -> [ [[i,string('1.0')],[v,string(a)]], [[i,string('1.1'),b]] ]
%     a(b(c)) -> [ [[i,'1.0'],[v,a]], [[i,'1.1.0'],[v,b]], [[i,'1.1.1'],[v,c]] ]
%
mng_flatten_term(Term, Ctx, array(Flattened)) :-
	findall(X,
		mng_flatten_term1(Term, Ctx, X),
		Flattened
	).

mng_flatten_term1(Term, Ctx, X) :-
	flatten_term0('', 1, Term, Ctx, X).

flatten_term0(Prefix, Index, Term, Ctx, Flattened) :-
	compound(Term),!,
	atom_number(IndexAtom,Index),
	(	Prefix==''
	->	InnerPrefix=IndexAtom
	;	atomic_list_concat([Prefix,IndexAtom],'.',InnerPrefix)
	),
	Term =.. [Functor|Args],
	(	flatten_term2(InnerPrefix, 0, Functor, Ctx, Flattened)
	;	flatten_term1(InnerPrefix, 1, Args, Ctx, Flattened)
	).

flatten_term0(Prefix, Index, Arg, Ctx, Flattened) :-
	flatten_term2(Prefix, Index, Arg, Ctx, Flattened).

flatten_term1(Prefix, Index, [Arg|Rest], Ctx, Flattened) :-
	NextIndex is Index + 1,
	(	flatten_term0(Prefix, Index, Arg, Ctx, Flattened)
	;	flatten_term1(Prefix, NextIndex, Rest, Ctx, Flattened)
	).

flatten_term2(Prefix, Index, Arg, Ctx, Out0) :-
	atom_number(IndexAtom, Index),
	(	Prefix==[]
	->	ArgIndex=IndexAtom
	;	atomic_list_concat([Prefix,IndexAtom],'.',ArgIndex)
	),
	(	arg_val(Arg, Ctx, Val)
	->	Out=[[i,string(ArgIndex)],[v,Val]]
	;	Out=[[i,string(ArgIndex)]]
	),
	(	option(keep_vars,Ctx)
	->	Out0=[[var,Arg]|Out]
	;	Out0=Out
	).

%% functor(?Term, ?Name, ?Arity) [ISO]
% True when Term is a term with functor Name/Arity.
%
mongolog:step_compile(functor(Term,Functor,Arity), Ctx, Pipeline) :-
	arg_val(Term,Ctx,Term0),
	arg_val(Functor,Ctx,Functor0),
	arg_val(Arity,Ctx,Arity0),
	findall(Step,
		(	set_if_var(Term, [
				['type', string('compound')],
				['arity', Arity0],
				['value', ['$concatArrays', array([
					array([ [ [i,string('1.0')], [v,Functor0] ] ]),
					['$map', [
						['input', ['$range', array([ integer(0), Arity0, integer(1) ])]],
						['in', [[i, ['$concat', array([
							string('1.'),
							['$toString', ['$add', array([string('$$this'), integer(1)]) ]]
						])]]]]
					]]
				])]]
			], Ctx, Step)
		;	Step=['$set', ['t_term', Term0]]
		;	Step=['$set',
				% functor is first element of array at field t_term.value
				['t_functor', ['$arrayElemAt', array([
					string('$t_term.value'),
					integer(0)
				])]]
			]
		;	set_if_var(Functor,    string('$t_functor.v'), Ctx, Step)
		;	match_equals(Functor0, string('$t_functor.v'), Step)
		;	set_if_var(Arity,    string('$t_term.arity'), Ctx, Step)
		;	match_equals(Arity0, string('$t_term.arity'), Step)
		;	Step=['$unset', array([
				string('t_functor'),
				string('t_term')
			])]
		),
		Pipeline).

%% arg(?Arg, +Term, ?Value) [ISO]
% Term should be instantiated to a term, Arg to an integer between 1 and the arity of Term.
% Value is unified with the Arg-th argument of Term.
% Arg may also be unbound. In this case Value will be unified with the successive
% arguments of the term. On successful unification, Arg is unified with the
% argument number. Backtracking yields alternative solutions.
%
mongolog:step_compile(arg(Arg,Term,Value), Ctx, Pipeline) :-
	arg_val(Arg,Ctx,Arg0),
	arg_val(Term,Ctx,Term0),
	findall(Step,
		(	Step=['$set', ['t_term', Term0]]
		% - compute t_index=[Arg] if ground(Arg) and t_index=[0,...,Arity] else;
		;	Step=['$set', ['t_index', ['$cond', [
				[if,   ['$eq', array([Arg0,constant(undefined)])]],
				[then, ['$range', array([
					integer(1),
					['$add', array([integer(1), string('$t_term.arity')])]
				])]],
				[else, array([Arg0])]
			]]]]
		% - then iterate over each index in $t_index
		;	Step=['$unwind', string('$t_index')]
		% - assign the Arg field to the unwinded index
		;	set_if_var(Arg, string('$t_index'), Ctx, Step)
		% - convert to index string "1.Arg"
		%   FIXME: should have a trailing dot! else BUG for terms with more then 9 arguments!!
		%          but probably need to add trailing dot everywhere...
		;	Step=['$set', ['t_index', ['$concat', array([
				string('1.'), ['$toString', string('$t_index')]
			])]]]
		% - retrieve t_index'th argument of term
		;	set_term_argument(
				string('$t_term.value'),
				string('$t_index'),
				't_val1', Step)
		% unify: Value = t_val1
		;	unify_arg_field(Value, 't_val1', Ctx, Step)
		% cleanup
		;	Step=['$unset', array([
				string('t_term'),
				string('t_index'),
				string('t_val1')
			])]
		),
		Pipeline).
	
%mongolog:step_compile(arg(Arg,Term,Value), Ctx, Pipeline) :-
%	% TODO: support var(Arg),var(Value):
%	%	- list all args with their index
%	%	- first add indices to list, then $unwind
%	% FIXME: arg also need to handle var unification as in:
%	%         arg(0,foo(X),Y) would imply X=Y
%	%		- can be handled with conditional $set, add [X,Y] to
%	%         var array if both of them are vars
%	%
%	arg_val(Arg,Ctx,Arg0),
%	arg_val(Term,Ctx,Term0),
%	arg_val(Value,Ctx,Value0),
%	% FIXME: use $filter to get all items with index prefix "1.$Arg"
%	findall(Step,
%		(	Step=['$set', ['t_term', Term0]]
%		;	set_if_var(Arg, ['$add', array([
%					['$indexOfArray', array([ string('$t_term.value.args'), Value0 ])],
%					integer(1)
%			])], Ctx, Step)
%		;	set_if_var(Value, ['$arrayElemAt', array([
%					string('$t_term.value.args'),
%					['$subtract', array([Arg0, integer(1)])]	
%			])], Ctx, Step)
%		;	match_equals(Value0, ['$arrayElemAt', array([
%					string('$t_term.value.args'),
%					['$subtract', array([Arg0, integer(1)])]	
%			])], Step)
%		;	Step=['$unset', string('t_term')]
%		),
%		Pipeline).

%% copy_term(+In, -Out) [ISO]
% Create a version of In with renamed (fresh) variables and unify it to Out.
%
mongolog:step_compile(
		copy_term(In,Out), Ctx,
		[['$set', [OutKey, In0]]]) :-
	arg_val(In,Ctx,In0),
	var_key(Out,Ctx,OutKey).
%	findall(Step,
%		(	Step=['$set', ['t_term', In0]]
%		;	Step=['$set', [OutKey, ['$cond', [
%				% FIXME "$not 0" and "$not false" evaluates to true!
%				['if', ['$not', array([string('$t_term.value')])]],
%				['then', string('$t_term')],
%				['else', [
%					['type', string('compound')],
%					['value', [
%						['functor', string('$t_term.value.functor')],
%						['args', ['$map', [
%							['input', string('$t_term.value.args')],
%							['in', ['$cond', [
%								% if array element is not a variable
%								['if', ['$ne', array([string('$$this.type'), string('var')])]],
%								% then yield the value
%								['then', string('$$this')],
%								% else map to new variable
%								['else', [['type', string('var')], ['value', string('_')]]]
%							]]]
%						]]]
%					]]
%				]]
%			]]]]
%		;	Step=['$unset', string('t_term')]
%		),
%		Pipeline).

%% ?Term =.. ?List [ISO]
% List is a list whose head is the functor of Term and the remaining arguments
% are the arguments of the term.
% Either side of the predicate may be a variable, but not both.
% This predicate is called "Univ". 
%
mongolog:step_compile(=..(Term,List), Ctx, Pipeline) :-
	% FIXME: it won't work to unify two variables with univ yet, as in:
	%			foo(X,a) =.. [foo,Z,a] would imply X=Z which is not handled here yet!
	%          - needs additional map/filter operation
	%				- get args that are different vars in list and term, then add to var array
	% TODO: I think it needs to use $map and then run unify on each argument?
	%
	arg_val(Term,Ctx,Term0),
	arg_val(List,Ctx,List0),
	% FIXME:
	findall(Step,
		(	set_if_var(Term, [
				['type', string('compound')],
				['value', [
					['functor', ['$arrayElemAt', array([List0,integer(0)])]],
					['args', ['$slice', array([
						List0, integer(1),
						['$subtract', array([['$size', List0], integer(1)])]
					])]]
				]]
			], Ctx, Step)
		;	Step=['$set', ['t_term', Term0]]
		;	set_if_var(List, ['$concatArrays', array([
				array([string('$t_term.value.functor')]),
				string('$t_term.value.args')
			])], Ctx, Step)
		;	match_equals(List0, ['$concatArrays', array([
				array([string('$t_term.value.functor')]),
				string('$t_term.value.args')
			])], Step)
		;	Step=['$unset', string('t_term')]
		),
		Pipeline).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_terms').

test('functor(+Term,-Functor,-Arity)'):-
	mongolog_tests:test_call(
		functor(Term,Functor,Arity),
		Term, foo(bar,45)),
	assert_equals(Functor, foo),
	assert_equals(Arity, 2).

test('functor(-Term,+Functor,+Arity)'):-
	mongolog_tests:test_call(
		functor(Term,foo,Arity), Arity, 2),
	assert_unifies(Term, foo(_,_)),
	assert_false(ground(Term)).

test('arg(+Index,+Term,+Value)'):-
	assert_true(mongolog_tests:test_call(
		arg(Index,foo(a,b,c),a), Index, 1)),
	assert_true(mongolog_tests:test_call(
		arg(Index,foo(a,b,c),b), Index, 2)),
	assert_false(mongolog_tests:test_call(
		arg(Index,foo(a,b,c),b), Index, 1)),
	assert_false(mongolog_tests:test_call(
		arg(Index,foo(a,b,c),d), Index, 1)).

test('arg(+Index,+Term,-Value)') :-
	mongolog_tests:test_call(
		arg(Index,foo(a,b,c),Value), Index, 1),
	assert_equals(Value,a),
	assert_false(mongolog_tests:test_call(
		arg(Index,foo(a,b,c),_), Index, 5)).

test('arg(-Index,+Term,+Value)'):-
	mongolog_tests:test_call(
		arg(Index,foo(a,b,c),Value), Value, b),
	assert_equals(Index,2),
	assert_false(mongolog_tests:test_call(
		arg(_,foo(a,b,c),Value), Value, d)).

test('arg(-UnwindedIndex,+Term,+Value)', fixme('$indexOfArray only returns the first occurence')):-
	findall(Index,
		mongolog_tests:test_call(
			arg(Index,foo(a,b,a),Value), Value, a),
		Results),
	assert_equals(Results, [1,3]).

test('copy_term(+In,-Out)::compound') :-
	mongolog_tests:test_call(copy_term(In,Out), In, foo(a)),
	assert_equals(Out,foo(a)).

test('copy_term(+In,-Out)::atom') :-
	mongolog_tests:test_call(copy_term(In,Out), In, a),
	assert_equals(Out,a).

test('copy_term(+In,-Out)::number') :-
	mongolog_tests:test_call(copy_term(In,Out), In, 7),
	assert_equals(Out,7.0).

test('copy_term(+In,-Out)::vars') :-
	mongolog_tests:test_call(copy_term(In,Out), In, foo(a,X)),
	assert_unifies(Out, foo(a,_)),
	(Out=foo(a,Y) -> assert_true(X \== Y) ; true).

test('=..(+Term,-List)::ground') :-
	mongolog_tests:test_call(=..(Term,List), Term, foo(a,b)),
	assert_equals(List,[foo,a,b]).

test('=..(+Term,-List)::nonground') :-
	mongolog_tests:test_call(=..(Term,List), Term, foo(a,B)),
	assert_equals(List,[foo,a,B]).

test('=..(-Term,+List)') :-
	mongolog_tests:test_call(=..(Term,List), List, [foo,a,b]),
	assert_equals(Term,foo(a,b)).

:- end_tests('mongolog_terms').

