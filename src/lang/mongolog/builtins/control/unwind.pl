:- module(mongolog_unwind, []).

:- use_module('../../mongolog').

:- mongolog:add_command(unwind).

%% unwind(+ListOfDocuments)
%
%
mongolog:step_compile(unwind(ListOfDocuments), Ctx, Pipeline) :-
	mongolog:step_compile(unwind(ListOfDocuments, bool(false)), Ctx, Pipeline).

%% unwind(+ListOfDocuments, +PreserveNullAndEmpty)
%
%
mongolog:step_compile(unwind(ListOfDocuments, PreserveNullAndEmpty), Ctx,
		[	['$set', ['t_list', ListOfDocuments0]],
			% unwind the array, result is in the t_list field
			['$unwind', [
				[path, string('$t_list')],
				[preserveNullAndEmptyArrays, PreserveNullAndEmpty0]
			] ],
			% merge the document $t_list into the root document
			% NOTE: this also works if the t_list field does not exist!
			['$replaceWith', ['$mergeObjects', array([
				string('$$ROOT'), string('$t_list')
			])]],
			% and remove the t_list field
			['$unset', string('t_list')]
		]) :-
	arg_val(ListOfDocuments, Ctx, ListOfDocuments0),
	arg_val(PreserveNullAndEmpty, Ctx, PreserveNullAndEmpty0).

		 /*******************************
		 *    	  UNIT TESTING     		*
		 *******************************/

:- begin_tests('mongolog_unwind').

test('unwind([])'):-
	assert_true( mongolog_call( unwind(array([]), bool(true))) ),
	assert_false(mongolog_call( unwind(array([]))) ),
	assert_false(mongolog_call( unwind(array([]), bool(false))) ).

test('unwind([Doc1,Doc2])'):-
	findall([],
		mongolog_call(unwind(array([
			[foo,integer(2)],
			[foo,integer(2)]
		]))),
		Xs
	),
	length(Xs,L),
	assert_equals(L,2).

:- end_tests('mongolog_unwind').
