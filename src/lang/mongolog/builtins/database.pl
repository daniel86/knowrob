:- module(mongolog_database, []).
/** <module> Storage of predicates in mongolog programs.

The following predicates are supported:

| Predicate    | Arguments |
| ---          | ---       |
| assert/1     | +Head |
| retractall/1 | +Head |

@author Daniel Beßler
@see https://www.swi-prolog.org/pldoc/man?section=dynpreds
@license BSD
*/

:- use_module('../mongolog').
:- use_module('../variables').
:- use_module('../stages/bulk_operation').
:- use_module('../kb/db_predicate').
:- use_module('../kb/edb').

%% query commands
:- mongolog:add_command(assert).
:- mongolog:add_command(retractall).

%%
lang_query:step_expand(project(Term), assert(Term)) :-
	db_predicate(Term, _, Opts),
	option(type(edb), Opts, edb),
	!.

%%
mongolog:step_compile1(assert(Literal), Ctx,
		[ document(Pipeline),
		  variables(StepVars)
		]) :-
	is_edb_predicate(Literal),!,
	db_predicate_zip(Literal, Ctx, Zipped, Ctx_pred, write),
	option(collection(Collection), Ctx_pred),
	option(step_vars(StepVars), Ctx_pred),
	% create a document
	findall([Field,Val],
		(	member([Field,Arg],Zipped),
			arg_val(Arg, Ctx_pred, Val)
		),
		PredicateDoc),
	% and add it to the list of asserted documents
	findall(Step,
		add_assertion(PredicateDoc, Collection, Step),
		Pipeline).

%%
mongolog:step_compile1(retractall(Literal), Ctx,
		[ document(Pipeline),
		  variables(StepVars)
		]) :-
	is_edb_predicate(Literal),!,
	db_predicate_zip(Literal, Ctx, Zipped, Ctx_pred, write),
	option(collection(Collection), Ctx_pred),
	option(step_vars(StepVars), Ctx_pred),
	mongolog_db_predicate:unpack_compound(Zipped, Unpacked),
	findall(InnerStep,
		(	mongolog_db_predicate:match_predicate(Unpacked, Ctx, Ctx_pred, InnerStep)
		% retractall first performs match, then only projects the id of the document
		;	project_retract(InnerStep)
		),
		InnerPipeline),
	%
	findall(Step,
		% look-up documents into 't_pred' array field
		(	mongolog_db_predicate:lookup_predicate('t_pred', InnerPipeline, Ctx_pred, Step)
		% add removed facts to assertions list
		;	add_assertions(string('$t_pred'), Collection, Step)
		;	Step=['$unset', string('t_pred')]
		),
		Pipeline
	).

%%
project_retract(Step) :-
	(	Step=['$project',[['_id',int(1)]]]
	;	Step=['$set',['delete',bool(true)]]
	).
