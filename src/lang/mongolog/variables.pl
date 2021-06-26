:- module(mongolog_variables,
	[ var_key/3,
	  arg_val/3,
	  arg_val_nested/3,
	  goal_vars/3,
	  goal_var/3,
	  goal_var_in_head/2,
	  context_var/2,
	  merge_substitutions/3
	]).


:- use_module(library('db/mongo/client')).

%% var_key(-Var, +Ctx, -Key) is det.
%
% Map a Prolog variable to the key that used to
% refer to this variable in mongo queries.
%
var_key(Var, Ctx, Key) :-
	var(Var),
	% TODO: can this be done better then iterating over all variables?
	%		- i.e. by testing if some variable is element of a list
	%		- member/2 cannot be used as it would unify each array element
	(	option(outer_vars(Vars), Ctx, [])
	;	option(step_vars(Vars), Ctx, [])
	),
	member([Key,ReferredVar],Vars),
	ReferredVar == Var,
	!.
var_key(Var, _Ctx, Key) :-
	var(Var),
	gensym('v_', Key).


%% arg_val(?ArgumentExpression, +Ctx, -Value) is det.
%
% yield either the key of a variable in mongo,
% or a typed term for some constant value provided
% in the query.
%
arg_val(In, Ctx, Out) :-
	mng_strip_operator(In, '=', In0),
	arg_val0(In0, Ctx, Out).
	
arg_val0(In, Ctx, string(Key)) :-
	mng_strip_type(In, _, In0),
	var_key(In0, Ctx, Out),
	% handle root_field/1 option that allows to select the root of the document
	% where the argument fields are stored.
	% By default this is "CURRENT" which must not be written out explicitely.
	% But e.g. in the scope of $map the root is at "this" which must be specified
	% explicitely when accessing a variable as in "$$this.foo".
	(	option(root_field(Root), Ctx)
	->	atomic_list_concat(['$$',Root,'.',Out],'',Key)
	;	atom_concat('$',Out,Key)
	),
	!.

arg_val0(In, _Ctx, Out) :-
	atomic(In),!,
	once(arg_constant(In,Out)).

arg_val0(In, Ctx, array(L)) :-
	is_list(In),!,
	findall(X,
		(	member(Y,In),
			arg_val0(Y, Ctx, X)
		),
		L).

arg_val0(:(NS,Atom), _, _) :-
	throw(unexpanded_namespace(NS,Atom)).

arg_val0(TypedValue, _Ctx, TypedValue) :-
	compound(TypedValue),
	TypedValue =.. [Type|_],
	mng_client:type_mapping(Type,_),
	!.

arg_val0(Term, Ctx, [
		['type', string('compound')],
		['value', Flattened]
	]) :-
	mng_strip_type(Term, term, Stripped),
	compound(Stripped),
	% FIXME
	mongolog_terms:mng_flatten_term(Stripped, Ctx, Flattened).

%%
%
arg_val_nested(In, Ctx, Out) :-
	arg_val(In, Ctx, X),
	(	(X=string(Str), atom(Str), atom_concat('$',_,Str))
	->	(X=string(Str), atom_concat('$',Str,Y), Out=string(Y))
	;	Out=X
	).

%% in case of atomic in query
arg_constant(Value, double(Value)) :- number(Value).
arg_constant(true,  bool(true)).
arg_constant(false, bool(false)).
arg_constant(Value, string(Value)) :- atom(Value).
arg_constant(Value, string(Value)) :- string(Value).


%% goal_vars(+Goal, +Ctx, -Vars) is det.
%
% read all variables referred to in Step into list StepVars
%
goal_vars(Step, Ctx, StepVars) :-
	(	bagof(Vs, goal_var(Step, Ctx, Vs), StepVars)
	;	StepVars=[]
	),!.

%% goal_var(+Var, +Ctx, -Var) is nondet.
%
%
goal_var(Var, Ctx, [Key,Var]) :-
	var(Var),!,
	var_key(Var, Ctx, Key).

goal_var(List, Ctx, Var) :-
	is_list(List),!,
	member(X,List),
	goal_var(X, Ctx, Var).

goal_var(Dict, Ctx, Var) :-
	is_dict(Dict),!,
	get_dict(Key, Dict, Value),
	(	goal_var(Key,Ctx,Var)
	;	goal_var(Value,Ctx,Var)
	).

goal_var(Compound, Ctx, Var) :-
	compound(Compound),!,
	Compound =.. [_Functor|Args],
	member(Arg,Args),
	goal_var(Arg, Ctx, Var).


%% goal_var_in_head(+Goal, +Ctx) is semidet.
%
goal_var_in_head(Goal, Ctx) :-
	option(head_vars(HeadVars), Ctx),
	goal_vars(Goal, Ctx, InnerVars),
	member([_,V],HeadVars),
	member([_,W],InnerVars),
	V == W,
	!.


%%
context_var(Ctx, [Key,ReferredVar]) :-
	option(scope(Scope), Ctx),
	% NOTE: vars are resolved to keys in scope already!
	%       e.g. `Since == =<(string($v_235472))`
	time_scope(Since, Until, Scope),
	member(X, [Since, Until]),
	mng_strip(X, _, string, Stripped),
	atom(Stripped),
	atom_concat('$', Key, Stripped),
	once((
		option(outer_vars(Vars), Ctx),
		member([Key,ReferredVar],Vars)
	)).


%%
merge_substitutions(New, Old, Merged) :-
	append(New, Old, X),
	list_to_set(X, Merged).
