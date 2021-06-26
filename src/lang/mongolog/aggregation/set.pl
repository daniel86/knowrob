:- module(mongolog_set,
	[ set_next_vars/2,
	  set_if_var/4
	]).

:- use_module('../variables').

%% set_next_vars(+Vars, -SetStage) is nondet.
%
% Move ground variables in "next" document to the document root.
% However, not all variables referred to in the goal may
% have a grounding, so we need to make a conditional $set here.
%
set_next_vars(Vars,
		['$set', [Key,
			% use value in next field if it is defined
			['$ifNull', array([
				string(NewVal),
				string(OldVal)
			])]
		]]) :-
	findall(Key0, member([Key0,_], Vars), Keys0),
	list_to_set(Keys0, Keys),
	member(Key, Keys),
	% TODO: use this instead of above
%	member([Key,_], Vars),
	atom_concat('$',Key,OldVal),
	atom_concat('$next.',Key,NewVal).

%% set_if_var(+Arg, +Exp, +Ctx, -SetStage) is semidet.
%
% Conditional $set command for ungrounded arguments.
%
set_if_var(Arg, Exp, Ctx,
		['$set', [ArgKey,
			['$ifNull', array([string(ArgVal),Exp])]
		]]) :-
	var_key(Arg, Ctx, ArgKey),
	atom_concat('$',ArgKey,ArgVal).

