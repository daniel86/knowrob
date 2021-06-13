:- module(mongolog_pragma, []).

:- use_module('../../mongolog').

%%
:- mongolog:add_command(pragma).

%%
% pragma(Goal) is evaluated compile-time by calling
% the Goal. This is usually done to unify variables
% used in the aggregation pipeline from the compile context.
%
mongolog:step_compile1(pragma(Goal), _, [document([]), variables([])]) :-
	% ignore vars referred to in pragma as these are handled compile-time.
	% only the ones also referred to in parts of the query are added to the document.
	call(Goal).
