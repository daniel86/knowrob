:- module(mongolog_touch, []).

:- use_module('../../mongolog').

:- mongolog:add_command(touch).

% touch is used such that the compiler knows about variables appearing
% in the touched term, and to associate keys to these variables.
mongolog:step_compile(touch(_TouchedTerm), _Ctx, []) :- true.
