:- module(mongolog_compiler,
	[ merge_substitutions/3
	]).

%%
merge_substitutions(New, Old, Merged) :-
	append(New, Old, X),
	list_to_set(X, Merged).
