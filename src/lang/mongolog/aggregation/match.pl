:- module(mongolog_match,
	[ match_equals/3,
	  match_scope/1
	]).

%%
match_equals(A, B,
	['$match', ['$expr', ['$eq', array([A,B])]]]).

%%
match_scope(
	['$match', ['$expr', ['$lt', array([
		string('$v_scope.time.since'),
		string('$v_scope.time.until')
	])]]]).