:- module(plprops, [det/1, semidet/1, nondet/1, multi/1, type/1]).

:- use_module(library(swi/assertions)).
:- use_module(library(swi/nativeprops)).
:- use_module(library(swi/basicprops)).
:- use_module(library(assertions/send_check)).

% SWI-Like Properties:

:- true prop type/1.
:- meta_predicate type(0).
type(Goal) :- call(Goal).

:- prop det(X) + equiv(not_fails(is_det(X))).
:- meta_predicate det(0).
% det(Goal) :- not_fails(is_det(Goal)).
det(Goal) :-
	Solved = solved(no),
	( true
	; arg(1, Solved, no) ->
	  send_comp_rtcheck(Goal, det, fails),
	  fail
	),
	prolog_current_choice(C0),
	Goal,
	prolog_current_choice(C1),
	( arg(1, Solved, no)
	-> true
	; send_comp_rtcheck(Goal, det, non_det)
	%% more than one solution!
	),
	( C0 == C1 -> !
	; nb_setarg(1, Solved, yes)
	).

:- prop semidet(X) + equiv(is_det(X)).

:- meta_predicate semidet(0).
semidet(Goal) :- is_det(Goal).

:- prop nondet/1.

:- meta_predicate nondet(0).
nondet(Goal) :- Goal.

:- prop multi(X) + equiv(not_fails(X)).

:- meta_predicate multi(0).
% multi(Goal) :- not_fails(Goal).
multi(Goal) :-
	Solved = solved(no),
	( true
	; arg(1, Solved, no) ->
	  send_comp_rtcheck(Goal, multi, fails),
	  fail
	),
	prolog_current_choice(C0),
	test_throw_2(Goal, multi, _, true),
	prolog_current_choice(C1),
	( C0 == C1 -> !
	; nb_setarg(1, Solved, yes)
	).
