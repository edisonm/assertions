:- module(basicprops, [list/2,
		       nlist/2,
		       sequence/2,
		       compat/2,
		       inst/2
		       ]).

%% A wrapper for the Ciao basic_props library

:- expects_dialect(ciao).
:- use_module(library(swi/assertions)).
:- use_module(library(engine/term_typing), [type/2]).
:- use_module(library(terms_check), [instance/2]).
:- reexport(engine(basic_props),
	    except([list/2,
		    nlist/2,
		    sequence/2,
		    compat/2,
		    inst/2])).

% Note that the following redefinitions can not replace those in basic_props.pl,
% otherwise the ciao emulation in SWI-Prolog will not longer work --EMM

:- true prop list/2 + regtype.
:- meta_predicate list(?, 1).

list([],_).
list([X|Xs], T) :-
        type(X, T),
        list(Xs, T).

:- true prop nlist/2 + regtype.
:- meta_predicate nlist(?, 1).

nlist([], _).
nlist([X|Xs], T) :-
        nlist(X, T),
        nlist(Xs, T).
nlist(X, T) :-
	type(X, T).

sequence(E, T) :- type(E, T).
sequence((E,S), T) :-
        type(E, T),
        sequence(S,T).

:- true prop compat/2.
:- meta_predicate compat(?, 1).
compat(T, P) :- \+ \+ type(P, T).

:- true prop inst/2.

inst(X, Prop) :-
	A = type(X, Prop),
	copy_term(A, AC),
	AC,
	instance(A, AC).
