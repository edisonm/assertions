/*  Part of Assertion Reader for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/assertions
    Copyright (C): 2017, Process Design Center, Breda, The Netherlands.
    All rights reserved.

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

    1. Redistributions of source code must retain the above copyright
       notice, this list of conditions and the following disclaimer.

    2. Redistributions in binary form must reproduce the above copyright
       notice, this list of conditions and the following disclaimer in
       the documentation and/or other materials provided with the
       distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
    "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
    LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
    FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
    COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
    INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
    BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
    LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
    CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
    LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
    ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
    POSSIBILITY OF SUCH DAMAGE.
*/

:- module(metaprops,
          [(declaration)/1,
           (declaration)/2,
           (global)/1,
           (global)/2,
           (type)/1,
           (type)/2,
           checkprop_goal/1,
           compat/1,
           compat/2,
           with_cv_module/2,
           cv_module/1,
           instan/1,
           instan/2,
           last_prop_failure/1
          ]).

:- use_module(library(apply)).
:- use_module(library(occurs)).
:- use_module(library(ordsets)).
:- use_module(library(assertions)).
:- use_module(library(resolve_calln)).
:- use_module(library(context_values)).
:- use_module(library(extend_args)).
:- use_module(library(qualify_meta_goal)).
:- use_module(library(safe_prolog_cut_to)).
:- use_module(library(gcb)).
:- use_module(library(list_sequence)).
:- use_module(library(substitute)).
:- use_module(library(clambda)).
:- use_module(library(terms_share)).
:- init_expansors.

:- true prop (type)/1 + (declaration(check), global(prop)) # "Defines a type.".

type(Goal) :- call(Goal).

:- true prop (global)/1 + (global(prop), declaration)
# "A property that is global, i.e., can appear after the + in the assertion.
and as meta predicates, meta_predicate F(0)".

global(Goal) :- call(Goal).

:- type assrt_type/1, assrt_status/1.

:- global global(Prop, Goal) : (assrt_type(Prop), callable(Goal))
# "Like global/1, but allows to specify the default assertion type".

global(_, Goal) :- call(Goal).

:- true prop (declaration)/1 + (global(prop), declaration)
# "A property that is a declaration, i.e., an operator is added as op(1125, fx, F). Implies global/1".

declaration(Goal) :- call(Goal).

:- true prop declaration(Status, Goal) : (assrt_status(Status), callable(Goal)) + global(prop)
# "Like declaration/1, but allows to specify the default assertion status".

declaration(_, Goal) :- call(Goal).

:- true prop cv_module/1.

cv_module(CM) :-
    current_context_value(current_module, CM),
    !.
cv_module(user).

:- true prop type(T, A)
# "~w is internally of type ~w, a predicate of arity 1 defined as a type/1."-[A, T].

:- meta_predicate
        type(1, ?),
        type(1, ?, -).

type(M:T, A) :-
    type(M:T, A, H),
    M:H.

type(M:T, A, H) :-
    extend_args(T, [Arg], H),
    ( cv_module(C),
      predicate_property(M:H, meta_predicate(Spec)),
      functor(H, _, N),
      arg(N, Spec, Meta),
      '$expand':meta_arg(Meta)
    ->Arg = C:A
    ; Arg = A
    ).

:- multifile
    unfold_calls:unfold_call_hook/4.

unfold_calls:unfold_call_hook(type(T, A), metaprops, M, M:call(T, A)).

:- true prop compat(Prop)
# "Uses ~w as a compatibility property."-[Prop].

:- meta_predicate compat(0 ).

compat(M:Goal) :-
    functor(Goal, _, A),
    arg(A, Goal, Last),
    \+ \+ compat(Goal, [Last], M).

:- thread_local
        '$last_prop_failure'/2.

generalize_term(STerm, Term, _) :-
    \+ terms_share(STerm, Term).

neg(nonvar(A), var(A)).
neg(A==B,  A \== B).
neg(A =B,  A  \= B).
neg(A=:=B, A =\= B).
neg(A,     \+A).

current_prop_failure((SG :- Body)) :-
    '$last_prop_failure'(Term, SubU),
    sort(SubU, Sub),
    greatest_common_binding(Term, Sub, ST, SSub, [[]], Unifier, []),
    substitute(generalize_term(SSub), ST, SG),
    maplist(\ A^NA^once(neg(A, NA)), SSub, NSub),
    foldl(simplify_unifier(SG-SSub), Unifier, LitL, NSub),
    LitL \= [],
    list_sequence(LitL, Body).

simplify_unifier(Term, A=B) -->
    ( {occurrences_of_var(A, Term, 0 )}
    ->{A=B}
    ; [A=B]
    ).

last_prop_failure(L) :-
    findall(E, once(current_prop_failure(E)), L),
    retractall('$last_prop_failure'(_, _)).

asserta_prop_failure(T, S) :-
    once(( retract('$last_prop_failure'(T, L))
         ; L = []
         )),
    asserta('$last_prop_failure'(T, [S|L])).

cleanup_prop_failure(T, S) :-
    retractall('$last_prop_failure'(_, _)),
    asserta('$last_prop_failure'(T, S)).

:- meta_predicate with_cv_module(0, +).
with_cv_module(Goal, CM) :-
    with_context_value(Goal, current_module, CM).

:- meta_predicate checkprop_goal(0 ).
checkprop_goal(Goal) :-
    ( current_context_value(checkprop, CheckProp)
    ->CheckProp = compat
    ; Goal
    ).

/*
:- meta_predicate compat1(1, ?).
compat1(M:Pred1, Arg) :-
    term_variables(Pred1, PVars),
    term_variables(Arg,   AVars),
    ord_subtract(AVars, PVars, Shared),
    \+ \+ compat(M:call(Pred1, Arg), Shared).
*/

:- meta_predicate compat(0, +).

compat(M:Goal, VarL) :-
    copy_term_nat(Goal-VarL, Term-VarTL), % get rid of corroutining while checking compatibility
    sort(VarTL, VS),
    cleanup_prop_failure(Term, []),
    prolog_current_choice(CP),
    with_context_value(
        compat(Term, data(VS, Term, CP), M), checkprop, compat).

% this small interpreter will reduce the possibility of loops if the goal being
% checked is not linear, i.e., if it contains linked variables:
compat(Var, _, _) :- var(Var), !.
compat(M:Goal, D, _) :-
    !,
    compat(Goal, D, M).
compat(G, _, M) :-
    ground(G),
    !,
    M:G. % this fixes a performance bug if G is big
compat(nonvar(_), _, _) :- !.
compat(A, D, M) :-
    do_resolve_calln(A, B),
    !,
    compat(B, D, M).
compat((A, B), D, M) :-
    !,
    compat(A, D, M),
    compat(B, D, M).
compat(type(T, A), D, M) :-
    !,
    strip_module(M:T, C, H),
    type(C:H, A, G),
    compat(G, D, C).
compat(compat(A), D, M) :-
    !,
    compat(A, D, M).
compat((A->B; C), D, M) :-
    !,
    (   call(M:A)
    ->  compat(B, D, M)
    ;   compat(C, D, M)
    ),
    !.
compat((A*->B; C), D, M) :-
    !,
    (   call(M:A)
    *-> compat(B, D, M)
    ;   compat(C, D, M)
    ),
    !.
compat(\+ G, _, M) :-
    !,
    \+ M:G.
compat((A->B), D, M) :-
    !,
    ( call(M:A)
    ->compat(B, D, M)
    ).
compat((A;B), D, M) :-
    !,
    ( compat(A, D, M)
    ; compat(B, D, M)
    ).
compat(!, data(_, _, CP), _) :-
    !,
    cut_from(CP).
compat(checkprop_goal(_), _, _) :- !.
compat(with_cv_module(A, C), D, M) :-
    !,
    with_cv_module(compat(A, D, M), C).
compat(mod_qual(T, A), D, M) :-
    !,
    strip_module(M:A, C, V),
    with_cv_module(compat(type(T, V), D, M), C).
compat(Term, D, M) :-
    D = data(_, T, _),
    asserta_prop_failure(T, Term),
    compat_1(Term, D, M),
    cleanup_prop_failure(T, []).

compat_1(@(A, C), D, M) :-
    !,
    compat_1(A, @(M:A, C), D, C, M).
compat_1(A, D, M) :-
    compat_1(A, M:A, D, M, M).

compat_1(A, G, D, C, M) :-
    D = data(V, _, _),
    compat_1(V, A, G, D, C, M).

compat_1(V, A, G, D, C, M) :-
    term_variables(A, AU), sort(AU, AVars),
    term_variables(V, TU), sort(TU, TVars),
    ord_intersect(AVars, TVars, Shared),
    ( functor(A, _, N),
      arg(N, A, Last),
      var(Last),
      ord_intersect([Last], Shared, [_])
    ->true
    ; Shared = []
    ->once(G)
    ; is_type(A, M)
    ->catch(compat_body(A, C, M, D), _, G)
    ; \+ ( \+ compat_safe(A, M),
           \+ ground(A),
           \+ aux_pred(A),
           \+ is_prop(A, M),
           print_message(warning, format("While checking compat, direct execution of predicate could cause infinite loops: ~q", [G-D])),
           fail
         ),
      once(G)
    ).

aux_pred(P) :-
    functor(P, F, _),
    atom_concat('__aux_', _, F).

compat_safe(_ =.. _, _).
compat_safe(_ = _, _).
compat_safe(_ is _, _).
compat_safe(call_cm(_, _, _), _).
compat_safe(context_module(_), _).
compat_safe(strip_module(_, _, _), _).
compat_safe(curr_arithmetic_function(_), _).
compat_safe(current_predicate(_), _).
compat_safe(functor(_, _, _), _).
compat_safe(freeze(_, _), _).
compat_safe(goal_2(_, _), _).
compat_safe(prop_asr(_, _, _, _), _).
compat_safe(static_strip_module(_, _, _, _), _).
compat_safe(freeze_cohesive_module_rt(_, _, _, _, _, _), _).
compat_safe(length(A, B), _) :- once((is_list(A) ; ground(B))).

is_prop(Head, M) :-
    prop_asr(Head, M, Stat, prop, _, _, _, _),
    memberchk(Stat, [check, true]).

is_type(Head, M) :-
    once(( prop_asr(Head, M, Stat, prop, _, _, _, Asr),
           memberchk(Stat, [check, true]),
           once(prop_asr(glob, type(_), _, Asr))
         )).

compat_body(M, H, C, V, T, CP) :-
    functor(H, F, A),
    functor(G, F, A),
    functor(P, F, A),
    (   % go right to the clauses with nonvar arguments that matches (if any):
        clause(M:H, Body, Ref),
        clause(M:G,    _, Ref),
        \+ P=@=G
    *-> true
    ;   clause(M:H, Body, Ref)
    ),
    clause_property(Ref, module(S)), % Source module
    ( predicate_property(M:H, transparent),
      \+ ( predicate_property(M:H, meta_predicate(Meta)),
           arg(_, Meta, Spec),
           '$expand':meta_arg(Spec)
         )
    ->CM = C
    ; CM = S
    ),
    compat(Body, data(V, T, CP), CM).

compat_body(G1, C, M, data(V, T, _)) :-
    qualify_meta_goal(G1, M, C, G),
    prolog_current_choice(CP),
    compat_body(M, G, C, V, T, CP).

cut_from(CP) :- catch(safe_prolog_cut_to(CP), _, true).

freeze_fail(CP, Term, V, N) :-
    freeze(V, ( prolog_cut_to(CP),
                cleanup_prop_failure(Term, [nonvar(N), N==V]),
                fail
              )).

:- global instan(Prop)
# "Uses Prop as an instantiation property. Verifies that execution of
   ~w does not produce bindings for the argument variables."-[Prop].

:- meta_predicate instan(0).

instan(Goal) :-
    term_variables(Goal, VS),
    instan(Goal, VS).

:- meta_predicate instan(0, +).

instan(Goal, VS) :-
    prolog_current_choice(CP),
    \+ \+ ( copy_term_nat(Goal-VS, Term-VN),
            maplist(freeze_fail(CP, Term), VS, VN),
            with_context_value(Goal, checkprop, instan)
          ).
