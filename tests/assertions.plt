:- begin_tests(assertions).

:- use_module(library(substitute)).
:- use_module(library(assertions), except([(test)/1])).
				% :- use_module(library(assertions/assrt_lib)).

				% Test the assertion reader:

test(assrt_lib_1) :-
    assrt_lib:assertion_records(m, [], (pred p(A, B)
				::int(A):(gnd(A),var(B))
				=>(gnd(A), gnd(B))
				+ (not_fails,is_det)), _, R, _),
    assertion(R=[assrt_lib:asr_head_prop(Idx, m, p(A, B), check, pred, [], _),
		 assrt_lib:asr_comm(Idx, "", _),
		 assrt_lib:asr_comp(Idx, m, int(A), _),
		 assrt_lib:asr_call(Idx, m, gnd(A), _),
		 assrt_lib:asr_call(Idx, m, var(B), _),
		 assrt_lib:asr_succ(Idx, m, gnd(A), _),
		 assrt_lib:asr_succ(Idx, m, gnd(B), _),
		 assrt_lib:asr_glob(Idx, m, not_fails(_), _),
		 assrt_lib:asr_glob(Idx, m, is_det(_), _)
		]).

test(assrt_lib_2) :-
    assrt_lib:assertion_records(m, [], (pred system:p(A, B)
				::int(A):(gnd(A), var(B))
				=>(gnd(A), gnd(B))
				+ not_fails), _, R, _),
    assertion(R=[assrt_lib:asr_head_prop(Idx, system, p(A, B), check, pred,[], _),
		 assrt_lib:asr_comm(Idx, "", _),
		 assrt_lib:asr_comp(Idx, m, int(A), _),
		 assrt_lib:asr_call(Idx, m, gnd(A), _),
		 assrt_lib:asr_call(Idx, m, var(B), _),
		 assrt_lib:asr_succ(Idx, m, gnd(A), _),
		 assrt_lib:asr_succ(Idx, m, gnd(B), _),
		 assrt_lib:asr_glob(Idx, m, not_fails(_), _)
		]).

% for a normal expression without syntax sugar:
test(assrt_lib_simple) :-
    assrt_lib:assrt_lib_tr((:- pred atomic_list_concat(A, B)
			   :: (list(A, ground), atom(B))
			   :  (list(A, atom),   term(B))
			   => (list(A, atom),   atom(B))
			   +  (is_det, iso) # "Write live comments here"),
			   Record, a, Dict),
    assertion(Record=[assrt_lib:asr_head_prop(Idx, a, atomic_list_concat(A, B), check, pred, Dict, _),
		      assrt_lib:asr_comm(Idx, "Write live comments here", _),
		      assrt_lib:asr_comp(Idx, a, list(A, ground), _),
		      assrt_lib:asr_comp(Idx, a, atom(B), _),
		      assrt_lib:asr_call(Idx, a, list(A, atom), _),
		      assrt_lib:asr_call(Idx, a, term(B), _),
		      assrt_lib:asr_succ(Idx, a, list(A, atom), _),
		      assrt_lib:asr_succ(Idx, a, atom(B), _),
		      assrt_lib:asr_glob(Idx, a, is_det(_), _),
		      assrt_lib:asr_glob(Idx, a, iso(_), _)
		     ]).

test(assrt_lib_comp) :-
    assrt_lib:assertion_records(m, [], true comp nfi1(G,V) + (sideff(free), no_rtcheck), _, R, _),
    assertion(R=[assrt_lib:asr_head_prop(Idx, m, nfi1(G, V), true, comp, [], _),
		 assrt_lib:asr_comm(Idx, "", _),
		 assrt_lib:asr_glob(Idx, m, sideff(_, free), _),
		 assrt_lib:asr_glob(Idx, m, no_rtcheck(_), _)
		]).

% for a complex expression with syntax sugar:
test(assrt_lib_sugar) :-
    assrt_lib:assrt_lib_tr((:- pred atomic_list_concat/2
			   :: list(ground) * atom
			   :  list(atom)   * term
			   => list(atom)   * atom
			   +  (is_det, iso) # "Write live comments here"),
			   Record, a, Dict),
    assertion(Record=[assrt_lib:asr_head_prop(Idx, a, atomic_list_concat(A, B), check, pred, Dict, _),
		      assrt_lib:asr_comm(Idx, "Write live comments here", _),
		      assrt_lib:asr_comp(Idx, a, list(A, ground), _),
		      assrt_lib:asr_comp(Idx, a, atom(B), _),
		      assrt_lib:asr_call(Idx, a, list(A, atom), _),
		      assrt_lib:asr_call(Idx, a, term(B), _),
		      assrt_lib:asr_succ(Idx, a, list(A, atom), _),
		      assrt_lib:asr_succ(Idx, a, atom(B), _),
		      assrt_lib:asr_glob(Idx, a, is_det(_), _),
		      assrt_lib:asr_glob(Idx, a, iso(_), _)
		     ]).

% a complex expression that compact multiple assertions:
test(assrt_lib_multi) :-
    assrt_lib:assrt_lib_tr((:- pred [(q:a/1+kbmask([+])), b/2+hidden]+kbrule), Records, m, []),
    assertion(Records=[assrt_lib:asr_head_prop(Idx1, q, a(_), check, pred, [], _),
		       assrt_lib:asr_comm(Idx1, "", _),
		       assrt_lib:asr_glob(Idx1, m, kbrule(_), _),
		       assrt_lib:asr_glob(Idx1, q, kbmask(_, [(+)]), _),
		       assrt_lib:asr_head_prop(Idx2, m, b(_, _), check, pred, [], _),
		       assrt_lib:asr_comm(Idx2, "", _),
		       assrt_lib:asr_glob(Idx2, m, kbrule(_), _),
		       assrt_lib:asr_glob(Idx2, m, hidden(_), _)
		      ]).

test(assrt_lib_mode1) :-
    assrt_lib:assertion_records(u, [], pred dict(+int), _, Re, _),
    assertion(Re=[assrt_lib:asr_head_prop(Idx, u, dict(A), check, pred, [], _),
		  assrt_lib:asr_comm(Idx, "", _),
		  assrt_lib:asr_call(Idx, u, int(A), _)]).

test(assrt_lib_is_plus) :-
    As1 = (prop (hidden)/1 : callable  + no_rtcheck # "Specifies a hidden rule."),
    As2 = (prop (hidden)/1 : callable is no_rtcheck # "Specifies a hidden rule."),
    assrt_lib:assertion_records(user, [], As1, _, R1, _),
    assrt_lib:assertion_records(user, [], As2, _, R2, _),
    R1 = [_, _, _:asr_call(Idx1, _, _, _)|_],
    R2 = [_, _, _:asr_call(Idx2, _, _, _)|_],
    assertion(substitute(substitute_idx(Idx1, Idx2), R1, R2)).

substitute_idx(Idx1, Idx2, Term, Idx2) :-
    nonvar(Term),
    Term = Idx1.

test(assrt_lib_oddity_1) :-
    assrt_lib:assertion_records(m, [], (pred a:b/2 : e * l + n), _, R, _),
    assertion(R=[assrt_lib:asr_head_prop(Idx, a, b(A, B), check, pred, [], _),
		 assrt_lib:asr_comm(Idx, "", _),
		 assrt_lib:asr_call(Idx, a, e(A), _),
		 assrt_lib:asr_call(Idx, a, l(B), _),
		 assrt_lib:asr_glob(Idx, a, n(_), _)
		]).

test(assrt_lib_oddity_2) :-
    assrt_lib:assertion_records(m, [], (pred (a:b/2) : e * l + n), _, R, _),
    assertion(R=[assrt_lib:asr_head_prop(Idx, a, b(A, B), check, pred, [], _),
		 assrt_lib:asr_comm(Idx, "", _),
		 assrt_lib:asr_call(Idx, m, e(A), _),
		 assrt_lib:asr_call(Idx, m, l(B), _),
		 assrt_lib:asr_glob(Idx, m, n(_), _)
		]).

test(assrt_lib_abridged_notation) :-
    assrt_lib:assertion_records(rt, [], pred check_to_messages(+Time      :ctime_t,
							       +RTCheck   :rtcheck_error,
							       ?Messages0 :list(message_info),
							       ?Messages  :list(message_info))#"c", _, R, _),
    assertion(R=[assrt_lib:asr_head_prop(Idx,
					 rt, check_to_messages(Time,
							   RTCheck,
							   Messages0,
							   Messages), check, pred, [], _),
		 assrt_lib:asr_comm(Idx, "c", _),
		 assrt_lib:asr_comp(Idx, rt, list(Messages0, message_info), _),
		 assrt_lib:asr_comp(Idx, rt, list(Messages,  message_info), _),
		 assrt_lib:asr_call(Idx, rt, ctime_t(Time), _),
		 assrt_lib:asr_call(Idx, rt, rtcheck_error(RTCheck), _)]).

:- end_tests(assertions).
