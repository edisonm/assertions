:- module(foreign_test_i,
          [ f_enum_example/4, f_union_example/4, f_setof_enum/4, fce/2, numl/2,
            fco/2, aa/2, eq/2, idx/3, get_arrays/4, positive_t/1, negative_t/1,
            show_arrays/3, fortran1/2, io/1, sio/1, fd1/4, fd2/4, test_array/3,
            fill_array/3, test_ireverse1/2, test_ireverse2/2, f_setof_enum_2/4,
            fd3/4, extend/2, f/1
          ]).

:- use_module(library(filesex)).
:- use_module(library(neck)).
:- use_module(library(assertions)).
:- use_module(library(plprops)).
:- use_module(library(foreign/foreign_interface)).
:- use_module(library(foreign/foreign_props)).
:- init_expansors.
% :- extra_compiler_opts('-O2 -gdwarf-2 -g3 -D__DEBUG_MALLOC__').
:- extra_compiler_opts('-O2 -gdwarf-2 -g3').
:- use_foreign_header(include/foreign_test).
:- use_foreign_source(foreign_test).
:- include_foreign_dir(include).
:- foreign_dependency(include/'includedf.for').
:- use_foreign_source('foreign_test.for').
:- gen_foreign_library(plbin(foreign_test_i)).

:- type negative_t/1 is (foreign(is_negative_t), tgen([gett, unif])).

/*
:- type bool_t/1 + tgen.

bool_t(fail).
bool_t(true).

:- type struct_example_t/1 + tgen.

struct_example_t(apple).
struct_example_t(orange).
struct_example_t(banana(IsFrying)) :- bool_t(IsFrying).
struct_example_t(rice(IsIntegral)) :- bool_t(IsIntegral).

:- type setof_struct_examples_t/1 + tgen.

setof_struct_examples_t(SExamples) :-
    setof(struct_example_t, SExamples).
*/

:- type enum_example_t/1 + tgen.
enum_example_t(element(1)).
enum_example_t(element(a)).
enum_example_t(element_3).
enum_example_t(element(f(g(h)))).

:- pred f_enum_example(+enum_example_t, enum_example_t, -enum_example_t, -int) is foreign(c_enum_example).

:- type setof_enum_s/1 + sgen.

setof_enum_s(S) :- setof(enum_example_t, S).

:- pred f_setof_enum(+setof_enum_s, setof_enum_s, -setof_enum_s, -long) is foreign(c_setof_enum).

:- type setof_body_s/1 + sgen.
setof_body_s(setof_body(Label, Set, Array)) :-
    atm(Label),
    setof(enum_example_t, Set),
    array(enum_example_t, [4], Array).

:- type enum32_s/1 + sgen.
enum32_s(X) :-
    between(1, 32, X),
    neck.

:- type setof_enum32_s/1 + sgen.
setof_enum32_s(S) :- setof(enum32_s, S).

:- type enum64_s/1 + sgen.
enum64_s(X) :-
    between(1, 64, X),
    neck.

:- type setof_enum64_s/1 + sgen.
setof_enum64_s(S) :- setof(enum64_s, S).

:- type enum128_s/1 + sgen.
enum128_s(X) :-
    between(1, 128, X),
    neck.

:- type setof_enum128_s/1 + sgen.
setof_enum128_s(S) :- setof(enum128_s, S).

:- type enum256_s/1 + sgen.
enum256_s(X) :-
    between(1, 256, X),
    neck.

:- type setof_enum256_s/1 + sgen.
setof_enum256_s(S) :- setof(enum256_s, S).

:- type enum512_s/1 + sgen.
enum512_s(X) :-
    between(1, 512, X),
    neck.

:- type setof_enum512_t/1 + tgen.
setof_enum512_t(S) :- setof(enum512_s, S).

:- type array_enum_512_t/1 + tgen.
array_enum512_t(A) :- array(enum512_s, [2], A).

:- pred f_setof_enum_2(+setof_enum256_s, setof_enum256_s, -setof_enum256_s, -long) is foreign(c_setof_enum256).

:- type temperature_t/1 + sgen.
temperature_t(T) :- num(T).

:- type nw_stream_s/1 + sgen.
nw_stream_s(NwStream) :-
    dict_t(nw_stream,
           [p:atm,
            e:list(atm),
            t:temperature_t,
            d:num,
            h:char,
            i:int
           ],
          NwStream).

:- type nw_stream_t/1 + sgen.
nw_stream_t(S) :- nw_stream_s(S).

this_dir(Dir) :-
    context_module(M),
    module_property(M, file(Path)),
    directory_file_path(Dir, _, Path).

:- ( \+ user:file_search_path('.', _)
    ->this_dir(Dir),
    asserta(user:file_search_path('.', Dir))
    ; true
    ).

:- type d_t/1 + sgen.

d_t(Dict) :-
    dict_t(d{value1:atm,
             value2:atm,
             listv:list(int)
            },
          Dict).

:- pred [fortran1(+num,-num),
         fd1(+d_t,atm,str,int),
         fd2(-d_t,+atm,+atm,+int)+memory_root,
         fd3(d_t,atm,atm,list(int))+memory_root,
         fd4(list(atm))+memory_root
        ] is foreign.

:- type positive_t/1 + sgen.
positive_t(N) :- int(N).

:- type union_s/1 + sgen.
union_s(u(First, Second)) :-
    int(First),
    int(Second).
union_s(num(Number)) :-
    num(Number).
union_s(positive(T)) :-
    positive_t(T).

:- type uniond_t/1 + tgen.

% :- type uniond_s_d/1.
% uniond_s_d(Dict) :- 
%     dict_t(d{value1:atm,
%              value2:list(atm)},
%            Dict).

uniond_t(u(Dict2, Num)) :-
    d_t(Dict2),
    num(Num).
uniond_t(d(Dict)) :-
    % uniond_s_d(Dict).
    dict_t(d{value1:atm,
             value2:list(atm)
            },
           Dict).
uniond_t(pair(X, Y)) :-
    num(X),
    num(Y).
uniond_t(positive(T)) :-
    positive_t(T).

:- pred f_union_example(+ptr(uniond_t), uniond_t, -uniond_t, -int) is foreign(c_union_example).

:- type contain_extern_t/1 + sgen.
contain_extern_t(contain_extern(Idx, Value)) :-
    int(Idx),
    positive_t(Value).

:- type contain_opaque_t/1 + sgen.
contain_opaque_t(contain_opaque(Idx, Value)) :-
    int(Idx),
    negative_t(Value).

:- type example_t/1 + sgen.
example_t(example(Name, Value)) :-
    atm(Name),
    num(Value).

:- type compound_t/1 + sgen.
compound_t(compound(Idx, Value, Example, Name, PExample)) :-
    int(Idx),
    ptr(int, Value),
    example_t(Example),
    ptr(atm, Name),
    ptr(example_t, PExample).

:- pred fce(+contain_extern_t, -contain_extern_t) is foreign.

:- pred fco(+contain_opaque_t, -contain_opaque_t) is foreign.

:- type flag_t/1 + sgen.

flag_t(Value) :- int(Value).

:- type field_t/1 + sgen.

field_t(field(A, B, Sum)) :- int(A), int(B), ptr(flag_t, Sum).

:- type position_t/1 + sgen.

position_t(position(X, Y)) :- int(X), int(Y).

:- type geometry_t/1 + sgen.

geometry_t(geometry(P, W, H)) :- position_t(P), int(W), int(H).

:- pred aa(+position_t, -position_t) is foreign(c_aa).

:- pred pp(+int,-int:C) is (foreign(c_pp), returns(C)).

:- pred a(+list(position_t), +position_t) is foreign(c_a).

:- pred extend(+list(int),-list(int)) is foreign.

:- pred eq(+int, -int) is foreign(c_eq).

:- pred idx(+list(num), +int, -num) is foreign(c_idx).

:- pred numl(+int, -list(num)) is (foreign(c_numl), memory_root).

:- pred f(?field_t) is (foreign(c_f), returns_state, memory_root).
:- pred pq(?position_t) is foreign(c_pq).

:- pred get_arrays(+int,-list(list(list(num))), -list(list(int)), -list(int))
    is (foreign(c_get_arrays), memory_root).

:- pred show_arrays(+list(list(list(num))), +list(list(int)), +list(int))
    is foreign.

:- pred io(int) is foreign(c_io).

:- pred sio(int) is (foreign(c_sio), returns_state, memory_root).

:- pred [ireverse1(     +list(int), -list(int)) is (fimport, returns_state, memory_root),
         test_ireverse1(+list(int), -list(int)) is (foreign, memory_root),
         ireverse2(+list(int):LIn,  -list(int)) is (fimport, returns_state, parent(LIn)),
         test_ireverse2(+list(int), -list(int)) is (foreign),
         ireverse3(     +list(int), -list(int)) is (nimport)
        ].

ireverse1(X, Y) :- reverse(X, Y).

ireverse2(X, Y) :- reverse(X, Y).

ireverse3(X, Y) :- reverse(X, Y).

% :- pred u(list(list(list(num))), list(list(int)), list(int), int)
%     is foreign(c_u).

:- style_check(-singleton).
:- pred test_array(+M:size_t, +array(num, [M, N]), -R:num) is (foreign, returns(R)).
:- style_check(+singleton).
:- pred fill_array(+M:size_t, +N:size_t, -array(num, [M, N])) is (foreign).

/*
:- true pred s(-list(list(list(num))):LLL, -list(list(int)):LLN, -list(int):LN, -int:N)
    is (foreign(c_s),
        size_of(LLL, LLN),
        size_of(LLN, LN),
        size_of(LN, N)
       ).
*/
