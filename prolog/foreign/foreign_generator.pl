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

:- module(foreign_generator,
          [generate_library/5,
           collect_prop/4,
           gen_foreign_library/3]).

:- use_module(library(apply)).
:- use_module(library(filesex)).
:- use_module(library(assertions)).
:- use_module(library(atomics_atom)).
:- use_module(library(codegen)).
:- use_module(library(call_ref)).
:- use_module(library(camel_snake)).
:- use_module(library(extend_args)).
:- use_module(library(extra_messages)).
:- use_module(library(foldil)).
:- use_module(library(foreign/foreign_props)).
:- use_module(library(key_value)).
:- use_module(library(lists)).
:- use_module(library(metaprops)).
:- use_module(library(neck)).
:- use_module(library(nmember)).
:- use_module(library(process)).
:- use_module(library(readutil)).
:- use_module(library(solution_sequences)).
:- use_module(library(substitute)).
:- use_module(library(terms)).
:- use_module(library(thread)).
:- use_module(library(transpose)).
:- use_module(library(pairs)).
:- init_expansors.

:- multifile
    foreign_dependency/2,
    gen_foreign_library/3,
    use_foreign_source/2,
    use_foreign_header/2,
    include_foreign_dir/2,
    library_foreign_dir/2,
    extra_compiler_opts/2,
    link_foreign_library/2,
    pkg_foreign_config/2.

:- discontiguous
    match_type//6,
    implement_type_unifier//3.

:- dynamic
    foreign_dependency/2,
    gen_foreign_library/3,
    use_foreign_source/2,
    use_foreign_header/2,
    include_foreign_dir/2,
    extra_compiler_opts/2,
    link_foreign_library/2,
    pkg_foreign_config/2.

:- table bind_type_names/2 as private.

% Predefined foreign dependencies:

foreign_dependency(M, HAlias) :- use_foreign_header(M, HAlias).
foreign_dependency(_, library('foreign/foreign_interface.h')).
foreign_dependency(_, library('foreign/foreign_swipl.h')).

command_to_atom(Command, Args, Atom) :-
    process_create(path(Command), Args, [stdout(pipe(Out))]),
    read_stream_to_codes(Out, String),
    atom_string(Atom, String).

language_command(for, M, path(gfortran), ValueL, ValueT) :-
    command_to_atom(swipl, ['--dump-runtime-variables'], Atom),
    atomic_list_concat(AtomL, ';\n', Atom),
    findall(Value,
            ( ( member(NameValue, AtomL),
                member(NameEq, ['PLCFLAGS="', 'PLLDFLAGS="']),
                atomics_atom([NameEq, Values, '"'], NameValue)
              ; extra_compiler_opts(M, Values)
              ),
              atomic_args(Values, ValueL1),
              member(Value, ValueL1)
            ),
            ValueL, ValueT).
language_command(c, M, path('swipl-ld'), ValueL, ValueT) :-
    findall(COpt, ( COpt = '-shared'
                  ; ( extra_compiler_opts(M, COpts)
                    ; pkg_foreign_config(M, Package),
                      command_to_atom('pkg-config', ['--cflags', Package], COpt1),
                      atom_concat(COpts, '\n', COpt1)
                    ),
                    atomic_args(COpts, COptL1),
                    member(COpt, COptL1)
                  ), ValueL, ValueT).

intermediate_obj(M, DirSO, OptL, LibL, Source, Object) -->
    { file_name_extension(Base, Ext, Source),
      file_base_name(Base, Name),
      ( Ext = for,
        memberchk(gfortran, LibL)
      ->true
      ; Ext = c
      ),
      intermediate_obj_cmd(Ext, Name, M, DirSO, OptL, Source, Object, Command)
    },
    !,
    ( {is_newer(Object, Source)}
    ->[]
    ; [Ext-Command]
    ).
intermediate_obj(_, _, _, _, Source, Source) --> [].

intermediate_obj_cmd(Ext, Name, M, DirSO, OptL, Source, Object, Compiler-Args) :-
    % Add a prefix to avoid problems with other files with the same base
    atomic_list_concat([Name, '_', Ext], NameFor),
    file_name_extension(NameFor, o, NameO),
    directory_file_path(DirSO, NameO, Object),
    append([OptL, ['-c', Source, '-o', Object]], FOptL),
    language_command(Ext, M, Compiler, Args, FOptL).

generate_library(M, AliasSO, AliasSOPl, InitL, File) :-
    absolute_file_name(AliasSO, FileSO, [file_type(executable),
                                         relative_to(File)]),
    findall(FSource, ( ( use_foreign_source(M, FAlias)
                       ; FAlias = library('foreign/foreign_interface.c')
                       ; FAlias = library('foreign/foreign_swipl.c')
                       ),
                       absolute_file_name(FAlias, FSource,
                                          [extensions(['.c', '']),
                                           access(read),
                                           relative_to(File)])
                     ), FSourceL),
    ( forall(( Dep = File
             ; member(Alias, [library(foreign/foreign_generator),
                              library(foreign/foreign_props),
                              library(foreign/foreign_interface)
                             ]),
               absolute_file_name(Alias, Dep, [file_type(prolog),
                                               access(read),
                                               relative_to(File)])),
             is_newer(FileSO, Dep))
    ->print_message(informational,
                    format("Skipping generation of ~w interface: is up to date", [File])),
      compile_library(M, FileSO, File, FSourceL)
    ; do_generate_library(M, FileSO, File, InitL),
      do_generate_wrapper(M, AliasSO, AliasSOPl, File),
      do_compile_library(M, FileSO, File, FSourceL)
    ).

compile_library(M, FileSO, File, FSourceL) :-
    intf_file(FileSO, IntfFile),
    ( forall(( member(Dep, [IntfFile|FSourceL])
             ; foreign_dependency(M, HAlias),
               absolute_file_name(HAlias, Dep,
                                  [extensions(['.h','']),
                                   access(read),
                                   relative_to(File)])
             ),
             is_newer(FileSO, Dep))
    ->print_message(informational,
                    format("Skipping compilation of ~w: is up to date", [FileSO]))
    ; do_compile_library(M, FileSO, File, FSourceL, IntfFile)
    ).

% Beyond MaxFLIArgs arguments we should pack foreign arguments due to a
% hard-coded limitation of SWI-Prolog:
max_fli_args(10 ).

do_generate_wrapper(M, AliasSO, AliasSOPl, File) :-
    max_fli_args(MaxFLIArgs),
    findall(F/A, ( current_foreign_prop(Head, M, _, _, Glob),
                   arg(1, Glob, Opts),
                   \+ ( nmember(lang(Lang), Opts),
                        lang(Lang)
                      ),
                   \+ ( predicate_property(M:Head, number_of_clauses(X)),
                        X>0
                      ),
                   functor(Head, F, A)
                 ), IntfPIU),
    sort(IntfPIU, IntfPIL),
    atom_concat(M, '$impl', IModule),
    absolute_file_name(AliasSOPl, FileSOPl, [file_type(prolog),
                                             relative_to(File)]),
    save_to_file(FileSOPl,
                 phrase(( add_autogen_note(M),
                          [(:- module(IModule, IntfPIL))],
                          generate_aux_clauses(M),
                          ["",
                           (:- use_foreign_library(AliasSO)),
                           % make these symbols public:
                           (:- initialization(( shlib:current_library(AliasSO, _, F1, IModule, _),
                                                open_shared_object(F1, _Handle, [global])), now))],
                          findall((Head :- Body),
                                  ( member(F/A, IntfPIL),
                                    A > MaxFLIArgs,
                                    atomic_list_concat(['__aux_pfa_', F, '_', A], NF),
                                    functor(Head, F, A),
                                    Body =.. [NF, Head]
                                  ))
                        ))).

atomic_args(String, ArgL) :-
    atomic_list_concat(ArgL1, ' ', String),
    subtract(ArgL1, [''], ArgL).

do_generate_library(M, FileSO, File, InitL) :-
    file_name_extension(BaseFile, _, FileSO),
    generate_foreign_interface(M, File, InitL, BaseFile).

dir_intf(File, DirIntf) :-
    absolute_file_name(library(foreign/foreign_interface),
                       IntfPl,
                       [file_type(prolog), access(read), relative_to(File)]),
    directory_file_path(DirIntf, _, IntfPl).

intf_file(FileSO, IntfFile) :-
    file_name_extension(BaseFile, _, FileSO),
    atom_concat(BaseFile, '_intf.c', IntfFile).

do_compile_library(M, FileSO, File, FSourceL) :-
    intf_file(FileSO, IntfFile),
    do_compile_library(M, FileSO, File, FSourceL, IntfFile).

do_compile_library(M, FileSO, File, FSourceL, IntfFile) :-
    dir_intf(File, DirIntf),
    directory_file_path(DirSO, _, FileSO),
    findall(IDir, ( ( Dir = DirSO
                    ; Dir = DirIntf
                    ; include_foreign_dir(M, DAlias),
                      absolute_file_name(DAlias, Dir, [file_type(directory),
                                                       relative_to(File)])
                    ),
                    atom_concat('-I', Dir, IDir)
                  ), IDirL),
    CommonOptL = ['-fPIC'|IDirL],
    foldl(intermediate_obj(M, DirSO, CommonOptL, LibL), [IntfFile|FSourceL], FTargetL, ExtCommands, []),
    once(append(LibL, [], _)),
    findall(COpt, ( COpt = '-shared'
                  ; ( extra_compiler_opts(M, COpts)
                    ; pkg_foreign_config(M, Package),
                      command_to_atom('pkg-config', ['--cflags', Package], COpt1),
                      atom_concat(COpts, '\n', COpt1)
                    ),
                    atomic_args(COpts, COptL1),
                    member(COpt, COptL1)
                  ), COptL),
    findall(CLib, ( ( link_foreign_library(M, Lib)
                    ; member(Lib, LibL)
                    ),
                    atom_concat('-l', Lib, CLib)
                  ; pkg_foreign_config(M, Package),
                    command_to_atom('pkg-config', ['--libs', Package], CLib1),
                    atom_concat(CLibs, '\n', CLib1),
                    atomic_args(CLibs, CLibL1),
                    member(CLib, CLibL1)
                  ), CLibL, ['-o', FileSO]),
    findall(LDir, ( library_foreign_dir(M, DAlias),
                    absolute_file_name(DAlias, Dir, [file_type(directory),
                                                     relative_to(File)]),
                    atom_concat('-L', Dir, LDir)
                  ),
            LDirL),
    append([COptL, CommonOptL, LDirL, FTargetL, CLibL], FArgsL),
    keysort(ExtCommands, Sorted),
    group_pairs_by_key(Sorted, Grouped),
    concurrent_maplist(compile_1, Grouped),
    compile_2(path('swipl-ld')-FArgsL).

compile_1(Ext-Commands) :- compile_1(Ext, Commands).

% Note: Due to the presence of Fortran modules, the compilation of Fortran can
% not be parallelized, since Prolog is not aware of Fortran dependencies, so we
% compile such modules serialized
compile_1(for, Commands) :-            maplist(compile_2, Commands).
compile_1(c,   Commands) :- concurrent_maplist(compile_2, Commands).

compile_2(Command-ArgL) :-
    process_create(Command, ArgL, [stdout(pipe(Out)),
                                   stderr(pipe(Err))]),
    read_string(Err, _, SErr),
    read_string(Out, _, SOut),
    close(Err),
    command_to_string(Command, ArgL, CommandS),
    catch(call_cleanup(
              close(Out),
              ( SOut = "",
                SErr = ""
              ->print_message(informational, format("~s", [CommandS]))
              ; print_message(warning, format("~s~s~nCommand: ~s", [SOut, SErr, CommandS]))
              )),
          Error,
          print_message(error, Error)).

command_to_string(Command, ArgL, CommandS) :-
    ( Command = path(RCommand)
    ->true
    ; RCommand = Command
    ),
    atomic_list_concat([RCommand|ArgL], ' ', CommandS).

generate_foreign_interface(Module, FilePl, IntL, BaseFile) :-
    abolish_module_tables(foreign_generator),
    atom_concat(BaseFile, '_impl', BaseFileImpl),
    file_name_extension(BaseFileImpl, h, FileImpl_h),
    atom_concat(BaseFile, '_intf', BaseFileIntf),
    file_name_extension(BaseFileIntf, h, FileIntf_h),
    file_name_extension(BaseFileIntf, c, FileIntf_c),
    directory_file_path(_, Base, BaseFile),
    save_to_file(FileImpl_h, generate_foreign_impl_h(Module)),
    save_to_file(FileIntf_h, generate_foreign_intf_h(Module, FileImpl_h)),
    save_to_file(FileIntf_c, generate_foreign_c(Module, Base, IntL, FilePl, FileIntf_h)).

c_var_name(Arg, "_c_"+Arg).

generate_foreign_intf_h(Module, FileImpl_h) -->
    add_autogen_note(Module),
    ["#ifndef __"+Module+"_INTF_H",
     "#define __"+Module+"_INTF_H",
     "",
     "",
     "#include <foreign_swipl.h>",
     "#include \""+FileImpl_h+"\"",
     "",
     "extern module_t __"+Module+"_impl;"],
    findall_tp(Module, type_props_nf(gett), declare_type(gett)),
    findall_tp(Module, type_props_nf(unif), declare_type(unif)),
    findall("extern "+Decl+";",
            ( current_foreign_prop(Head, _, Module, _, _, _, _, Dict, FuncName, _, BindName, _, Type),
              apply_dict(Head, Dict),
              declare_intf_head(Type, FuncName, BindName, Head, Decl)
            )),
    ["",
     "#endif /* __"+Module+"_INTF_H */"].

declare_intf_head(foreign(Opts, _), _, BindName, _, Decl) :-
    once(( nmember(lang(Lang), Opts),
           lang(Lang)
         )),
    declare_intf_fimp_head(BindName, Decl).
declare_intf_head(foreign(Opts, _), FuncName, _, Head, Decl) :-
    once(nmember(lang(native), Opts)),
    declare_intf_head(FuncName, Head, Decl).
declare_intf_head(Type, _, BindName, Head, Decl) :-
    \+ ( Type = foreign(Opts, _),
         nmember(lang(Lang), Opts),
         lang(Lang)
       ),
    declare_intf_head(BindName, Head, Decl).

declare_intf_fimp_head(BindName, "predicate_t "+BindName+"").

generate_foreign_impl_h(Module) -->
    add_autogen_note(Module),
    ["#ifndef __"+Module+"_IMPL_H",
     "#define __"+Module+"_IMPL_H",
     "",
     "#include <foreign_interface.h>"],
    findall_tp(Module, type_props_nf(decl), declare_struct),
    declare_foreign_bind(Module),
    ["#endif /* __"+Module+"_IMPL_H */"].

add_autogen_note(Module) -->
    ["/* NOTE: File generated automatically from "+Module+" */",
     ""].

generate_foreign_c(Module, Base, InitL, FilePl, FileIntf_h) -->
    add_autogen_note(Module),
    findall("#include \""+File_h+"\"",
            ( use_foreign_header(Module, HAlias),
              absolute_file_name(HAlias, File_h, [extensions(['.h', '']),
                                                  access(read),
                                                  relative_to(FilePl)])
            )),
    ["#include \""+FileIntf_h+"\"",
     "",
     "module_t __"+Module+";",
     "module_t __"+Module+"_impl;"
    ],
    findall_tp(Module, type_props_nft(gett), implement_type_getter),
    findall_tp(Module, type_props_nft(unif), implement_type_unifier),
    generate_foreign_register(Module, Base, InitL),
    generate_foreign_intf(Module).

generate_foreign_register(Module, Base, InitL) -->
    ["install_t install_"+Base+"() {",
     "    __system_dict_create        =PL_predicate(\"dict_create\", 3, \"system\");",
     "    __system_get_dict           =PL_predicate(\"get_dict\",    3, \"system\");",
     "    __system_put_dict           =PL_predicate(\"put_dict\",    4, \"system\");",
     "    __foreign_generator_call_idx=PL_predicate(\"call_idx\",    2, \"foreign_generator\");",
     "    __foreign_generator_idx_call=PL_predicate(\"idx_call\",    2, \"foreign_generator\");",
     "    __"+Module+"     =PL_new_module(PL_new_atom(\""+Module+"\"));",
     "    __"+Module+"_impl=PL_new_module(PL_new_atom(\""+Module+"$impl\"));"],
    findall_tp(Module, type_props_nf([gett, unif]), define_aux_variables),
    findall(Line,
            ( current_foreign_prop(_, M, Module, _, _, _, _, _, _, PredName, BindName, Arity, Type),
              write_register_sentence(Type, M, Module, PredName, Arity, BindName, Line))),
    foldl(generate_init, InitL),
    ["} /* install_"+Base+" */",
     ""].

generate_init(Init) --> ["    "+Init+"();"].

write_register_sentence(foreign(Opts, _), M, _, PredName, Arity, BindName, Line) :-
    nmember(lang(Lang), Opts),
    lang(Lang),
    !,
    write_init_import_binding(M, PredName, Arity, BindName, Line).
write_register_sentence(_, M, CM, PredName, Arity, BindName, Line) :-
    write_register_foreign_native(M, CM, PredName, Arity, BindName, Line).

write_register_foreign_native(M, CM, PredName, Arity, BindName, L) :-
    max_fli_args(MaxFLIArgs),
    ( M == CM
    ->L1="    PL_register_foreign("
    ; L1="    PL_register_foreign_in_module(\""+M+"\","
    ),
    ( Arity =< MaxFLIArgs
    ->L = L1+"\""+PredName+"\", "+Arity+", "+BindName+", 0);"
    ; L = L1+"\"__aux_pfa_"+PredName+"_"+Arity+"\", 1, __aux_pfa_"+BindName+"_"+Arity+", 0);"
    ).

write_init_import_binding(M, PN, A, BN,
                          "    "+BN+" = PL_predicate(\""+PN+"\", "+A+", \""+M+"\");").

:- meta_predicate findall_tp(+,4,5,?,?).

findall_tp(Module, TypeProps, Call) -->
    findall(List,
            ( call(TypeProps, Module, TypePropLDictL, Pos, _Asr),
              maplist(apply_dict_tp, TypePropLDictL),
              phrase(type_components(Module, TypePropLDictL, Call, Pos), List)
            )).

apply_dict_tp(_-TypePropLDictL) :- maplist(apply_dict_tp_2, TypePropLDictL).

apply_dict_tp_2(t(Type, PropL, GlobL, Dict)) :- apply_dict(Type-PropL-GlobL, Dict).

auto_generated_types(M, GlobL, p(Type, PropL, Dict), t(Type, PropS, GlobL, Dict)) -->
    { get_type_name(Type, Name),
      foldl(match_unknown_type(M, Name), PropL, PropTypeL1, []),
      foldl(cleanup_redundant(Type, PropL), PropTypeL1, PropTypeL, []),
      substitute_values(PropTypeL, PropL, PropS)
    },
    foldl(add_dict(Dict), PropTypeL).

cleanup_redundant(Type, PropL, Prop=SubType) -->
    ( { functor(Type, _, A),
        arg(A, Type, Arg),
        functor(SubType, _, SA),
        arg(SA, SubType, SubArg),
        Arg==SubArg,
        PropL==[Prop]
      }
    ->[]
    ; [Prop=SubType]
    ).

add_dict(Dict, Prop=Type) --> [Type-[t(Type, [Prop], [], Dict)]].

match_unknown_type(M, Name, Prop) --> match_type(Prop, M, unknown, Name, _, _), !.

is_type(CM, Head) :-
    once(( prop_asr(Head, CM, check, prop, _, _, Asr),
           once(prop_asr(glob, type(_), _, Asr))
         )).

type_props(M, TypePropLDictL, Pos, Asr) :-
    type_props(M, _, TypePropLDictL, Pos, Asr).

type_props(M, Type, TypePropLDictL, Pos, Asr) :-
    type_props1(M, Type, TDict, Pos, Asr),
    type_props2(M, Type, TDict, TypePropLDictL, Asr).

type_props2(M, Type, TDict, TypePropLDictL, Asr) :-
    collect_prop(Asr, M, comp, TPropL),
    collect_prop(Asr, M, glob, TGlobL),
    ( TPropL \= []
    ->TypePropLDictL1 = [p(Type, TPropL, TDict)]
    ; bind_type_names(M:Type, TypePropLDictL1)
    ->true
    ; TypePropLDictL1 = [p(Type, [], TDict)]
    ),
    phrase(foldl(auto_generated_types(M, TGlobL), TypePropLDictL1, TypePropLDictL2),
           TypePropLDictL3, [Type-TypePropLDictL2]),
    maplist(resolve_special_terms, TypePropLDictL3, TypePropLDictL).

resolve_special_term(V, V) :- var(V).
resolve_special_term([], nil).
resolve_special_term([H|T], edge(H, T)).
resolve_special_term(T, T).

resolve_special_terms(Type1-TypePropLDictL1, Type-TypePropLDictL) :-
    resolve_special_arg(Type1, Type),
    maplist(resolve_special_term2, TypePropLDictL1, TypePropLDictL).

resolve_special_arg(Type1, Type) :-
    Type1 =.. List1,
    once(append(Left, [Last1], List1)),
    once(resolve_special_term(Last1, Last)),
    append(Left, [Last], List),
    Type =.. List.

resolve_special_term2(t(Type1, PropL, GlobL, Dict), t(Type, PropL, GlobL, Dict)) :- resolve_special_arg(Type1, Type).

type_props1(CM, Head, Dict, Pos, Asr) :-
    % Only consider assertions defined in this module
    asr_head_prop(Asr, CM, Head, check, prop, Dict, _, Pos),
    % But tye type definition could come from a different place
    is_type(CM, Head).

type_props_nf(Opts1, Module, TypePropLDictL, Pos, Asr) :-
    type_props_nf(Opts1, Module, _, TypePropLDictL, Pos, Asr).

type_props_nf(Opts1, Module, Type, TypePropLDictL, Pos, Asr) :-
    type_props(Module, Type, TypePropLDictL, Pos, Asr),
    once(( normalize_ftgen(Glob1, tgen(Opts2, _)),
           prop_asr(glob, Glob1, _, Asr),
           nmember(Opt, Opts1),
           nmember(Opt, Opts2)
         )),
    \+ ( normalize_ftype(Glob, NType),
         prop_asr(glob, Glob, _, Asr),
         arg(1, NType, Opts),
         \+ ( nmember(lang(Lang), Opts),
              lang(Lang)
            )).

type_props_nft(Opt, Module, TypePropLDictL, Pos, Asr) :-
    type_props_nf(Opt, Module, Type, TypePropLDictL, Pos, Asr),
    % Don't create getters and unifiers for
    % typedefs, they are just casts:
    \+ type_is_tdef(Module, Type, _, _).

define_aux_variables(dict_ini(_, Name, M, _), _, _) -->
    !,
    ["    __rtcwarn((__"+M+"_aux_keyid_index_"+Name+"=PL_pred(PL_new_functor(PL_new_atom(\"__aux_keyid_index_"+Name+"\"), 2), __"+M+"_impl))!=NULL);"].
define_aux_variables(dict_key_value(_, _, _, _), _, _) --> !, {fail}.
define_aux_variables(_, _, _) --> [].

implement_type_getter_ini(PName, CName, Spec, Name) -->
    { ( memberchk(Spec, [array(_, _), setof(_, _, _, _)])
      ->Decl = Name
      ; Decl = Name+"*"
      )
    },
    ["int FI_get_"+Name+"(root_t __root, term_t "+PName+", "+Decl+" "+CName+") {"].

c_get_argument_getter(Spec, CNameArg, PNameArg, GetArg) :-
    c_get_argument(Spec, in, CNameArg, PNameArg, GetArg).

implement_type_getter_union_ini_join(SubType, Spec, Term, Name, UType) -->
    { term_pcname(Term, Name, PName, CName),
      cname_utype(SubType, CName, UType1),
      ( \+ref_type(Spec)
      ->UType = "*"+UType1
      ; UType = UType1
      ),
      get_type_name(Term, Func),
      '$current_source_module'(CM)
    },
    implement_type_getter_ini(PName, CName, Spec, Name),
    ["    term_t __args = PL_new_term_refs(2);",
     "    int __utype;",
     "    __rtcheck(PL_unify_term(__args, PL_FUNCTOR_CHARS, \""+Func+"\", 1, PL_TERM, "+PName+"));",
     "    __rtcheck(__rtctype(PL_call_predicate(__"+CM+", PL_Q_NORMAL,",
     "                                          __foreign_generator_call_idx, __args),",
     "                        __args, "+Name+"));",
     "    __rtcheck(PL_get_integer(__args + 1, &__utype));",
     "    "+UType+"=__utype;"
    ].

implement_type_getter_union_ini(union, Spec, Term, Name) -->
    implement_type_getter_union_ini_join(union, Spec, Term, Name, UType),
    ["    switch ("+UType+") {"].
implement_type_getter_union_ini(cdef,   _, _, _) --> [].
implement_type_getter_union_ini(struct, _, _, _) --> [].
implement_type_getter_union_ini(enum, Spec, Term, Name) -->
    implement_type_getter_union_ini_join(enum, Spec, Term, Name, _).

implement_type_getter_union_end(union) -->
    ["    default:",
     "        return FALSE;",
     "    };"],
    implement_type_end.
implement_type_getter_union_end(cdef  ) --> [].
implement_type_getter_union_end(struct) --> [].
implement_type_getter_union_end(enum  ) --> implement_type_end.

enum_elem(Name, Term, Name+"_"+Suff) :- enum_suff(Term, Suff).

enum_suff(Term, Elem) :- get_type_name(Term, Elem).

implement_type_getter(union_ini(SubType, Spec, _), Term, Name) -->
    implement_type_getter_union_ini(SubType, Spec, Term, Name).
implement_type_getter(union_end(SubType, _), _, _) -->
    implement_type_getter_union_end(SubType).
implement_type_getter(func_ini(SubType, Spec), Term, Name) -->
    ( {SubType = union}
    ->{enum_elem(Name, Term, Elem)},
      ["    case "+Elem+":",
       "    {"]
    ; {func_pcname(Name, PName, CName)},
      implement_type_getter_ini(PName, CName, Spec, Name)
    ).
implement_type_getter(func_rec(SubType, N, Term, Name), Spec, Arg) -->
    { SubType = union
    ->enum_suff(Term, Suff),
      line_atom(Suff, TName),
      format(atom(CRecordName), "~w.~w", [TName, Arg]),
      format(atom(TNameArg), "~w_~w", [TName, Arg]),
      camel_snake(PRecordName, TNameArg),
      Indent = "        "
    ; CRecordName = Arg,
      camel_snake(PRecordName, Arg),
      Indent = "    "
    },
    { func_pcname(Name, PName, CName),
      ( memberchk(Spec, [setof(_, _, _, _)])
      ->CRef=""
      ; CRef="&"
      ),
      CNameArg=CRef+CName+"->"+CRecordName+"",
      PNameArg=PName+"_"+PRecordName
    },
    ( {SubType = union_type}
    ->{c_get_argument_getter(Spec, CNameArg, PName, GetArg)}
    ; [Indent+"term_t "+PNameArg+"=PL_new_term_ref();",
       Indent+"__rtcheck(PL_get_arg("+N+","+PName+","+PNameArg+"));"],
      {c_get_argument_getter(Spec, CNameArg, PNameArg, GetArg)}
    ),
    [Indent+GetArg+";"].
implement_type_getter(func_end(SubType, _), _, _) -->
    ( {SubType = union}
    ->["        break;",
       "    }"]
    ; implement_type_end
    ).
implement_type_getter(atomic(SubType, Name), Spec, Term) -->
    {enum_elem(Name, Term, Elem)},
    ( {SubType = union}
    ->{ func_pcname(Name, PName, CName1),
        enum_suff(Term, Suff),
        CName = CName1+"->"+Suff,
        Indent = "        "
      },
      ["    case "+Elem+":"]
    ; { func_pcname(Name, PName, CName),
        Indent = "    "
      },
      implement_type_getter_ini(PName, CName, Spec, Name)
    ),
    {c_get_argument_getter(Spec, CName, PName, GetArg)},
    [Indent+GetArg+";"],
    ( {SubType = union}
    ->[Indent+"break;"]
    ; implement_type_end
    ).
implement_type_getter(dict_ini(SubType, Name, M, _), Spec, Term) -->
    ( {SubType = union}
    ->{enum_elem(Name, Term, Elem)},
      ["    case "+Elem+":",
       "    {"]
    ; ["predicate_t __"+M+"_aux_keyid_index_"+Name+";"],
      {term_pcname(Term, Name, PName, CName)},
      %% TBD: This will fail for structures with dict_t
      implement_type_getter_dict_ini(M, PName, CName, Spec, Name)
    ).
implement_type_getter(dict_key_value(Dict, _, N, _), Key, Value) -->
    {key_value_from_dict(Dict, N, Key, Value)}.
implement_type_getter(dict_rec(SubType, _, Term, N, Name), Spec, Arg) -->
    { ( SubType = union
      ->enum_suff(Term, Suff),
        format(atom(CRecordName), "~w.~w", [Suff, Arg]),
        Indent = "        "
      ; CRecordName = Arg,
        Indent = "    "
      ),
      term_pcname(Term, Name, PName, CName),
      CNameArg = "&"+CName+"->"+CRecordName,
      c_get_argument_getter(Spec, CNameArg, PName, GetArg)
    },
    [Indent+"    case "+N+": "+GetArg+"; break;"].
implement_type_getter(dict_end(SubType, _, _), _, _) -->
    ["        }"],
    ( {SubType = union}
    ->["        break;",
       "    }"]
    ; implement_type_end
    ).

implement_type_getter_dict_ini(Module, PName, CName, Spec, Name) -->
    {ctype_decl(Spec, Decl)},
    ["static int get_pair_"+Name+"(root_t __root, term_t __keyid, term_t "+PName+", "+Decl+"* "+CName+");",
     ""],
    implement_type_getter_ini(PName, CName, Spec, Name),
    ["    memset("+CName+", 0, sizeof("+Decl+"));",
     "    FI_get_dict_t("+Name+", "+PName+", "+CName+");"
    ],
    implement_type_end,
    ["static int get_pair_"+Name+"(root_t __root, term_t __keyid, term_t "+PName+", "+Decl+"* "+CName+") {",
     "    int __index;",
     "    FI_get_keyid_index(__"+Module+"_aux_keyid_index_"+Name
     +", __keyid, __index);",
     "    switch (__index) {"].

implement_type_end -->
    ["    return TRUE;",
     "}",
     ""].

term_pcname(Term, NameL, Name) :-
    ( compound(Term)
    ->get_type_name(Term, Func)
    ; Func = Term
    ),
    ( valid_csym(Func)
    ->Name = Func
    ; Name = NameL
    ).

term_pcname(Term, NameL, PName, CName) :-
    term_pcname(Term, NameL, Name),
    func_pcname(Name, PName, CName).

func_pcname(NameL, PName, CName) :-
    ( is_list(NameL)
    ->atomic_list_concat(NameL, Name)
    ; Name = NameL
    ),
    camel_snake(PName, Name),
    c_var_name(Name, CName).

type_char(Type, Char) :- char_type(Char, Type).

valid_csym(Func) :-
    atom_codes(Func, Codes),
    maplist(type_char(csym), Codes).

implement_type_unifier(atomic(SubType, Name), Spec, Term) -->
    {enum_elem(Name, Term, Elem)},
    ( {SubType = union}
    ->{ func_pcname(Name, PName, CName1),
        enum_suff(Term, Suff),
        CName = CName1+"->"+Suff,
        Indent = "        "
      },
      ["    case "+Elem+":"]
    ; { func_pcname(Name, PName, CName),
        Indent = "    "
      },
      implement_type_unifier_ini(PName, CName, Name, Spec)
    ),
    { ( SubType = union
      ->Mode = inout
      ; Mode = out
      ),
      c_set_argument(Spec, Mode, CName, PName, SetArg)
    },
    [Indent+SetArg+";"],
    ( {SubType = union}
    ->[Indent+"break;"]
    ; implement_type_end
    ).
implement_type_unifier(union_ini(SubType, Spec, _), Term, Name) -->
    implement_type_unifier_union_ini(SubType, Spec, Term, Name).

cname_utype(union, CName, CName+"->utype").
cname_utype(enum,  CName, CName).

implement_type_unifier_union_ini_join(SubType, Spec, Term, Name, UType) -->
    { term_pcname(Term, Name, PName, CName),
      cname_utype(SubType, CName, UType),
      get_type_name(Term, Func),
      '$current_source_module'(CM)
    },
    implement_type_unifier_ini(PName, CName, Name, Spec),
    ["    term_t __args = PL_new_term_refs(2);",
     "    __rtcheck(PL_put_integer(__args, "+UType+"));",
     "    __rtcheck(PL_unify_term(__args + 1, PL_FUNCTOR_CHARS, \""+Func+"\", 1, PL_TERM, "+PName+"));",
     "    __rtcheck(__rtctype(PL_call_predicate(__"+CM+", PL_Q_NORMAL,",
     "                                          __foreign_generator_idx_call, __args),",
     "                        __args, "+Name+"));"
    ].

implement_type_unifier_union_ini(union, Spec, Term, Name) -->
    implement_type_unifier_union_ini_join(union, Spec, Term, Name, UType),
    ["    switch ("+UType+") {"].
implement_type_unifier_union_ini(enum, Spec, Term, Name) -->
    implement_type_unifier_union_ini_join(enum, Spec, Term, Name, _).
implement_type_unifier_union_ini(cdef,   _, _, _) --> [].
implement_type_unifier_union_ini(struct, _, _, _) --> [].

implement_type_unifier(union_end(SubType, _), _, _) -->
    implement_type_unifier_union_end(SubType).

implement_type_unifier_union_end(union) -->
    ["    default:",
     "        return FALSE;",
     "    };"],
    implement_type_end.
implement_type_unifier_union_end(cdef  ) --> [].
implement_type_unifier_union_end(struct) --> [].
implement_type_unifier_union_end(enum  ) --> implement_type_end.

implement_type_unifier(func_ini(SubType, Spec), Term, Name) -->
    {func_pcname(Name, PName, CName)},
    ( {SubType = union}
    ->{enum_elem(Name, Term, Elem)},
      ["    case "+Elem+":",
       "    {"]
    ; implement_type_unifier_ini(PName, CName, Name, Spec),
      {functor(Term, Func, Arity)},
      ["        __rtcheck(PL_unify_functor("+PName+", PL_new_functor(PL_new_atom(\""+Func+"\"), "+Arity+")));"]
    ).
implement_type_unifier(func_rec(SubType, N, Term, Name), Spec, Arg) -->
    {type_unifiers_elem_names(SubType, Term, Name, Arg, Indent, PName, CNameArg, PNameArg)},
    ( {SubType = union_type}
    ->{c_set_argument(Spec, out, CNameArg, PName, SetArg)}
    ; [Indent+"term_t "+PNameArg+"=PL_new_term_ref();",
       Indent+"__rtcheck(PL_unify_arg("+N+","+PName+","+PNameArg+"));"],
      {c_set_argument(Spec, out, CNameArg, PNameArg, SetArg)}
    ),
    [Indent+SetArg+";"].

type_unifiers_elem_names(SubType, Term, Name, Arg, Indent, PName, CNameArg, PNameArg) :-
    func_pcname(Name, PName, CName),
    ( SubType = union
    ->enum_suff(Term, Suff),
      line_atom(Suff, TName),
      format(atom(CRecordName), "~w.~w", [TName, Arg]),
      format(atom(TNameArg), "~w_~w", [TName, Arg]),
      camel_snake(PRecordName, TNameArg),
      Indent = "        "
    ; CRecordName = Arg,
      camel_snake(PRecordName, Arg),
      ( SubType = union_type
      ->Indent = "        "
      ; Indent = "    "
      )
    ),
    CNameArg = CName+"->"+CRecordName,
    PNameArg = PName+"_"+PRecordName.

implement_type_unifier(func_end(SubType, _), _, _) -->
    ( {SubType = union}
    ->["        break;",
       "    }"]
    ; implement_type_end
    ).
implement_type_unifier(dict_ini(SubType, Name, _, _), Spec, Term) -->
    ( {SubType = union}
    ->{enum_elem(Name, Term, Elem)},
      ["    case "+Elem+":",
       "    {"]
    ; {func_pcname(Term, PName, CName)},
      implement_type_unifier_ini(PName, CName, Name, Spec)
    ),
    ["    term_t __desc=PL_new_term_ref();",
     "    term_t __tail=PL_copy_term_ref(__desc);"].
implement_type_unifier(dict_key_value(Dict, _, N, _), Key, Value) -->
    {key_value_from_dict(Dict, N, Key, Value)}. % Placed in 'dict' order
implement_type_unifier(dict_rec(SubType, _, Term, _N, NameL), Spec, Arg) -->
    {term_pcname(Term, NameL, Name)},
    {type_unifiers_elem_names(SubType, Term, Name, Arg, Indent, _, CNameArg, PNameArg)},
    ( {spec_pointer(Spec)}
    ->with_wrapper(
          Indent+"if("+CNameArg+") {",
          type_unifiers_elem_dict_settle(Spec, Arg, Indent+"    ", CNameArg, PNameArg),
          Indent+"}")
    ; type_unifiers_elem_dict_settle(Spec, Arg, Indent, CNameArg, PNameArg)
    ).

type_unifiers_elem_dict_settle(Spec, Arg, Indent, CNameArg, PNameArg) -->
    [Indent+"term_t "+PNameArg+"=PL_new_term_ref();"],
    [Indent+"FI_put_desc(__tail, \""+Arg+"\", "+PNameArg+");"],
    {c_set_argument(Spec, out, CNameArg, PNameArg, SetArg)},
    [Indent+SetArg+";"].

with_wrapper(Ini, Goal, End) -->
    [Ini],
    call(Goal),
    [End].

implement_type_unifier(dict_end(SubType, _, Tag), _, Term) -->
    {func_pcname(Term, PName, _)},
    ["    __rtcheck(PL_unify_nil(__tail));",
     "    FI_dict_create("+PName+", \""+Tag+"\", __desc);"],
    ( {SubType = union}
    ->["        break;",
       "    }"]
    ; implement_type_end
    ).

spec_pointer(chrs(_)).
spec_pointer(string(_)).
spec_pointer(ptr(_)).
spec_pointer(ntype(_, pointer)).
spec_pointer(list(_)).
spec_pointer(tdef(_, Spec)) :- spec_pointer(Spec).
% spec_pointer(type(_)).

implement_type_unifier_ini(PName, CName, Name, Spec) -->
    { ( \+ref_type(Spec)
      ->DRef = ""
      ; DRef = "*"
      ),
      ctype_suff(Spec, Suff)
    },
    ["int FI_unify_"+Name+"(term_t "+PName+", "+Name+DRef+" const "+CName+Suff+") {"].

apply_name(Name=Value) :-
    camel_snake(Name, Arg),
    ignore(Value=Arg).

apply_dict(Head, Dict) :-
    maplist(apply_name, Dict),
    term_variables(Head, Vars),
    fg_numbervars(Vars, 1, Dict).

fg_numbervars([], _, _).
fg_numbervars([V|Vs], N, Dict) :-
    format(atom(T), "var_~d", [N]),
    succ(N, N1),
    ( memberchk(_=T, Dict)
    ->fg_numbervars([V|Vs], N1, Dict)
    ; V=T,
      fg_numbervars(Vs, N1, Dict)
    ).

bind_type_names(MType, TypeMPropLDictL) :-
    predicate_property(MType, interpreted),
    strip_module(MType, _, Type),
    findall(p(Type, MPropL, Dict),
            bind_tn_clause(MType, MPropL, Dict),
            TypeMPropLDictL).

:- meta_predicate
    bind_tn_clause(0, -, -).

bind_tn_clause(MType, MPropL, Dict) :-
    strip_module(MType, M, Type),
    catch(clause(MType, Body, Ref), _, fail),
    ( clause_property(Ref, file(File)),
      clause_property(Ref, line_count(Line)),
      get_dictionary(Type :- Body, File, Line, M, Dict)
    ->true
    ; Dict = []
    ),
    clause_property(Ref, module(CM)),
    sequence_list(Body, PropL, []),
    maplist(cond_qualify_with(CM), PropL, MPropL).

ds_union_ini(SubType, Name, TPDL1) -->
    { TPDL1 = [TPD1|_],
      TPD1 = t(Type1, _, _, _),
      Type1 =.. Args1,
      append(Left, [_], Args1),
      append(Left, ["NUM"], ArgsN),
      TypeN =.. ArgsN,
      TPDN = t(TypeN, _, _, _),
      append(TPDL1, [TPDN], TPDL),
      !
    },
    foldil(ds_union_ini_1(SubType, Name), 0, TPDL).

ds_union_ini_1(SubType, Name, Idx, t(Type, _, _, _)) -->
    { functor(Type, _, N),
      arg(N, Type, Term),
      ( SubType = enum
      ->format(codes(Codes), "~w", [Term]),
        sanitize_csym(Codes, [], CName, []),
        atom_codes(TName, CName),
        Elem = Name+"_"+TName
      ; enum_elem(Name, Term, Elem)
      )
    },
    ["    "+Elem+" = "+Idx+","].

sanitize_csym([],    _ ) --> [].
sanitize_csym([C|L], S1) -->
    ( {type_char(csym, C)}
    ->S1,
      [C],
      {S = []}
    ; [],
      {S = [0'_|S1]}
    ),
    sanitize_csym(L, S).

declare_struct_union_ini(union, Spec, TPDL, Name) -->
    ["typedef enum {"],
    ds_union_ini(union, Name, TPDL),
    ["} "+Name+"_utype;"],
    {ctype_ini(Spec, Decl)},
    [Decl+" {",
     "  "+Name+"_utype utype;",
     "  union {"
    ].
declare_struct_union_ini(cdef, _, _, _) --> [].
declare_struct_union_ini(struct, _, _, _) --> [].
declare_struct_union_ini(enum, Spec, TPDL, Name) -->
    {ctype_ini(Spec, CIni)},
    [CIni+" {"],
    ds_union_ini(enum, Name, TPDL),
    {ctype_end(Spec, CEnd)},
    ["}"+CEnd+";"].

declare_struct_union_end(union, Spec) -->
    {ctype_end(Spec, CEnd)},
    ["  };",
     "}"+CEnd+";"
    ].
declare_struct_union_end(cdef,   _) --> [].
declare_struct_union_end(struct, _) --> [].
declare_struct_union_end(enum,   _) --> [].

ctype_decl_suff(array(Spec,    Dim)) -->
    !,
    "[", acodes(Dim), "]", ctype_decl_suff(Spec).
ctype_decl_suff(setof(_, _, _, Dim)) -->
    !,
    ( {Dim = 1}
    ->""
    ; "[", acodes(Dim), "]"
    ).
ctype_decl_suff(_) --> "".

ctype_decl_suff(Spec, Suff) :-
    ctype_decl_suff(Spec, Codes, []),
    atom_codes(Suff, Codes).

declare_getset_macros(setof(_, _, _, Dim), Name) -->
    !,
    {c_dim_mult(Dim, Mult)},
    ["#define FI_empty_"+Name+"(__set) FI_empty_set_"+Mult+"(__set, "+Dim+")"],
    ["#define FI_chk_element_"+Name+"(__elem, __set) FI_chk_element_"+Mult+"(__elem, __set)"],
    ["#define FI_add_element_"+Name+"(__elem, __set) FI_add_element_"+Mult+"(__elem, __set)"],
    ["#define FI_del_element_"+Name+"(__elem, __set) FI_del_element_"+Mult+"(__elem, __set)"],
    ["#define FI_xor_element_"+Name+"(__elem, __set) FI_xor_element_"+Mult+"(__elem, __set)"].
declare_getset_macros(_, _) --> "".

declare_struct(union_ini(SubType, Spec, TPDL), _, Name) -->
    declare_struct_union_ini(SubType, Spec, TPDL, Name).
declare_struct(union_end(SubType, Spec), _, _) -->
    declare_struct_union_end(SubType, Spec).
declare_struct(atomic(SubType, Name), Spec, Term) -->
    { ctype_decl(Spec, Decl),
      ctype_decl_suff(Spec, Suff)
    },
    ( {SubType = union}
    ->{get_type_name(Term, TName)},
      ["    "+Decl+" "+TName+Suff+";"]
    ; ["typedef "+Decl+" "+Name+Suff+";"],
      declare_getset_macros(Spec, Name)
    ).
declare_struct(func_ini(SubType, Spec), Term, _) -->
    ( {SubType = union,
       atom(Term)
      }
    ->[]
    ; ( {SubType = union}
      ->{Decl = "  struct"}
      ; {ctype_ini(Spec, Decl)}
      ),
      [Decl+" {"]
    ).
declare_struct(func_end(SubType, Spec), Term, _) -->
    ( {SubType = union,
       atom(Term)
      }
    ->[]
    ; ( {SubType = union}
      ->{enum_suff(Term, TName)},
        ["    } "+TName+";"]
      ; {ctype_end(Spec, Decl)},
        ["}"+Decl+";"]
      )
    ).
declare_struct(func_rec(_, _, _, _), Spec, Name) -->
    { ctype_decl(Spec, Decl),
      ctype_suff(Spec, Suff)
    },
    ["    "+Decl+" "+Name+Suff+";"].
%%
declare_struct(dict_ini(_, _, _, _), Spec, _) -->
    {ctype_ini(Spec, Decl)},
    ["",
     Decl+" {"].
declare_struct(dict_key_value(Dict, Desc, N, _), Key, Value) -->
    {key_value_from_desc(Dict, Desc, N, Key, Value)}.
declare_struct(dict_rec(_, _, _, _, _), Spec, Name) -->
    { ctype_decl(Spec, Decl),
      ctype_suff(Spec, Suff)
    },
    ["    "+Decl+" "+Name+Suff+";"].
declare_struct(dict_end(_, _, _), Spec, _) -->
    {ctype_end(Spec, Decl)},
    ["}"+Decl+";"].

declare_type_union_ini(union, Opt, Name, Spec) -->  declare_type(Opt, Name, Spec).
declare_type_union_ini(enum,  Opt, Name, Spec) -->  declare_type(Opt, Name, Spec).
declare_type_union_ini(cdef,   _, _, _) --> [].
declare_type_union_ini(struct, _, _, _) --> [].

declare_type(Opt, Data, Type, Name) --> declare_type_(Data, Opt, Type, Name).

% declare_type_(atomic(_, _), _, _, _) --> [].
declare_type_(atomic(SubType, Name), Opt, Spec, _) -->
    ( {SubType = union}
    ->[]
    ; declare_type(Opt, Name, Spec)
    ).
declare_type_(union_ini(SubType, Spec, _), Opt, _, Name) -->
    declare_type_union_ini(SubType, Opt, Name, Spec).
declare_type_(union_end(_, _), _, _, _) --> [].
declare_type_(func_ini(SubType, Spec), Opt, _, Name) -->
    ( {SubType = union}
    ->[]
    ; declare_type(Opt, Name, Spec)
    ).
declare_type_(func_end(_, _), _, _, _) --> [].
declare_type_(func_rec(_, _, _, _), _, _, _) --> [].
declare_type_(dict_ini(_, Name, M, _), _, _, _) -->
    ["predicate_t __"+M+"_aux_keyid_index_"+Name+";"].
declare_type_(dict_end(_, _, _), _, _, _) --> [].
declare_type_(dict_rec(_, _, _, _, _), _, _, _) --> [].

declare_type(gett, Name, Spec) -->
    ( {member(Spec, [ntype(_, Type), tdef(Type, _)])}
    ->["#define FI_get_"+Name+"(__root, __term, __value) FI_get_"+Type+"(__root, __term, __value)"]
    ; { ( memberchk(Spec, [array(_, _), setof(_, _, _, _)])
        ->Decl = Name
        ; Decl = Name+"*"
        )
      },
      ["int FI_get_"+Name+"(root_t __root, term_t, "+Decl+");"]
    ).
declare_type(unif, Name, Spec) -->
    ( {member(Spec, [ntype(_, Type), tdef(Type, _)])}
    ->["#define FI_unify_"+Name+"(__term, __value) FI_unify_"+Type+"(__term, __value)"]
    ; { ( \+ref_type(Spec)
        ->DRef = Name
        ; DRef = Name+"*"
        )
      },
      ["int FI_unify_"+Name+"(term_t, "+DRef+" const);"]
    ).

generate_aux_clauses(Module) -->
    findall_tp(Module, type_props, generate_aux_clauses).

% This will create an efficient method to convert keys to indexes in the C side,
% avoiding string comparisons.
generate_aux_clauses(dict_ini(_, Name, _, _), _, _) -->
    !,
    {atom_concat('__aux_keyid_index_', Name, F)},
    [(:- public F/2)].
generate_aux_clauses(dict_key_value(Dict, _, N, _), Key, Value) -->
    !,
    {key_value_from_dict(Dict, N, Key, Value)}.
generate_aux_clauses(dict_rec(_, _, _, N, Name), _, Key) -->
    !,
    { atom_concat('__aux_keyid_index_', Name, F),
      Pred =.. [F, Key, N]
    },
    [(Pred :- true)].
generate_aux_clauses(_, _, _) --> [].

:- multifile
    prolog:message//1.

prolog:message(ignored_type(Name, Arg)) -->
    ["~w->~w ignored"-[Name, Arg]].

prolog:message(failed_binding(TypeComponents)) -->
    ["~w failed"-[TypeComponents]].

:- meta_predicate type_components(+,+,5,+,?,?).

type_components(M, TypePropLDictL, Call, Loc) -->
    foldl(type_components_1(M, Call, Loc), TypePropLDictL).

fix_reserved_name(if, '_if').

get_type_name(Type, Name) :-
    functor(Type, Name1, _),
    ( fix_reserved_name(Name1, Name)
    ->true
    ; Name = Name1
    ).

type_components_1(M, Call, Loc, Type-TypePropLDictL) -->
    { get_type_name(Type, Name),
      ( TypePropLDictL = [t(_, [], _, _)]
      ->SubType = cdef,
        Spec = cdef(Name)
      ; forall(member(t(Type, PropL, _, _), TypePropLDictL), PropL = [])
      ->SubType = enum,
        length(TypePropLDictL, N),
        Spec = enum(Name, N)
      ; Spec = struct(Name),
        ( TypePropLDictL = [_, _|_]
        ->SubType = union,
          ISpec = struct(Name)
        ; SubType = struct,
          ISpec = Spec
        )
      )
    },
    { nb_setval('$recursive', fail),
      nb_setval('$type_name', Name)
    },
    [UnionIni],
    foldl(type_components_one(M, SubType, ISpec, Name, Call, Loc), TypePropLDictL),
    {phrase(call(Call, union_ini(SubType, Spec, TypePropLDictL), Type, Name), UnionIni)},
    call(Call, union_end(SubType, Spec), Type, Name),
    { nb_setval('$recursive', fail),
      nb_setval('$type_name', $$$$)
    }.

type_components_one(M, SubType, TSpec, Name, Call, Loc, t(Type, PropL, _, _)) -->
    { functor(Type, _, Arity),
      arg(Arity, Type, Term)
    },
    ( { PropL = [],
        SubType \= union
      }
    ->[]
    ; { compound(Term)
      ; atom(Term),
        SubType = union
      }
    ->[FuncIni],
      ( {compound(Term)}
      ->findall(Lines,
                ( arg(N, Term, Arg),
                  phrase(( { member(Prop, PropL),
                             match_known_type(Prop, M, Name, Spec, Arg)
                           },
                           call(Call, func_rec(SubType, N, Term, Name), Spec, Arg)
                         ->[]
                         ; {print_message(
                                warning,
                                at_location(Loc, ignored_type(func(Name), Arg)))}
                         ), Lines)
                ))
      ; { atom(Term),
          SubType = union,
          PropL = [Prop]
        }
      ->( { match_known_type(Prop, M, Name, Spec, Arg)
          },
          call(Call, func_rec(union_type, 1, Term, Name), Spec, Arg)
        ->[]
        ; {print_message(
               warning,
               at_location(Loc, ignored_type(func(Name), _)))}
        )
      ; []
      ),
      {phrase(call(Call, func_ini(SubType, TSpec), Term, Name), FuncIni)},
      call(Call, func_end(SubType, TSpec), Term, Name)
    ; { select(dict_t(Desc, Term), PropL, PropL1)
      ; select(dict_t(Tag, Desc, Term), PropL, PropL1)
      ; select(dict_join_t(Tag, Type1, Type2, Term), PropL, PropL1),
        join_dict_types(Type1, M, Type2, M, Tag, Desc)
      ; select(dict_extend_t(Term, Type, Tag, Desc2), PropL, PropL1),
        join_type_desc(M:Type, Tag, Desc2, Desc)
      }
    ->{ is_dict(Desc, Tag)
      ->Dict=Desc
      ; dict_create(Dict, Tag, Desc)
      },
      {ignore(Tag = Name)},
      call(Call, dict_ini(SubType, Name, M, Dict), TSpec, Term),
      findall(Lines,
              phrase(( call(Call, dict_key_value(Dict, Desc, N, Name), Arg, Value),
                       ( { fetch_kv_prop_arg(Arg,  M, Value, PropL1, Prop),
                           match_known_type(Prop, M, Name, Spec, Arg)
                         },
                         call(Call, dict_rec(SubType, M, Term, N, Name), Spec, Arg)
                       ->[]
                       ; {print_message(
                              warning,
                              at_location(Loc, ignored_type(dict(Name), Arg)))}
                       )), Lines)),
      call(Call, dict_end(SubType, M, Tag), TSpec, Term)
    ; { member(Prop, PropL),
        match_known_type(Prop, M, Name, Spec, Term)
      }
    ->call(Call, atomic(SubType, Name), Spec, Term)
    ),
    !.
type_components_one(M, ST, TS, N, G, Loc, T) -->
    {print_message(
         error,
         at_location(
             Loc,
             failed_binding(type_components_one(M, ST, TS, N, G, Loc, T))))}.

key_value_from_dict(Dict, N, Key, Value) :-
    S = s(0),
    Value=Dict.Key,
    S = s(N),
    succ(N, N2),
    nb_setarg(1, S, N2).

key_value_from_list(Desc, N, Key, Value) :-
    nth0(N, Desc, KeyValue),
    key_value(KeyValue, Key, Value).

key_value_from_desc(_, Desc, N, Key, Value) :-
    is_list(Desc), !,
    key_value_from_list(Desc, N, Key, Value).
key_value_from_desc(Dict, _, N, Key, Value) :-
    key_value_from_dict(Dict, N, Key, Value).

fetch_kv_prop_arg(Key, CM, Value, PropL, M:Prop) :-
    ( member(MProp, PropL),
      strip_module(CM:MProp, M, Prop),
      functor(Prop, _, N),
      arg(N, Prop, Key)
    ; extend_args(Value, [Key], Prop),
      M=CM
    ).

declare_intf_head(PCN, Head, "foreign_t __aux_pfa_"+PCN+"_"+N+"(term_t __args)") :-
    max_fli_args(MaxFLIArgs),
    functor(Head, _, N),
    N > MaxFLIArgs,
    !.
declare_intf_head(PCN, Head, "foreign_t "+PCN+"("+TxtL/", "+")") :-
    findall("term_t "+Arg,
            ( compound(Head),
              arg(_, Head, Arg)
            ), TxtL).

declare_foreign_bind(CM) -->
    findall(Line+";",
            ( read_foreign_properties(Head, M, CM, Comp, Call, Succ, Glob, Bind, Type),
              \+ ( Type = foreign(Opts, _),
                   nmember(lang(native), Opts)
                 ),
              declare_impl_head(Type, Head, M, CM, Comp, Call, Succ, Glob, Bind, Line)
            )).

declare_impl_head(foreign(Opts, _), Head, _, _, _, _, _, _, Bind, IntfHead) :-
    nmember(lang(native), Opts),
    !,
    Bind = (FN/_ as _/_ + _),
    declare_intf_head(FN, Head, IntfHead).
declare_impl_head(_, Head, M, CM, Comp, Call, Succ, Glob, (CN/_ as _ + _), Type+FHD) :-
    nonvar(CN),
    ( member(RS, [returns_state(_), type(_)]),
      memberchk(RS, Glob)
    ->Type = "int ",       % int to avoid SWI-Prolog.h dependency at this level
      CHead = Head
    ; member(returns(Var, _), Glob)
    ->bind_argument(Head, M, CM, Comp, Call, Succ, Glob, Var, Spec, Mode),
      ctype_arg_decl(Spec, Mode, Decl),
      Type = Decl+" ",
      Head =.. [F|Args],
      once(select(Var, Args, CArgs)),
      CHead =.. [F|CArgs]
    ; Type = "void ",
      CHead = Head
    ),
    declare_foreign_head(CHead, M, CM, Comp, Call, Succ, Glob, CN, FHD),
    !.

declare_foreign_head(Head, M, CM, Comp, Call, Succ, Glob, CN, CN+"("+ArgL/", "+")") :-
    phrase(( ( {memberchk(memory_root(_), Glob)}
             ->["root_t __root"]
             ; []
             ),
             findall(
                 Line,
                 distinct(
                     Key,
                     ( compound(Head),
                       arg(_, Head, Arg),
                       bind_argument(Head, M, CM, Comp, Call, Succ, Glob, Arg, Spec, Mode),
                       curr_arg_decl(Arg, Spec, Mode, Key, Line)
                     )))
           ), ArgL).

extra_arg_decl(array(Spec, Dim), Key, Line) :-
    ( \+ integer(Dim),
      curr_arg_decl(Dim, ntype(size_t, size_t), in, Key, Line)
    ; extra_arg_decl(Spec, Key, Line)
    ).

curr_arg_decl(_, Spec, Mode, Key, Line) :-
    memberchk(Mode, [in, inout]),
    extra_arg_decl(Spec, Key, Line).
curr_arg_decl(Arg, Spec, Mode, Arg, Decl+" "+Arg+Suff) :-
    ctype_barg_decl(Spec, Mode, Decl),
    ctype_barg_suff(Spec, Suff).

ctype_barg_decl(Spec, Mode, Decl) :-
    ctype_barg_decl(Spec, Mode, Codes, []),
    atom_codes(Decl, Codes).

ctype_barg_suff(Spec, Suff) :-
    ctype_suff(Spec, Codes, []),
    atom_codes(Suff, Codes).

ctype_barg_decl(Spec, Mode) -->
    ctype_arg_decl(Spec, Mode),
    ({ Mode = in,
       \+ ref_type(Spec)
     ; Spec = array(_, _)
     } -> []
    ; "*"
    ),
    ( {Mode = in}  % Ensure const correctness
    ->" const"
    ; []
    ).

ctype_arg_decl(setof(Name, _, _, _), Mode) -->
    !,
    acodes(Name),
    ({member(Mode, [in, out])} -> [] ; "*").
ctype_arg_decl(Spec, Mode) -->
    ctype_decl(Spec),
    ({is_ref(Spec, Mode)} -> [] ; "*").

ctype_arg_decl(Spec, Mode, Decl) :-
    ctype_arg_decl(Spec, Mode, Codes, []),
    atom_codes(Decl, Codes).

ctype_suff(array(Spec, Dim), CDim) --> !, "[", call(CDim, Dim), "]", ctype_suff(Spec, CDim).
ctype_suff(_, _) --> "".

ctype_suff(Spec) --> ctype_suff(Spec, acodes).

is_ref(term,      _) :- !.
is_ref(list(_),   _) :- !.        % Always ref
is_ref(ptr(_),    _) :- !.        % Always ref
is_ref(chrs(_),   _) :- !.
is_ref(string(_), _) :- !.
is_ref(array(_, _), _) :- !.
is_ref(_, in).
is_ref(_, out).
% is_ref(inout, _) :- fail.
% Allow pointer to NULL, the equivalent to free variables in imperative
% languages --EMM

% Types that are passed by reference
ref_type(struct(_)).
ref_type(tdef(_, Spec)) :- ref_type(Spec).

ctype_ini(struct(CType))    --> \+ {nb_current('$recursive', true)}, !, "typedef struct ", acodes(CType).
/* None: we need to use __CType for the typedef struct, in order to let recursive types work */
ctype_ini(struct(CType))    --> "typedef struct __", acodes(CType), " ", acodes(CType), ";\n",
                               "struct __", acodes(CType).
ctype_ini(enum(_, _))       --> "typedef enum".
ctype_ini(cdef(_))          --> "".

ctype_end(struct(CType))    --> \+ {nb_current('$recursive', true)}, !, " ", acodes(CType).
ctype_end(struct(_))        --> "".
ctype_end(enum(CType, _))   --> " ", acodes(CType).
ctype_end(cdef(CType))      --> " ", acodes(CType).

ctype_decl(struct(CType))   --> acodes(CType).
ctype_decl(list(Spec))      --> ctype_decl(Spec), "*".
ctype_decl(array(Spec, _))  --> ctype_decl(Spec).
ctype_decl(ptr(Spec))       --> ctype_decl(Spec), "*".
ctype_decl(chrs(CType))     --> acodes(CType).
ctype_decl(string(CType))   --> acodes(CType).
ctype_decl(enum(CType, _))  --> acodes(CType).
ctype_decl(term)            --> "term_t".
ctype_decl(tdef(CType, _))  --> acodes(CType).
ctype_decl(setof(_, CType, _, _)) --> acodes(CType).
ctype_decl(cdef(CType))     --> acodes(CType).
ctype_decl(ntype(CType, _))         --> acodes(CType).

ctype_ini(Spec, Decl) :- phrase(ctype_ini(Spec), Codes), atom_codes(Decl, Codes).
ctype_end(Spec, Decl) :- phrase(ctype_end(Spec), Codes), atom_codes(Decl, Codes).

ctype_decl(Spec, Decl) :-
    ctype_decl(Spec, Codes, []),
    atom_codes(Decl, Codes).

ctype_suff(Spec, Suff) :-
    ctype_suff(Spec, Codes, []),
    atom_codes(Suff, Codes).

acodes(Atom, List, Tail) :-
    atom_codes(Atom, Codes),
    append(Codes, Tail, List).

cond_qualify_with(CM, MProp1, MProp) :-
    strip_module(CM:MProp1, M, Prop),
    ( CM = M
    ->MProp = Prop
    ; MProp = M:Prop
    ).

:- meta_predicate collect(?,^,-).
collect(Tmpl, Goal, List) :-
    (bagof(Tmpl, Goal, List) *-> true ; List = []).

collect_props(Asr, CM, CompL, CallL, SuccL, GlobL) :-
    maplist(collect_prop(Asr, CM),
            [comp, call, succ, glob],
            [CompL, CallL, SuccL, GlobL]).

collect_prop(Asr, CM, Part, PropL) :-
    collect(MProp,
            (M, Prop, From)^( curr_prop_asr(Part, M:Prop, From, Asr),
                              ( M \= CM
                              ->MProp = M:Prop
                              ; MProp = Prop
                              )
                            ), PropL).

assertion_db(Asr, Head, M, CM, Status, Type, Comp, Call, Succ, Glob, Dict) :-
    asr_head_prop(Asr, HM, Head, Status, Type, Dict, CM, _Loc),
    predicate_property(HM:Head, implementation_module(M)),
    collect_props(Asr, CM, Comp, Call, Succ, Glob).

current_foreign_prop(Head, Module, Context, CompL, CallL, SuccL, GlobL,
                     DictL, FuncName, PredName, BindName, Arity, NKeyProp) :-
    current_foreign_prop(Head, Module, Type, Context, NKeyProp),
    findall(Head-[MComp, MCall, MSucc, MGlob, Dict],
            ( assertion_db(_, Head, Module, CM, check, Type, Comp, Call, Succ, Glob, Dict),
              maplist(maplist(cond_qualify_with(CM)),
                      [ Comp,  Call,  Succ,  Glob],
                      [MComp, MCall, MSucc, MGlob])
            ), KPropLL),
    maplist(=(Head-_), KPropLL),
    pairs_values(KPropLL, PropLL),
    transpose(PropLL, PropTL),
    maplist(append, PropTL, [CompU, CallU, SuccU, GlobU, DictL]),
    maplist(sort, [CompU, CallU, SuccU, GlobU], [CompL, CallL, SuccL, GlobL]),
    functor(Head, PredName, Arity),
    ( member(FGlob, GlobL),
      normalize_ftype(FGlob, foreign(FuncSpecs, _)),
      nmember(FuncSpec, FuncSpecs),
      resolve_name(FuncSpec, PredName, FuncName)
    ->true
    ; true
    ),
    ( ( member(NGlob, GlobL),
        normalize_ftype(NGlob, native(BindSpecs, _)),
        nmember(BindSpec, BindSpecs),
        Name = PredName
      ; nonvar(FuncName),
        BindSpec = prefix(pl_),
        Name = FuncName
      ),
      resolve_name(BindSpec, Name, BindName)
    ->true
    ).

current_foreign_prop(Head, Module, Type, Context, NKeyProp) :-
    asr_head_prop(Asr, HM, Head, check, Type, _, Context, _),
    memberchk(Type, [pred, prop]),
    predicate_property(HM:Head, implementation_module(Module)),
    once(( normalize_ftype(KeyProp, NKeyProp),
           prop_asr(glob, KeyProp, _, Asr)
         )).

resolve_name(BindName,       _,        BindName) :- atom(BindName), !.
resolve_name(name(BindName), _,        BindName).
resolve_name(prefix(Prefix), PredName, BindName) :- atom_concat(Prefix, PredName, BindName).
resolve_name(suffix(Suffix), PredName, BindName) :- atom_concat(PredName, Suffix, BindName).

read_foreign_properties(Head, M, CM, Comp, Call, Succ, Glob, CN/A as PN/BN + CheckMode, T) :-
    current_foreign_prop(Head, M, CM, Comp, Call, Succ, Glob, Dict, CN, PN, BN, A, T),
    ( memberchk(type(_), Glob)
    ->CheckMode=(type)
    ; CheckMode=pred
    ),
    apply_dict(Head, Dict).

generate_foreign_intf(CM) -->
    findall(Lines,
            ( read_foreign_properties(Head, M, CM, Comp, Call, Succ, Glob, Bind, Type),
              declare_impl_head(Type, Head, M, CM, Comp, Call, Succ, Glob, Bind, ImplHead),
              phrase(declare_intf_impl(Type, Head, M, CM, Comp, Call, Succ, Glob, Bind, ImplHead),
                     Lines))).

declare_intf_impl(foreign(Opts, _), Head, M, Module, Comp, Call, Succ, Glob, Bind, ImplHead) -->
    { nmember(lang(Lang), Opts),
      lang(Lang)
    },
    !,
    declare_fimp_impl(Lang, Head, M, Module, Comp, Call, Succ, Glob, Bind, ImplHead).
declare_intf_impl(_, Head, M, Module, Comp, Call, Succ, Glob, Bind, ImplHead) -->
    declare_forg_impl(Head, M, Module, Comp, Call, Succ, Glob, Bind, ImplHead).

declare_fimp_impl(prolog, Head, M, CM, Comp, Call, Succ, Glob, Bind, ImplHead) -->
    { Bind = (_/A as PN/BN + _),
      declare_intf_fimp_head(BN, BNHead)
    },
    [BNHead+"=NULL;"],
    [ImplHead+" {",
     "    term_t "+BN+"_args = PL_new_term_refs("+A+");"],
    ( {memberchk(parent(Var, _), Glob)}
    ->["    __leaf_t *__root = LF_ROOT(LF_PTR(FI_array_ptr("+Var+")));"]
    ; []
    ),
    bind_outs_arguments(Head, M, CM, Comp, Call, Succ, Glob, Bind),
    ["} /* "+PN/A+" */",
     ""].
declare_fimp_impl(native, Head, _, CM, _, _, _, Glob, Bind, ImplHead) -->
    { Bind = (FN/A as _/BN + _),
      declare_intf_fimp_head(BN, BNHead)
    },
    [BNHead+"=NULL;"],
    [ImplHead+" {",
     "    term_t "+BN+"_args = PL_new_term_refs("+A+");"],
    findall(["    __rtcheck(PL_unify_arg("+Idx+","+BN+"_args,"+Arg+"));"], arg(Idx, Head, Arg)),
    bind_call_predicate(CM, Glob, BN),
    ["} /* "+FN/A+" */",
     ""].

bind_call_predicate(CM, Glob, BN) -->
    {CallPred = "PL_call_predicate(__"+CM+", PL_Q_NORMAL, "+BN+", "+BN+"_args)"},
    ( { member(RS, [returns_state(_), type(_)]),
        memberchk(RS, Glob)
      }
    ->["    int __result = "+CallPred+";"]
    ; ["    __rtcwarn("+CallPred+");"]
    ).

declare_forg_impl(Head, M, Module, Comp, Call, Succ, Glob, Bind, _ImplHead) -->
    { max_fli_args(MaxFLIArgs),
      neck,
      Bind = (PI as _/PCN + CheckMode),
      declare_intf_head(PCN, Head, PCNH)
    },
    [PCNH+" {"],
    ( { functor(Head, _, Arity),
        Arity > MaxFLIArgs
      }
    ->findall(["    term_t "+Arg+" = PL_new_term_ref();",
               "    __rtcheck(PL_get_arg("+N+", __args, "+Arg+"));"],
              arg(N, Head, Arg))
    ; []
    ),
    % If is variable then succeed (because is compatible)
    findall("    if(PL_is_variable("+Arg+")) return TRUE;",
            ( CheckMode==(type),
              arg(_, Head, Arg)
            )),
    ["    __mkroot(__root);"],
    bind_arguments(Head, M, Module, Comp, Call, Succ, Glob, Bind, Return),
    ["    __delroot(__root);",
     "    return "+Return+";",
     "} /* "+PI+" */",
     ""].

enum_name(enum(Name, _), Name).

c_get_argument(T, M, C, A, L) :- c_argument(T, get, M, C, A, L).

c_set_argument(T, M, C, A, L) :- c_argument(T, set, M, C, A, L).

c_argument(list(S),     G, M, C, A, L) :- c_argument_rec(G, M, list, S, C, A, L).
c_argument(array(S, D), G, _, C, A, L) :- c_argument_array(G, S, D, C, A, L).
c_argument(ptr(S),      G, M, C, A, L) :- c_argument_rec(G, M, ptr,  S, C, A, L).
c_argument(struct(T),   G, M, C, A, L) :- c_argument_type(G, M, T, C, A, L).
c_argument(enum(T, _),  G, M, C, A, L) :- c_argument_one(G, M, T, C, A, L).
c_argument(cdef(T),     G, M, C, A, L) :- c_argument_one(G, M, T, C, A, L).
c_argument(ntype(_, T), G, M, C, A, L) :- c_argument_one(G, M, T, C, A, L).
c_argument(chrs(_),     G, M, C, A, L) :- c_argument_chrs(G, M, C, A, L).
c_argument(string(_),   G, M, C, A, L) :- c_argument_string(G, M, C, A, L).
c_argument(tdef(T, _),  G, M, C, A, L) :- c_argument_one(G, M, T, C, A, L).
c_argument(setof(_, _, S, D), G, M, C, A, L) :- c_argument_setof(G, M, S, D, C, A, L).
c_argument(term,        G, _, C, A, L) :- c_argument_term(G, C, A, L).

getset_smode(get, in).
getset_smode(set, out).

getset_unify(get, get).
getset_unify(set, unify).

c_argument_rec(GetSet, Mode, Type, Spec, CArg, Arg, L) :-
    Arg_ = Arg+"_",
    c_var_name(Arg_, CArg_),
    getset_smode(GetSet, SMode),
    getset_unify(GetSet, Unify),
    c_argument(Spec, GetSet, SMode, CArg_, Arg_, L1),
    c_argument_rec_2(GetSet, Unify, Mode, Type, CArg, Arg, L1, L).

c_argument_rec_2(get, Unify, Mode, Type, CArg, Arg, L1, "FI_"+Unify+"_"+Mode+"_"+Type+"("+L1+", "+Arg+", "+CArg+")").
c_argument_rec_2(set, Unify, _,    Type, CArg, Arg, L1, "FI_"+Unify+"_"         +Type+"("+L1+", "+Arg+", "+CArg+")").

c_argument_array(GetSet, Spec, Dim, CArg, Arg, "FI_"+Unify+"_array("+L+", "+CDim+", "+Arg+")") :-
    Arg_ = Arg+"_",
    c_var_name(Arg_, CArg_),
    c_dim(Dim, CDim),
    getset_smode(GetSet, SMode),
    getset_unify(GetSet, Unify),
    c_argument(Spec, GetSet, SMode, CArg+"["+CArg_+"]", Arg_, L).

c_argument_type(G, M, T, C, A, L) :-
    getset_unify(G, U),
    c_argument_type_2(M, U, T, C, A, L).

c_argument_type_2(in,    Unify, Type, CArg, Arg, "__rtc_FI_"+Unify+"("+Type+", "+Arg+", "+CArg+")").
c_argument_type_2(out,   Unify, Type, CArg, Arg, "__rtc_FI_"+Unify+"("+Type+", "+Arg+", &"+CArg+")").
c_argument_type_2(inout, Unify, Type, CArg, Arg, "FI_"+Unify+"_inout_type("+Type+", "+Arg+", "+CArg+")").

c_argument_one(G, M, T, C, A, L) :-
    getset_unify(G, U),
    c_argument_one_2(M, U, T, C, A, L).

c_argument_one_2(in,    Unify, Type, CArg, Arg, "__rtc_FI_"+Unify+"("+Type+", "+Arg+", "+CArg+")").
c_argument_one_2(out,   Unify, Type, CArg, Arg, "__rtc_FI_"+Unify+"("+Type+", "+Arg+", "+CArg+")").
c_argument_one_2(inout, Unify, Type, CArg, Arg, "FI_"+Unify+"_inout("+Type+", "+Arg+", "+CArg+")").

c_argument_chrs(G, M, C, A, L) :-
    getset_unify(G, U),
    c_argument_chrs_2(M, U, C, A, L).

c_argument_chrs_2(in,    Unify, CArg, Arg, "__rtc_FI_"+Unify+"(chrs, "+Arg+", "+CArg+")").
c_argument_chrs_2(out,   Unify, CArg, Arg, "__rtc_FI_"+Unify+"(chrs, "+Arg+", "+CArg+")").
c_argument_chrs_2(inout, Unify, CArg, Arg, "FI_"+Unify+"_inout_chrs(" +Arg+", "+CArg+")").

c_argument_string(G, M, C, A, L) :-
    getset_unify(G, U),
    c_argument_string_2(M, U, C, A, L).

c_argument_string_2(in,    Unify, CArg, Arg, "__rtc_FI_"+Unify+"(string, "+Arg+", "+CArg+")").
c_argument_string_2(out,   Unify, CArg, Arg, "__rtc_FI_"+Unify+"(string, "+Arg+", "+CArg+")").
c_argument_string_2(inout, Unify, CArg, Arg, "FI_"+Unify+"_inout_string(" +Arg+", "+CArg+")").

c_argument_setof(GetSet, Mode, Spec, Dim, CArg, Arg, "FI_"+Unify+"_"+Mode+"_setof("+L+", "+Type+", "+Mult+", "+Dim+", "+Name+", "+Arg+", "+CArg+")") :-
    Arg_ = Arg+"_",
    c_var_name(Arg_, CArg_),
    ctype_decl(Spec, Type),
    enum_name(Spec, Name),
    c_dim_mult(Dim, Mult),
    getset_unify(GetSet, Unify),
    getset_smode(GetSet, SMode),
    c_argument(Spec, GetSet, SMode, CArg_, Arg_, L).

c_argument_term(get, C, A, "*"+C+"=PL_copy_term_ref("+A+")").
c_argument_term(set, C, A, "__rtcheck(PL_unify("+A+", "+C+"))").

c_dim_mult(1, single) :- !.
c_dim_mult(_, vector).

c_dim(Dim) --> {integer(Dim)}, !, acodes(Dim).
c_dim(Dim) --> "_c_", acodes(Dim).

c_dim(Dim, CDim) :-
    c_dim(Dim, Codes, []),
    atom_codes(CDim, Codes).

ctype_c_suff(Spec) --> ctype_suff(Spec, c_dim).

ctype_c_suff(Spec, Suff) :-
    ctype_c_suff(Spec, Codes, []),
    atom_codes(Suff, Codes).

extra_var_def(array(Spec, Dim), Head, Arg, Key, Line) :-
    ( \+ integer(Dim),
      curr_bind_line(dim(Arg), Head, Dim, ntype(size_t, size_t), in, Key, Line)
    ; extra_var_def(Spec, Head, Arg+"_"+Dim, Key, Line)
    ).

curr_bind_line(arg, Head, Arg, Spec, Mode, Key, Line) :-
    memberchk(Mode, [in, inout]),
    extra_var_def(Spec, Head, Arg, Key, Line).
curr_bind_line(_, _, Arg, Spec, Mode, dec(Arg), Line) :-
    ctype_arg_decl(Spec, Mode, Decl),
    c_var_name(Arg, CArg),
    ( Spec = term
    ->DN=" "+CArg+"=PL_new_term_ref();"
    ; ctype_c_suff(Spec, CSuff),
      DN=" "+CArg+CSuff+";"
    ),
    Line = "    "+Decl+DN.
curr_bind_line(arg, _, Arg, Spec, Mode, def(Arg), Line) :-
    memberchk(Mode, [in, inout]),
    c_var_name(Arg, CArg1),
    ( member(Spec, [setof(_, _, _, _)])
    ->CArg = CArg1
    ; CArg = "&"+CArg1
    ),
    c_get_argument(Spec, Mode, CArg, Arg, GetArg),
    Line = ["    "+GetArg+";"].
curr_bind_line(dim(Arg), Head, Dim, _, _, def(CDim1), LineL) :-
    \+ arg(_, Head, Dim),
    c_var_name(Dim, CDim1),
    CDim = "&"+CDim1,
    Line = "    FI_get_dim("+Arg+", "+CDim+");",
    ( arg(_, Head, Arg)
    ->LineL = [Line]
    ; Arg = Arg2+"_"+_,
      LineL = ["    term_t "+Arg+"=PL_new_term_ref();",
               "    __rtcheck(PL_get_arg(1, "+Arg2+", "+Arg+"));",
               Line]
    ).

bind_arguments(Head, M, CM, Comp, Call, Succ, Glob, Bind, Return) -->
    ( {compound(Head)}
    ->findall(Line,
              distinct(
                  Key, % This hack allows automatic definition of dimensions on input arrays
                  ( arg(_, Head, Arg),
                    bind_argument(Head, M, CM, Comp, Call, Succ, Glob, Arg, Spec, Mode),
                    curr_bind_line(arg, Head, Arg, Spec, Mode, Key, Line)
                  )
              ))
    ; []
    ),
    {generate_foreign_call(Bind-Head, M, CM, Comp, Call, Succ, Glob, Return, ForeignCall)},
    [ForeignCall],
    ( {compound(Head)}
    ->findall("    "+SetArg+";",
              ( arg(_, Head, Arg),
                bind_argument(Head, M, CM, Comp, Call, Succ, Glob, Arg, Spec, Mode),
                memberchk(Mode, [out, inout]),
                c_var_name(Arg, CArg),
                c_set_argument(Spec, Mode, CArg, Arg, SetArg)
              ))
    ; []
    ).

invert_mode(in, out).
invert_mode(out, in).
invert_mode(inout, inout).

bind_outs_arguments(Head, M, CM, Comp, Call, Succ, Glob, (_ as _/BN +_)) -->
    findall("    "+Decl+Line,
            ( memberchk(returns(Arg, _), Glob)
            ->bind_argument(Head, M, CM, Comp, Call, Succ, Glob, Arg, Spec, Mode),
              memberchk(Mode, [out, inout]),
              ctype_arg_decl(Spec, Mode, Decl),
              ( Spec = term
              ->Line=" "+Arg+"=PL_new_term_ref();"
              ; Line=" "+Arg+";"
              )
            )),
    ( {compound(Head)}
    ->findall(["    term_t "+PArg+"="+BN+"_args + "+Idx1+";",
               "    "+SetArg+";"],
              ( arg(Idx, Head, Arg),
                succ(Idx1, Idx),
                bind_argument(Head, M, CM, Comp, Call, Succ, Glob, Arg, Spec, Mode),
                memberchk(Mode, [in, inout]),
                ( Mode = in,
                  Spec \= struct(_)
                ->CArg = Arg
                ; CArg = "*"+Arg
                ),
                PArg = "_p_"+Arg,
                invert_mode(Mode, InvM),
                c_set_argument(Spec, InvM, CArg, PArg, SetArg)
              ))
    ; []
    ),
    bind_call_predicate(CM, Glob, BN),
    ( {compound(Head)}
    ->findall(Line,
              ( arg(Idx, Head, Arg),
                succ(Idx1, Idx),
                bind_argument(Head, M, CM, Comp, Call, Succ, Glob, Arg, Spec, Mode),
                memberchk(Mode, [out, inout]),
                invert_mode(Mode, InvM),
                ( memberchk(returns(Arg, _), Glob)
                ->CArg = "&"+Arg
                ; CArg = Arg
                ),
                PArg = "_p_"+Arg,
                c_get_argument(Spec, InvM, CArg, PArg, SetArg),
                ( Mode = out,
                  Line = "    term_t "+PArg+"="+BN+"_args + "+Idx1+";"
                ; Line = "    "+SetArg+";"
                )
              )),
      ( { memberchk(returns(Arg, _), Glob)
        ; memberchk(returns_state(_), Glob),
          Arg = "__result"
        }
      ->["    return "+Arg+";"]
      ; []
      )
    ; []
    ).

generate_foreign_call((CN/_A as _ + _)-Head1, M, CM, Comp, Call, Succ, Glob, Return,
                      "    "+HLine+CN+"("+MR+LineL/", "+");") :-
    ( member(RS, [returns_state(_), type(_)]),
      memberchk(RS, Glob)
    ->HLine="foreign_t __result=",
      Head = Head1,
      Return = "__result"
    ; ( member(returns(Var, _), Glob)
      ->c_var_name(Var, CVar),
        HLine=CVar+"=",
        Head1 =.. [F|Args],
        once(select(Var, Args, CArgs)),
        Head =.. [F|CArgs]
      ; Head = Head1,
        HLine=""
      ),
      ( member(no_exception, Glob)
      ->Return = "TRUE"
      ; Return = "!PL_exception(0)"
      )
    ),
    ( memberchk(memory_root(_), Glob)
    ->MR="__root, "
    ; MR=""
    ),
    findall(Line,
            distinct(Key,
                     ( compound(Head),
                       arg(_, Head, Arg),
                       bind_argument(Head, M, CM, Comp, Call, Succ, Glob, Arg, Spec, Mode),
                       curr_arg_call(Arg, Spec, Mode, Key-Line)
                     )
                    ), LineL).

extra_arg_call(array(Spec, Dim), KeyLine) :-
    ( \+ integer(Dim),
      curr_arg_call(Dim, ntype(size_t, size_t), in, KeyLine)
    ; extra_arg_call(Spec, KeyLine)
    ).

curr_arg_call(_, Spec, Mode, KeyLine) :-
    memberchk(Mode, [in, inout]),
    extra_arg_call(Spec, KeyLine).
curr_arg_call(Arg, Spec, Mode, Arg-(Deref+CArg)) :-
    c_var_name(Arg, CArg),
    ( ( Mode = in,
        \+ ref_type(Spec)
      ; Spec = array(_, _)
      )
    ->Deref = ""
    ; Deref = "&"
    ).

:- use_module(library(sequence_list)).
:- use_module(library(prolog_clause), []).

get_dictionary(Term, File, Line, M, Dict) :-
    ( prolog_clause:read_term_at_line(File, Line, M, RawTerm1, _TermPos, Dict),
      ( RawTerm1 \= (_ :- _)
      ->RawTerm = (RawTerm1 :- true)
      ; RawTerm1 = RawTerm
      ),
      subsumes(RawTerm, Term) -> true
    ; Dict = []
    ).

match_known_type(Prop, M, Name, Spec, Arg) :-
    match_type(Prop, M, known, Name, Spec, Arg, _, _),
    ( nb_current('$type_name', TName),
      sub_term(TName, Spec)
    ->nb_setval('$recursive', true)
    ; true
    ).

match_type(M:Prop,       _, K, Name, Spec, Arg) -->
    ( match_type(Prop, M, K, Name, Spec, Arg)
    ->[]
    ).
match_type(dict_t(Desc, A), _, _, Name, Spec, A) -->
    {is_dict(Desc, Tag)},
    !,
    match_known_type_dict(dict_t(Desc, A), Tag, A, Name, Spec).
match_type(dict_t(Tag, Desc, A), _, _, Name, Spec, A) -->
    {dict_create(_, Tag, Desc)},
    !,
    match_known_type_dict(dict_t(Tag, Desc, A), Tag, A, Name, Spec).
match_type(Prop, M, K, N, Spec, A) -->
    match_type_k(K, Prop, M, N, Spec, A).

match_type_k(known, Prop, M, N, Spec, A) --> match_known_type(Prop, M, N, Spec, A).
match_type_k(unknown, _, _, _, _, _) --> [].

match_known_type_type(Type, A, M, N, MSpec, A) -->
    {extend_args(Type, [A], Prop)},
    match_type(Prop, M, known, N, MSpec, A).

match_known_array([], T, A, M, N, MSpec, A) -->
    match_known_type_type(T, A, M, N, MSpec, A).
match_known_array([D|L], T, A, M, N, array(Spec, D), A) -->
    match_known_array(L, T, E, M, N, Spec, E).

match_known_type(atm(A),            _, _, chrs('char*'),           A) --> [].
match_known_type(atom(A),           _, _, chrs('char*'),           A) --> [].
match_known_type(str(A),            _, _, string('char*'),         A) --> [].
match_known_type(string(A),         _, _, string('char*'),         A) --> [].
match_known_type(ptr(A),            _, _, ntype('void*', pointer), A) --> [].
match_known_type(long(A),           _, _, ntype(long, long),       A) --> [].
match_known_type(int(A),            _, _, ntype(int, integer),     A) --> [].
match_known_type(int64(A),          _, _, ntype(int64_t, int64),   A) --> [].
match_known_type(nnegint(A),        _, _, ntype('unsigned int', integer), A) --> [].
match_known_type(integer(A),        _, _, ntype(int, integer),     A) --> [].
match_known_type(character_code(A), _, _, ntype(char, char_code),  A) --> [].
match_known_type(char(A),           _, _, ntype(char, char),       A) --> [].
match_known_type(num(A),            _, _, ntype(double, float),    A) --> [].
match_known_type(size_t(A),         _, _, ntype(size_t, size_t),   A) --> [].
match_known_type(float_t(A),        _, _, ntype(float, float_t),   A) --> [].
match_known_type(number(A),         _, _, ntype(double, float),    A) --> [].
match_known_type(term(A),           _, _, term,                    A) --> [].
match_known_type(type(Type, A),     M, N, MSpec,                   A) -->
    {nonvar(Type)},
    match_known_type_type(Type, A, M, N, MSpec, A).
match_known_type(array(Type, DimL, A), M, N, MSpec, A) -->
    {nonvar(Type)},
    match_known_array(DimL, Type, A, M, N, MSpec, A),
    !.
match_known_type(MType, M, N, MSpec, A) -->
    { member(MType-MSpec, [ptr( Type, A)-ptr( Spec),
                           list(Type, A)-list(Spec)])
    },
    neck,
    {nonvar(Type)},
    match_known_type_type(Type, E, M, N, Spec, E),
    !.
match_known_type(Type, M, _, tdef(Name, Spec), A) -->
    { type_is_tdef(M, Type, Spec, A),
      get_type_name(Type, Name)
    },
    !.
match_known_type(setof(Type, A), M, N, Spec, A) -->
    { nonvar(Type),
      extend_args(Type, [E], Prop)
    },
    match_type(Prop, M, known, N, PSpec, E),
    { ( PSpec = tdef(EName, ESpec)
      ->true
      ; ESpec = PSpec,
        EName = TName
      ),
      ( ESpec = enum(_, C),
        ( ( C =< 16
          ->TName = short
          ; C =< 32
          ->TName = int
          ; C =< 64
          ->TName = long
          )
        ->Dim = 1
        ; current_prolog_flag(address_bits, AB),
          ( AB >= 64
          ->TName = '__int128',
            ElemSize = 128
          ; TName = long,
            ElemSize = AB
          ),
          Dim is (C+ElemSize-1)//ElemSize
        )
      ->Spec = setof(N, EName, ESpec, Dim)
      ; Spec = list(PSpec)
      )
    }.
match_known_type(Type, M, _, Spec, A) -->
    { compound(Type),
      functor(Type, Name, Arity),
      arg(Arity, Type, A),
      functor(Head, Name, Arity),
      % Note: type_props will call match_unknown_type internally,
      % that is why this clause is only valid for match_known_type
      type_props(M, HeadTypePropLDictL, _, _)
    },
    ( { HeadTypePropLDictL = [Head-[t(Head2, [], _, _)]],
        Head == Head2
      }
    ->{Spec=cdef(Name)}
    ; { HeadTypePropLDictL = [Head-TypePropLDictL],
        forall(member(t(Head, PropL, _, _), TypePropLDictL), PropL = [])
      }
    ->{ length(TypePropLDictL, N),
        Spec=enum(Name, N)
      }
    ; { member(_-TypePropLDictL, HeadTypePropLDictL),
        member(t(Head, PropL, _, _), TypePropLDictL),
        PropL \= []
      }
    ->( { PropL = [setof(EType, A)],
          nonvar(EType)
        }
      ->match_known_type(setof(EType, A), M, Name, Spec, A)
      ; {Spec=struct(Name)}
      )
    ),
    !.

match_known_type_dict(Prop, Tag, A, Name, struct(TypeName)) -->
    { atomic_list_concat([Name, '_', Tag], TypeName),
      Type =.. [TypeName, A]
    },
    [Prop=Type].

type_is_tdef(M, Type, Spec, A) :-
    compound(Type),
    functor(Type, TName, Arity),
    arg(Arity, Type, A),
    functor(Head, TName, Arity),
    type_props1(M, Head, _, _, Asr),
    \+ curr_prop_asr(comp, _, _, Asr),
    bind_type_names(M:Head, TypeMPropLDictL),
    TypeMPropLDictL = [p(Head, [Prop], _)],
    \+ member(Prop, [dict_t(_, _), dict_t(_, _, _), setof(_, _)]),
    arg(Arity, Head, A),
    functor(Prop, _, PA),
    arg(PA, Prop, B),
    A==B,
    match_known_type(Prop, M, TName, Spec, A),
    !.

bind_argument(Head, M, CM, CompL, CallL, SuccL, GlobL, Arg, Spec, Mode) :-
    get_type_name(Head, Name),
    ( member(Comp, CompL),
      once(match_known_type(Comp, CM, Name, Spec, Arg1)),
      Arg1 == Arg
    ->true
    ; true
    ),
    ( member(Call, CallL),
      once(match_known_type(Call, CM, Name, Spec, Arg1)),
      Arg1 == Arg
    ->Mode = in
    ; true
    ),
    ( member(Succ, SuccL),
      once(match_known_type(Succ, CM, Name, Spec, Arg1)),
      Arg1 == Arg
    ->Mode = out
    ; true
    ),
    ( memberchk(type(_), GlobL),
      once(match_known_type(Head, M, Name, Spec, Arg1)),
      Arg1 == Arg
    ->Mode = in
    ; true
    ),
    ignore(Mode = inout),
    ignore(Spec = term).

:- public call_idx/2.
:- meta_predicate call_idx(0, -).
call_idx(Call, Idx) :-
    findall(Ref, once(call_ref(Call, Ref)), [Ref]), % avoid unifications
    nth_clause(_, Idx1, Ref),
    succ(Idx, Idx1).

:- public idx_call/2.
:- meta_predicate idx_call(+, 0).
idx_call(Idx1, Call) :-
    succ(Idx1, Idx),
    nth_clause(Call, Idx, Ref),
    clause(Call, _, Ref).
