/*  Part of Extended Libraries for Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/xlibrary
    Copyright (C): 2020, Process Design Center, Breda, The Netherlands.
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

:- module(libarithex, []).

:- use_module(library(assertions)).
:- use_module(library(typeprops)).
:- use_module(library(plprops)).
:- use_module(library(foreign/foreign_interface)).
:- use_module(library(foreign/foreign_props)).
:- init_expansors.
:- link_foreign_library(m).
:- gen_foreign_library(plbin(libarithex)).

% TBD: make this work:
% :- pred [user:cbrt(  +num, -B:num),
%          user:exp10( +num, -B:num),
%          user:exp2(  +num, -B:num),
%          user:expm1( +num, -B:num),
%          user:log1p( +num, -B:num),
%          user:log2(  +num, -B:num),
%          user:tgamma(+num, -B:num),
%          user:hypot(+num, +num, -B:num)
%         ] is (det, returns(B), foreign).

:- pred [(user:cbrt(  A, B)):(num(A),var(A))=>num(B),
         (user:exp10( A, B)):(num(A),var(A))=>num(B),
         (user:exp2(  A, B)):(num(A),var(A))=>num(B),
         (user:expm1( A, B)):(num(A),var(A))=>num(B),
         (user:log1p( A, B)):(num(A),var(A))=>num(B),
         (user:log2(  A, B)):(num(A),var(A))=>num(B),
         (user:tgamma(A, B)):(num(A),var(A))=>num(B),
         (user:hypot(A, X, B)):(num(A),var(A),num(X),var(X))=>num(B)
        ] is (det, returns(B), foreign).
