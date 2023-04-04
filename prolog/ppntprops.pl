/*  Part of Assertion Reader for SWI-Prolog

    Author:        Edison Mera
    E-mail:        efmera@gmail.com
    WWW:           https://github.com/edisonm/assertions
    Copyright (C): 2023, Process Design Center, Breda, The Netherlands.
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

:- module(ppntprops,
          [ pp_status/1,
            check/1,
            check/2,
            false/1,
            false/2,
            true/1,
            true/2,
            trust/1,
            trust/2
          ]
         ).

:- reexport(library(compound_expand)).
:- use_module(library(neck)).
:- use_module(library(filepos_line)).
:- init_expansors.

/** <module> Program point assertions

    Assertions status that can be used at literal level, for instance:

```
p(A, B) :-
    q(A, B),
    check((int(A),int(B))).
```

    this differs from simply call check/1 in which it will add location
    information fo facilitate debuging.

*/


pp_status(check).
pp_status(trust).
pp_status(true ).
pp_status(false).

:-  pp_status(Status),
    ( Call =.. [Status, 0   ]
    ; Call =.. [Status, 0, +]
    ),
    neck,
    meta_predicate(Call).

Call :-
    pp_status(Status),
    ( Call =.. [Status, _]
    ; Call =.. [Status, _, _]
    ),
    neck.

goal_expansion(Check, TermPos1, CheckLoc, TermPos) :-
    pp_status(Status),
    Check =.. [Status, Pred],
    CheckLoc =.. [Status, Pred, Loc],
    Loc = file(File, Line, Pos, _),
    neck,
    source_location(File, Line1),
    ( var(TermPos1)
    ->Line = Line1,
      Pos = -1,
      TermPos = TermPos1
    ; TermPos1 = term_position(From, To, FFrom, FTo, [APos]),
      integer(From),
      filepos_line(File, From, Line, Pos),
      TermPos  = term_position(From, To, FFrom, FTo, [APos, _])
    ).
