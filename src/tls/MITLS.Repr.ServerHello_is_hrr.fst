(*
  Copyright 2015--2019 INRIA and Microsoft Corporation

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

  Authors: T. Ramananandro, A. Rastogi, N. Swamy
*)
module MITLS.Repr.ServerHello_is_hrr
(* Summary:

   This module encapsulates wire-format representations of
   Parsers.ServerHello messages.

   Its main type, `repr b` is an instance of MITLS.Repr.repr
   instantiated with serverHello_parser
*)
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = LowParse.Repr
module SH = Parsers.ServerHello
module SHB = Parsers.ServerHello_is_hrr
module SHK = Parsers.SHKind
module HRK = Parsers.HRRKind

open FStar.Integers
open FStar.HyperStack.ST

let t = SH.serverHello_is_hrr

let ptr = R.repr_ptr_p t SH.serverHello_is_hrr_parser

let pos (b:R.const_buffer) = R.repr_pos_p t b SH.serverHello_is_hrr_parser

let is_hrr_true =
  R.FieldAccessor
    SHB.serverHello_is_hrr_accessor_true
    Parsers.HRRKind.hRRKind_jumper
    Parsers.HRRKind.hRRKind_parser32

let is_hrr_false =
  R.FieldAccessor
    SHB.serverHello_is_hrr_accessor_false
    Parsers.SHKind.sHKind_jumper
    Parsers.SHKind.sHKind_parser32

let is_hrr_test (p:ptr)
  : Stack bool
    (requires fun h ->
      R.valid p h)
    (ensures fun h0 b h1 ->
      B.modifies B.loc_none h0 h1 /\
      b = Parsers.ServerHello_is_hrr.ServerHello_is_hrr_true? (R.value p))
 = R.reveal_valid();
   Parsers.ServerHello_is_hrr.serverHello_is_hrr_test (LowStar.ConstBuffer.cast (R.Ptr?.b p)) 0ul
