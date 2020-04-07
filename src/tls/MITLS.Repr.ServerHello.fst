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
module MITLS.Repr.ServerHello
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
module SHK = MITLS.Repr.SHKind
module HRK = MITLS.Repr.HRRKind

open FStar.Integers
open FStar.HyperStack.ST

let t = SH.serverHello

let ptr = R.repr_ptr_p t SH.serverHello_parser

let pos (b:R.const_slice) = R.repr_pos_p SH.serverHello b SH.serverHello_parser

let field_is_hrr =
  R.FieldAccessor
    SH.accessor_serverHello_is_hrr
    SH.serverHello_is_hrr_jumper
    SH.serverHello_is_hrr_parser32

let cipherSuite (p:ptr)
  : Stack Parsers.CipherSuite.cipherSuite
    (requires R.valid p)
    (ensures fun h0 cs h1 ->
      B.modifies B.loc_none h0 h1 /\
      cs == (match (R.value p).SH.is_hrr with
             | SHB.ServerHello_is_hrr_true hrr -> HRK.(hrr.cipher_suite)
             | SHB.ServerHello_is_hrr_false sh -> SHK.(sh.SHB.value.cipher_suite)))
  = let open MITLS.Repr.ServerHello_is_hrr in
    let sh_is_hrr = R.get_field field_is_hrr p in
    let b = is_hrr_test sh_is_hrr in
    if b
    then let hrrk = R.get_field is_hrr_true sh_is_hrr in
         R.read_field HRK.field_cipherSuite hrrk
    else let shk = R.get_field is_hrr_false sh_is_hrr in
         R.read_field SHK.field_cipherSuite shk

// The low-level way:
// #push-options "--max_fuel 1 --max_ifuel 1 --z3rlimit_factor 3"
// let cipherSuite (p:ptr)
//   : Stack Parsers.CipherSuite.cipherSuite
//     (requires R.valid p)
//     (ensures fun h0 cs h1 ->
//       B.modifies B.loc_none h0 h1 /\
//       cs == (match (R.value p).SH.is_hrr with
//              | SHB.ServerHello_is_hrr_true hrr -> HRK.(hrr.cipher_suite)
//              | SHB.ServerHello_is_hrr_false sh -> SHK.(sh.SHB.value.cipher_suite)))
//   = let open R in
//     R.reveal_valid();
//     let b = R.temp_slice_of_repr_ptr p in
//     let pos0 = SH.accessor_serverHello_is_hrr b 0ul in
//     if SHB.serverHello_is_hrr_test b pos0 then
//       let pos1 = SH.serverHello_is_hrr_accessor_true b pos0 in
//       let pos2 = HRK.accessor_hRRKind_cipher_suite b pos1 in
//       Parsers.CipherSuite.cipherSuite_reader b pos2
//     else
//       let pos1 = SH.serverHello_is_hrr_accessor_false b pos0 in
//       let pos2 = SHK.accessor_sHKind_cipher_suite b pos1 in
//       Parsers.CipherSuite.cipherSuite_reader b pos2
// #pop-options
