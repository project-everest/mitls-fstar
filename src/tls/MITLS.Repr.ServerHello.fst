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
module R = MITLS.Repr
module SH = Parsers.ServerHello
module SHB = Parsers.ServerHello_is_hrr
module SHK = Parsers.SHKind
module HRK = Parsers.HRRKind

open FStar.Integers
open FStar.HyperStack.ST

let t = SH.serverHello

let repr (b:R.const_slice) =
  R.repr_p SH.serverHello b SH.serverHello_parser32

#push-options "--z3rlimit 16 --max_fuel 1 --max_ifuel 1"
let cipherSuite (#b:R.const_slice) (r:repr b)
  : Stack Parsers.CipherSuite.cipherSuite
    (requires R.valid r)
    (ensures fun h0 cs h1 ->
      B.modifies B.loc_none h0 h1 /\
      cs == (match SH.((R.value r).is_hrr) with
      | SHB.ServerHello_is_hrr_true hrr -> HRK.(hrr.cipher_suite)
      | SHB.ServerHello_is_hrr_false sh -> SHK.(sh.SHB.value.cipher_suite)))
  = let open R in
    R.reveal_valid();
    let b = R.to_slice b in
    let pos0 = SH.accessor_serverHello_is_hrr b r.start_pos in
    if SHB.serverHello_is_hrr_test b pos0 then
      let pos1 = SH.serverHello_is_hrr_accessor_true b pos0 in
      let pos2 = HRK.accessor_hRRKind_cipher_suite b pos1 in
      Parsers.CipherSuite.cipherSuite_reader b pos2
    else
      let pos1 = SH.serverHello_is_hrr_accessor_false b pos0 in
      let pos2 = SHK.accessor_sHKind_cipher_suite b pos1 in
      Parsers.CipherSuite.cipherSuite_reader b pos2
#pop-options
