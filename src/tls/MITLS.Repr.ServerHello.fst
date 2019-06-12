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
open FStar.Integers
open FStar.HyperStack.ST

let t = SH.serverHello

let repr (b:R.const_slice) =
  R.repr_p SH.serverHello b SH.serverHello_parser

let cipherSuite (#b:R.const_slice) (r:repr b)
  : Stack Parsers.CipherSuite.cipherSuite
    (requires R.valid r)
    (ensures fun h0 cs h1 ->
      B.modifies B.loc_none h0 h1 /\
      cs == SH.((R.value r).cipher_suite))
  = let open R in
    R.reveal_valid();
    let b = R.to_slice b in
    let pos = SH.accessor_serverHello_cipher_suite b r.start_pos in
    Parsers.CipherSuite.cipherSuite_reader b pos
