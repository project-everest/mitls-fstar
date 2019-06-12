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
module MITLS.Repr.ClientHello
(* Summary:

   This module encapsulates wire-format representations of
   Parsers.ClientHello messages.

   Its main type, `repr b` is an instance of MITLS.Repr.repr
   instantiated with clientHello_parser
*)
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = MITLS.Repr
module CH = Parsers.ClientHello
open FStar.Integers
open FStar.HyperStack.ST

let t = CH.clientHello

let repr (b:R.const_slice) =
  R.repr_p CH.clientHello b CH.clientHello_parser

let version (#b:R.const_slice) (r:repr b)
  : Stack Parsers.ProtocolVersion.protocolVersion
    (requires R.valid r)
    (ensures fun h0 pv h1 ->
      B.modifies B.loc_none h0 h1 /\
      pv == CH.((R.value r).version))
  = let open R in
    R.reveal_valid();
    let b = R.to_slice b in
    let pos = CH.accessor_clientHello_version b r.start_pos in
    Parsers.ProtocolVersion.protocolVersion_reader b pos
