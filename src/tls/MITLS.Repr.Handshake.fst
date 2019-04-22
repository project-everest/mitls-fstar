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
module MITLS.Repr.Handshake
(* Summary:

   This module encapsulates wire-format representations of
   Parsers.Handshake messages.

   Its main type, `repr b` is an instance of MITLS.Repr.repr
   instantiated with serverHello_parser
*)
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = MITLS.Repr
module HSM = Parsers.Handshake
module RCH = MITLS.Repr.ClientHello
module RSH = MITLS.Repr.ServerHello
open FStar.Integers
open FStar.HyperStack.ST

let t = HSM.handshake

let repr (b:R.slice) =
  R.repr_p HSM.handshake b HSM.handshake_parser

let handshakeType (#b:R.slice) (r:repr b)
  : Stack Parsers.HandshakeType.handshakeType
    (requires
      R.valid r)
    (ensures fun h0 ht h1 ->
      B.modifies B.loc_none h0 h1 /\
      ht == HSM.tag_of_handshake (R.value r))
  = let open R in
    let open Parsers.HandshakeType in
    R.reveal_valid();
    handshakeType_reader b r.start_pos

let clientHello (#b:R.slice) (r:repr b)
  : Stack (RCH.repr b)
    (requires fun h ->
      R.valid r h /\
      HSM.M_client_hello? (R.value r))
    (ensures fun h0 ch h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid ch h1 /\
      R.value ch == HSM.M_client_hello?._0 (R.value r))
  = let open R in
    let open Parsers.HandshakeType in
    R.reveal_valid();
    let h = get () in
    let pos = HSM.handshake_accessor_client_hello b r.start_pos in
    let pos = HSM.handshake_m_client_hello_accessor b pos in
    let end_pos = Parsers.ClientHello.clientHello_jumper b pos in
    let ch_repr = R.mk b pos end_pos Parsers.ClientHello.clientHello_parser in
    ch_repr

let serverHello (#b:R.slice) (r:repr b)
  : Stack (RSH.repr b)
    (requires fun h ->
      R.valid r h /\
      HSM.M_server_hello? (R.value r))
    (ensures fun h0 sh h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid sh h1 /\
      R.value sh == HSM.M_server_hello?._0 (R.value r))
  = let open R in
    let open Parsers.HandshakeType in
    R.reveal_valid();
    let h = get () in
    let pos = HSM.handshake_accessor_server_hello b r.start_pos in
    let pos = HSM.handshake_m_server_hello_accessor b pos in
    let end_pos = Parsers.ServerHello.serverHello_jumper b pos in
    let sh_repr = R.mk b pos end_pos Parsers.ServerHello.serverHello_parser in
    sh_repr
