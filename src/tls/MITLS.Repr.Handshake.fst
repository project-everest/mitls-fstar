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

   Its main type, `ptr` is an instance of MITLS.Repr.repr_ptr
   instantiated with serverHello_parser
*)
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = LowParse.Repr
module HSM = Parsers.Handshake
module RCH = MITLS.Repr.ClientHello
module RSH = MITLS.Repr.ServerHello
module HSTag = Parsers.HandshakeType
open FStar.Integers
open FStar.HyperStack.ST

let t = HSM.handshake

let ptr = R.repr_ptr_p t HSM.handshake_parser

let pos (b:R.const_slice) = R.repr_pos_p t b HSM.handshake_parser

module LL = LowParse.Low.Base

let handshakeType_clens
  : LL.clens t Parsers.HandshakeType.handshakeType
  = let open LL in
    { clens_cond = (fun _ -> True);
      clens_get = HSM.tag_of_handshake }

let tag_gaccessor_body #k #t (p:LP.parser k t) (sl:LowParse.Bytes.bytes) =
  if Some k.LP.parser_kind_low = k.LP.parser_kind_high
  && k.LP.parser_kind_low <= Seq.length sl
  then 0, k.LP.parser_kind_low
  else 0, 0

let handshakeType_gaccessor
  : LL.gaccessor
             HSM.handshake_parser
             Parsers.HandshakeType.handshakeType_parser
             handshakeType_clens
  = fun (sl:_) ->
    admit();
    tag_gaccessor_body Parsers.HandshakeType.handshakeType_parser sl

let handshakeType_accessor
  : LL.accessor handshakeType_gaccessor
  = fun #rrel #rel sl pos ->
    let h = get () in
    LL.slice_access_eq h handshakeType_gaccessor sl pos;
    pos

let field_handshakeType =
  R.FieldReader handshakeType_accessor Parsers.HandshakeType.handshakeType_reader

let read_handshakeType = R.read_field field_handshakeType

let is_ch (p:ptr) : GTot bool =
  HSM.tag_of_handshake (R.value p) = HSTag.Client_hello

let is_sh (p:ptr) : GTot bool =
  HSM.tag_of_handshake (R.value p) = HSTag.Server_hello

type ch_ptr = m:ptr{is_ch m}
type sh_ptr = m:ptr{is_sh m}

let clientHello (r:ch_ptr)
  : Stack RCH.ptr
    (requires fun h ->
      R.valid r h)
    (ensures fun h0 ch h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid ch h1 /\
      R.value ch == HSM.M_client_hello?._0 (R.value r) /\
      ch `R.sub_ptr` r)
  = let open R in
    let open Parsers.HandshakeType in
    R.reveal_valid();
    let h = get () in
    let s = R.temp_slice_of_repr_ptr r in
    let pos = HSM.handshake_accessor_client_hello s 0ul in
    let pos = HSM.handshake_m_client_hello_accessor s pos in
    let end_pos = Parsers.ClientHello.clientHello_jumper s pos in
    let ch = R.mk s pos end_pos Parsers.ClientHello.clientHello_parser32 in
    R.intro_sub_ptr ch r pos end_pos;
    ch

let serverHello (r:sh_ptr)
  : Stack RSH.ptr
    (requires fun h ->
      R.valid r h)
    (ensures fun h0 sh h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid sh h1 /\
      R.value sh == HSM.M_server_hello?._0 (R.value r) /\
      sh `R.sub_ptr` r)
  = let open R in
    let open Parsers.HandshakeType in
    R.reveal_valid();
    let h = get () in
    let s = R.temp_slice_of_repr_ptr r in
    let pos = HSM.handshake_accessor_server_hello s 0ul in
    let pos = HSM.handshake_m_server_hello_accessor s pos in
    let end_pos = Parsers.ServerHello.serverHello_jumper s pos in
    let sh = R.mk s pos end_pos Parsers.ServerHello.serverHello_parser32 in
    R.intro_sub_ptr sh r pos end_pos;
    sh

(* Serializer from high-level value via intermediate-level formatter *)

let serialize (b:LP.slice R.mut_p R.mut_p{ LP.(b.len <= validator_max_length) })
              (from:R.index (R.of_slice b))
              (x:t)
  : Stack (option (pos (R.of_slice b)))
    (requires fun h ->
      LP.live_slice h b)
    (ensures fun h0 r h1 ->
      B.modifies (LP.loc_slice_from b from) h0 h1 /\
      begin
      match r with
      | None ->
        (* not enough space in output slice *)
        Seq.length (LP.serialize HSM.handshake_serializer x) > FStar.UInt32.v (b.LP.len - from)
      | Some r ->
        R.repr_pos_valid r h1 /\
        r.R.start_pos == from /\
        R.value_pos r == x
      end)
  = R.mk_repr_pos_from_serialize b from HSM.handshake_parser32 HSM.handshake_serializer32 HSM.handshake_size32 x
