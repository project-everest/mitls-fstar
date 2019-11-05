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

(* This is working around the inability to define null-accessors for
   the tag of a sum type. It will eventually be provided by EverParse
   *)

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
(* End workaround *)

let field_handshakeType =
  R.FieldReader handshakeType_accessor Parsers.HandshakeType.handshakeType_reader

private
let field_vldata_client_hello =
  R.FieldAccessor
    HSM.handshake_accessor_client_hello
    HSM.handshake_m_client_hello_jumper
    HSM.handshake_m_client_hello_parser32

private
let field_m_client_hello_client_hello =
  R.FieldAccessor
    HSM.handshake_m_client_hello_accessor
    Parsers.ClientHello.clientHello_jumper
    Parsers.ClientHello.clientHello_parser32

let field_clientHello =
  R.field_accessor_comp field_vldata_client_hello field_m_client_hello_client_hello

private
let field_vldata_server_hello =
  R.FieldAccessor
    HSM.handshake_accessor_server_hello
    HSM.handshake_m_server_hello_jumper
    HSM.handshake_m_server_hello_parser32

private
let field_m_server_hello_server_hello =
  R.FieldAccessor
    HSM.handshake_m_server_hello_accessor
    Parsers.ServerHello.serverHello_jumper
    Parsers.ServerHello.serverHello_parser32

let field_serverHello =
  R.field_accessor_comp field_vldata_server_hello field_m_server_hello_server_hello

(* Serializer from high-level value via intermediate-level formatter *)
let serialize =
  R.mk_repr_pos_from_serialize
    HSM.handshake_parser32
    HSM.handshake_serializer32
    HSM.handshake_size32

////////////////////////////////////////////////////////////////////////////////
// Some additional conveniences ... maybe not necessary?
////////////////////////////////////////////////////////////////////////////////

let is_ch (x:t) : GTot bool =
  HSM.tag_of_handshake x = HSTag.Client_hello

let is_sh (x:t) : GTot bool =
  HSM.tag_of_handshake x = HSTag.Server_hello

type ch_ptr = m:ptr{is_ch (R.value m)}
type ch_pos b = m:pos b{is_ch (R.value_pos m)}

type sh_ptr = m:ptr{is_sh (R.value m)}
type sh_pos b = m:pos b{is_sh (R.value_pos m)}

let get_handshakeType = R.read_field field_handshakeType

let get_clientHello = R.get_field field_clientHello

let get_serverHello = R.get_field field_serverHello
