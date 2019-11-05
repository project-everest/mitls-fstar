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
module MITLS.Repr.Handshake12

(*
 * This module provides a repr for Handshake12 messages
 *   i.e. Parsers.Handshake12
 *
 * It defines predicates for indicating that a repr from
 *   this module is a specific instance (such as CR or SHD)
 *
 * Given such a predicate (and validity of the repr),
 *   clients can obtain reprs for the instance types
 *   (e.g. repr for CR or SHD messages)
 *)

module ST = FStar.HyperStack.ST
module LP = LowParse.Low.Base
module LS = LowParse.SLow.Base
module B  = LowStar.Buffer
module HS = FStar.HyperStack
module R  = LowParse.Repr

open FStar.Integers
open FStar.HyperStack.ST

module HSM12 = Parsers.Handshake12

module HRRepr  = MITLS.Repr.HelloRequest12
module CRepr   = MITLS.Repr.Certificate12
module SKERepr = MITLS.Repr.ServerKeyExchange12
module CRRepr  = MITLS.Repr.CertificateRequest12
module SHDRepr = MITLS.Repr.ServerHelloDone12
module CVRepr  = MITLS.Repr.CertificateVerify12
module CKERepr = MITLS.Repr.ClientKeyExchange12
module NSTRepr = MITLS.Repr.NewSessionTicket12
module FinRepr = MITLS.Repr.Finished12

type t = HSM12.handshake12

type ptr =
  R.repr_ptr_p t HSM12.handshake12_parser

type pos (b:R.const_slice) =
  R.repr_pos_p t b HSM12.handshake12_parser

open Parsers.HandshakeType

let is_hr (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12 (R.value_pos r) = Hello_request

let is_c (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12 (R.value_pos r) = Certificate

let is_ske (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12 (R.value_pos r) = Server_key_exchange

let is_cr (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12 (R.value_pos r) = Certificate_request

let is_shd (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12 (R.value_pos r) = Server_hello_done

let is_cv (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12  (R.value_pos r) = Certificate_verify

let is_cke (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12  (R.value_pos r) = Client_key_exchange

let is_nst (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12 (R.value_pos r) = New_session_ticket

let is_fin (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM12.tag_of_handshake12 (R.value_pos r) = Finished

type hr12_pos (b:R.const_slice) = m:pos b{is_hr m}
type c12_pos (b:R.const_slice) = m:pos b{is_c m}
type ske12_pos (b:R.const_slice) = m:pos b{is_ske m}
type cr12_pos (b:R.const_slice) = m:pos b{is_cr m}
type shd12_pos (b:R.const_slice) = m:pos b{is_shd m}
type cv12_pos (b:R.const_slice) = m:pos b{is_cv m}
type cke12_pos (b:R.const_slice) = m:pos b{is_cke m}
type nst12_pos (b:R.const_slice) = m:pos b{is_nst m}
type fin12_pos (b:R.const_slice) = m:pos b{is_fin m}

unfold
let field_hello_request =
  R.FieldAccessor
    HSM12.handshake12_accessor_hello_request
    HSM12.handshake12_m12_hello_request_jumper
    HSM12.handshake12_m12_hello_request_parser32


unfold
let field_certificate =
  let acc1 =
    R.FieldAccessor
      HSM12.handshake12_accessor_certificate
      HSM12.handshake12_m12_certificate_jumper
      HSM12.handshake12_m12_certificate_parser32
  in
  let acc2 =
    R.FieldAccessor
      HSM12.handshake12_m12_certificate_accessor
      Parsers.Certificate12.certificate12_jumper
      Parsers.Certificate12.certificate12_parser32
  in
  R.field_accessor_comp acc1 acc2

unfold
let field_ske =
  R.FieldAccessor
    HSM12.handshake12_accessor_server_key_exchange
    HSM12.handshake12_m12_server_key_exchange_jumper
    HSM12.handshake12_m12_server_key_exchange_parser32

unfold
let field_cr =
  let acc1 =
    R.FieldAccessor
      HSM12.handshake12_accessor_certificate_request
      HSM12.handshake12_m12_certificate_request_jumper
      HSM12.handshake12_m12_certificate_request_parser32
  in
  let acc2 =
    R.FieldAccessor
      HSM12.handshake12_m12_certificate_request_accessor
      Parsers.CertificateRequest12.certificateRequest12_jumper
      Parsers.CertificateRequest12.certificateRequest12_parser32
  in
  R.field_accessor_comp acc1 acc2


unfold
let field_shd =
  R.FieldAccessor
    HSM12.handshake12_accessor_server_hello_done
    HSM12.handshake12_m12_server_hello_done_jumper
    HSM12.handshake12_m12_server_hello_done_parser32

unfold
let field_cv =
  let acc1 =
    R.FieldAccessor
      HSM12.handshake12_accessor_certificate_verify
      HSM12.handshake12_m12_certificate_verify_jumper
      HSM12.handshake12_m12_certificate_verify_parser32
  in
  let acc2 =
    R.FieldAccessor
      HSM12.handshake12_m12_certificate_verify_accessor
      Parsers.CertificateVerify12.certificateVerify12_jumper
      Parsers.CertificateVerify12.certificateVerify12_parser32
  in
  R.field_accessor_comp acc1 acc2

unfold
let field_cke =
  R.FieldAccessor
    HSM12.handshake12_accessor_client_key_exchange
    HSM12.handshake12_m12_client_key_exchange_jumper
    HSM12.handshake12_m12_client_key_exchange_parser32

unfold
let field_nst =
  let acc1 =
    R.FieldAccessor
      HSM12.handshake12_accessor_new_session_ticket
      HSM12.handshake12_m12_new_session_ticket_jumper
      HSM12.handshake12_m12_new_session_ticket_parser32
  in
  let acc2 =
    R.FieldAccessor
      HSM12.handshake12_m12_new_session_ticket_accessor
      Parsers.NewSessionTicket12.newSessionTicket12_jumper
      Parsers.NewSessionTicket12.newSessionTicket12_parser32
  in
  R.field_accessor_comp acc1 acc2

unfold
let field_fin =
  R.FieldAccessor
    HSM12.handshake12_accessor_finished
    HSM12.handshake12_m12_finished_jumper
    HSM12.handshake12_m12_finished_parser32

(* Serializer from high-level value via intermediate-level formatter *)

let serialize =
  R.mk_repr_pos_from_serialize
        HSM12.handshake12_parser32
        HSM12.handshake12_serializer32
        HSM12.handshake12_size32
