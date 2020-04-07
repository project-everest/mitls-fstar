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
module MITLS.Repr.Handshake13

(*
 * This module provides a repr for Handshake13 messages
 *   i.e. Parsers.Handshake13
 *
 * It defines predicates for indicating that a repr from
 *   this module is a specific instance (such as EE or Fin)
 *
 * Given such a predicate (and validity of the repr),
 *   clients can obtain reprs for the instance types
 *   (e.g. repr for EE or Fin messages)
 *)

module ST = FStar.HyperStack.ST
module LP = LowParse.Low.Base
module LS = LowParse.SLow.Base
module B  = LowStar.Buffer
module HS = FStar.HyperStack
module R  = LowParse.Repr

open FStar.Integers
open FStar.HyperStack.ST

module HSM13 = Parsers.Handshake13

module EERepr   = MITLS.Repr.EncryptedExtensions
module CRepr    = MITLS.Repr.Certificate13
module CVRepr   = MITLS.Repr.CertificateVerify13
module FinRepr  = MITLS.Repr.Finished13
module CRRepr   = MITLS.Repr.CertificateRequest13
module EoEDRepr = MITLS.Repr.EndOfEarlyData13
module NSTRepr  = MITLS.Repr.NewSessionTicket13

type t = HSM13.handshake13

type ptr =
  R.repr_ptr_p t HSM13.handshake13_parser

type pos (b:R.const_slice) =
  R.repr_pos_p t b HSM13.handshake13_parser

open Parsers.HandshakeType

let is_eoed (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM13.tag_of_handshake13 (R.value_pos r) = End_of_early_data

let is_ee (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM13.tag_of_handshake13 (R.value_pos r) = Encrypted_extensions

let is_cr (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM13.tag_of_handshake13 (R.value_pos r) = Certificate_request

let is_c (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM13.tag_of_handshake13 (R.value_pos r) = Certificate

let is_cv (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM13.tag_of_handshake13 (R.value_pos r) = Certificate_verify

let is_fin (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM13.tag_of_handshake13 (R.value_pos r) = Finished

let is_nst (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM13.tag_of_handshake13 (R.value_pos r) = New_session_ticket

let is_kupd (#b:R.const_slice) (r:pos b) : GTot bool =
  HSM13.tag_of_handshake13  (R.value_pos r) = Key_update

type ee13_pos (b:R.const_slice) = r:pos b{is_ee r}
type c13_pos (b:R.const_slice) = r:pos b{is_c r}
type cv13_pos (b:R.const_slice) = r:pos b{is_cv r}
type fin13_pos (b:R.const_slice) = r:pos b{is_fin r}
type cr13_pos (b:R.const_slice) = r:pos b{is_cr r}
type eoed13_pos (b:R.const_slice) = r:pos b{is_eoed r}
type nst13_pos (b:R.const_slice) = r:pos b{is_nst r}

unfold noextract
let field_ee =
  [@inline_let] let acc1 =
    R.FieldAccessor
      HSM13.handshake13_accessor_encrypted_extensions
      HSM13.handshake13_m13_encrypted_extensions_jumper
      HSM13.handshake13_m13_encrypted_extensions_parser32
  in
  [@inline_let] let acc2 =
    R.FieldAccessor
      HSM13.handshake13_m13_encrypted_extensions_accessor
      Parsers.EncryptedExtensions.encryptedExtensions_jumper
      Parsers.EncryptedExtensions.encryptedExtensions_parser32
  in
  R.field_accessor_comp acc1 acc2

unfold noextract
let field_certificate =
  [@inline_let] let acc1 =
    R.FieldAccessor
      HSM13.handshake13_accessor_certificate
      HSM13.handshake13_m13_certificate_jumper
      HSM13.handshake13_m13_certificate_parser32
  in
  [@inline_let] let acc2 =
    R.FieldAccessor
      HSM13.handshake13_m13_certificate_accessor
      Parsers.Certificate13.certificate13_jumper
      Parsers.Certificate13.certificate13_parser32
  in
  R.field_accessor_comp acc1 acc2

unfold noextract
let field_cv =
  [@inline_let] let acc1 =
    R.FieldAccessor
      HSM13.handshake13_accessor_certificate_verify
      HSM13.handshake13_m13_certificate_verify_jumper
      HSM13.handshake13_m13_certificate_verify_parser32
  in
  [@inline_let] let acc2 =
    R.FieldAccessor
      HSM13.handshake13_m13_certificate_verify_accessor
      Parsers.CertificateVerify13.certificateVerify13_jumper
      Parsers.CertificateVerify13.certificateVerify13_parser32
  in
  R.field_accessor_comp acc1 acc2

unfold noextract
let field_fin =
  R.FieldAccessor
    HSM13.handshake13_accessor_finished
    HSM13.handshake13_m13_finished_jumper
    HSM13.handshake13_m13_finished_parser32

unfold noextract
let field_cr =
  [@inline_let] let acc1 =
    R.FieldAccessor
      HSM13.handshake13_accessor_certificate_request
      HSM13.handshake13_m13_certificate_request_jumper
      HSM13.handshake13_m13_certificate_request_parser32
  in
  [@inline_let] let acc2 =
    R.FieldAccessor
      HSM13.handshake13_m13_certificate_request_accessor
      Parsers.CertificateRequest13.certificateRequest13_jumper
      Parsers.CertificateRequest13.certificateRequest13_parser32
  in
  R.field_accessor_comp acc1 acc2

unfold noextract
let field_eoed =
  R.FieldAccessor
    HSM13.handshake13_accessor_end_of_early_data
    HSM13.handshake13_m13_end_of_early_data_jumper
    HSM13.handshake13_m13_end_of_early_data_parser32

unfold noextract
let field_nst =
  [@inline_let] let acc1 =
    R.FieldAccessor
      HSM13.handshake13_accessor_new_session_ticket
      HSM13.handshake13_m13_new_session_ticket_jumper
      HSM13.handshake13_m13_new_session_ticket_parser32
  in
  [@inline_let] let acc2 =
    R.FieldAccessor
      HSM13.handshake13_m13_new_session_ticket_accessor
      Parsers.NewSessionTicket13.newSessionTicket13_jumper
      Parsers.NewSessionTicket13.newSessionTicket13_parser32
  in
  R.field_accessor_comp acc1 acc2

(* Serializer from high-level value via intermediate-level formatter *)

let serialize = R.mk_repr_pos_from_serialize HSM13.handshake13_parser32 HSM13.handshake13_serializer32 HSM13.handshake13_size32
