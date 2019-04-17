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
module MITLS.Repr.HSM13

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
module B  = LowStar.Buffer
module HS = FStar.HyperStack
module R  = MITLS.Repr

open FStar.Integers
open FStar.HyperStack.ST

module HSM13 = Parsers.Handshake13

module EERepr  = MITLS.Repr.EncryptedExtensions
module CRepr   = MITLS.Repr.Certificate13
module CVRepr  = MITLS.Repr.CertificateVerify13
module FinRepr = MITLS.Repr.Finished13

type t = HSM13.handshake13

type repr (b:R.slice) =
  R.repr_p t b HSM13.handshake13_parser

let is_eoed (#b:R.slice) (r:repr b) : GTot bool =
  HSM13.M13_end_of_early_data? (R.value r)

let is_ee (#b:R.slice) (r:repr b) : GTot bool =
  HSM13.M13_encrypted_extensions? (R.value r)

let is_cr (#b:R.slice) (r:repr b) : GTot bool =
  HSM13.M13_certificate_request? (R.value r)

let is_c (#b:R.slice) (r:repr b) : GTot bool =
  HSM13.M13_certificate? (R.value r)

let is_cv (#b:R.slice) (r:repr b) : GTot bool =
  HSM13.M13_certificate_verify? (R.value r)

let is_fin (#b:R.slice) (r:repr b) : GTot bool =
  HSM13.M13_finished? (R.value r)

let is_nst (#b:R.slice) (r:repr b) : GTot bool =
  HSM13.M13_new_session_ticket? (R.value r)

let is_kupd (#b:R.slice) (r:repr b) : GTot bool =
  HSM13.M13_key_update? (R.value r)

(*
 * Common precondition for functions that return the
 *   reprs for specific instance types
 *)
unfold let repr_pre (#b:R.slice) (r:repr b)
  : HS.mem -> Type0
  = fun h -> R.valid r h

(*
 * Common postcondition for functions that return the
 *   reprs for specific instance types
 *)
unfold let repr_post
  (#b:R.slice)
  (#a:Type) (#k:LP.parser_kind) (#p:LP.parser k a)
  (r:repr b)  //input repr
  (f:a -> HSM13.handshake13)  //one of the data-constructors for Parsers.Handshake13.handshake13
  : HS.mem -> R.repr_p a b p -> HS.mem -> Type0
  = fun h0 rr h1 ->
    let open R in
    B.(modifies loc_none h0 h1) /\
    valid rr h1 /\  //the returned repr is valid in h1
    value r == f (value rr) /\  //relation between the values of the two reprs
    r.start_pos <= rr.start_pos /\  //slice indices for the instance repr are contained in the slice indices of r ...
    rr.end_pos <= r.end_pos  //... useful for framing

let get_ee_repr (#b:R.slice) (r:repr b{is_ee r})
  : Stack (EERepr.repr b)
    (requires repr_pre r)
    (ensures  repr_post r HSM13.M13_encrypted_extensions)
  = R.reveal_valid ();
    let ee_begin = HSM13.handshake13_accessor_encrypted_extensions b r.R.start_pos in
    let ee_end = HSM13.handshake13_m13_encrypted_extensions_validator b ee_begin in

    R.mk b ee_begin ee_end HSM13.handshake13_m13_encrypted_extensions_parser

let get_c_repr (#b:R.slice) (r:repr b{is_c r})
  : Stack (CRepr.repr b)
    (requires repr_pre r)
    (ensures  repr_post r HSM13.M13_certificate)
  = R.reveal_valid ();
    let c_begin = HSM13.handshake13_accessor_certificate b r.R.start_pos in
    let c_end = HSM13.handshake13_m13_certificate_validator b c_begin in
    
    R.mk b c_begin c_end HSM13.handshake13_m13_certificate_parser

let get_cv_repr (#b:R.slice) (r:repr b{is_cv r})
  : Stack (CVRepr.repr b)
    (requires repr_pre r)
    (ensures  repr_post r HSM13.M13_certificate_verify)
  = R.reveal_valid ();
    let cv_begin = HSM13.handshake13_accessor_certificate_verify b r.R.start_pos in
    let cv_end = HSM13.handshake13_m13_certificate_verify_validator b cv_begin in

    R.mk b cv_begin cv_end HSM13.handshake13_m13_certificate_verify_parser

let get_fin_repr (#b:R.slice) (r:repr b{is_fin r})
  : Stack (FinRepr.repr b)
    (requires repr_pre r)
    (ensures  repr_post r HSM13.M13_finished)
  = R.reveal_valid ();
    let f_begin = HSM13.handshake13_accessor_finished b r.R.start_pos in
    let f_end = HSM13.handshake13_m13_finished_validator b f_begin in
    
    R.mk b f_begin f_end HSM13.handshake13_m13_finished_parser
