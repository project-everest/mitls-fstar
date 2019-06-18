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
module B  = LowStar.Buffer
module HS = FStar.HyperStack
module R  = MITLS.Repr

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

type repr (b:R.const_slice) =
  R.repr_p t b HSM13.handshake13_parser

let is_eoed (#b:R.const_slice) (r:repr b) : GTot bool =
  HSM13.M13_end_of_early_data? (R.value r)

let is_ee (#b:R.const_slice) (r:repr b) : GTot bool =
  HSM13.M13_encrypted_extensions? (R.value r)

let is_cr (#b:R.const_slice) (r:repr b) : GTot bool =
  HSM13.M13_certificate_request? (R.value r)

let is_c (#b:R.const_slice) (r:repr b) : GTot bool =
  HSM13.M13_certificate? (R.value r)

let is_cv (#b:R.const_slice) (r:repr b) : GTot bool =
  HSM13.M13_certificate_verify? (R.value r)

let is_fin (#b:R.const_slice) (r:repr b) : GTot bool =
  HSM13.M13_finished? (R.value r)

let is_nst (#b:R.const_slice) (r:repr b) : GTot bool =
  HSM13.M13_new_session_ticket? (R.value r)

let is_kupd (#b:R.const_slice) (r:repr b) : GTot bool =
  HSM13.M13_key_update? (R.value r)

(*
 * Common precondition for functions that return the
 *   reprs for specific instance types
 *)
unfold let repr_pre (#b:R.const_slice) (r:repr b)
  : HS.mem -> Type0
  = fun h -> R.valid r h

(*
 * Common postcondition for functions that return the
 *   reprs for specific instance types
 *)
unfold let repr_post_common
  (#b:R.const_slice)
  (#a:Type) (#k:LP.parser_kind) (#p:LP.parser k a)
  (r:repr b)  //input repr
  : HS.mem -> R.repr_p a b p -> HS.mem -> Type0
  = fun h0 rr h1 ->
    let open R in
    B.(modifies loc_none h0 h1) /\
    valid rr h1 /\  //the returned repr is valid in h1
    r.start_pos <= rr.start_pos /\  //slice indices for the instance repr are contained in the slice indices of r ...
    rr.end_pos <= r.end_pos  //... useful for framing

let get_ee_repr (#b:R.const_slice) (r:repr b{is_ee r})
  : Stack (EERepr.repr b)
    (requires repr_pre r)
    (ensures  fun h0 rr h1 ->
      R.value r == HSM13.M13_encrypted_extensions (R.value rr) /\
      repr_post_common r h0 rr h1)
  = R.reveal_valid ();
    let lp_b = R.to_slice b in
    let pos = HSM13.handshake13_accessor_encrypted_extensions lp_b r.R.start_pos in
    let pos = HSM13.handshake13_m13_encrypted_extensions_accessor lp_b pos in
    let end_pos = Parsers.EncryptedExtensions.encryptedExtensions_jumper lp_b pos in

    R.mk_from_const_slice b pos end_pos Parsers.EncryptedExtensions.encryptedExtensions_parser

let get_c_repr (#b:R.const_slice) (r:repr b{is_c r})
  : Stack (CRepr.repr b)
    (requires repr_pre r)
    (ensures  fun h0 rr h1 ->
      let l = Parsers.Certificate13.certificate13_bytesize (R.value rr) in
      0 <= l /\ l <= 16777215 /\
      R.value r == HSM13.M13_certificate (R.value rr) /\
      repr_post_common r h0 rr h1)
  = R.reveal_valid ();
    let lp_b = R.to_slice b in
    let pos = HSM13.handshake13_accessor_certificate lp_b r.R.start_pos in
    let pos = HSM13.handshake13_m13_certificate_accessor lp_b pos in
    let end_pos = Parsers.Certificate13.certificate13_jumper lp_b pos in

    R.mk_from_const_slice b pos end_pos Parsers.Certificate13.certificate13_parser

let get_cv_repr (#b:R.const_slice) (r:repr b{is_cv r})
  : Stack (CVRepr.repr b)
    (requires repr_pre r)
    (ensures  fun h0 rr h1 ->
      R.value r = HSM13.M13_certificate_verify (R.value rr) /\
      repr_post_common r h0 rr h1)
  = R.reveal_valid ();
    let lp_b = R.to_slice b in
    let pos = HSM13.handshake13_accessor_certificate_verify lp_b r.R.start_pos in
    let pos = HSM13.handshake13_m13_certificate_verify_accessor lp_b pos in
    let end_pos = Parsers.CertificateVerify13.certificateVerify13_jumper lp_b pos in

    R.mk_from_const_slice b pos end_pos Parsers.CertificateVerify13.certificateVerify13_parser

let get_fin_repr (#b:R.const_slice) (r:repr b{is_fin r})
  : Stack (FinRepr.repr b)
    (requires repr_pre r)
    (ensures  fun h0 rr h1 ->
      R.value r == HSM13.M13_finished (R.value rr) /\
      repr_post_common r h0 rr h1)
  = R.reveal_valid ();
    let lp_b = R.to_slice b in
    let pos = HSM13.handshake13_accessor_finished lp_b r.R.start_pos in
    let end_pos = HSM13.handshake13_m13_finished_jumper lp_b pos in

    R.mk_from_const_slice b pos end_pos HSM13.handshake13_m13_finished_parser

let get_cr_repr (#b:R.const_slice) (r:repr b{is_cr r})
  : Stack (CRRepr.repr b)
    (requires repr_pre r)
    (ensures  fun h0 rr h1 ->
      R.value r == HSM13.M13_certificate_request (R.value rr) /\
      repr_post_common r h0 rr h1)
  = R.reveal_valid ();
    let lp_b = R.to_slice b in

    let pos = HSM13.handshake13_accessor_certificate_request lp_b r.R.start_pos in
    let pos = HSM13.handshake13_m13_certificate_request_accessor lp_b pos in
    let end_pos = Parsers.CertificateRequest13.certificateRequest13_jumper lp_b pos in

    R.mk_from_const_slice b pos end_pos Parsers.CertificateRequest13.certificateRequest13_parser

let get_eoed_repr (#b:R.const_slice) (r:repr b{is_eoed r})
  : Stack (EoEDRepr.repr b)
    (requires repr_pre r)
    (ensures  fun h0 rr h1 ->
      R.value r == HSM13.M13_end_of_early_data (R.value rr) /\
      repr_post_common r h0 rr h1)
  = R.reveal_valid ();
    let lp_b = R.to_slice b in

    let pos = HSM13.handshake13_accessor_end_of_early_data lp_b r.R.start_pos in
    let end_pos = HSM13.handshake13_m13_end_of_early_data_jumper lp_b pos in

    R.mk_from_const_slice b pos end_pos HSM13.handshake13_m13_end_of_early_data_parser

let get_nst_repr (#b:R.const_slice) (r:repr b{is_nst r})
  : Stack (NSTRepr.repr b)
    (requires repr_pre r)
    (ensures  fun h0 rr h1 ->
      R.value r == HSM13.M13_new_session_ticket (R.value rr) /\
      repr_post_common r h0 rr h1)
  = R.reveal_valid ();
    let lp_b = R.to_slice b in

    let pos = HSM13.handshake13_accessor_new_session_ticket lp_b r.R.start_pos in
    let pos = HSM13.handshake13_m13_new_session_ticket_accessor lp_b pos in
    let end_pos = Parsers.NewSessionTicket13.newSessionTicket13_jumper lp_b pos in

    R.mk_from_const_slice b pos end_pos Parsers.NewSessionTicket13.newSessionTicket13_parser

(* Serializer from high-level value via intermediate-level formatter *)

let serialize
  (b:LP.slice R.mut_p R.mut_p{ LP.(b.len <= validator_max_length) })
  (from:R.index (R.of_slice b))
  (x: t)
: Stack (option (repr (R.of_slice b)))
    (requires fun h ->
      LP.live_slice h b)
    (ensures fun h0 r h1 ->
      B.modifies (LP.loc_slice_from b from) h0 h1 /\
      begin match r with
      | None ->
        (* not enough space in output slice *)
        Seq.length (LP.serialize HSM13.handshake13_serializer x) > FStar.UInt32.v (b.LP.len - from)
      | Some r ->
        R.valid r h1 /\
        r.R.start_pos == from /\
        R.value r == x
      end
    )
= R.mk_from_serialize b from HSM13.handshake13_serializer32 HSM13.handshake13_size32 x
