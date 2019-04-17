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
module HSL.Receive

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module LP = LowParse.Low.Base

module E = FStar.Error

module HSM13 = Parsers.Handshake13
module HSMType = Parsers.HandshakeType
module R = MITLS.Repr
module HSM13R = MITLS.Repr.HSM13

open HSL.Common

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

type inc_st_t = G.erased (bytes & in_progress_flt_t)

noeq
type hsl_state = {
  rgn: Mem.rgn;
  inc_st: (p:B.pointer inc_st_t{
    rgn `region_includes` B.loc_buffer p
  });
}

let region_of st = st.rgn

let parsed_bytes st h = fst (G.reveal (B.deref h st.inc_st))

let in_progress_flt st h = snd (G.reveal (B.deref h st.inc_st))

let invariant s h = B.live h s.inc_st

let footprint s = B.loc_buffer s.inc_st

let frame_hsl_state _ _ _ _ = ()

let create r =
  let inc_st = B.malloc r (G.hide (Seq.empty, F_none)) 1ul in
  { rgn = r; inc_st = inc_st }

assume val parsing_error : TLSError.error
assume val unexpected_flight_error : TLSError.error
assume val bytes_remain_error : TLSError.error

inline_for_extraction
noextract
let parse_hsm13
  (#a:Type) (#k:R.strong_parser_kind)
  (#p:LP.parser k a) (#cl:LP.clens HSM13.handshake13 a)
  (#gacc:LP.gaccessor HSM13.handshake13_parser p cl)
  (tag:HSMType.handshakeType{
    forall (m:HSM13.handshake13).
      (HSM13.tag_of_handshake13 m == tag) <==> cl.LP.clens_cond m})
  (acc:LP.accessor gacc)
  : b:slice -> from:uint_32 ->
    Stack (TLSError.result (option (HSM13R.repr b & uint_32)))
    (requires fun h ->
      B.live h b.LP.base /\
      from <= b.LP.len)
    (ensures fun h0 r h1 ->
      B.modifies B.loc_none h0 h1 /\
      (match r with
       | E.Error _ -> True
       | E.Correct None -> True
       | E.Correct (Some (repr, pos)) ->
         repr.R.start_pos == from /\
         repr.R.end_pos == pos /\
         R.valid repr h1 /\
         cl.LP.clens_cond (R.value repr)))
         
  = fun b from ->
    
    let pos = HSM13.handshake13_validator b from in

    if pos <= LP.validator_max_length then begin
      let parsed_tag = HSMType.handshakeType_reader b from in
      if parsed_tag = tag then
        let r = R.mk b from pos HSM13.handshake13_parser in
        E.Correct (Some (r, pos))
      else E.Error unexpected_flight_error
    end
    else if pos = LP.validator_error_not_enough_data then E.Correct None
    else E.Error parsing_error

let reset_incremental_state (st:hsl_state)
  : Stack unit
    (requires fun h -> B.live h st.inc_st)
    (ensures fun h0 _ h1 ->
      B.modifies (footprint st) h0 h1 /\
      parsed_bytes st h1 == Seq.empty /\
      in_progress_flt st h1 == F_none)
  =  let inc_st = G.hide (Seq.empty, F_none) in
     B.upd st.inc_st 0ul inc_st

let err_or_insufficient_data
  (#a:Type) (#t:Type)
  (parse_result:TLSError.result (option a))
  (in_progress:in_progress_flt_t)
  (st:hsl_state) (b:slice) (from to:uint_32)
  : Stack (TLSError.result (option t))
    (requires fun h ->
      B.live h st.inc_st /\ B.live h b.LP.base /\
      B.loc_disjoint (footprint st) (B.loc_buffer b.LP.base) /\
      from <= to /\ to <= b.LP.len /\
      (E.Error? parse_result \/ parse_result == E.Correct None))
    (ensures  fun h0 r h1 ->
      B.modifies (footprint st) h0 h1 /\
      (match parse_result with
       | E.Error e -> r == E.Error e
       | E.Correct None ->
         r == E.Correct None /\
         parsed_bytes st h1 ==
           Seq.slice (B.as_seq h0 b.LP.base) (v from) (v to) /\
         in_progress_flt st h1 == in_progress))
  = match parse_result with
    | E.Error e -> E.Error e
    | E.Correct None ->
      let inc_st =
        let h = ST.get () in
        let parsed_bytes = LP.bytes_of_slice_from_to h b from to in
        G.hide (parsed_bytes, in_progress)
      in
      B.upd st.inc_st 0ul inc_st;
      E.Correct None

let parse_hsm13_ee
  =  parse_hsm13
      HSM.Encrypted_extensions
      HSM.handshake13_accessor_encrypted_extensions
      
let parse_hsm13_c
  = parse_hsm13
      HSM.Certificate
      HSM.handshake13_accessor_certificate

let parse_hsm13_cv
  = parse_hsm13
      HSM.Certificate_verify
      HSM.handshake13_accessor_certificate_verify

let parse_hsm13_fin
  = parse_hsm13 
      HSM.Finished
      HSM.handshake13_accessor_finished

let parse_hsm13_cr
  = parse_hsm13 
      HSM.Certificate_request
      HSM.handshake13_accessor_certificate_request

let parse_hsm13_eoed
  = parse_hsm13 
      HSM.End_of_early_data
      HSM.handshake13_accessor_end_of_early_data

let parse_hsm13_nst
  = parse_hsm13 
      HSM.New_session_ticket
      HSM.handshake13_accessor_new_session_ticket

let receive_flight13_ee_c_cv_fin st b from to =
  let r = parse_hsm13_ee b from in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r F13_ee_c_cv_fin st b from to
  | E.Correct (Some (ee_repr, c_begin)) ->
    let r = parse_hsm13_c b c_begin in
    match r with
    | E.Error _ | E.Correct None ->
      err_or_insufficient_data r F13_ee_c_cv_fin st b from to
    | E.Correct (Some (c_repr, cv_begin)) ->
      let r = parse_hsm13_cv b cv_begin in
      match r with
      | E.Error _ | E.Correct None ->
        err_or_insufficient_data r F13_ee_c_cv_fin st b from to
      | E.Correct (Some (cv_repr, fin_begin)) ->
        let r = parse_hsm13_fin b fin_begin in
        match r with
        | E.Error _ | E.Correct None ->
          err_or_insufficient_data r F13_ee_c_cv_fin st b from to
        | E.Correct (Some (fin_repr, pos)) ->
          if pos <> to then E.Error bytes_remain_error
          else begin
            reset_incremental_state st;
            E.Correct (Some ({
              ee_msg = ee_repr;
              c_msg = c_repr;
              cv_msg = cv_repr;
              fin_msg = fin_repr
            }))
          end

// let receive_flight13_ee_cr_c_cv_fin st b from to =
//   let r = parse_hsm13_ee b from in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r F13_ee_cr_c_cv_fin st b from to
//   | E.Correct (Some (ee_payload, cr_begin)) ->
//     let r = parse_hsm13_cr b cr_begin in
//     match r with
//     | E.Error _ | E.Correct None ->
//       err_or_insufficient_data r F13_ee_cr_c_cv_fin st b from to
//     | E.Correct (Some (cr_payload, c_begin)) ->
//       let r = parse_hsm13_c b c_begin in
//       match r with
//       | E.Error _ | E.Correct None ->
//         err_or_insufficient_data r F13_ee_cr_c_cv_fin st b from to
//       | E.Correct (Some (c_payload, cv_begin)) ->
//         let r = parse_hsm13_cv b cv_begin in
//         match r with
//         | E.Error _ | E.Correct None ->
//           err_or_insufficient_data r F13_ee_cr_c_cv_fin st b from to
//         | E.Correct (Some (cv_payload, fin_begin)) ->
//           let r = parse_hsm13_fin b fin_begin in
//           match r with
//           | E.Error _ | E.Correct None ->
//             err_or_insufficient_data r F13_ee_cr_c_cv_fin st b from to
//           | E.Correct (Some (fin_payload, pos)) ->
//             if pos <> to then E.Error bytes_remain_error
//             else begin
//               reset_incremental_state st;
//               E.Correct (Some ({
//                 begin_cr = cr_begin;
//                 begin_c = c_begin;
//                 begin_cv = cv_begin;
//                 begin_fin = fin_begin;
//                 ee_msg = ee_payload;
//                 cr_msg = cr_payload;
//                 c_msg = c_payload;
//                 cv_msg = cv_payload;
//                 fin_msg = fin_payload
//               }))
//             end

// let mk_ee_fin
//   (begin_fin:uint_32)
//   (ee_msg:G.erased HSM.handshake13_m13_encrypted_extensions) 
//   (fin_msg:G.erased HSM.handshake13_m13_finished)
//   : flight13_ee_fin
//   = Mkflight13_ee_fin begin_fin ee_msg fin_msg

// let receive_flight13_ee_fin st b from to =
//   let r = parse_hsm13_ee b from in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r F13_ee_fin st b from to
//   | E.Correct (Some (ee_payload, fin_begin)) ->
//     let r = parse_hsm13_fin b fin_begin in
//     match r with
//     | E.Error _ | E.Correct None ->
//       err_or_insufficient_data r F13_ee_fin st b from to
//     | E.Correct (Some (fin_payload, pos)) ->
//       if pos <> to then E.Error bytes_remain_error
//       else begin
//         reset_incremental_state st;
//         E.Correct (Some (mk_ee_fin fin_begin ee_payload fin_payload))
//       end

// let receive_flight13_fin st b from to =
//   let r = parse_hsm13_fin b from in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r F13_fin st b from to
//   | E.Correct (Some (fin_payload, pos)) ->
//     if pos <> to then E.Error bytes_remain_error
//     else begin
//       reset_incremental_state st;
//       E.Correct (Some ({ fin_msg = fin_payload }))
//     end

// let receive_flight13_c_cv_fin st b from to =
//   let r = parse_hsm13_c b from in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r F13_c_cv_fin st b from to
//   | E.Correct (Some (c_payload, cv_begin)) ->
//     let r = parse_hsm13_cv b cv_begin in
//     match r with
//     | E.Error _ | E.Correct None ->
//       err_or_insufficient_data r F13_c_cv_fin st b from to
//     | E.Correct (Some (cv_payload, fin_begin)) ->
//       let r = parse_hsm13_fin b fin_begin in
//       match r with
//       | E.Error _ | E.Correct None ->
//         err_or_insufficient_data r F13_c_cv_fin st b from to
//       | E.Correct (Some (fin_payload, pos)) ->
//         if pos <> to then E.Error bytes_remain_error
//         else begin
//           reset_incremental_state st;
//           E.Correct (Some ({
//             begin_cv = cv_begin;
//             begin_fin = fin_begin;
//             c_msg = c_payload;
//             cv_msg = cv_payload;
//             fin_msg = fin_payload }))
//         end

// let receive_flight13_eoed st b from to =
//   let r = parse_hsm13_eoed b from in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r F13_eoed st b from to
//   | E.Correct (Some (eoed_payload, pos)) ->
//     if pos <> to then E.Error bytes_remain_error
//     else begin
//       reset_incremental_state st;
//       E.Correct (Some ({ eoed_msg = eoed_payload }))
//     end

// let receive_flight13_nst st b from to =
//   let r = parse_hsm13_nst b from in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r F13_nst st b from to
//   | E.Correct (Some (nst_payload, pos)) ->
//     if pos <> to then E.Error bytes_remain_error
//     else begin
//       reset_incremental_state st;
//       E.Correct (Some ({ nst_msg = nst_payload }))
//     end
