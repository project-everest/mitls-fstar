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


(*** The module is deprecated
     Instead we are trying out a state-passing version of it from TLS.Handshake.ParseFlights ***)


open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

module LP = LowParse.Low.Base

module E = FStar.Error

module HSM13 = Parsers.Handshake13
module HSM12 = Parsers.Handshake12
module HSM   = Parsers.Handshake

module HSMType = Parsers.HandshakeType
module R = MITLS.Repr

module HSM13R = MITLS.Repr.Handshake13
module HSM12R = MITLS.Repr.Handshake12
module HSMR   = MITLS.Repr.Handshake

open HSL.Common

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection -LowParse + LowParse.Slice'"

type inc_st_t = G.erased (bytes & in_progress_flt_t)


/// inc_st is a pointer to erased data

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


/// Main workhorse of parsing messages
///
/// Later we partially apply this function to parse
/// 1.3, 1.2, and CH and SH messages

inline_for_extraction noextract
let parse_common
  (#a1:Type) (#k1:R.strong_parser_kind)
  (#p1:LP.parser k1 a1)
  (validator:LP.validator #k1 #a1 p1)  //a1, p1, etc. are HSM12, HSM13, or HSM
  (tag_fn:a1 -> HSMType.handshakeType{  //this refinment is basically capturing lemma_valid_handshake13_valid_handshakeType kind of lemmas
    forall (b:R.const_slice) (pos:UInt32.t) (h:HS.mem).
      let b = R.to_slice b in
      LP.valid p1 h b pos ==>
      (LP.valid HSMType.handshakeType_parser h b pos /\
       LP.contents HSMType.handshakeType_parser h b pos ==
       tag_fn (LP.contents p1 h b pos))})
  (#a2:Type) (#k2:R.strong_parser_kind)
  (#p2:LP.parser k2 a2) (#cl:LP.clens a1 a2)  //a2, p2, etc. are specific kind of messages such as EE, Fin, etc.
  (#gacc:LP.gaccessor p1 p2 cl)
  (tag:HSMType.handshakeType{
    forall (m:a1).
      (tag_fn m == tag) <==> cl.LP.clens_cond m})
  (acc:LP.accessor gacc)
: b:R.const_slice -> f_begin:uint_32 ->
  Stack (TLSError.result (option (R.repr_p a1 b p1 & uint_32)))
  (requires fun h ->
    R.live h b /\
    f_begin <= b.R.len)
  (ensures fun h0 r h1 ->
    B.modifies B.loc_none h0 h1 /\
    (match r with
     | E.Error _ -> True
     | E.Correct None -> True
     | E.Correct (Some (repr, pos)) ->  //on a successful parse it returns a valid repr with lens condition
       repr.R.start_pos == f_begin /\
       repr.R.end_pos == pos /\
       R.valid repr h1 /\
       cl.LP.clens_cond (R.value repr)))
         
= fun b f_begin ->
  let lp_b = R.to_slice b in
  let pos = validator lp_b f_begin in  //validator gives us the valid postcondition

  if pos <= LP.validator_max_length then begin
    let parsed_tag = HSMType.handshakeType_reader lp_b f_begin in
    if parsed_tag = tag then  //and this dynamic check gives us the lens postcondition
      let r = R.mk_from_const_slice b f_begin pos p1 in
      E.Correct (Some (r, pos))
    else E.Error unexpected_flight_error
  end
  else if pos = LP.validator_error_not_enough_data then E.Correct None
  else E.Error parsing_error


/// Helper function to reset incremental state
/// Will be used when we have successfully parsed the requested flight

private let reset_incremental_state (st:hsl_state)
: Stack unit
  (requires fun h -> B.live h st.inc_st)
  (ensures fun h0 _ h1 ->
    B.modifies (footprint st) h0 h1 /\
    parsed_bytes st h1 == Seq.empty /\
    in_progress_flt st h1 == F_none)
= let inc_st = G.hide (Seq.empty, F_none) in
  B.upd st.inc_st 0ul inc_st


/// Helper function to handle the error case or the insufficient data case
///
/// In the first case, it just returns the error as is
/// In the second case, it saves the incremental state

private let err_or_insufficient_data
  (#a:Type) (#t:Type)
  (parse_result:TLSError.result (option a))
  (in_progress:in_progress_flt_t)
  (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
: Stack (TLSError.result (option t))
  (requires fun h ->
    B.live h st.inc_st /\ R.live h b /\
    B.loc_disjoint (footprint st) (R.loc b) /\
    f_begin <= f_end /\ f_end <= b.R.len /\
    (E.Error? parse_result \/ parse_result == E.Correct None))
  (ensures  fun h0 r h1 ->
    B.modifies (footprint st) h0 h1 /\
    (match parse_result with
     | E.Error e -> r == E.Error e
     | E.Correct None ->
       r == E.Correct None /\
       parsed_bytes st h1 ==
         Seq.slice (R.as_seq h0 b) (v f_begin) (v f_end) /\
       in_progress_flt st h1 == in_progress))
= match parse_result with
  | E.Error e -> E.Error e
  | E.Correct None ->
    let inc_st =
      let h = ST.get () in
      let parsed_bytes = LP.bytes_of_slice_from_to h (R.to_slice b) f_begin f_end in
      G.hide (parsed_bytes, in_progress)
    in
    B.upd st.inc_st 0ul inc_st;
    E.Correct None

/// Helper function to check that pos matches f_end
///   and then either return an error or the flight flt

inline_for_extraction noextract
let check_eq_end_index_and_return
  (#a:Type)
  (st:hsl_state)
  (pos f_end:uint_32)
  (flt:a)
: Stack (TLSError.result (option a))
  (requires fun h -> B.live h st.inc_st)
  (ensures fun h0 res h1 ->
    if pos <> f_end
    then res == E.Error unexpected_end_index_error /\ h0 == h1
    else
      B.modifies (footprint st) h0 h1 /\
      res == E.Correct (Some flt) /\
      parsed_bytes st h1 == Seq.empty /\
      in_progress_flt st h1 == F_none)
= if pos <> f_end then E.Error unexpected_end_index_error
  else begin
    reset_incremental_state st;
    E.Correct (Some flt)
  end


/// Helper function to check that pos is leq f_end
///   and then either return an error or the flight flt

inline_for_extraction noextract
let check_leq_end_index_and_return
  (#a:Type)
  (st:hsl_state)
  (pos f_end:uint_32)
  (flt:a)
: Stack (TLSError.result (option (a & uint_32)))
  (requires fun h -> B.live h st.inc_st)
  (ensures fun h0 res h1 ->
    if pos > f_end
    then res == E.Error unexpected_end_index_error /\ h0 == h1
    else
      B.modifies (footprint st) h0 h1 /\
      res == E.Correct (Some (flt, pos)) /\
      parsed_bytes st h1 == Seq.empty /\
      in_progress_flt st h1 == F_none)
= if pos > f_end then E.Error unexpected_end_index_error
  else begin
    reset_incremental_state st;
    E.Correct (Some (flt, pos))
  end


(*** ClientHello and ServerHello flights ***)


inline_for_extraction noextract
let parse_hsm_ch
= parse_common
    HSM.handshake_validator
    HSM.tag_of_handshake
    HSMType.Client_hello
    HSM.handshake_accessor_client_hello

inline_for_extraction noextract
let parse_hsm_sh
= parse_common
    HSM.handshake_validator
    HSM.tag_of_handshake
    HSMType.Server_hello
    HSM.handshake_accessor_server_hello

let receive_s_Idle st b f_begin f_end
= let flt = F_s_Idle in

  let r = parse_hsm_ch b f_begin in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (ch_repr, pos)) ->
    check_eq_end_index_and_return st pos f_end ({ ch_msg = ch_repr })

let receive_c_wait_ServerHello st b f_begin f_end
= let flt = F_c_wait_ServerHello in

  let r = parse_hsm_sh b f_begin in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (sh_repr, pos)) ->
    check_leq_end_index_and_return st pos f_end ({sh_msg = sh_repr})


(*** 1.3 flights ***)


/// Specialize the parse_common function for Handshake13 messages

inline_for_extraction noextract
let parse_hsm13_ee
= parse_common
    HSM13.handshake13_validator
    HSM13.tag_of_handshake13
    HSMType.Encrypted_extensions
    HSM13.handshake13_accessor_encrypted_extensions
      
inline_for_extraction noextract
let parse_hsm13_c
= parse_common
    HSM13.handshake13_validator
    HSM13.tag_of_handshake13
    HSMType.Certificate
    HSM13.handshake13_accessor_certificate

inline_for_extraction noextract
let parse_hsm13_cv
= parse_common
    HSM13.handshake13_validator
    HSM13.tag_of_handshake13
    HSMType.Certificate_verify
    HSM13.handshake13_accessor_certificate_verify

inline_for_extraction noextract
let parse_hsm13_fin
= parse_common
    HSM13.handshake13_validator
    HSM13.tag_of_handshake13
    HSMType.Finished
    HSM13.handshake13_accessor_finished

inline_for_extraction noextract
let parse_hsm13_cr
= parse_common
    HSM13.handshake13_validator
    HSM13.tag_of_handshake13
    HSMType.Certificate_request
    HSM13.handshake13_accessor_certificate_request

inline_for_extraction noextract
let parse_hsm13_eoed
= parse_common
    HSM13.handshake13_validator
    HSM13.tag_of_handshake13
    HSMType.End_of_early_data
    HSM13.handshake13_accessor_end_of_early_data

inline_for_extraction noextract
let parse_hsm13_nst
= parse_common
    HSM13.handshake13_validator
    HSM13.tag_of_handshake13
    HSMType.New_session_ticket
    HSM13.handshake13_accessor_new_session_ticket


/// Helper function to parse c13 and cv13 that appear together in a flight

private let parse_hsm13_c_cv
  (b:R.const_slice) (f_begin:uint_32)
: Stack (TLSError.result (option (HSM13R.c13_repr b & HSM13R.cv13_repr b & uint_32)))
  (requires fun h ->
    R.live h b /\
    f_begin <= b.R.len)
  (ensures fun h0 r h1 ->
    B.modifies B.loc_none h0 h1 /\
    (match r with
     | E.Error _ -> True
     | E.Correct None -> True
     | E.Correct (Some (c13, cv13, pos)) ->
       c13.R.start_pos == f_begin /\
       c13.R.end_pos == cv13.R.start_pos /\
       cv13.R.end_pos == pos /\
       R.valid c13 h1 /\
       R.valid cv13 h1))
= let r = parse_hsm13_c b f_begin in
  match r with
  | E.Error e -> E.Error e
  | E.Correct None -> E.Correct None
  | E.Correct (Some (c_repr, c_end)) ->
    let r = parse_hsm13_cv b c_end in
    match r with
    | E.Error e -> E.Error e
    | E.Correct None -> E.Correct None
    | E.Correct (Some (cv_repr, cv_end)) ->
      E.Correct (Some (c_repr, cv_repr, cv_end))

#set-options "--z3rlimit 50"
let receive_c13_wait_Finished1 st b f_begin f_end
= let flt = F_c13_wait_Finished1 in

  let r = parse_hsm13_ee b f_begin in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (ee_repr, ee_end)) ->
    let r = parse_hsm13_cr b ee_end in
    match r with
    | E.Correct None ->
      err_or_insufficient_data r flt st b f_begin f_end
    | _ ->
     let cr_repr, c_cv_begin =
       match r with
       | E.Error _ -> None, ee_end
       | E.Correct (Some (cr_repr, cr_end)) ->
         Some cr_repr, cr_end
     in
     let r = parse_hsm13_c_cv b c_cv_begin in
     match r with
     | E.Correct None ->
       err_or_insufficient_data r flt st b f_begin f_end
     | _ ->
       let c_cv_repr, fin_begin =
         match r with
         | E.Error _ -> None, c_cv_begin
         | E.Correct (Some (c_repr, cv_repr, c_cv_end)) ->
           Some (c_repr, cv_repr), c_cv_end
       in
       let r = parse_hsm13_fin b fin_begin in
       match r with
       | E.Error _ | E.Correct None ->
         err_or_insufficient_data r flt st b f_begin f_end
       | E.Correct (Some (fin_repr, fin_end)) ->
         check_eq_end_index_and_return st fin_end f_end ({
           ee_msg = ee_repr;
           cr_msg = cr_repr;
           c_cv_msg = c_cv_repr;
           fin_msg = fin_repr
         })

let receive_s13_wait_Finished2 st b f_begin f_end
= let flt = F_s13_wait_Finished2 in

  let r = parse_hsm13_c_cv b f_begin in
  match r with
  | E.Correct None -> err_or_insufficient_data r flt st b f_begin f_end
  | _ ->
    let c_cv_repr, fin_begin =
      match r with
      | E.Error _ -> None, f_begin
      | E.Correct (Some (c_repr, cv_repr, c_cv_end)) ->
        Some (c_repr, cv_repr), c_cv_end
    in
    let r = parse_hsm13_fin b fin_begin in
    match r with
    | E.Error _ | E.Correct None -> err_or_insufficient_data r flt st b f_begin f_end
    | E.Correct (Some (fin_repr, fin_end)) ->
      check_eq_end_index_and_return st fin_end f_end ({
        c_cv_msg = c_cv_repr;
        fin_msg = fin_repr
      })

let receive_s13_wait_EOED st b f_begin f_end
= let flt = F_s13_wait_EOED in

  let r = parse_hsm13_eoed b f_begin in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (eoed_repr, pos)) ->
    check_eq_end_index_and_return st pos f_end ({ eoed_msg = eoed_repr })

let receive_c13_Complete st b f_begin f_end
= let flt = F_c13_Complete in

  let r = parse_hsm13_nst b f_begin in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (nst_repr, pos)) ->
    check_eq_end_index_and_return st pos f_end ({ nst_msg = nst_repr })


(*** 1.2 flights ***)


inline_for_extraction noextract
let parse_hsm12_c
= parse_common
    HSM12.handshake12_validator
    HSM12.tag_of_handshake12
    HSMType.Certificate
    HSM12.handshake12_accessor_certificate

inline_for_extraction noextract
let parse_hsm12_ske
= parse_common
    HSM12.handshake12_validator
    HSM12.tag_of_handshake12
    HSMType.Server_key_exchange
    HSM12.handshake12_accessor_server_key_exchange

inline_for_extraction noextract
let parse_hsm12_shd
= parse_common
    HSM12.handshake12_validator
    HSM12.tag_of_handshake12
    HSMType.Server_hello_done
    HSM12.handshake12_accessor_server_hello_done

inline_for_extraction noextract
let parse_hsm12_cr
= parse_common
    HSM12.handshake12_validator
    HSM12.tag_of_handshake12
    HSMType.Certificate_request
    HSM12.handshake12_accessor_certificate_request

inline_for_extraction noextract
let parse_hsm12_fin
= parse_common
    HSM12.handshake12_validator
    HSM12.tag_of_handshake12
    HSMType.Finished
    HSM12.handshake12_accessor_finished

inline_for_extraction noextract
let parse_hsm12_nst
= parse_common
    HSM12.handshake12_validator
    HSM12.tag_of_handshake12
    HSMType.New_session_ticket
    HSM12.handshake12_accessor_new_session_ticket

inline_for_extraction noextract
let parse_hsm12_cke
= parse_common
    HSM12.handshake12_validator
    HSM12.tag_of_handshake12
    HSMType.Client_key_exchange
    HSM12.handshake12_accessor_client_key_exchange


let receive_c12_wait_ServerHelloDone st b f_begin f_end
= let flt = F_c12_wait_ServerHelloDone in

  let r = parse_hsm12_c b f_begin in
  match r with
  | E.Error _ | E.Correct None -> err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (c_repr, c_end)) ->
    let r = parse_hsm12_ske b c_end in
    match r with
    | E.Error _ | E.Correct None -> err_or_insufficient_data r flt st b f_begin f_end
    | E.Correct (Some (ske_repr, ske_end)) ->
      let r = parse_hsm12_cr b ske_end in
      match r with
      | E.Correct None -> err_or_insufficient_data r flt st b f_begin f_end
      | _ ->
        let cr_repr, shd_begin =
          match r with
          | E.Error _ -> None, ske_end
          | E.Correct (Some (cr_repr, cr_end)) -> Some cr_repr, cr_end
        in
        let r = parse_hsm12_shd b shd_begin in
        match r with
        | E.Error _ | E.Correct None ->
          err_or_insufficient_data r flt st b f_begin f_end
        | E.Correct (Some (shd_repr, pos)) ->
          check_eq_end_index_and_return st pos f_end ({
            c_msg = c_repr;
            ske_msg = ske_repr;
            cr_msg = cr_repr;
            shd_msg = shd_repr
          })

let receive_cs12_wait_Finished st b f_begin f_end
= let flt = F_cs12_wait_Finished in

  let r = parse_hsm12_fin b f_begin in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (fin_repr, pos)) ->
    check_eq_end_index_and_return st pos f_end ({ fin_msg = fin_repr })

let receive_c12_wait_NST st b f_begin f_end
= let flt = F_c12_wait_NST in

  let r = parse_hsm12_nst b f_begin in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (nst_repr, pos)) ->
    check_eq_end_index_and_return st pos f_end ({ nst_msg = nst_repr })

let receive_s12_wait_CCS1 st b f_begin f_end
= let flt = F_s12_wait_CCS1 in

  let r = parse_hsm12_cke b f_begin in
  match r with
  | E.Error _ | E.Correct None ->
    err_or_insufficient_data r flt st b f_begin f_end
  | E.Correct (Some (cke_repr, pos)) ->
    check_eq_end_index_and_return st pos f_end ({ cke_msg = cke_repr })
