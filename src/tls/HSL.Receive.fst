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

noeq
type state = {
  parsed_bytes : G.erased bytes;
  in_progress : G.erased in_progress_flt_t;
  buf : R.const_slice;
  f_begin : uint_32;
  f_end : i:uint_32{
    f_begin <= i /\
    i <= buf.R.len
  };
  from_idx : i:uint_32{i <= buf.R.len}
}

let parsed_bytes st = G.reveal st.parsed_bytes

let in_progress_flt st = G.reveal st.in_progress

let reset () = {
  parsed_bytes = G.hide Seq.empty;
  in_progress = G.hide F_none;
  buf = R.of_slice (LP.make_slice B.null 0ul);
  f_begin = 0ul;
  f_end = 0ul;
  from_idx = 0ul
}

let create () = reset ()



(*** Layered effect definition ***)


type pre_t = state -> HS.mem -> Type0
type post_t (a:Type) = TLSError.result (option a & state) -> HS.mem -> Type0
type wp_t (a:Type) = post_t a -> pre_t


assume WP_monotonic_pure:
  (forall (a:Type) (wp:pure_wp a).
     (forall (p q:pure_post a).
        (forall (x:a). p x ==> q x) ==>
        (wp p ==> wp q)))

assume WP_monotonic_stexn:
  (forall (a:Type) (wp:wp_t a).
     (forall (p q:post_t a).
        (forall (x:TLSError.result (option a & state)) (h:HS.mem). p x h ==> q x h) ==>
        (forall (st:state) (h:HS.mem). wp p st h ==> wp q st h)))



type repr (a:Type) (wp:wp_t a) =
  st:state -> STATE (TLSError.result (option a & state)) (fun p h -> wp p st h)

inline_for_extraction
let return (a:Type) (x:a)
: repr a (fun p st h -> p (E.Correct (Some x, st)) h)
= fun st -> E.Correct (Some x, st)

inline_for_extraction
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
: repr b
  (fun p st h ->
    wp_f (fun r h1 ->
      match r with
      | E.Error e -> p (E.Error e) h1
      | E.Correct (None, st1) -> p (E.Correct (None, st1)) h1
      | E.Correct (Some x, st1) -> (wp_g x) p st1 h1) st h)
= fun st ->
  let r = f st in
  match r with
  | E.Error e -> E.Error e
  | E.Correct (None, st1) -> E.Correct (None, st1)
  | E.Correct (Some x, st1) -> (g x) st1

let stronger (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f)
: Pure (repr a wp_g)
  (requires forall p st h. wp_g p st h ==> wp_f p st h)
  (ensures fun _ -> True)
= f

let conjunction (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f) (g:repr a wp_g)
  (p:Type0)
: Type
= repr a
  (fun post st h ->
   (p ==> wp_f post st h) /\
   ((~ p) ==> wp_g post st h))


reifiable reflectable
layered_effect {
  STEXN : a:Type -> wp_t a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  stronger = stronger;
  conjunction = conjunction
}


inline_for_extraction
let lift_div_stexn (a:Type) (wp:pure_wp a) (f:unit -> DIV a wp)
: repr a (fun p st h -> wp (fun x -> p (E.Correct (Some x, st)) h))
= fun st -> E.Correct (Some (f ()), st)

sub_effect DIV ~> STEXN = lift_div_stexn


effect StExn (a:Type) (pre:state -> HS.mem -> Type0) (post:state -> HS.mem -> TLSError.result (option a & state) -> HS.mem -> Type0)
= STEXN a (fun p st h -> pre st h /\ (forall x h1. (equal_stack_domains h h1 /\ post st h x h1) ==> p x h1))


(*** End layered effect definition ***)


private let err_or_insufficient_data
  (#a:Type) (#t:Type)
  (parse_result:TLSError.result (option a))
  (st:state)
: Stack (TLSError.result (option t & state))
  (requires fun h ->
    R.live h st.buf /\
    (match parse_result with
     | E.Error _ -> True
     | E.Correct opt -> opt == None))
  (ensures  fun h0 r h1 ->
    h0 == h1 /\
    (match parse_result with
     | E.Error e -> r == E.Error e
     | E.Correct None ->
       (match r with
        | E.Correct (None, rst) ->
          parsed_bytes rst ==
            Seq.slice (R.as_seq h0 st.buf) (v st.f_begin) (v st.f_end) /\
          in_progress_flt rst == in_progress_flt st
        | _ -> False)))
= match parse_result with
  | E.Error e -> E.Error e
  | E.Correct None ->
    let parsed_bytes =
      let h = ST.get () in
      G.hide (LP.bytes_of_slice_from_to h (R.to_slice st.buf) st.f_begin st.f_end)
    in
    E.Correct (None, ({ st with parsed_bytes = parsed_bytes }))


inline_for_extraction noextract
let check_eq_end_index_and_return
  (#a:Type)
  (pos f_end:uint_32)
  (flt:a)
: TLSError.result (option a & state)
= if pos <> f_end then E.Error unexpected_end_index_error
  else E.Correct (Some flt, reset ())

inline_for_extraction noextract
let check_leq_end_index_and_return
  (#a:Type)
  (pos f_end:uint_32)
  (flt:a)
: TLSError.result (option (a & uint_32) & state)
= if pos > f_end then E.Error unexpected_end_index_error
  else E.Correct (Some (flt, pos), reset ())


inline_for_extraction noextract
let parse_common_st
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
: b:R.const_slice ->
  st:state ->
  ST (TLSError.result ((option (R.repr_p a1 b p1)) & state))
  (requires fun h -> b == st.buf /\ R.live h b)
  (ensures fun h0 r h1 ->
    B.modifies B.loc_none h0 h1 /\
    (match r with
     | E.Error _ -> True
     | E.Correct (None, rst) ->
       parsed_bytes rst ==
         Seq.slice (R.as_seq h0 b) (v st.f_begin) (v st.f_end) /\
       in_progress_flt rst == in_progress_flt st
     | E.Correct (Some repr, rst) ->  //on a successful parse it returns a valid repr with lens condition
       repr.R.start_pos == st.from_idx /\
       R.valid repr h1 /\
       cl.LP.clens_cond (R.value repr) /\
       rst == ({ st with from_idx = repr.R.end_pos })))
         
= fun b st ->
  let lp_b = R.to_slice b in
  let pos = validator lp_b st.from_idx in  //validator gives us the valid postcondition

  if pos <= LP.validator_max_length then begin
    let parsed_tag = HSMType.handshakeType_reader lp_b st.from_idx in
    if parsed_tag = tag then  //and this dynamic check gives us the lens postcondition
      let r = R.mk_from_const_slice b st.from_idx pos p1 in
      E.Correct (Some r, { st with from_idx = pos })
    else E.Error unexpected_flight_error
  end
  else if pos = LP.validator_error_not_enough_data
  then err_or_insufficient_data #unit #_ (E.Correct None) st
  else E.Error parsing_error

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
  (b:R.const_slice)
: StExn (R.repr_p a1 b p1)
  (requires fun st h -> st.buf == b /\ R.live h b)
  (ensures fun st h0 r h1 ->
    st.buf == b /\
    B.modifies B.loc_none h0 h1 /\
    (match r with
     | E.Error _ -> True
     | E.Correct (None, rst) ->
       parsed_bytes rst ==
         Seq.slice (R.as_seq h0 st.buf) (v st.f_begin) (v st.f_end) /\
       in_progress_flt rst == in_progress_flt st
     | E.Correct (Some repr, rst) ->  //on a successful parse it returns a valid repr with lens condition
       repr.R.start_pos == st.from_idx /\
       R.valid repr h1 /\
       cl.LP.clens_cond (R.value repr) /\
       rst == ({ st with from_idx = repr.R.end_pos })))
= STEXN?.reflect (parse_common_st validator tag_fn tag acc b)



/// Helper function to handle the case when there is an error or insufficient data



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

let receive_s_Idle st b f_begin f_end = admit ()
// = let flt = F_s_Idle in

//   let r = parse_hsm_ch b f_begin in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (ch_repr, pos)) ->
//     check_eq_end_index_and_return pos f_end ({ ch_msg = ch_repr })

let receive_c_wait_ServerHello st b f_begin f_end = admit ()
// = let flt = F_c_wait_ServerHello in

//   let r = parse_hsm_sh b f_begin in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (sh_repr, pos)) ->
//     check_leq_end_index_and_return pos f_end ({sh_msg = sh_repr})


(*** 1.3 flights ***)


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

inline_for_extraction noextract
let init_ (flt:in_progress_flt_t) (b:R.const_slice) (f_begin:uint_32) (f_end:uint_32{f_begin <= f_end /\ f_end <= b.R.len})
: st:state ->
  ST (TLSError.result (option unit & state))
  (requires fun _ -> True)
  (ensures fun h0 r h1 ->
    h0 == h1 /\
    r == E.Correct (Some (),
      { st with
        in_progress = G.hide flt;
        buf = b;
        f_begin = f_begin;
        f_end = f_end;
        from_idx = f_begin }))
= fun (st:state) ->
  E.Correct (Some (), { st with
    in_progress = G.hide flt;
    buf = b;
    f_begin = f_begin;
    f_end = f_end;
    from_idx = f_begin })

inline_for_extraction noextract
let init (flt:in_progress_flt_t) (b:R.const_slice) (f_begin:uint_32) (f_end:uint_32{f_begin <= f_end /\ f_end <= b.R.len})
: StExn unit
  (requires fun st h -> True)
  (ensures fun st h0 r h1 ->
    h0 == h1 /\
    h0 == h1 /\
    r == E.Correct (Some (),
      { st with
        in_progress = G.hide flt;
        buf = b;
        f_begin = f_begin;
        f_end = f_end;
        from_idx = f_begin }))
= STEXN?.reflect (init_ flt b f_begin f_end)

#push-options "--max_fuel 0 --initial_ifuel 2 --max_ifuel 2 --z3rlimit 10"
inline_for_extraction noextract
let receive_c13_wait_Finished1_
  (b:R.const_slice) (f_begin f_end:uint_32)
: StExn (c13_wait_Finished1 b)
  (requires fun st h -> receive_pre st b f_begin f_end F_c13_wait_Finished1 h)
  (ensures fun st h0 r h1 ->
    receive_pre st b f_begin f_end F_c13_wait_Finished1 h0 /\
    B.(modifies loc_none h0 h1) /\
    (match r with
     | E.Error e -> True
     | E.Correct (None, rst) ->
       parsed_bytes rst ==
         Seq.slice (R.as_seq h0 b) (v f_begin) (v f_end) /\
       in_progress_flt rst == F_c13_wait_Finished1
     | E.Correct (Some flt, rst) ->
       valid_c13_wait_Finished1 f_begin rst.from_idx flt h1))
= init F_c13_wait_Finished1 b f_begin f_end;
  let ee = parse_hsm13_ee b in
  let cr = parse_hsm13_cr b in
  let c = parse_hsm13_c b in
  let cv = parse_hsm13_cv b in
  let fin = parse_hsm13_fin b in
  { ee_msg = ee;
    cr_msg = cr;
    c_msg = c;
    cv_msg = cv;
    fin_msg = fin }
#pop-options

let receive_c13_wait_Finished1 st b f_begin f_end
= let r = reify (receive_c13_wait_Finished1_ b f_begin f_end) st in
  match r with
  | E.Error _
  | E.Correct (None, _) -> r
  | E.Correct (Some flt, rst) ->
    check_eq_end_index_and_return rst.from_idx f_end flt



// /// Helper function to parse c13 and cv13 that appear together in a flight

// private let parse_hsm13_c_cv
//   (b:R.const_slice) (f_begin:uint_32)
// : Stack (TLSError.result (option (HSM13R.c13_repr b & HSM13R.cv13_repr b & uint_32)))
//   (requires fun h ->
//     R.live h b /\
//     f_begin <= b.R.len)
//   (ensures fun h0 r h1 ->
//     B.modifies B.loc_none h0 h1 /\
//     (match r with
//      | E.Error _ -> True
//      | E.Correct None -> True
//      | E.Correct (Some (c13, cv13, pos)) ->
//        c13.R.start_pos == f_begin /\
//        c13.R.end_pos == cv13.R.start_pos /\
//        cv13.R.end_pos == pos /\
//        R.valid c13 h1 /\
//        R.valid cv13 h1))
// = let r = parse_hsm13_c b f_begin in
//   match r with
//   | E.Error e -> E.Error e
//   | E.Correct None -> E.Correct None
//   | E.Correct (Some (c_repr, c_end)) ->
//     let r = parse_hsm13_cv b c_end in
//     match r with
//     | E.Error e -> E.Error e
//     | E.Correct None -> E.Correct None
//     | E.Correct (Some (cv_repr, cv_end)) ->
//       E.Correct (Some (c_repr, cv_repr, cv_end))

// #set-options "--z3rlimit 50"
// let receive_c13_wait_Finished1 st b f_begin f_end
// = let flt = F_c13_wait_Finished1 in

//   let r = parse_hsm13_ee b f_begin in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (ee_repr, ee_end)) ->
//     let r = parse_hsm13_cr b ee_end in
//     match r with
//     | E.Correct None ->
//       err_or_insufficient_data r flt b f_begin f_end
//     | _ ->
//      let cr_repr, c_cv_begin =
//        match r with
//        | E.Error _ -> None, ee_end
//        | E.Correct (Some (cr_repr, cr_end)) ->
//          Some cr_repr, cr_end
//      in
//      let r = parse_hsm13_c_cv b c_cv_begin in
//      match r with
//      | E.Correct None ->
//        err_or_insufficient_data r flt b f_begin f_end
//      | _ ->
//        let c_cv_repr, fin_begin =
//          match r with
//          | E.Error _ -> None, c_cv_begin
//          | E.Correct (Some (c_repr, cv_repr, c_cv_end)) ->
//            Some (c_repr, cv_repr), c_cv_end
//        in
//        let r = parse_hsm13_fin b fin_begin in
//        match r with
//        | E.Error _ | E.Correct None ->
//          err_or_insufficient_data r flt b f_begin f_end
//        | E.Correct (Some (fin_repr, fin_end)) ->
//          check_eq_end_index_and_return fin_end f_end ({
//            ee_msg = ee_repr;
//            cr_msg = cr_repr;
//            c_cv_msg = c_cv_repr;
//            fin_msg = fin_repr
//          })

// let receive_s13_wait_Finished2 st b f_begin f_end
// = let flt = F_s13_wait_Finished2 in

//   let r = parse_hsm13_c_cv b f_begin in
//   match r with
//   | E.Correct None -> err_or_insufficient_data r flt b f_begin f_end
//   | _ ->
//     let c_cv_repr, fin_begin =
//       match r with
//       | E.Error _ -> None, f_begin
//       | E.Correct (Some (c_repr, cv_repr, c_cv_end)) ->
//         Some (c_repr, cv_repr), c_cv_end
//     in
//     let r = parse_hsm13_fin b fin_begin in
//     match r with
//     | E.Error _ | E.Correct None -> err_or_insufficient_data r flt b f_begin f_end
//     | E.Correct (Some (fin_repr, fin_end)) ->
//       check_eq_end_index_and_return fin_end f_end ({
//         c_cv_msg = c_cv_repr;
//         fin_msg = fin_repr
//       })

// let receive_s13_wait_EOED st b f_begin f_end
// = let flt = F_s13_wait_EOED in

//   let r = parse_hsm13_eoed b f_begin in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (eoed_repr, pos)) ->
//     check_eq_end_index_and_return pos f_end ({ eoed_msg = eoed_repr })

// let receive_c13_Complete st b f_begin f_end
// = let flt = F_c13_Complete in

//   let r = parse_hsm13_nst b f_begin in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (nst_repr, pos)) ->
//     check_eq_end_index_and_return pos f_end ({ nst_msg = nst_repr })


// (*** 1.2 flights ***)


// inline_for_extraction noextract
// let parse_hsm12_c
// = parse_common
//     HSM12.handshake12_validator
//     HSM12.tag_of_handshake12
//     HSMType.Certificate
//     HSM12.handshake12_accessor_certificate

// inline_for_extraction noextract
// let parse_hsm12_ske
// = parse_common
//     HSM12.handshake12_validator
//     HSM12.tag_of_handshake12
//     HSMType.Server_key_exchange
//     HSM12.handshake12_accessor_server_key_exchange

// inline_for_extraction noextract
// let parse_hsm12_shd
// = parse_common
//     HSM12.handshake12_validator
//     HSM12.tag_of_handshake12
//     HSMType.Server_hello_done
//     HSM12.handshake12_accessor_server_hello_done

// inline_for_extraction noextract
// let parse_hsm12_cr
// = parse_common
//     HSM12.handshake12_validator
//     HSM12.tag_of_handshake12
//     HSMType.Certificate_request
//     HSM12.handshake12_accessor_certificate_request

// inline_for_extraction noextract
// let parse_hsm12_fin
// = parse_common
//     HSM12.handshake12_validator
//     HSM12.tag_of_handshake12
//     HSMType.Finished
//     HSM12.handshake12_accessor_finished

// inline_for_extraction noextract
// let parse_hsm12_nst
// = parse_common
//     HSM12.handshake12_validator
//     HSM12.tag_of_handshake12
//     HSMType.New_session_ticket
//     HSM12.handshake12_accessor_new_session_ticket

// inline_for_extraction noextract
// let parse_hsm12_cke
// = parse_common
//     HSM12.handshake12_validator
//     HSM12.tag_of_handshake12
//     HSMType.Client_key_exchange
//     HSM12.handshake12_accessor_client_key_exchange


// let receive_c12_wait_ServerHelloDone st b f_begin f_end
// = let flt = F_c12_wait_ServerHelloDone in

//   let r = parse_hsm12_c b f_begin in
//   match r with
//   | E.Error _ | E.Correct None -> err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (c_repr, c_end)) ->
//     let r = parse_hsm12_ske b c_end in
//     match r with
//     | E.Error _ | E.Correct None -> err_or_insufficient_data r flt b f_begin f_end
//     | E.Correct (Some (ske_repr, ske_end)) ->
//       let r = parse_hsm12_cr b ske_end in
//       match r with
//       | E.Correct None -> err_or_insufficient_data r flt b f_begin f_end
//       | _ ->
//         let cr_repr, shd_begin =
//           match r with
//           | E.Error _ -> None, ske_end
//           | E.Correct (Some (cr_repr, cr_end)) -> Some cr_repr, cr_end
//         in
//         let r = parse_hsm12_shd b shd_begin in
//         match r with
//         | E.Error _ | E.Correct None ->
//           err_or_insufficient_data r flt b f_begin f_end
//         | E.Correct (Some (shd_repr, pos)) ->
//           check_eq_end_index_and_return pos f_end ({
//             c_msg = c_repr;
//             ske_msg = ske_repr;
//             cr_msg = cr_repr;
//             shd_msg = shd_repr
//           })

// let receive_cs12_wait_Finished st b f_begin f_end
// = let flt = F_cs12_wait_Finished in

//   let r = parse_hsm12_fin b f_begin in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (fin_repr, pos)) ->
//     check_eq_end_index_and_return pos f_end ({ fin_msg = fin_repr })

// let receive_c12_wait_NST st b f_begin f_end
// = let flt = F_c12_wait_NST in

//   let r = parse_hsm12_nst b f_begin in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (nst_repr, pos)) ->
//     check_eq_end_index_and_return pos f_end ({ nst_msg = nst_repr })

// let receive_s12_wait_CCS1 st b f_begin f_end
// = let flt = F_s12_wait_CCS1 in

//   let r = parse_hsm12_cke b f_begin in
//   match r with
//   | E.Error _ | E.Correct None ->
//     err_or_insufficient_data r flt b f_begin f_end
//   | E.Correct (Some (cke_repr, pos)) ->
//     check_eq_end_index_and_return pos f_end ({ cke_msg = cke_repr })
