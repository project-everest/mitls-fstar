module HSL.Receive

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module LP = LowParse.Low.Base

open HSL.Common

module HSM = Parsers.Handshake
module HSM12 = Parsers.Handshake12
module HSM13 = Parsers.Handshake13

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"


/// HSL main API

type slice =
  sl:LP.slice
       (LP.srel_of_buffer_srel (B.trivial_preorder LP.byte))
       (LP.srel_of_buffer_srel (B.trivial_preorder LP.byte)){
         v sl.LP.len <= v LP.validator_max_length
     }


/// For incremental parsing, flight receiving functions have
///   preconditions on the current in-progress flight

type in_progress_flt_t =
  | F_none
  | F13_ee_c_cv_fin
  | F13_ee_cr_c_cv_fin
  | F13_ee_fin
  | F13_fin
  | F13_c_cv_fin
  | F13_eoed
  | F13_nst  // ... more 12 and CH flights to come


/// Abstract HSL state

val hsl_state : Type0

val region_of (st:hsl_state) : GTot Mem.rgn


/// Bytes parsed so far, in the current flight

val parsed_bytes (st:hsl_state) (h:HS.mem) : GTot bytes

let length_parsed_bytes (st:hsl_state) (h:HS.mem) : GTot nat =
  Seq.length (parsed_bytes st h)

val in_progress_flt (st:hsl_state) (h:HS.mem) : GTot in_progress_flt_t


/// Abstract invariant

val invariant (st:hsl_state) (h:HS.mem) : Type0


/// HSL footprint

val footprint (st:hsl_state) : GTot B.loc


/// State that is framed across framing kind of lemmas

unfold let frame_state (st:hsl_state) (h0 h1:HS.mem) =
  parsed_bytes st h1 == parsed_bytes st h0 /\
  in_progress_flt st h1 == in_progress_flt st h0


/// Framing lemma

val frame_hsl_state (st:hsl_state) (h0 h1:HS.mem) (l:B.loc)
  : Lemma
    (requires 
      B.modifies l h0 h1 /\
      B.loc_disjoint (footprint st) l /\
      invariant st h0)
    (ensures 
      invariant st h1 /\
      frame_state st h0 h1)


/// Creation of the log

unfold
let create_post (r:Mem.rgn)
  : HS.mem -> hsl_state -> HS.mem -> Type0
  = fun h0 st h1 ->
    region_of st == r /\
    parsed_bytes st h1 == Seq.empty /\
    in_progress_flt st h1 == F_none /\
    B.fresh_loc (footprint st) h0 h1 /\
    r `region_includes` footprint st /\    
    B.modifies B.loc_none h0 h1 /\
    invariant st h1
  
val create (r:Mem.rgn)
  : ST hsl_state 
       (requires fun h0 -> True)
       (ensures create_post r)


/// Receive API

#push-options "--max_ifuel 2 --initial_ifuel 2 --z3rlimit 20"  //increase ifuel for inverting options and tuples

unfold
let basic_pre_post (st:hsl_state) (b:slice) (from to:uint_32) (in_progress:in_progress_flt_t)
  : HS.mem -> Type0
  = fun h ->
    let open B in let open LP in
    
    invariant st h /\

    live_slice h b /\
    loc_disjoint (footprint st) (loc_buffer b.base) /\
    
    v from + length_parsed_bytes st h <= v to /\
    v to <= v b.len /\
    
    Seq.equal (Seq.slice (as_seq h b.base)
                         (v from)
                         (v from + length_parsed_bytes st h))
              (parsed_bytes st h) /\

    (in_progress_flt st h == F_none \/ in_progress_flt st h == in_progress)


let valid_flight_t 'a =
  (flt:'a) -> (from:uint_32) -> (to:uint_32) -> (b:slice) -> (h:HS.mem) -> Type0

unfold private
let receive_post 
  (st:hsl_state)
  (b:slice)
  (from to:uint_32)
  (f:valid_flight_t 'a)
  (in_progress:in_progress_flt_t)
  (h0:HS.mem)
  (x:TLSError.result (option 'a))
  (h1:HS.mem)
  = basic_pre_post st b from to in_progress h0 /\
    B.modifies (footprint st) h0 h1 /\
    (let open FStar.Error in
     match x with
     | Error _ -> True
     | Correct None ->
       in_progress_flt st h1 == in_progress /\
       parsed_bytes st h1 ==
         Seq.slice (B.as_seq h0 b.LP.base) (v from) (v to)
     | Correct (Some flt) ->
       f flt from to b h1 /\
       parsed_bytes st h1 == Seq.empty /\
       in_progress_flt st h1 == F_none
     | _ -> False)
#pop-options //remove the increased ifuel


/// ad-hoc flight types
/// HS would ask HSL to parse specific flight types, depending on where its own state machine is

/// First 13 flights

/// Common function for slice being a valid 13 message msg

let valid_parsing13
  (msg:HSM13.handshake13)
  (buf:slice)
  (from to:uint_32)
  (h:HS.mem)
  = let parser = HSM13.handshake13_parser in
    from <= to /\
    LP.valid parser h buf from /\
    LP.contents parser h buf from == msg /\
    LP.content_length parser h buf from == UInt32.v (to - from)


(****** Flight [ EncryptedExtensions; Certificate13; CertificateVerify; Finished ] ******)

module EE  = Parsers.Handshake13_m_encrypted_extensions
module C13 = Parsers.Handshake13_m_certificate
module CV13 = Parsers.Handshake13_m_certificate_verify
module Fin13 = Parsers.Handshake13_m_finished

noeq
type flight13_ee_c_cv_fin = {
  begin_c   : uint_32;
  begin_cv  : uint_32;
  begin_fin : uint_32;

  ee_msg  : G.erased EE.handshake13_m_encrypted_extensions;
  c_msg   : G.erased C13.handshake13_m_certificate;
  cv_msg  : G.erased CV13.handshake13_m_certificate_verify;
  fin_msg : G.erased Fin13.handshake13_m_finished
}


let valid_flight13_ee_c_cv_fin
  : valid_flight_t flight13_ee_c_cv_fin
  = fun (flt:flight13_ee_c_cv_fin) (from to:uint_32) (b:slice) (h:HS.mem) ->

    valid_parsing13 (HSM13.M_encrypted_extensions (G.reveal flt.ee_msg)) b from flt.begin_c h /\
    valid_parsing13 (HSM13.M_certificate (G.reveal flt.c_msg)) b flt.begin_c flt.begin_cv h /\
    valid_parsing13 (HSM13.M_certificate_verify (G.reveal flt.cv_msg)) b flt.begin_cv flt.begin_fin h /\
    valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flt.begin_fin to h


val receive_flight13_ee_c_cv_fin
  (st:hsl_state) (b:slice) (from to:uint_32)
  : ST (TLSError.result (option flight13_ee_c_cv_fin))
       (requires basic_pre_post st b from to F13_ee_c_cv_fin)
       (ensures  receive_post st b from to valid_flight13_ee_c_cv_fin F13_ee_c_cv_fin)


(****** Flight [EncryptedExtensions; Certificaterequest13; Certificate13; CertificateVerify; Finished ] ******)

module CR13 = Parsers.Handshake13_m_certificate_request

noeq
type flight13_ee_cr_c_cv_fin = {
  begin_cr  : uint_32;
  begin_c   : uint_32;
  begin_cv  : uint_32;
  begin_fin : uint_32;

  ee_msg  : G.erased EE.handshake13_m_encrypted_extensions;
  cr_msg  : G.erased CR13.handshake13_m_certificate_request;
  c_msg   : G.erased C13.handshake13_m_certificate;
  cv_msg  : G.erased CV13.handshake13_m_certificate_verify;
  fin_msg : G.erased Fin13.handshake13_m_finished
}


let valid_flight13_ee_cr_c_cv_fin
  : valid_flight_t flight13_ee_cr_c_cv_fin
  = fun (flt:flight13_ee_cr_c_cv_fin) (from to:uint_32) (b:slice) (h:HS.mem) ->

    valid_parsing13 (HSM13.M_encrypted_extensions (G.reveal flt.ee_msg)) b from flt.begin_cr h /\
    valid_parsing13 (HSM13.M_certificate_request (G.reveal flt.cr_msg)) b flt.begin_cr flt.begin_c h /\
    valid_parsing13 (HSM13.M_certificate (G.reveal flt.c_msg)) b flt.begin_c flt.begin_cv h /\
    valid_parsing13 (HSM13.M_certificate_verify (G.reveal flt.cv_msg)) b flt.begin_cv flt.begin_fin h /\
    valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flt.begin_fin to h


val receive_flight13_ee_cr_c_cv_fin
  (st:hsl_state) (b:slice) (from to:uint_32)
  : ST (TLSError.result (option flight13_ee_cr_c_cv_fin))
       (requires basic_pre_post st b from to F13_ee_cr_c_cv_fin)
       (ensures  receive_post st b from to valid_flight13_ee_cr_c_cv_fin F13_ee_cr_c_cv_fin)


(****** Flight [EncryptedExtensions; Finished] ******)

noeq
type flight13_ee_fin = {
  begin_fin : uint_32;

  ee_msg    : G.erased EE.handshake13_m_encrypted_extensions;
  fin_msg   : G.erased Fin13.handshake13_m_finished
}

let valid_flight13_ee_fin : valid_flight_t flight13_ee_fin =
  fun (flt:flight13_ee_fin) (from to:uint_32) (b:slice) (h:HS.mem) ->

  valid_parsing13 (HSM13.M_encrypted_extensions (G.reveal flt.ee_msg)) b from flt.begin_fin h /\
  valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flt.begin_fin to h

val receive_flight13_ee_fin (st:hsl_state) (b:slice) (from to:uint_32)
  : ST (TLSError.result (option flight13_ee_fin))
       (requires basic_pre_post st b from to F13_ee_fin)
       (ensures  receive_post st b from to valid_flight13_ee_fin F13_ee_fin)


(****** Flight [ Finished ] ******)

noeq
type flight13_fin = {
  fin_msg : G.erased Fin13.handshake13_m_finished
}


let valid_flight13_fin : valid_flight_t flight13_fin =
  fun (flt:flight13_fin) (from to:uint_32) (b:slice) (h:HS.mem) ->

  valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b from to h

val receive_flight13_fin (st:hsl_state) (b:slice) (from to:uint_32)
  : ST (TLSError.result (option flight13_fin))
       (requires basic_pre_post st b from to F13_fin)
       (ensures  receive_post st b from to valid_flight13_fin F13_fin)


(****** Flight [ Certificate13; CertificateVerify; Finished ] ******)

noeq
type flight13_c_cv_fin = {
  begin_cv  : uint_32;
  begin_fin : uint_32;

  c_msg   : G.erased C13.handshake13_m_certificate;
  cv_msg  : G.erased CV13.handshake13_m_certificate_verify;
  fin_msg : G.erased Fin13.handshake13_m_finished
}


let valid_flight13_c_cv_fin
  : valid_flight_t flight13_c_cv_fin
  = fun (flt:flight13_c_cv_fin) (from to:uint_32) (b:slice) (h:HS.mem) ->

    valid_parsing13 (HSM13.M_certificate (G.reveal flt.c_msg)) b from flt.begin_cv h /\
    valid_parsing13 (HSM13.M_certificate_verify (G.reveal flt.cv_msg)) b flt.begin_cv flt.begin_fin h /\
    valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flt.begin_fin to h


val receive_flight13_c_cv_fin
  (st:hsl_state) (b:slice) (from to:uint_32)
  : ST (TLSError.result (option flight13_c_cv_fin))
       (requires basic_pre_post st b from to F13_c_cv_fin)
       (ensures  receive_post st b from to valid_flight13_c_cv_fin F13_c_cv_fin)


(****** Flight [ EndOfEarlyData ] ******)

module EoED13 = Parsers.Handshake13_m_end_of_early_data

noeq
type flight13_eoed = {
  eoed_msg : G.erased (EoED13.handshake13_m_end_of_early_data)
}


let valid_flight13_eoed : valid_flight_t flight13_eoed =
  fun (flt:flight13_eoed) (from to:uint_32) (b:slice) (h:HS.mem) ->

  valid_parsing13 (HSM13.M_end_of_early_data (G.reveal flt.eoed_msg)) b from to h

val receive_flight13_eoed (st:hsl_state) (b:slice) (from to:uint_32)
  : ST (TLSError.result (option flight13_eoed))
       (requires basic_pre_post st b from to F13_eoed)
       (ensures  receive_post st b from to valid_flight13_eoed F13_eoed)


(****** Flight [ NewSessionTicket13 ] ******)

module NST13 = Parsers.Handshake13_m_new_session_ticket

noeq
type flight13_nst = {
  nst_msg : G.erased (NST13.handshake13_m_new_session_ticket)
}


let valid_flight13_nst : valid_flight_t flight13_nst =
  fun (flt:flight13_nst) (from to:uint_32) (b:slice) (h:HS.mem) ->

  valid_parsing13 (HSM13.M_new_session_ticket (G.reveal flt.nst_msg)) b from to h

val receive_flight13_nst (st:hsl_state) (b:slice) (from to:uint_32)
  : ST (TLSError.result (option flight13_nst))
       (requires basic_pre_post st b from to F13_nst)
       (ensures  receive_post st b from to valid_flight13_nst F13_nst)


/// TODO: 12 flights
