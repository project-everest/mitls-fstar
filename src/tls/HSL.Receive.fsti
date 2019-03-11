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

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection -LowParse'"


/// HSL main API

type lbuffer8 (l:uint_32) = b:B.buffer uint_8{B.len b == l}

type range_t = t:(uint_32 & uint_32){fst t <= snd t}


/// Abstract HSL state

val hsl_state : Type0

val region_of : hsl_state -> GTot Mem.rgn

/// These are indices that are used if the client is calling receive again for the same flight
/// For example, say the client calls receive with a buffer, and HSL signals to the client
///   that the data in the buffer is incomplete. In that case, HSL will set these indices,
///   and the next time client calls receive for the same flight, it will pass the new indices
///   with the precondition that from index in the second call is same as the to index in the
///   first call, and that the buffer bytes between from and to of the first call are the same.
///   When the flight is complete, these indices are set to None, and for the next flight the
///   caller can pass different buffer with different indices if it wants.

val index_from_to : st:hsl_state -> HS.mem -> GTot (option range_t)

/// Bytes parsed so far, in the current flight

val parsed_bytes : st:hsl_state -> HS.mem -> GTot bytes

/// The invariant is quite light, includes liveness of local state etc.

val invariant : hsl_state -> HS.mem -> prop

/// HSL footprint
val footprint : hsl_state -> GTot B.loc

/// Frame the mem-dependent functions

unfold let state_framing (st:hsl_state) (h0 h1:HS.mem)
  = index_from_to st h0 == index_from_to st h1 /\
    parsed_bytes st h0 == parsed_bytes st h1

val frame_hsl_state (st:hsl_state) (h0 h1:HS.mem) (l:B.loc)
  : Lemma
    (requires 
      B.modifies l h0 h1 /\
      B.loc_disjoint (footprint st) l /\
      invariant st h0)
    (ensures 
      state_framing st h0 h1 /\
      invariant st h1)


/// Creation of the log
unfold
let create_post (r:Mem.rgn)
  : HS.mem -> hsl_state -> HS.mem -> Type0
  = fun h0 st h1 ->
    region_of st == r /\
    index_from_to st h1 = None /\
    parsed_bytes st h1 == Seq.empty /\
    B.fresh_loc (footprint st) h0 h1 /\  //local footprint is fresh
    r `region_includes` footprint st /\    
    B.modifies B.loc_none h0 h1 /\ //did not modify anything
    invariant st h1
  
val create (r:Mem.rgn)
  : ST hsl_state 
       (requires fun h0 -> True)
       (ensures create_post r)


/// Receive API

type b8 = B.buffer uint_8

#push-options "--max_ifuel 2 --initial_ifuel 2 --z3rlimit 20"  //increase ifuel for inverting options and tuples

let range_extension (r0:option range_t) (from to:uint_32) =
    from <= to /\
    (match r0 with
     | None -> True  //nothing to prove if prev_from_to is not set
     | Some r ->
       from = snd r)

let get_range (r0:option range_t) : range_t =
  match r0 with
  | None -> 0ul, 0ul
  | Some r -> r
  
unfold private
let basic_pre_post (st:hsl_state) (b:b8) (from to:uint_32) : HS.mem -> Type0
  = fun h ->
    let prev_from_to = index_from_to st h in
    invariant st h /\
    range_extension prev_from_to from to /\
    to <= B.len b /\
    (let start, finish = get_range prev_from_to in
     B.as_seq h (B.gsub b start (finish - start)) == parsed_bytes st h)

let update_window (r0:option range_t)
                  (from:uint_32)
                  (to:uint_32{range_extension r0 from to})
  : option range_t
  = match r0 with
    | None -> Some (from, to)
    | Some (from_0, _) -> Some (from_0, to)

let valid_flight_t 'a =
  (flt:'a) -> (flight_begin:uint_32) -> (flight_end:uint_32) -> (b:b8) -> (h:HS.mem) -> Type0

unfold private
let receive_post 
  (st:hsl_state)
  (b:b8)
  (from to:uint_32)
  (f:valid_flight_t 'a)
  (h0:HS.mem)
  (x:TLSError.result (option 'a))
  (h1:HS.mem)
  = basic_pre_post st b from to h0 /\
    B.modifies (footprint st) h0 h1 /\  //only local footprint is modified
    (let open FStar.Error in
     match x, index_from_to st h1 with
     | Error _, _ -> True  //underspecified
     | Correct None, Some r ->  //waiting for more data
       let start = fst r in
       let finish = snd r in
       finish == to /\
       parsed_bytes st h1 == B.as_seq h0 (B.gsub b start (finish - start)) /\
       index_from_to st h1 == update_window (index_from_to st h0) from to
     | Correct (Some flt), None ->
       f flt from to b h1 /\  //flight specific postcondition
       //Internal state for partial parse is reset
       //Ready to receive another flight
       parsed_bytes st h1 == Seq.empty
     | _ -> False)
#pop-options //remove the increased ifuel


/// ad-hoc flight types
/// HS would ask HSL to parse specific flight types, depending on where its own state machine is

/// First 13 flights

/// Common function for buffer being a valid 13 message msg

let valid_parsing13
  (msg:HSM13.handshake13)
  (buf:b8)
  (from:uint_32) (to:uint_32)
  (h:HS.mem)
  = let parser = HSM13.handshake13_parser in
    let slice = { LP.base = buf; LP.len = B.len buf } in
    from <= to /\
    LP.valid parser h slice from /\
    LP.contents parser h slice from == msg /\
    LP.content_length parser h slice from == UInt32.v (to - from)


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
  = fun (flt:flight13_ee_c_cv_fin) (flight_begin:uint_32) (flight_end:uint_32) (b:b8) (h:HS.mem) ->

    valid_parsing13 (HSM13.M_encrypted_extensions (G.reveal flt.ee_msg)) b flight_begin flt.begin_c h /\
    valid_parsing13 (HSM13.M_certificate (G.reveal flt.c_msg)) b flt.begin_c flt.begin_cv h /\
    valid_parsing13 (HSM13.M_certificate_verify (G.reveal flt.cv_msg)) b flt.begin_cv flt.begin_fin h /\
    valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flt.begin_fin flight_end h


val receive_flight13_ee_c_cv_fin
  (st:hsl_state) (b:b8) (from to:uint_32)
  : ST (TLSError.result (option flight13_ee_c_cv_fin))
       (requires basic_pre_post st b from to)
       (ensures  receive_post st b from to valid_flight13_ee_c_cv_fin)


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
  = fun (flt:flight13_ee_cr_c_cv_fin) (flight_begin:uint_32) (flight_end:uint_32) (b:b8) (h:HS.mem) ->

    valid_parsing13 (HSM13.M_encrypted_extensions (G.reveal flt.ee_msg)) b flight_begin flt.begin_cr h /\
    valid_parsing13 (HSM13.M_certificate_request (G.reveal flt.cr_msg)) b flt.begin_cr flt.begin_c h /\
    valid_parsing13 (HSM13.M_certificate (G.reveal flt.c_msg)) b flt.begin_c flt.begin_cv h /\
    valid_parsing13 (HSM13.M_certificate_verify (G.reveal flt.cv_msg)) b flt.begin_cv flt.begin_fin h /\
    valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flt.begin_fin flight_end h


val receive_flight13_ee_cr_c_cv_fin
  (st:hsl_state) (b:b8) (from to:uint_32)
  : ST (TLSError.result (option flight13_ee_cr_c_cv_fin))
       (requires basic_pre_post st b from to)
       (ensures  receive_post st b from to valid_flight13_ee_cr_c_cv_fin)


(****** Flight [EncryptedExtensions; Finished] ******)

noeq
type flight13_ee_fin = {
  begin_fin : uint_32;

  ee_msg    : G.erased EE.handshake13_m_encrypted_extensions;
  fin_msg   : G.erased Fin13.handshake13_m_finished
}

let valid_flight13_ee_fin : valid_flight_t flight13_ee_fin =
  fun (flt:flight13_ee_fin) (flight_begin:uint_32) (flight_end:uint_32) (b:b8) (h:HS.mem) ->

  valid_parsing13 (HSM13.M_encrypted_extensions (G.reveal flt.ee_msg)) b flight_begin flt.begin_fin h /\
  valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flt.begin_fin flight_end h

val receive_flight13_ee_fin (st:hsl_state) (b:b8) (from to:uint_32)
  : ST (TLSError.result (option flight13_ee_fin))
       (requires basic_pre_post st b  from to)
       (ensures  receive_post st b from to valid_flight13_ee_fin)


(****** Flight [ Finished ] ******)

noeq
type flight13_fin = {
  fin_msg : G.erased Fin13.handshake13_m_finished
}


let valid_flight13_fin : valid_flight_t flight13_fin =
  fun (flt:flight13_fin) (flight_begin:uint_32) (flight_end:uint_32) (b:b8) (h:HS.mem) ->

  valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flight_begin flight_end h

val receive_flight13_fin (st:hsl_state) (b:b8) (from to:uint_32)
  : ST (TLSError.result (option flight13_fin))
       (requires basic_pre_post st b  from to)
       (ensures  receive_post st b from to valid_flight13_fin)


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
  = fun (flt:flight13_c_cv_fin) (flight_begin:uint_32) (flight_end:uint_32) (b:b8) (h:HS.mem) ->

    valid_parsing13 (HSM13.M_certificate (G.reveal flt.c_msg)) b flight_begin flt.begin_cv h /\
    valid_parsing13 (HSM13.M_certificate_verify (G.reveal flt.cv_msg)) b flt.begin_cv flt.begin_fin h /\
    valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) b flt.begin_fin flight_end h


val receive_flight13_c_cv_fin
  (st:hsl_state) (b:b8) (from to:uint_32)
  : ST (TLSError.result (option flight13_c_cv_fin))
       (requires basic_pre_post st b from to)
       (ensures  receive_post st b from to valid_flight13_c_cv_fin)


(****** Flight [ EndOfEarlyData ] ******)

module EoED13 = Parsers.Handshake13_m_end_of_early_data

noeq
type flight13_eoed = {
  eoed_msg : G.erased (EoED13.handshake13_m_end_of_early_data)
}


let valid_flight13_eoed : valid_flight_t flight13_eoed =
  fun (flt:flight13_eoed) (flight_begin:uint_32) (flight_end:uint_32) (b:b8) (h:HS.mem) ->

  valid_parsing13 (HSM13.M_end_of_early_data (G.reveal flt.eoed_msg)) b flight_begin flight_end h

val receive_flight13_eoed (st:hsl_state) (b:b8) (from to:uint_32)
  : ST (TLSError.result (option flight13_eoed))
       (requires basic_pre_post st b  from to)
       (ensures  receive_post st b from to valid_flight13_eoed)


(****** Flight [ NewSessionTicket13 ] ******)

module NST13 = Parsers.Handshake13_m_new_session_ticket

noeq
type flight13_nst = {
  nst_msg : G.erased (NST13.handshake13_m_new_session_ticket)
}


let valid_flight13_nst : valid_flight_t flight13_nst =
  fun (flt:flight13_nst) (flight_begin:uint_32) (flight_end:uint_32) (b:b8) (h:HS.mem) ->

  valid_parsing13 (HSM13.M_new_session_ticket (G.reveal flt.nst_msg)) b flight_begin flight_end h

val receive_flight13_nst (st:hsl_state) (b:b8) (from to:uint_32)
  : ST (TLSError.result (option flight13_nst))
       (requires basic_pre_post st b  from to)
       (ensures  receive_post st b from to valid_flight13_nst)


/// TODO: 12 flights
