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

#reset-options
   "--max_fuel 0 --max_ifuel 0 \
    --using_facts_from '* -FStar.Tactics -FStar.Reflection -FStar.UInt128 -FStar.Math -LowParse +LowParse.Low.Base +LowParse.Spec.Base'"


    // --using_facts_from 'Prims FStar LowStar -FStar.Reflection -FStar.Tactics -FStar.UInt128 -FStar.Math' \
    // --using_facts_from 'Mem HSL Types_s Words_s Spec.Hash.Definitions.bytes' \
    // --using_facts_from 'TLSError'"


// /// HandshakeMessages related definitions

// type msg = HSM.hs_msg

// /// Specifies which messages indicate the end of incoming flights
// /// Triggers their Handshake processing

// let end_of_flight : msg -> bool =
//   let open HandshakeMessages in
//   function
//   | ClientHello _
//   | HelloRetryRequest _
//   | EndOfEarlyData
//   | ServerHello _
//   | ServerHelloDone
//   | NewSessionTicket13 _
//   | Finished _ -> true
//   | _ -> false
// // No support for binders yet -- comment copied from HandshakeLog


// /// Specifies which messages require an intermediate transcript hash
// /// in incoming flights. In doubt, we hash!

// let tagged : msg -> bool =
//   let open HSM in
//   function
//   | ClientHello _
//   | ServerHello _
//   | EndOfEarlyData        // for Client finished -- comment (and other comments below) copied from HandshakeLog
//   | Certificate13 _       // for CertVerify payload in TLS 1.3
//   | EncryptedExtensions _ // For PSK handshake: [EE; Finished]
//   | CertificateVerify _   // for ServerFinish payload in TLS 1.3
//   | ClientKeyExchange _   // only for client signing
//   | NewSessionTicket _    // for server finished in TLS 1.2
//   | Finished _ -> true     // for 2nd Finished
//   | _ -> false
// // NB CCS is not explicitly handled here, but can trigger tagging and end-of-flights -- comment copied from HandshakeLog

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

/// Bytes parsed so far

val parsed_bytes : st:hsl_state -> HS.mem -> GTot hbytes

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


/// AR: 01/29: verifying this create_post takes a long time, TODO: profile

/// Creation of the log
unfold
private
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
/// Until a full flight is received, we lose "writing" capability -- as per the comment in HandshakeLog

/// ad-hoc flight types
/// HS would ask HSL to parse specific flight types, depending on where its own state machine is

type b8 = B.buffer uint_8

module HSM13 = Parsers.Handshake13

module EE  = Parsers.Handshake13_m_encrypted_extensions
module Fin = Parsers.Handshake13_m_finished

noeq
type flight_ee_fin = {
  begin_ee  : uint_32;
  begin_fin : uint_32;
  ee_msg    : G.erased EE.handshake13_m_encrypted_extensions;
  fin_msg   : G.erased Fin.handshake13_m_finished
}

let valid_flight_t 'a =
  (flt:'a) -> (flight_end:uint_32) -> (b:b8) -> (h:HS.mem) -> Type0


/// AR: 01/29: up to this point proofs are fine, but beyond this the performance drops

let valid_parsing (msg:HSM13.handshake13) (from to:uint_32) (buf:b8{from <= to /\ B.len buf == to - from}) (h:HS.mem) =
  let parser = HSM13.handshake13_parser in
  let slice = { LP.base = buf; LP.len = to - from } in
  LP.valid parser h slice from /\
  LP.contents parser h slice from == msg /\
  LP.content_length parser h slice from == UInt32.v (to - from)

let valid_flight_ee_fin : valid_flight_t flight_ee_fin =
  fun (flt:flight_ee_fin) (flight_end:uint_32) (b:b8) (h:HS.mem) ->

  flt.begin_ee <= flt.begin_fin /\
  flt.begin_fin <= flight_end /\
  flight_end <= B.len b /\

  (let ee_buf = B.gsub b flt.begin_ee (flt.begin_fin - flt.begin_ee) in
   let fin_buf = B.gsub b flt.begin_fin (flight_end - flt.begin_fin) in
   
   valid_parsing (HSM13.M_encrypted_extensions (G.reveal flt.ee_msg)) flt.begin_ee flt.begin_fin ee_buf h /\
   valid_parsing (HSM13.M_finished (G.reveal flt.fin_msg)) flt.begin_fin flight_end fin_buf h)

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

#push-options "--max_ifuel 2 --initial_ifuel 2 --z3rlimit 20"
let update_window (r0:option range_t)
                  (from:uint_32)
                  (to:uint_32{range_extension r0 from to})
  : option range_t
  = match r0 with
    | None -> Some (from, to)
    | Some (from_0, _) -> Some (from_0, to)

unfold private
let receive_post 
      (st:hsl_state)
      (b:b8)
      (from to:uint_32)
      (f:valid_flight_t 'a)
      (h0:HS.mem)
      (x:TLSError.result (option 'a))
      (h1:HS.mem) =
  basic_pre_post st b from to h0 /\
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
     f flt to b h1 /\  //flight specific postcondition
     //Internal state for partial parse is reset
     //Ready to receive another flight
     parsed_bytes st h1 == Seq.empty
   | _ -> False)
#pop-options

val receive_flight_ee_fin (st:hsl_state) (b:b8) (from to:uint_32)
  : ST (TLSError.result (option flight_ee_fin))    //end input buffer index for the flight
       (requires basic_pre_post st b  from to)
       (ensures  receive_post st b from to valid_flight_ee_fin)

// val receive_flight_c_ske_shd (st:hsl_state) (b:b8) (from to:uint_32)
//   : ST (TLSError.result (option flight_c_ske_shd))
//        (requires basic_pre_post st b from to)
//        (ensures  receive_post st b from to valid_flight_c_ske_shd)


(*
 * framing for local footprints, and input index etc. since they are stateful
 * output index may be we don't need (no incremental serializations)
 * do we need the writing bit, it was inconclusive the other day
 * reset of HSL state?
 * currently we are not telling the client that parsing of the input buffer for current flight started at the end index of last flight, may be that's ok?
 *)


// unfold private let receive_post (st:hsl_state) (p:uint_32)
//   : HS.mem -> (TLSError.result (option (
//                                flight_t &
//                                G.erased (list msg) &
//                                uint_32 & uint_32))) -> HS.mem -> Type0
//   = fun h0 r h1 ->  
//     let open FStar.Error in
//     let oa = hash_alg h0 st in
//     let t0 = transcript h0 st in
//     let t1 = transcript h1 st in
//     (match r with
//      | Error _ -> True  //underspecified
//      | Correct None -> t0 == t1  //waiting for more data
//      | Correct (Some (flt, ms, p0, p1, hs)) ->
//        let ms = G.reveal ms in
//        t1 == t0 @ ms /\  //added ms to the transcript
//        writing h1 st /\  //Handshake can now write
//        p <= hsl_input_buf_len st /\
//        p0 <= p1 /\ p1 <= p /\  //returned indices are valid in the input buffer
//        msg_list_parsing_of ms st p0 p1 h1 /\  //ms is a valid parsing of input buffer contents between p0 and p1
//        flight_parsing_of flt ms st h1 /\  //the indices in the returned flight are valid parsings
//        (match oa with
//         | Some a -> tags a t0 ms hs  //hashed properly
//         | None -> hs == []))





(*
 * CF: make these fine grained, in collaboration with HS
 *)
// type flight_t =
//   | F_HRR: init:uint_32 -> len:uint_32 -> flight_t
//   | F_SH: init:uint_32 -> len:uint_32 -> flight_t
//   | F_C_SKE_SHD: c_init:uint_32 -> c_len:uint_32 ->
//                  ske_init:uint_32 -> ske_len:uint_32 -> 
// 		 -> erased certificate -> erased ske ->
// 		 flight_t
//   | F_C_SKE_CR_SHD: c_init:uint_32 -> c_len:uint_32 ->
//                     ske_init:uint_32 -> ske_len:uint_32 ->
//                     cr_init:uint_32 -> cr_len:uint_32 -> flight_t
//   | F_EE_C13_CV_Fin: ee_init:uint_32 ->
//                      c13_init:uint_32 ->
// 		     cv_init:uint_32 ->
// 		     fin_init:uint_32 -> fin_len:uint_32 -> flight_t
//   | F_EE_CR13_C13_CV_Fin: ee_init:uint_32 -> ee_len:uint_32 ->
//                           cr13_init:uint_32 -> cr13_len:uint_32 ->
// 			  c13_init:uint_32 -> c13_len:uint_32 ->
// 			  cv_init:uint_32 -> cv_len:uint_32 ->
// 			  fin_init:uint_32 -> fin_len:uint_32 -> flight_t
//   | F_EE_Fin: ee_init:uint_32 -> ee_len:uint_32 ->
//               fin_init:uint_32 -> fin_len:uint_32 -> flight_t
//   | F_Fin: fin_init:uint_32 -> fin_len:uint_32 -> flight_t
//   | F_CH: ch_init:uint_32 -> ch_len:uint_32 -> flight_t
//   | F_CH_Bind: ch_init:uint_32 -> ch_len:uint_32 ->
//                bind_init:uint_32 -> bind_len:uint_32 -> flight_t
//   | F_C13_CV_Fin: c13_init:uint_32 -> c13_len:uint_32 ->
//                   cv_init:uint_32 -> cv_len:uint_32 ->
// 		  fin_init:uint_32 -> fin_len:uint_32 -> flight_t
//   | F_EoED: flight_t
//   | F_NST13: nst13_init:uint_32 -> nst13_len:uint_32 -> flight_t


// /// Current flight that has been dispatched to Handshake but is in the process of being hashed

// val current_flight (st:hsl_state) (h:HS.mem) : GTot flight_t


// type flgithval current_hash_index (st:hsl_state) (h:HS.mem) : GTot uint_32

// /// Framing of current flight, current flight index w.r.t. modifications to local state


// let is_valid_hash_index (st:hsl_state) (i:uint_32) (h:HS.mem) : GTot bool =
//   let flt = current_flight st h in
//   match flt with
//   | F_HRR init len -> i == init + len
//   | _ -> admit ()

// let end_of_flight_index (st:hsl_state) (h:HS.memt) : GTot uint_32 =
//   let flt = current_flight st h in
//   match flt with
//   | F_HRR init len -> init + len
//   | _ -> admit ()


// /// Do we need to provide 

// (*
//  * Separate into two: one that computes hash and one that returns it
//  * Transcript should reflect partial flights that have been hashed
//  * Additional state in HSL to maintain this
//  *)
// val hash (st:hsl_state) (i:uint_32)
//   : ST unit (requires (fun h0 -> is_valid_hash_index st i /\ i > current_hash_index st h))
//             (ensures  (fun h0 _ h1 -> current_hash_index st h1 == i /\ modifies (hsl_local_footprint st) h0 h1 /\
// 	               i == end_of_flight_index st h0 ==>
// 		         (writing h1 st /\
// 			  transcript h1 st == transcript h0 st @ current_hs_flight st h0)))



// // Option a.

// // HSL doesn't care what you hash on the receive side.
// // HS maintains enough invariants to make sure
// // it has hashed the input messages using the ghost messages HSL.receive returned.
// // HS maintains the postcondition that transcript has increased when it calls HSL.hash
// // Generic precondition of calling HSL.hash

// // Pros: helps with binders, can hash in the middle of messages

// // Cons: writing capability maintenance moves to HS for the input flight hashing part, except when HSL is in the middle of reading a flight, HSL switches to writing when it has received a flight

// // hash (i:uint_32) (j:uint_32)
// //      (msgs:erased (list msgs){msgs is parsing of input buffer from i to j})
// //      (* can we make it so that it is not erased (list (erased msg)) *)
// //   : ensures (transcript is appended to by msgs)


// // On the writing side, it is the same--hashing is done by HSL when HS calls HSL.send

// // send (...)
// //   : ensures (transcript is extedned automatically)


// // -- State of hash
// // -- State of incoming flight, what we are trying to receive
// // -- Internal state of HSL is like a tree what all flights can we receive
// // -- Precondition of receive depending on the states
// //    Next kind of flight? Should HSL keep track of it?
// // -- No flight_t and having ad-hoc receive messages


// // Whatever we send is a valid receive flight at the other end?
// // Peer state machine will accept what we send

// #reset-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

// /// TODO: should come from QD


// val hrr_parser : parser_t HSM.hrr
// val sh_parser : parser_t HSM.sh
// val c_parser : parser_t HSM.crt
// val ske_parser : parser_t HSM.ske
// val cr_parser : parser_t HSM.cr

// unfold let valid_parsing (#a:Type) (m:a) (parser:parser_t a) (buf:B.buffer uint_8) (h:HS.mem) =
//   match LP.parse parser (B.as_seq h buf) with
//   | None -> False
//   | Some (parse, consumed) -> parse == m /\ consumed == B.length buf

// unfold let valid_init_and_len (init len:uint_32) (st:hsl_state) =
//   init <= len /\ within_bounds (Unsigned W32) (v init + v len) /\ init + len <= hsl_input_buf_len st  

// /// Predicate for flight being a valid parsing
// /// In addition to this, the postcondition of receive also establishes valid parsing of the transcript itself

// let flight_parsing_of (flt:flight_t) (msgs:hs_transcript) (st:hsl_state) (h:HS.mem) =
//   match flt with
//   | F_HRR init len ->
//     valid_init_and_len init len st /\
//     (match msgs with
//      | [ HSM.HelloRetryRequest r ] -> valid_parsing r hrr_parser (B.gsub (hsl_input_buf st) init len) h
//      | _ -> False)

//   | F_SH init len ->
//     valid_init_and_len init len st /\
//     (match msgs with
//      | [ HSM.ServerHello sh ] -> valid_parsing sh sh_parser (B.gsub (hsl_input_buf st) init len) h
//      | _ -> False)

//   | F_C_SKE_SHD c_init ske_init ske_len ->
//     valid_init_and_len c_init c_len st /\ valid_init_and_len ske_init ske_len st /\
//     (match msgs with
//      | [ HSM.Certificate c; HSM.ServerKeyExchange ske; HSM.ServerHelloDone ] ->
//        valid_parsing c c_parser (B.gsub (hsl_input_buf st) c_init c_len) h /\
//        valid_parsing ske ske_parser (B.gsub (hsl_input_buf st) ske_init ske_len) h
//      | _ -> False)

//   | F_C_SKE_CR_SHD c_init c_len ske_init ske_len cr_init cr_len ->
//     valid_init_and_len c_init c_len st /\ valid_init_and_len ske_init ske_len st /\ valid_init_and_len cr_init cr_len st /\
//     (match msgs with
//      | [ HSM.Certificate c; HSM.ServerKeyExchange ske; HSM.CertificateRequest cr; HSM.ServerHelloDone ] ->
//        valid_parsing c c_parser (B.gsub (hsl_input_buf st) c_init c_len) h /\
//        valid_parsing ske ske_parser (B.gsub (hsl_input_buf st) ske_init ske_len) h /\
//        valid_parsing cr cr_parser (B.gsub (hsl_input_buf st) cr_init cr_len) h
//      | _ -> False)

//   //TODO: fill other entries similarly

//   | _ -> False
       
  
// /// TODO: Should come from QD

// val hs_transcript_parser : LP.parser (LP.strong_parser_kind 8 8 ({ LP.parser_kind_metadata_total = true })) hs_transcript

// (* msgs is parsing of the input sub-buffer between p0 and p1 *)
// unfold private let msg_list_parsing_of (msgs:hs_transcript) (st:hsl_state)
//                                        (p0:uint_32) (p1:uint_32{p0 <= p1 /\ p1 <= hsl_input_buf_len st})
// 			               (h:HS.mem)
//   = let delta = p1 - p0 in
//     let sub = B.gsub (hsl_input_buf st) p0 delta in
//     match LP.parse hs_transcript_parser (B.as_seq h sub) with
//     | None -> False
//     | Some (parse, consumed) -> parse == msgs /\ consumed == v delta

// (*
//  * CF: Remember indices in the input buffer for transcripts
//  *     May be just keep index until t0
//  *     For incremental hashing for t1, keep states in between
//  *     Hashing can be part of the state
//  *     After delivering the flight, and before starting new flight,
//  *       remember where is hashing state (index)
//  *     Also hashing state is just Evercrypt hash state
//  *     Return hash value on the caller stack
//  *     Transcript is the hashed transcript? Add messages to transcrip
//  *       when hashed after call to HS
//  *     HSLog maintains hashed transcript
//  *       and indices for the last flight returned -- so that it can relate Hash calls from HS
//  *)

// (* pair of ints can be computed from flight_t *)
// (* flight_t with indices and erased messages with postconditions for relating them *)


// //TODO: delay the hashing OR Handshake explicitly calls Log to compute the digest 


// /// TODO: receive_CCS


// /// Send API

// /// TODO: should come from QD

// val msg_parser : parser_t msg

// unfold private let msg_parsing_of (m:msg) (st:hsl_state)
//                                   (p0:uint_32) (p1:uint_32{p0 <= p1 /\ p1 <= hsl_output_buf_len st})
// 			          (h:HS.mem)
//   = let delta = p1 - p0 in
//     let sub = B.gsub (hsl_output_buf st) p0 delta in
//     match LP.parse msg_parser (B.as_seq h sub) with
//     | None -> False
//     | Some (parse, consumed) -> parse == m /\ consumed == v delta

// unfold private let send_pre (st:hsl_state) (p:uint_32) (m:G.erased msg)
//   : HS.mem -> Type0
//   = fun h0 ->
//     let open HandshakeMessages in
//     hsl_invariant h0 st /\  //invariant holds
//     hsl_output_index h0 st <= p /\ p <= hsl_output_buf_len st /\  //p is in range of output buffer
//     msg_parsing_of (G.reveal m) st (hsl_output_index h0 st) p h0 /\  //m is a valid parsing of sub-buffer between p0 and p1
//     writing h0 st /\  //Handshake is allowed to write
//     valid_transcript (transcript h0 st @ [G.reveal m]) /\  //valid transcript
//     (match G.reveal m with  //copied from HandshakeLog as is
//      | HelloRetryRequest req -> Some? (C.cipherSuite_of_name req.hrr_cipher_suite)
//      | _ -> True)

// unfold private let send_post (st:hsl_state) (p:uint_32) (m:G.erased msg)
//   : HS.mem -> unit -> HS.mem -> Type0
//   = fun h0 _ h1 ->
//     B.modifies (hsl_local_footprint st) h0 h1 /\  //only local footprint is modified
//     writing h1 st /\  //writing capability remains
//     hash_alg h1 st == hash_alg h0 st /\  //hash algorithm is same as before
//     transcript h1 st == transcript h0 st @ [G.reveal m] /\  //transcript includes m
//     hsl_invariant h1 st /\  //invariant hold
//     hsl_input_index h1 st == hsl_input_index h0 st /\  //input buffer index remains same
//     hsl_output_index h1 st == p  //output buffer index is advanced to p

// val send (st:hsl_state) (p:uint_32) (m:G.erased msg)
//   : ST unit (requires (send_pre st p m))
//             (ensures  (send_post st p m))
		       
// /// hash_tag API

// /// TODO: the postcondition fails to typecheck

// #push-options "--admit_smt_queries true"
// val hash_tag (a:Hash.alg) (st:hsl_state)
//   : ST (Hash.tag a) (requires (fun h0 -> hsl_invariant h0 st))
//                     (ensures  (fun h0 r h1 ->
// 		               let bs = transcript_bytes (transcript h1 st) in
// 			       h0 == h1 /\ Hashing.CRF.hashed a bs /\ r == Hash.h a bs))
// #pop-options
