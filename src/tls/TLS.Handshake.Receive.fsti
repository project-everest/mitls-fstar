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

  Authors: C.Fournet, T. Ramananandro, A. Rastogi, N. Swamy
*)
module TLS.Handshake.Receive

(*
 * This module provides the receive flights functionality to the Handshake
 *)

open FStar.Integers
open FStar.HyperStack.ST

module G = FStar.Ghost
module List = FStar.List.Tot

module HS = FStar.HyperStack
module B = LowStar.Buffer

module LP = LowParse.Low.Base

open HSL.Common

module HSM = HandshakeMessages

module R = MITLS.Repr

module HSM13R = MITLS.Repr.Handshake13
module HSM12R = MITLS.Repr.Handshake12
module HSMR   = MITLS.Repr.Handshake

#reset-options "--max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"


/// HSL main API


/// The interface supports incremental parsing. For example, let's say a client
/// asks for a TLS1.3 flight [EE; Fin]. HSL.Receive successfully parses an EE
/// message but figures that it needs more data (from the other end) to parse the
/// Fin message. In that case, HSL.Receive returns a Some (Correct None) return
/// value, and the client is then supposed to call HSL.Receive again once it has
/// more data.
///
/// For this second call, in incremental parsing, HSL.Receive would only parse the
/// Finished message -- relying on the EE message parsing from the first call.
///
/// However, we need to make sure that the client has not modified the input
/// buffer between the two calls, so that the EE message parsing from the first
/// call remains valid.
///
/// To enforce this, we rely on two stateful, ghost predicates: the in-progress
/// flight, and bytes parsed so far. These two predicates are returned in the
/// postcondition from an incomplete receive flight call, and the client is then
/// expected to provide them as preconditions in the next call.
///
/// The interface provides flexibility to the clients to use different input buffers
/// between such calls -- since the interface only requires bytes parsed so far to remain
/// same, the client can use different buffers, indices, etc., as long as the prefix
/// bytes remain same.
///
/// While the interface is designed to support such incremental parsing, as of 04/22,
/// the implementation is not incremental.

type in_progress_flt_t =
  | F_none
  | F_s_Idle  //server waiting for CH
  | F_c_wait_ServerHello
  | F_c13_wait_Finished1
  | F_s13_wait_Finished2
  | F_s13_wait_EOED
  | F_c13_Complete
  | F_c12_wait_ServerHelloDone
  | F_cs12_wait_Finished
  | F_c12_wait_NST
  | F_s12_wait_CCS1


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


/// State that is framed across framing lemmas

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


/// Creation of an instance

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

/// Common pre- and postcondition for receive functions

unfold
let receive_pre (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32) (in_progress:in_progress_flt_t)
  : HS.mem -> Type0
  = fun h ->
    let open B in let open LP in let open R in 
    
    invariant st h /\

    R.live h b /\
    loc_disjoint (footprint st) (R.loc b) /\
    
    v f_begin + length_parsed_bytes st h <= v f_end /\
    v f_end <= v b.len /\
    
    Seq.equal (Seq.slice (R.as_seq h b)
                         (v f_begin)
                         (v f_begin + length_parsed_bytes st h))
              (parsed_bytes st h) /\

    (in_progress_flt st h == F_none \/ in_progress_flt st h == in_progress)


unfold private
let receive_post
  (#flt:Type)
  (st:hsl_state)
  (b:R.const_slice)
  (f_begin f_end:uint_32)
  (in_progress:in_progress_flt_t)
  (valid:uint_32 -> uint_32 -> flt -> HS.mem -> Type0)
  (h0:HS.mem)
  (x:TLSError.result (option flt))
  (h1:HS.mem)
  = receive_pre st b f_begin f_end in_progress h0 /\
    B.modifies (footprint st) h0 h1 /\
    (let open FStar.Error in
     match x with
     | Error _ -> True
     | Correct None ->
       invariant st h1 /\
       in_progress_flt st h1 == in_progress /\
       parsed_bytes st h1 ==
         Seq.slice (R.as_seq h0 b) (v f_begin) (v f_end)
     | Correct (Some flt) ->
       invariant st h1 /\
       valid f_begin f_end flt h1 /\
       parsed_bytes st h1 == Seq.empty /\
       in_progress_flt st h1 == F_none
     | _ -> False)

unfold private
let receive_post_with_leftover
  (#flt:Type)
  (st:hsl_state)
  (b:R.const_slice)
  (f_begin f_end:uint_32)
  (in_progress:in_progress_flt_t)
  (valid:uint_32 -> uint_32 -> flt -> HS.mem -> Type0)
  (h0:HS.mem)
  (x:TLSError.result (option (flt & uint_32)))
  (h1:HS.mem)
  = receive_pre st b f_begin f_end in_progress h0 /\
    B.modifies (footprint st) h0 h1 /\
    (let open FStar.Error in
     match x with
     | Error _ -> True
     | Correct None ->
       invariant st h1 /\
       in_progress_flt st h1 == in_progress /\
       parsed_bytes st h1 ==
         Seq.slice (R.as_seq h0 b) (v f_begin) (v f_end)
     | Correct (Some (flt, idx_end)) ->
       invariant st h1 /\
       idx_end <= f_end /\  //AR: do we need this?
       valid f_begin idx_end flt h1 /\
       in_progress_flt st h1 == F_none /\
       parsed_bytes st h1 == Seq.empty
     | _ -> False)


/// Error codes returned by the receive functions

let parsing_error : TLSError.error = {
  Parsers.Alert.level = Parsers.AlertLevel.Fatal;
  Parsers.Alert.description = Parsers.AlertDescription.Unexpected_message
}, ""

let unexpected_flight_error : TLSError.error = {
  Parsers.Alert.level = Parsers.AlertLevel.Fatal;
  Parsers.Alert.description = Parsers.AlertDescription.Unexpected_message
}, ""

let unexpected_end_index_error : TLSError.error = {
  Parsers.Alert.level = Parsers.AlertLevel.Fatal;
  Parsers.Alert.description = Parsers.AlertDescription.Unexpected_message
}, ""

/// ad-hoc flight types
/// HS would ask HSL to parse specific flight types, depending on where its own state machine is


/// The receive functions return instances of MITLS.Repr.* types
/// with appropriate valid postconditions
///
/// The flight types contain appropriate refinements to say, for example,
/// that a particular HSM13 repr is EE or Fin
///
/// Other facts such as ranges and (stateful) validity are provided in
/// the postconditions of the receive functions


(*** ClientHello and ServerHello flights ***)


(****** Handshake state S_Idle ******)


/// Handshake state S_Idle expects the following flight
///
/// [ ClientHello ]
///
/// The following flight type covers this case


noeq type s_Idle (b:R.const_slice) = {
  ch_msg : HSMR.ch_repr b
}

let valid_s_Idle
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:s_Idle b) (h:HS.mem)
  = let open R in

    flt.ch_msg.start_pos == f_begin /\
    flt.ch_msg.end_pos == f_end /\

    valid flt.ch_msg h


val receive_s_Idle (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (s_Idle b)))
       (requires receive_pre st b f_begin f_end F_s_Idle)
       (ensures  receive_post st b f_begin f_end F_s_Idle valid_s_Idle)


(****** Handshake state C_wait_ServerHello ******)


/// Handshake state C_wait_ServerHello expects the following flight
///
/// [ ServerHello ]
///
/// The following flight type covers this case

noeq type c_wait_ServerHello (b:R.const_slice) = {
  sh_msg : m:HSMR.sh_repr b
}

let valid_c_wait_ServerHello
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:c_wait_ServerHello b) (h:HS.mem)
  = let open R in

    flt.sh_msg.start_pos == f_begin /\
    flt.sh_msg.end_pos == f_end /\

    valid flt.sh_msg h

(*
 * AR: 07/23: Cedric mentioned that for this flight, the buffer may have leftover bytes
 *            So we should not insist of consuming all the bytes [f_begin, f_end]
 *            In general, since the interface is ad-hoc anyway, we will decide this on a flight-by-flight basis
 *            Also, we don't enforce anything about the flight in the leftover bytes
 *
 *            The receive function then returns the flight and the index upto which the buffer was consumed
 *)

val receive_c_wait_ServerHello (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (c_wait_ServerHello b & uint_32)))
       (requires receive_pre st b f_begin f_end F_c_wait_ServerHello)
       (ensures  receive_post_with_leftover st b f_begin f_end F_c_wait_ServerHello valid_c_wait_ServerHello)


(*** 1.3 flights ***)

/// The receive functions, and the flight types are designed as per the Handshake state

unfold let in_range_and_valid
  (#a:Type0) (#b:R.const_slice) (r:R.repr a b)
  (f_begin f_end:uint_32) (h:HS.mem)
   = let open R in
     f_begin <= r.start_pos /\ r.end_pos <= f_end /\  //in-range
     valid r h  //valid

(****** Handshake state C13_wait_Finished1 ******)

//19-05-28 CF: could we use vale-style metaprogramming on message lists? fine as is. 


/// Handshake state C13_wait_Finished1 expects three flights:
///
/// [ EncryptedExtensions13; Certificate13; CertificateVerify13; Finished13 ]
/// [ EncryptedExtensions13; CertificateRequest13; Certificate13; CertificateVerify13; Finished13 ]
/// [ EncryptedExtensions13; Finished13 ]
///
/// The following type covers all these cases

noeq type c13_wait_Finished1 (b:R.const_slice) = {
  ee_msg   : HSM13R.ee13_repr b;
  cr_msg   : option (HSM13R.cr13_repr b);
  c_cv_msg : option (HSM13R.c13_repr b & HSM13R.cv13_repr b);
  fin_msg  : HSM13R.fin13_repr b
}


/// The validity predicate, such as the following, are underspecified in that
///   they only say that all the messages in the flight are between from and to
///   and don't say that they are actually stitched in order


unfold let valid_c13_wait_Finished1
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:c13_wait_Finished1 b) (h:HS.mem)
  = R.(flt.ee_msg.start_pos == f_begin /\
       flt.fin_msg.end_pos == f_end)   /\  //flight begins at from and finishes at to

    in_range_and_valid flt.ee_msg f_begin f_end h /\
    
    (Some? flt.cr_msg ==> in_range_and_valid (Some?.v flt.cr_msg) f_begin f_end h) /\
    
    (Some? flt.c_cv_msg ==>
      (let c13_msg, cv13_msg = Some?.v flt.c_cv_msg in
       in_range_and_valid c13_msg f_begin f_end h /\
       in_range_and_valid cv13_msg f_begin f_end h)) /\

    in_range_and_valid flt.fin_msg f_begin f_end h


val receive_c13_wait_Finished1
  (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (c13_wait_Finished1 b)))
       (requires receive_pre st b f_begin f_end F_c13_wait_Finished1)
       (ensures  receive_post st b f_begin f_end F_c13_wait_Finished1 valid_c13_wait_Finished1)


(****** Handshake state S13_wait_Finished2 ******)


/// Handshake state S13_wait_Finished2 expects two flights:
///
/// [ Finished13 ]
/// [ Certificate13; CertificateVerify13; Finished13 ]
///
/// The following type covers both these cases


noeq type s13_wait_Finished2 (b:R.const_slice) = {
  c_cv_msg : option (HSM13R.c13_repr b & HSM13R.cv13_repr b);
  fin_msg  : HSM13R.fin13_repr b
}

unfold let valid_s13_wait_Finished2
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:s13_wait_Finished2 b) (h:HS.mem)
  = match flt.c_cv_msg with
    | Some (c_msg, cv_msg) ->
      R.(c_msg.start_pos == f_begin    /\
         flt.fin_msg.end_pos == f_end) /\

      in_range_and_valid c_msg f_begin f_end h /\

      in_range_and_valid cv_msg f_begin f_end h /\

      in_range_and_valid flt.fin_msg f_begin f_end h

    | None ->
      R.(flt.fin_msg.start_pos == f_begin /\
         flt.fin_msg.end_pos   == f_end)  /\

      in_range_and_valid flt.fin_msg f_begin f_end h

val receive_s13_wait_Finished2 (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (s13_wait_Finished2 b)))
       (requires receive_pre st b f_begin f_end F_s13_wait_Finished2)
       (ensures  receive_post st b f_begin f_end F_s13_wait_Finished2 valid_s13_wait_Finished2)


(****** Handshake state S13_wait_EOED ******)


/// Handshake state S13_wait_EOED expects
///
/// [ EndOfEarlyData13 ]
///
/// The following flight type covers this


noeq type s13_wait_EOED (b:R.const_slice) = {
  eoed_msg : HSM13R.eoed13_repr b
}


let valid_s13_wait_EOED
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:s13_wait_EOED b) (h:HS.mem)
  = let open R in

    flt.eoed_msg.start_pos == f_begin /\
    flt.eoed_msg.end_pos == f_end     /\

    valid flt.eoed_msg h

val receive_s13_wait_EOED (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (s13_wait_EOED b)))
       (requires receive_pre st b f_begin f_end F_s13_wait_EOED)
       (ensures  receive_post st b f_begin f_end F_s13_wait_EOED valid_s13_wait_EOED)


(****** Handshake state C13_Complete ******)


/// Handshake state C13_Complete expects
///
/// [ NewSessionTicket13 ]
///
/// The following flight type covers this


noeq type c13_Complete (b:R.const_slice) = {
  nst_msg : HSM13R.nst13_repr b
}


let valid_c13_Complete
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:c13_Complete b) (h:HS.mem)
  = let open R in

    flt.nst_msg.start_pos == f_begin /\
    flt.nst_msg.end_pos == f_end     /\

    valid flt.nst_msg h

val receive_c13_Complete (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (c13_Complete b)))
       (requires receive_pre st b f_begin f_end F_c13_Complete)
       (ensures  receive_post st b f_begin f_end F_c13_Complete valid_c13_Complete)


(*** 1.2 flights ***)


(****** Handshake state C12_wait_ServerHelloDone ******)


/// Handshake state C12_wait_ServerHelloDone expects two flights
///
/// [ Certificate12; ServerKeyExchange12; ServerHelloDone12 ]
/// [ Certificate12; ServerKeyExchange12; CertificateRequest12; ServerHelloDone12 ]
///
/// The following flight type covers both these cases


noeq type c12_wait_ServerHelloDone (b:R.const_slice) = {
  c_msg   : HSM12R.c12_repr b;
  ske_msg : HSM12R.ske12_repr b;
  cr_msg  : option (HSM12R.cr12_repr b);
  shd_msg : HSM12R.shd12_repr b
}

let valid_c12_wait_ServerHelloDone
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:c12_wait_ServerHelloDone b) (h:HS.mem)
  = R.(flt.c_msg.start_pos == f_begin /\
       flt.shd_msg.end_pos == f_end)  /\

    in_range_and_valid flt.c_msg f_begin f_end h /\

    in_range_and_valid flt.ske_msg f_begin f_end h /\

    (Some? flt.cr_msg ==> in_range_and_valid (Some?.v flt.cr_msg) f_begin f_end h) /\

    in_range_and_valid flt.shd_msg f_begin f_end h
  

val receive_c12_wait_ServerHelloDone (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (c12_wait_ServerHelloDone b)))
       (requires receive_pre st b f_begin f_end F_c12_wait_ServerHelloDone)
       (ensures  receive_post st b f_begin f_end F_c12_wait_ServerHelloDone valid_c12_wait_ServerHelloDone)


(****** Handshake states C12_wait_Finished2, C12_wait_R_Finished1, S12_wait_Finished1, and S12_wait_CF2 ******)


/// All the above mentioned Handshake states expect the following flight
///
/// [ Finished12 ]
///
/// The following flight type covers this case


noeq type cs12_wait_Finished (b:R.const_slice) = {
  fin_msg : HSM12R.fin12_repr b
}


let valid_cs12_wait_Finished
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:cs12_wait_Finished b) (h:HS.mem)
  = let open R in

    flt.fin_msg.start_pos == f_begin /\
    flt.fin_msg.end_pos == f_end /\

    valid flt.fin_msg h


val receive_cs12_wait_Finished (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (cs12_wait_Finished b)))
       (requires receive_pre st b f_begin f_end F_cs12_wait_Finished)
       (ensures  receive_post st b f_begin f_end F_cs12_wait_Finished valid_cs12_wait_Finished)


(****** Handshake state C12_wait_NST ******)


/// Handshake state C12_wait_NST expects the following flight
///
/// [ NewSessionticket12 ]
///
/// The following flight type covers this case

noeq type c12_wait_NST (b:R.const_slice) = {
  nst_msg : HSM12R.nst12_repr b
}


let valid_c12_wait_NST
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:c12_wait_NST b) (h:HS.mem)
  = let open R in

    flt.nst_msg.start_pos == f_begin /\

    flt.nst_msg.end_pos == f_end /\

    valid flt.nst_msg h


val receive_c12_wait_NST (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (c12_wait_NST b)))
       (requires receive_pre st b f_begin f_end F_c12_wait_NST)
       (ensures  receive_post st b f_begin f_end F_c12_wait_NST valid_c12_wait_NST)



(****** Handshake state S12_wait_CCS1 ******)


/// Handshake state S12_wait_CCS1 expects the following flight
///
/// [ ClientKeyExchange12 ]
///
/// The following flight type covers this case


noeq type s12_wait_CCS1 (b:R.const_slice) = {
  cke_msg : HSM12R.cke12_repr b
}


let valid_s12_wait_CCS1
  (#b:R.const_slice) (f_begin f_end:uint_32)
  (flt:s12_wait_CCS1 b) (h:HS.mem)
  = let open R in

    flt.cke_msg.start_pos == f_begin /\
    flt.cke_msg.end_pos == f_end /\

    valid flt.cke_msg h


val receive_s12_wait_CCS1 (st:hsl_state) (b:R.const_slice) (f_begin f_end:uint_32)
  : ST (TLSError.result (option (s12_wait_CCS1 b)))
       (requires receive_pre st b f_begin f_end F_s12_wait_CCS1)
       (ensures  receive_post st b f_begin f_end F_s12_wait_CCS1 valid_s12_wait_CCS1)




// /// Stub that will remain in HandshakeLog.state, at least for now,
// /// replacing {incoming, parsed, hashes}. It may actually be
// /// convenient for each of the receive functions and conditions above
// /// to take the same struct as input instead of 4 parameters.

// noeq type receive_state = { 
//     st: hsl_state; 
//     input: R.const_slice; // large enough in practice; TODO not const! 
//     from: UInt32.t;
//     to: UInt32.t; // both within the slice 
//     // with invariant framed on input
//     // with state disjoint from input and everything else
//     }

// let receive f s = f s.st s.input s.from s.to 

//type receive_t flt flight valid_flight = 
//  s:receive_state -> 
//  ST (TLSError.result (option (flight s.input)))
//    (requires receive_pre s.st s.input s.from s.to F_sh)
//    (ensures receive_post s.st s.input s.from s.to F_sh valid_flight)


// TODO code for storing high-level bytes received through the HS
// interface into [input], between [to] and the end of the slice.

// TODO code for updating from..to based on Receive result and
// processing within Handshake.

// TODO write sample code bridging high-level HS and low-level
// receive, e.g. calling parse32 on the received flights and computing
// a few tags before calling the functions on the rhs of the patterns
// at the end of Old.Handshake.
