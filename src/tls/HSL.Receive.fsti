(*
  Copyright 2015--2019 INRIA and Microsoft Corporation

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to_ in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

  Authors: C.Fournet, T. Ramananandro, A. Rastogi, N. Swamy
*)
module HSL.Receive

(*
 * This module provides the receive flights functionality to_ the Handshake
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
/// message but figures that it needs more data (from the other end) to_ parse the
/// Fin message. In that case, HSL.Receive returns a Some (Correct None) return
/// value, and the client is then supposed to_ call HSL.Receive again once it has
/// more data.
///
/// For this second call, in incremental parsing, HSL.Receive would only parse the
/// Finished message -- relying on the EE message parsing from the first call.
///
/// However, we need to_ make sure that the client has not modified the input
/// buffer between the two calls, so that the EE message parsing from the first
/// call remains valid.
///
/// To_ enforce this, we rely on two stateful, ghost predicates: the in-progress
/// flight, and bytes parsed so far. These two predicates are returned in the
/// postcondition from an incomplete receive flight call, and the client is then
/// expected to_ provide them as preconditions in the next call.
///
/// The interface provides flexibility to_ the clients to_ use different input buffers
/// between such calls -- since the interface only requires bytes parsed so far to remain
/// same, the client can use different buffers, indices, etc., as long as the prefix
/// bytes remain same.
///
/// While the interface is designed to_ support such incremental parsing, as of 04/22,
/// the implementation is not incremental.

type in_progress_flt_t =
  | F_none
  | F13_ee_c_cv_fin
  | F13_ee_cr_c_cv_fin
  | F13_ee_fin
  | F13_fin
  | F13_c_cv_fin
  | F13_eoed
  | F13_nst
  | F12_c_ske_shd
  | F12_c_ske_cr_shd
  | F12_fin
  | F12_nst
  | F12_cke
  | F_ch
  | F_sh


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
let receive_pre (st:hsl_state) (b:R.const_slice) (from to_:uint_32) (in_progress:in_progress_flt_t)
  : HS.mem -> Type0
  = fun h ->
    let open B in let open LP in let open R in 
    
    invariant st h /\

    R.live h b /\
    loc_disjoint (footprint st) (R.loc b) /\
    
    v from + length_parsed_bytes st h <= v to_ /\
    v to_ <= v b.len /\
    
    Seq.equal (Seq.slice (R.as_seq h b)
                         (v from)
                         (v from + length_parsed_bytes st h))
              (parsed_bytes st h) /\

    (in_progress_flt st h == F_none \/ in_progress_flt st h == in_progress)


unfold private
let receive_post
  (#flt:Type)
  (st:hsl_state)
  (b:R.const_slice)
  (from to_:uint_32)
  (in_progress:in_progress_flt_t)
  (valid:uint_32 -> uint_32 -> flt -> HS.mem -> Type0)
  (h0:HS.mem)
  (x:TLSError.result (option flt))
  (h1:HS.mem)
  = receive_pre st b from to_ in_progress h0 /\
    B.modifies (footprint st) h0 h1 /\
    (let open FStar.Error in
     match x with
     | Error _ -> True
     | Correct None ->
       in_progress_flt st h1 == in_progress /\
       parsed_bytes st h1 ==
         Seq.slice (R.as_seq h0 b) (v from) (v to_)
     | Correct (Some flt) ->
       valid from to_ flt h1 /\
       parsed_bytes st h1 == Seq.empty /\
       in_progress_flt st h1 == F_none
     | _ -> False)


/// ad-hoc flight types
/// HS would ask HSL to_ parse specific flight types, depending on where its own state machine is


/// The receive functions return instances of MITLS.Repr.* types
/// with appropriate valid postconditions
///
/// The flight types contain appropriate refinements to_ say, for example,
/// that a particular HSM13 repr is EE or Fin
///
/// Other facts such as stitched indices and (stateful) validity are provided in
/// the postconditions of the receive functions


(*** 1.3 flights ***)


(****** Flight [ EncryptedExtensions; Certificate13; CertificateVerify; Finished ] ******)

//19-05-28 could we use vale-style metaprogramming on message lists? fine as is. 


noeq
type flight13_ee_c_cv_fin (b:R.const_slice) = {
  ee_msg  : HSM13R.repr b;
  c_msg   : HSM13R.repr b;
  cv_msg  : HSM13R.repr b;
  fin_msg : m:HSM13R.repr b{
    HSM13R.is_ee ee_msg /\
    HSM13R.is_c c_msg /\
    HSM13R.is_cv cv_msg /\
    HSM13R.is_fin m
  }
}

//19-05-28 why not refining each message individually? or have a
// function from tags to_ those refined types? such type abbreviations
// may be useful additions to_ their repr modules, e.g.
// 
type ee_repr b  = m:HSM13R.repr b { HSM13R.is_ee m }
type cr_repr b  = m:HSM13R.repr b { HSM13R.is_cr m } 
type c_repr b   = m:HSM13R.repr b { HSM13R.is_c m } 
type cv_repr b  = m:HSM13R.repr b { HSM13R.is_cv m } 
type fin_repr b = m:HSM13R.repr b { HSM13R.is_fin m } 
// (those could be defined in HSM13R)
// now covering all 3 variants of this flight (and a 4th one, which we may support later)
noeq type c13_Finished1 b = {
  ee: ee_repr b;
  cr: option (cr_repr b); 
  ccv: option (c_repr b & cv_repr b);
  fin: fin_repr b;
}  


//19-05-28 the handshake may not need the position details; the only
// thing that matters is that all messages are within from..to_.

unfold let valid_flight13_ee_c_cv_fin
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight13_ee_c_cv_fin b) (h:HS.mem)
  = let open R in  
  
    flt.ee_msg.start_pos == from /\
    flt.ee_msg.end_pos == flt.c_msg.start_pos /\
    flt.c_msg.end_pos == flt.cv_msg.start_pos /\
    flt.cv_msg.end_pos == flt.fin_msg.start_pos /\
    flt.fin_msg.end_pos == to_ /\
  
    valid flt.ee_msg h /\
    valid flt.c_msg h /\
    valid flt.cv_msg h /\
    valid flt.fin_msg h

// c13_wait_Finished1 for all 3 ee...fin
val receive_flight13_ee_c_cv_fin
  (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight13_ee_c_cv_fin b)))
       (requires receive_pre st b from to_ F13_ee_c_cv_fin)
       (ensures  receive_post st b from to_ F13_ee_c_cv_fin valid_flight13_ee_c_cv_fin)


(****** Flight [EncryptedExtensions; Certificaterequest13; Certificate13; CertificateVerify; Finished ] ******)

noeq
type flight13_ee_cr_c_cv_fin (b:R.const_slice) = {
  ee_msg  : HSM13R.repr b;
  cr_msg  : HSM13R.repr b;
  c_msg   : HSM13R.repr b;
  cv_msg  : HSM13R.repr b;
  fin_msg : m:HSM13R.repr b{
    HSM13R.is_ee ee_msg /\
    HSM13R.is_cr cr_msg /\
    HSM13R.is_c c_msg /\
    HSM13R.is_cv cv_msg /\
    HSM13R.is_fin m
  }
}


unfold let valid_flight13_ee_cr_c_cv_fin
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight13_ee_cr_c_cv_fin b) (h:HS.mem)
  = let open R in

    flt.ee_msg.start_pos == from /\
    flt.ee_msg.end_pos == flt.cr_msg.start_pos /\
    flt.cr_msg.end_pos == flt.c_msg.start_pos /\
    flt.c_msg.end_pos == flt.cv_msg.start_pos /\
    flt.cv_msg.end_pos == flt.fin_msg.start_pos /\
    flt.fin_msg.end_pos == to_ /\

    valid flt.ee_msg h /\
    valid flt.cr_msg h /\
    valid flt.c_msg h /\
    valid flt.cv_msg h /\
    valid flt.fin_msg h

val receive_flight13_ee_cr_c_cv_fin
  (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight13_ee_cr_c_cv_fin b)))
       (requires receive_pre st b from to_ F13_ee_cr_c_cv_fin)
       (ensures  receive_post st b from to_ F13_ee_cr_c_cv_fin valid_flight13_ee_cr_c_cv_fin)


(****** Flight [EncryptedExtensions; Finished] ******)

noeq
type flight13_ee_fin (b:R.const_slice) = {
  ee_msg  : HSM13R.repr b;
  fin_msg : m:HSM13R.repr b{
    HSM13R.is_ee ee_msg /\
    HSM13R.is_fin m
  }
}

let valid_flight13_ee_fin
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight13_ee_fin b) (h:HS.mem)
  = let open R in

    flt.ee_msg.start_pos == from /\
    flt.ee_msg.end_pos == flt.fin_msg.start_pos /\
    flt.fin_msg.end_pos == to_ /\

    valid flt.ee_msg h /\
    valid flt.fin_msg h

val receive_flight13_ee_fin (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight13_ee_fin b)))
       (requires receive_pre st b from to_ F13_ee_fin)
       (ensures  receive_post st b from to_ F13_ee_fin valid_flight13_ee_fin)


(****** Flight [ Finished13 ] ******)

noeq
type flight13_fin (b:R.const_slice) = {
  fin_msg : m:HSM13R.repr b{HSM13R.is_fin m}
}


let valid_flight13_fin
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight13_fin b) (h:HS.mem)
  = let open R in

    flt.fin_msg.start_pos == from /\
    flt.fin_msg.end_pos == to_ /\

    valid flt.fin_msg h

// s13_wait_Finished2 (with a second case below)
val receive_flight13_fin (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight13_fin b)))
       (requires receive_pre st b from to_ F13_fin)
       (ensures  receive_post st b from to_ F13_fin valid_flight13_fin)


(****** Flight [ Certificate13; CertificateVerify; Finished ] ******)

noeq
type flight13_c_cv_fin (b:R.const_slice) = {
  c_msg   : HSM13R.repr b;
  cv_msg  : HSM13R.repr b;
  fin_msg : m:HSM13R.repr b{
    HSM13R.is_c c_msg /\
    HSM13R.is_cv cv_msg /\
    HSM13R.is_fin m
  }
}


let valid_flight13_c_cv_fin
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight13_c_cv_fin b) (h:HS.mem)
  = let open R in

    flt.c_msg.start_pos == from /\
    flt.c_msg.end_pos == flt.cv_msg.start_pos /\
    flt.cv_msg.end_pos == flt.fin_msg.start_pos /\
    flt.fin_msg.end_pos == to_ /\

    valid flt.c_msg h /\
    valid flt.cv_msg h /\
    valid flt.fin_msg h

val receive_flight13_c_cv_fin
  (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight13_c_cv_fin b)))
       (requires receive_pre st b from to_ F13_c_cv_fin)
       (ensures  receive_post st b from to_ F13_c_cv_fin valid_flight13_c_cv_fin)


(****** Flight [ EndOfEarlyData ] ******)

noeq
type flight13_eoed (b:R.const_slice) = {
  eoed_msg : m:HSM13R.repr b{HSM13R.is_eoed m}
}


let valid_flight13_eoed
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight13_eoed b) (h:HS.mem)
  = let open R in

    flt.eoed_msg.start_pos == from /\
    flt.eoed_msg.end_pos == to_ /\

    valid flt.eoed_msg h

// s13_wait_EOED
val receive_flight13_eoed (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight13_eoed b)))
       (requires receive_pre st b from to_ F13_eoed)
       (ensures  receive_post st b from to_ F13_eoed valid_flight13_eoed)


(****** Flight [ NewSessionTicket13 ] ******)

noeq
type flight13_nst (b:R.const_slice) = {
  nst_msg : m:HSM13R.repr b{HSM13R.is_nst m}
}


let valid_flight13_nst
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight13_nst b) (h:HS.mem)
  = let open R in

    flt.nst_msg.start_pos == from /\
    flt.nst_msg.end_pos == to_ /\

    valid flt.nst_msg h

// c13_complete 
val receive_flight13_nst (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight13_nst b)))
       (requires receive_pre st b from to_ F13_nst)
       (ensures  receive_post st b from to_ F13_nst valid_flight13_nst)


(*** 1.2 flights ***)


(****** Flight [ Certificate12; ServerKeyExchange12; ServerHelloDone12 ] ******)

noeq
type flight12_c_ske_shd (b:R.const_slice) = {
  c_msg   : HSM12R.repr b;
  ske_msg : HSM12R.repr b;
  shd_msg : m:HSM12R.repr b{
    HSM12R.is_c c_msg /\
    HSM12R.is_ske ske_msg /\
    HSM12R.is_shd m
  }
}


let valid_flight12_c_ske_shd
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight12_c_ske_shd b) (h:HS.mem)
  = let open R in

    flt.c_msg.start_pos == from /\
    flt.c_msg.end_pos == flt.ske_msg.start_pos /\
    flt.ske_msg.end_pos == flt.shd_msg.start_pos /\
    flt.shd_msg.end_pos == to_ /\

    valid flt.c_msg h /\
    valid flt.ske_msg h /\
    valid flt.shd_msg h

// c12_wait_ServerHelloDone (2 variants)
val receive_flight12_c_ske_shd (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight12_c_ske_shd b)))
       (requires receive_pre st b from to_ F12_c_ske_shd)
       (ensures  receive_post st b from to_ F12_c_ske_shd valid_flight12_c_ske_shd)


(****** Flight [ Certificate12; ServerKeyExchange12; CertificateRequest12; ServerHelloDone12 ] ******)

noeq
type flight12_c_ske_cr_shd (b:R.const_slice) = {
  c_msg   : HSM12R.repr b;
  ske_msg : HSM12R.repr b;
  cr_msg  : HSM12R.repr b;
  shd_msg : m:HSM12R.repr b{
    HSM12R.is_c c_msg /\
    HSM12R.is_ske ske_msg /\
    HSM12R.is_cr cr_msg /\
    HSM12R.is_shd m
  }
}


let valid_flight12_c_ske_cr_shd
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight12_c_ske_cr_shd b) (h:HS.mem)
  = let open R in

    flt.c_msg.start_pos == from /\
    flt.c_msg.end_pos == flt.ske_msg.start_pos /\
    flt.ske_msg.end_pos == flt.cr_msg.start_pos /\
    flt.cr_msg.end_pos == flt.shd_msg.start_pos /\
    flt.shd_msg.end_pos == to_ /\

    valid flt.c_msg h /\
    valid flt.ske_msg h /\
    valid flt.cr_msg h /\
    valid flt.shd_msg h

val receive_flight12_c_ske_cr_shd (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight12_c_ske_cr_shd b)))
       (requires receive_pre st b from to_ F12_c_ske_cr_shd)
       (ensures  receive_post st b from to_ F12_c_ske_cr_shd valid_flight12_c_ske_cr_shd)


(****** Flight [ Finished12 ] ******)

noeq
type flight12_fin (b:R.const_slice) = {
  fin_msg : m:HSM12R.repr b{HSM12R.is_fin m}
}


let valid_flight12_fin
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight12_fin b) (h:HS.mem)
  = let open R in

    flt.fin_msg.start_pos == from /\
    flt.fin_msg.end_pos == to_ /\

    valid flt.fin_msg h

// c12_wait_Finished [used for both Finished1 and Finished2]
val receive_flight12_fin (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight12_fin b)))
       (requires receive_pre st b from to_ F12_fin)
       (ensures  receive_post st b from to_ F12_fin valid_flight12_fin)


(****** Flight [ NewSessionTicket12 ] ******)

noeq
type flight12_nst (b:R.const_slice) = {
  nst_msg : m:HSM12R.repr b{HSM12R.is_nst m}
}


let valid_flight12_nst
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight12_nst b) (h:HS.mem)
  = let open R in

    flt.nst_msg.start_pos == from /\
    flt.nst_msg.end_pos == to_ /\

    valid flt.nst_msg h

// c12_wait_NewSessionTicket 
val receive_flight12_nst (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight12_nst b)))
       (requires receive_pre st b from to_ F12_nst)
       (ensures  receive_post st b from to_ F12_nst valid_flight12_nst)

(****** Flight [ ClientKeyExchange12 ] ******)

noeq
type flight12_cke (b:R.const_slice) = {
  cke_msg : m:HSM12R.repr b{HSM12R.is_cke m}
}


let valid_flight12_cke
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight12_cke b) (h:HS.mem)
  = let open R in

    flt.cke_msg.start_pos == from /\
    flt.cke_msg.end_pos == to_ /\

    valid flt.cke_msg h

// s12_wait_ClientKeyExchange 
// note the HS should wait for CCS1 before accepting this message.

val receive_flight12_cke (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight12_cke b)))
       (requires receive_pre st b from to_ F12_cke)
       (ensures  receive_post st b from to_ F12_cke valid_flight12_cke)


(*** ClientHello and ServerHello flights ***)


(****** Flight [ ClientHello ] ******)


noeq
type flight_ch (b:R.const_slice) = {
  ch_msg : m:HSMR.repr b{HSMR.is_ch m}
}

let valid_flight_ch
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight_ch b) (h:HS.mem)
  = let open R in

    flt.ch_msg.start_pos == from /\
    flt.ch_msg.end_pos == to_ /\

    valid flt.ch_msg h

// s_wait_ClientHello 
val receive_flight_ch (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight_ch b)))
       (requires receive_pre st b from to_ F_ch)
       (ensures  receive_post st b from to_ F_ch valid_flight_ch)


(****** Flight [ ServerHello ] ******)


noeq
type flight_sh (b:R.const_slice) = {
  sh_msg : m:HSMR.repr b{HSMR.is_sh m}
}

let valid_flight_sh
  (#b:R.const_slice) (from to_:uint_32)
  (flt:flight_sh b) (h:HS.mem)
  = let open R in

    flt.sh_msg.start_pos == from /\
    flt.sh_msg.end_pos == to_ /\

    valid flt.sh_msg h

// c_wait_ServerHello 
val receive_flight_sh (st:hsl_state) (b:R.const_slice) (from to_:uint_32)
  : ST (TLSError.result (option (flight_sh b)))
       (requires receive_pre st b from to_ F_sh)
       (ensures  receive_post st b from to_ F_sh valid_flight_sh)



/// Stub that will remain in HandshakeLog.state, at least for now,
/// replacing {incoming, parsed, hashes}. It may actually be
/// convenient for each of the receive functions and conditions above
/// to_ take the same struct as input instead of 4 parameters.

noeq type receive_state = { 
    st: hsl_state; 
    input: R.const_slice; // large enough in practice; TODO not const! 
    from: UInt32.t;
    to_: UInt32.t; // both within the slice 
    // with invariant framed on input
    // with state disjoint from input and everything else
    }

let receive f s = f s.st s.input s.from s.to_ 

//type receive_t flt flight valid_flight = 
//  s:receive_state -> 
//  ST (TLSError.result (option (flight s.input)))
//    (requires receive_pre s.st s.input s.from s.to_ F_sh)
//    (ensures receive_post s.st s.input s.from s.to_ F_sh valid_flight)


// TODO code for storing high-level bytes received through the HS
// interface into_ [input], between [to_] and the end of the slice.

// TODO code for updating from..to_ based on Receive result and
// processing within Handshake.

// TODO write sample code bridging high-level HS and low-level
// receive, e.g. calling parse32 on the received flights and computing
// a few tags before calling the functions on the rhs of the patterns
// at the end of Old.Handshake.

