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
/// Until a full flight is received, we lose "writing" capability -- as per the comment in HandshakeLog

/// ad-hoc flight types
/// HS would ask HSL to parse specific flight types, depending on where its own state machine is

type b8 = B.buffer uint_8

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

let valid_parsing13
  (msg:HSM13.handshake13)
  (from to:uint_32)
  (buf:b8{from <= to /\ B.len buf == to - from})
  (h:HS.mem)
  = let parser = HSM13.handshake13_parser in
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
   
   valid_parsing13 (HSM13.M_encrypted_extensions (G.reveal flt.ee_msg)) flt.begin_ee flt.begin_fin ee_buf h /\
   valid_parsing13 (HSM13.M_finished (G.reveal flt.fin_msg)) flt.begin_fin flight_end fin_buf h)

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

