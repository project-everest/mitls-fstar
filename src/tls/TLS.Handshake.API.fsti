module TLS.Handshake.API

open Mem
open TLSConstants

module Send = TLS.Handshake.Send
module Recv = TLS.Handshake.Receive
module PF = TLS.Handshake.ParseFlights
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module I = Crypto.Indexing
module EE = EverCrypt.Error

unfold type uint8_p = B.buffer UInt8.t
unfold type uint32_t = UInt32.t
unfold type uint32_p = B.pointer uint32_t
unfold type uint16_t = UInt16.t

// CEnum
type early_data_status =
| OMITTED  // the client won't send early data
| PROPOSED // the client is sending early data
| ACCEPTED // ... and the server is receiving it
| REJECTED // ... but the server will ignore it

// CEnum
type traffic_secret_epoch =
| INITIAL     // unprotected Hello messages
| EARLY       // early application data (only client --> server)
| HANDSHAKE   // handshake messages only
| APPLICATION // open connection (application + late handshake)

// Calling convention
// ----------------------------
// The input buffer is associated to the reader epoch at the start of the call
// The output buffer is also associated with the writer epoch at the start,
// if the writer epoch is updated, the data in the previous epoch's
// buffer must be fully sent before the next call

noeq type hs_ctx = {
  // Reading buffer for handshake messages
  // (const buffer, not written by handshake)
  in_epoch: traffic_secret_epoch;
  in_buffer: uint8_p;
  in_buffer_len: uint32_t; // input only
  in_buffer_pos: uint32_t; // input/output

  // Writing buffer for handshake messages
  out_epoch: traffic_secret_epoch;
  out_buffer: uint8_p; // write only
  out_buffer_len: uint32_t; // read only
  out_buffer_pos: uint32_t; // input/output

  // Output values
  early_cipher_suite: uint16_t; // assigned before EARLY
  cipher_suite: uint16_t;       // assigned before HANDSHAKE
  secrets: uint8_p;             // assigned before advancing epoch
  early_data: early_data_status;// see state machine above
  error_msg: C.String.t; // uint_p, assigned before returning a fatal alert description as result.
}

// Can send application data
let is_writable (ctx:hs_ctx) =
  (ctx.out_epoch = EARLY && ctx.early_data <> REJECTED)
  || ctx.out_epoch = APPLICATION

// 1 RTT
let is_complete (ctx:hs_ctx) =
  ctx.in_epoch = APPLICATION && ctx.out_epoch = APPLICATION

// 0.5 RTT
let is_half_complete (ctx:hs_ctx) =
  ctx.out_epoch = APPLICATION && ctx.in_epoch = HANDSHAKE

let live_ctx h ctx =
  B.live h ctx.in_buffer

let disjoint_ctx ctx =
  B.all_disjoint [
    B.loc_buffer ctx.in_buffer;
    B.loc_buffer ctx.out_buffer;
    B.loc_buffer ctx.secrets
  ]

let valid_ctx (m:HS.mem) ctx =
  let open FStar.Integers in
  UInt32.v ctx.in_buffer_len <= B.length ctx.in_buffer /\
  ctx.in_buffer_pos < ctx.in_buffer_len /\
  UInt32.v ctx.out_buffer_len <= B.length ctx.out_buffer /\
  ctx.out_buffer_pos < ctx.out_buffer_len /\
  B.length ctx.secrets == 324

[@CAbstractStruct]
val state_s: Type0

let state = B.pointer state_s

val footprint_s: HS.mem -> state_s -> GTot (l:B.loc{
  B.loc_all_regions_from true tls_region `B.loc_includes` l})
let footprint (m: HS.mem) (s: state) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s m (B.deref m s)))

let loc_includes_union_l_footprint_s
  (m: HS.mem) (l1 l2: B.loc) (s: state_s)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s m s) \/ B.loc_includes l2 (footprint_s m s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s m s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s m s))]
= B.loc_includes_union_l l1 l2 (footprint_s m s)

/// Ghost accessors (not needing the invariant)
/// -------------------------------------------
val g_current_index: s: state_s -> HS.mem -> I.id

val g_state: s:state_s -> HS.mem -> TLSError.result unit // (TLS.Handshake.Machine.state)

/// Invariant
/// ---------

val invariant_s: HS.mem -> state_s -> Type0
let invariant (m: HS.mem) (s: state) =
  let r = B.frameOf s in
  ST.is_eternal_region r /\
  B.loc_includes (B.loc_region_only true r) (footprint m s) /\
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s m (B.deref m s))) /\
  invariant_s m (B.get m s 0)

val invariant_loc_in_footprint (s:state) (m:HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]

val frame_invariant: l:B.loc -> s:state -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures invariant h1 s /\ footprint h0 s == footprint h1 s)
  [ SMTPatOr [
    [ SMTPat (B.modifies l h0 h1); SMTPat (invariant h1 s) ];
    [ SMTPat (B.modifies l h0 h1); SMTPat (footprint h1 s) ];
  ]]


/// Actual stateful API
/// -------------------

val create: r:HS.rid -> cfg:config ->
  dst: B.pointer (B.pointer_or_null state_s) ->
  ST EE.error_code
    (requires fun h0 ->
      B.g_is_null dst /\
      ST.is_eternal_region r /\
      B.live h0 dst)
    (ensures fun h0 e h1 ->
      match e with
      | EE.DecodeError // Invalid configuration
      | EE.AuthenticationFailure -> // Sealing failure
          B.(modifies loc_none h0 h1)
      | EE.Success ->
          let s = B.deref h1 dst in
          not (B.g_is_null s) /\
          invariant h1 s /\
          B.(modifies (loc_buffer dst) h0 h1) /\
          B.fresh_loc (footprint h1 s) h0 h1
      | _ -> False)

val process: st:state ->
  ctx: B.pointer hs_ctx ->
  ST UInt16.t
  (requires fun h0 -> B.live h0 ctx /\
    (let ctx = B.deref h0 ctx in
    disjoint_ctx ctx /\
    live_ctx h0 ctx /\
    valid_ctx h0 ctx /\
    invariant h0 st
  ))
  (ensures fun h0 r h1 ->
    B.modifies (footprint h1 st `B.loc_union` B.loc_buffer ctx) h0 h1 /\
    (let s = B.deref h1 st in
    let ctx' = B.deref h1 ctx in
    if r = 0us then (
      invariant h1 st /\
      valid_ctx h1 ctx' /\
      live_ctx h1 ctx'
    ) else (
      match g_state s h1 with
      | TLSError.Error e -> True
      | _ -> False
    ))
  )
