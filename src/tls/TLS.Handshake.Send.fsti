module TLS.Handshake.Send

/// Adding an interface to hoist definitions from HandshakeLog.fsti

module Transcript = HSL.Transcript

module HSM = HandshakeMessages

type msg =
| Msg of HSM.handshake
| Msg12 of HSM.handshake12
| Msg13 of HSM.handshake13

let tag_of = function
| Msg h -> HSM.tag_of_handshake h
| Msg12 h -> HSM.tag_of_handshake12 h
| Msg13 h -> HSM.tag_of_handshake13 h

let msg_bytes = function
| Msg h -> HSM.handshake_serializer32 h
| Msg12 h -> HSM.handshake12_serializer32 h
| Msg13 h -> HSM.handshake13_serializer32 h

// FRAGMENT INTERFACE
//
// for outgoing messages, Handshake.Log maintains
// - an output buffer (bytes) for handshake messages
// - the three flags below, to be echoed and cleared once the buffer is empty

type id = TLSInfo.id

module Range = Range // for now
open Range

// payload of a handshake fragment, to be made opaque eventually
type fragment (i:id) = ( rg: frange i & rbytes rg )
//let out_msg i rg b : msg i = (|rg, b|)

type next_keys_use = {
  out_appdata  : bool; // the new key enables sending AppData fragments
  out_ccs_first: bool; // send a CCS fragment *before* installing the new key
  out_skip_0RTT: bool; // skip void server-to-client 0RTT epoch
}

// What the HS asks the record layer to do, in that order.
type outgoing (i:id) (* initial index *) =
  | Outgoing:
      send_first: option (fragment i)  -> // HS fragment to be sent (using the current id)
      next_keys : option next_keys_use -> // the writer index increases; details included
      complete: bool                   -> // the handshake is complete!
      outgoing i

//17-03-26 now return an outgoing result, for uniformity
// | OutError: error -> outgoing i       // usage? send a polite Alert in case something goes wrong when preparing messages

//17-03-29  these cause a mysterious error
//let out_next_keys (#i:id) (r:outgoing i) = Outgoing? r /\ Outgoing?.next_keys r
//let out_complete (#i:id) (r:outgoing i)  = Outgoing? r /\ Outgoing?.complete r


/// towards separate high-level temporary HSL.Send
///
///
open FStar.Integers
open FStar.Bytes

/// To be included in the context shared with by the application in
/// QUIC.API.
// TODO functions to treat it as a lowParse-writer slice

module B = LowStar.Buffer
module LP = LowParse.Low.Base

(* TODO: do we need a separate type for outbuffer, or can we inline the slice and the position into the output state? *)

noeq type send_state = {
  // outgoing data, already formatted and hashed. Overflows are fatal.
  out_slice: (out_slice: LP.slice (B.trivial_preorder _) (B.trivial_preorder _) { out_slice.LP.len <= LP.validator_max_length }) ; // provided by caller, filled by Send
  out_pos: (pos: UInt32.t{ v pos <= v out_slice.LP.len }); // updated by Send, QD-style

  outgoing: bytes; // TODO: remove, being replaced with [out] above

  // still supporting the high-level API to TLS and Record;
  // as next_keys_use, with next fragment after CCS
  outgoing_next_keys: option (bool & option bytes & bool);
  outgoing_complete: bool;
}

let footprint
  (sto: send_state)
: GTot B.loc
= B.loc_buffer sto.out_slice.LowParse.Low.Base.base

let invariant
  (sto: send_state)
  (h: _)
: GTot Type0
= B.loc_disjoint (footprint sto) (B.loc_region_only true Mem.tls_tables_region) /\
  LowParse.Low.Base.live_slice h sto.out_slice /\
  sto.out_pos <= sto.out_slice.LowParse.Low.Base.len /\
  FStar.Bytes.len sto.outgoing <= sto.out_pos // TODO: remove once fully lowered
  // TODO: what more to stick into this invariant?

let send_state0 = {
  out_slice = LP.make_slice B.null 0ul;
  out_pos = 0ul;
  outgoing = empty_bytes;
  outgoing_next_keys = None;
  outgoing_complete = false; }

// used within QUIC, to be revised with i/o buffer management policy.
let to_be_written (s:send_state): nat =
  Bytes.length s.outgoing


val write_at_most: sto:send_state -> i:id -> max:nat -> send_state & outgoing i

val signals:
  sto:send_state ->
  option (bool & bool) ->
  bool ->
  send_state


inline_for_extraction
type transcript_state (a:EverCrypt.Hash.alg) = Transcript.state a

inline_for_extraction
type transcript = Ghost.erased Transcript.transcript_t

open FStar.HyperStack.ST
open TLSError


// Can we avoid writing so many transient wrappers?

/// Serializes and buffers a ClientHello to be sent.  We write the
/// whole message, even if it includes dummies.  We will probably need
/// a resulting slice representing the message. No transcript yet.

val send_tch
  (sto: send_state)
  (m: HSM.clientHello)
: Stack (result send_state)
  (requires fun h -> invariant sto h)
  (ensures fun h res h' ->
    B.modifies (footprint sto) h h' /\ (
    match res with
    | Correct sto' ->
      invariant sto' h' /\
      sto'.out_slice == sto.out_slice /\
      sto'.out_pos >= sto.out_pos
    | _ -> True
  ))

/// Overwrites the binders in the output buffer, and extend the digest
/// accordingly. Always succeeds.
// TODO unclear how we compute & pass the position to overwrite within stt

val patch_binders
  (#a:EverCrypt.Hash.alg)
  (stt: transcript_state a)
  (t: Transcript.g_transcript_n (Ghost.hide 0) {Transcript.TruncatedClientHello? (Ghost.reveal t)})
  (sto: send_state)
  (m: HandshakeMessages.binders)
: Stack (t':Transcript.g_transcript_n (Ghost.hide 0) {Transcript.ClientHello? (Ghost.reveal t')})
  (requires fun h ->
    invariant sto h /\
    Transcript.invariant stt (Ghost.reveal t) h /\
    B.loc_disjoint (footprint sto) (Transcript.footprint stt))
  (ensures fun h t' h' ->
    let Transcript.TruncatedClientHello retry tch = Ghost.reveal t in
    let Transcript.ClientHello retry' ch = Ghost.reveal t' in
    retry == retry' /\
    tch = HSM.clear_binders ch /\
    B.modifies (footprint sto `B.loc_union` Transcript.footprint stt) h h' /\
    invariant sto h' /\
    Transcript.invariant stt (Ghost.reveal t') h' )

/// Serializes and buffers a message to be sent, and extends the
/// transcript digest with it.

val send_ch
  (#a:EverCrypt.Hash.alg)
  (stt: transcript_state a)
  (#n: Ghost.erased nat)
  (t: Transcript.g_transcript_n n { Ghost.reveal n < Transcript.max_transcript_size - 1 })
  (sto: send_state)
  (m: Transcript.hs_ch)
: Stack (result (send_state & Transcript.g_transcript_n n))
  (requires (fun h ->
    invariant sto h /\
    Transcript.invariant stt (Ghost.reveal t) h /\
    B.loc_disjoint (footprint sto) (Transcript.footprint stt) /\
    Transcript.Start? (Ghost.reveal t)
  ))
  (ensures (fun h res h' ->
    B.modifies (footprint sto `B.loc_union` Transcript.footprint stt) h h' /\
    begin match res with
    | Correct (sto', t') ->
      invariant sto' h' /\
      sto'.out_slice == sto.out_slice /\
      sto'.out_pos >= sto.out_pos /\
      Transcript.invariant stt (Ghost.reveal t') h' /\
      Ghost.reveal t' == Transcript.ClientHello (Transcript.Start?.retried (Ghost.reveal t)) (HSM.M_client_hello?._0 m)
    | _ -> True
    end
  ))

#push-options "--z3rlimit 32"
val send_hrr
  (#a:EverCrypt.Hash.alg)
  (stt: transcript_state a)
  (#n: Ghost.erased nat)
  (t: Transcript.g_transcript_n n { Ghost.reveal n < Transcript.max_transcript_size - 1 })
  (sto: send_state)
  (tag: Transcript.any_hash_tag)
  (hrr: Transcript.hs_sh { HSM.is_valid_hrr (HSM.M_server_hello?._0 hrr) })
: Stack (result (send_state & Transcript.g_transcript_n n))
  (requires (fun h ->
    invariant sto h /\
    Transcript.invariant stt (Ghost.reveal t) h /\
    B.loc_disjoint (footprint sto) (Transcript.footprint stt) /\
    HSM.is_hrr (HSM.M_server_hello?._0 hrr) /\
    Ghost.reveal t == Transcript.Start None
  ))
  (ensures (fun h res h' ->
    B.modifies (footprint sto `B.loc_union` Transcript.footprint stt) h h' /\
    begin match res with
    | Correct (sto', t') ->
      let hrr = HSM.M_server_hello?._0 hrr in
      invariant sto' h' /\
      sto'.out_slice == sto.out_slice /\
      sto'.out_pos >= sto.out_pos /\
      Transcript.invariant stt (Ghost.reveal t') h' /\
      Ghost.reveal t' == Transcript.Start (Some (tag, hrr))
    | _ -> True
    end
  ))
#pop-options
// 19-09-05 not sure what I broke :(

// TODO: Copied from Machine. Should agree on where to put it to define it only once
type client_retry_info = {
  ch0: HSM.ch;
  sh0: HSM.valid_hrr; }

#push-options "--z3rlimit 32" // what makes it so slow?
let retry_info_digest (r:client_retry_info): GTot Transcript.retry =
  let ha = HSM.hrr_ha r.sh0 in
  let th = Transcript.transcript_hash ha (Transcript.ClientHello None r.ch0) in
  HSM.M_message_hash (Bytes.hide th), r.sh0
#pop-options

/// Stateful implementation? As discussed, we need a new Transcript
/// transition ClientHello None ch0 --hrr--> Start (Some (digest_retry
/// {ch0 = ch0; sh0=hrr})). Here is the spec

val extend_hrr
  (#ha:_)
  (sending: send_state)
  (di:Transcript.state ha)
  (retry: client_retry_info) (* its ch0 could be ghost *)
  // AF: What is the role of the following argument? Maybe a copy/paste mistake?
  (msg: HSM.handshake13)
  (#n: Ghost.erased nat)
  (tx0: Transcript.g_transcript_n n { Ghost.reveal n < Transcript.max_transcript_size - 1 }):
  // AF: Why were we not also returning the send state here?
  ST (result (send_state & Transcript.g_transcript_n n))
  (requires fun h0 ->
    let tx0 = Ghost.reveal tx0 in
    ha == HSM.hrr_ha retry.sh0 /\
    tx0 == Transcript.ClientHello None retry.ch0 /\
    B.loc_disjoint (footprint sending) (Transcript.footprint di) /\
    invariant sending h0 /\
    Transcript.invariant di tx0 h0)
  (ensures fun h0 r h1 ->
    B.(modifies (footprint sending `B.loc_union` Transcript.footprint di
                                   `B.loc_union` B.loc_region_only true Mem.tls_tables_region)
       h0 h1) /\ (
    match r with
    | Error _ -> True
    | Correct (sending', tx1) ->
      let tx1 = Ghost.reveal tx1 in
      // enabling ch0 CRF-based injectivity:
      Transcript.hashed ha (Transcript.ClientHello None retry.ch0) /\
      Transcript.invariant di tx1 h1 /\
      sending'.out_slice == sending.out_slice /\
      sending'.out_pos >= sending.out_pos /\
      invariant sending' h1 /\
      tx1 == Transcript.Start(Some (retry_info_digest retry))))

val send13
  (#a:EverCrypt.Hash.alg)
  (stt: transcript_state a)
  (#n: Ghost.erased nat)
  (t: Transcript.g_transcript_n n { Ghost.reveal n < Transcript.max_transcript_size - 1 })
  (sto: send_state)
  (m: HSM.handshake13)
: Stack (result (send_state & Transcript.g_transcript_n (Ghost.hide (Ghost.reveal n + 1))))
  (requires (fun h ->
    invariant sto h /\
    Transcript.invariant stt (Ghost.reveal t) h /\
    B.loc_disjoint (footprint sto) (Transcript.footprint stt) /\
    Transcript.Transcript13? (Ghost.reveal t)
  ))
  (ensures (fun h res h' ->
    B.modifies (footprint sto `B.loc_union` Transcript.footprint stt) h h' /\
    begin match res with
    | Correct (sto', t') ->
      invariant sto' h' /\
      sto'.out_slice == sto.out_slice /\
      sto'.out_pos >= sto.out_pos /\
//      LowParse.Low.Base.bytes_of_slice_from_to h' sto.out_slice sto.out_pos sto'.out_pos == LowParse.Spec.Base.serialize handshake13_serializer m /\ // TODO: is this needed? if so, then TR needs to enrich MITLS.Repr.* with the suitable lemmas
      Transcript.invariant stt (Ghost.reveal t') h' /\
      Ghost.reveal t' == Transcript.snoc13 (Ghost.reveal t) m
    | _ -> True
    end
  ))

val send_tag13
  (#a:EverCrypt.Hash.alg)
  (stt: transcript_state a)
  (#n: Ghost.erased nat)
  (t: Transcript.g_transcript_n n { Ghost.reveal n < Transcript.max_transcript_size - 1 })
  (sto: send_state)
  (m: HSM.handshake13)
  (tag:Hacl.Hash.Definitions.hash_t a)
: ST (result (send_state & Transcript.g_transcript_n (Ghost.hide (Ghost.reveal n + 1))) )
  (requires (fun h ->
    invariant sto h /\
    Transcript.invariant stt (Ghost.reveal t) h /\
    B.loc_disjoint (footprint sto) (Transcript.footprint stt) /\
    B.loc_disjoint (footprint sto) (B.loc_buffer tag) /\
    B.loc_disjoint (Transcript.footprint stt) (B.loc_buffer tag) /\
    B.loc_disjoint (B.loc_buffer tag) (B.loc_region_only true Mem.tls_tables_region) /\
    B.live h tag /\
    Transcript.Transcript13? (Ghost.reveal t)
  ))
  (ensures (fun h res h' ->
    B.modifies (footprint sto `B.loc_union` Transcript.footprint stt `B.loc_union`
      B.loc_buffer tag `B.loc_union` B.loc_region_only true Mem.tls_tables_region) h h' /\
    B.live h' tag /\
    begin match res with
    | Correct (sto', t') ->
      invariant sto' h' /\
      sto'.out_slice == sto.out_slice /\
      sto'.out_pos >= sto.out_pos /\
//      LowParse.Low.Base.bytes_of_slice_from_to h' sto.out_slice sto.out_pos sto'.out_pos == LowParse.Spec.Base.serialize handshake13_serializer m /\ // TODO: is this needed? if so, then TR needs to enrich MITLS.Repr.* with the suitable lemmas
      Transcript.invariant stt (Ghost.reveal t') h' /\
      Ghost.reveal t' == Transcript.snoc13 (Ghost.reveal t) m /\
      B.as_seq h' tag == Transcript.transcript_hash a (Ghost.reveal t') /\
      Transcript.hashed a (Ghost.reveal t')
    | _ -> True
    end
  ))

val send_extract13
  (#a:EverCrypt.Hash.alg)
  (stt: transcript_state a)
  (#n: Ghost.erased nat)
  (t: Transcript.g_transcript_n n { Ghost.reveal n < Transcript.max_transcript_size - 1 })
  (sto: send_state)
  (m: HSM.handshake13)
: ST (result (send_state & Bytes.bytes & Transcript.g_transcript_n (Ghost.hide (Ghost.reveal n + 1))) )
  (requires (fun h ->
    invariant sto h /\
    Transcript.invariant stt (Ghost.reveal t) h /\
    B.loc_disjoint (footprint sto) (Transcript.footprint stt) /\
    Transcript.Transcript13? (Ghost.reveal t)
  ))
  (ensures (fun h res h' ->
    B.modifies (footprint sto `B.loc_union` Transcript.footprint stt `B.loc_union`
      B.loc_region_only true Mem.tls_tables_region) h h' /\
    begin match res with
    | Correct (sto', tag, t') ->
      invariant sto' h' /\
      sto'.out_slice == sto.out_slice /\
      sto'.out_pos >= sto.out_pos /\
//      LowParse.Low.Base.bytes_of_slice_from_to h' sto.out_slice sto.out_pos sto'.out_pos == LowParse.Spec.Base.serialize handshake13_serializer m /\ // TODO: is this needed? if so, then TR needs to enrich MITLS.Repr.* with the suitable lemmas
      Transcript.invariant stt (Ghost.reveal t') h' /\
      Ghost.reveal t' == Transcript.snoc13 (Ghost.reveal t) m /\
      Bytes.reveal  tag == Transcript.transcript_hash a (Ghost.reveal t') /\
      Transcript.hashed a (Ghost.reveal t')
    | _ -> True
    end
  ))
