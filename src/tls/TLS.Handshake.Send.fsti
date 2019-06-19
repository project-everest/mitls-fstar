module TLS.Handshake.Send

/// Adding an interface to hoist definitions from HandshakeLog.fsti

open HandshakeMessages

type msg =
| Msg of handshake
| Msg12 of handshake12
| Msg13 of handshake13

let tag_of = function
| Msg h -> tag_of_handshake h
| Msg12 h -> tag_of_handshake12 h
| Msg13 h -> tag_of_handshake13 h

let msg_bytes = function
| Msg h -> handshake_serializer32 h
| Msg12 h -> handshake12_serializer32 h
| Msg13 h -> handshake13_serializer32 h

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
= LowParse.Low.Base.live_slice h sto.out_slice /\
  sto.out_pos <= sto.out_slice.LowParse.Low.Base.len /\
  FStar.Bytes.len sto.outgoing <= sto.out_pos // TODO: remove once fully lowered
  // TODO: what more to stick into this invariant?

let send_state0 = {
  out_slice = LP.make_slice B.null 0ul;
  out_pos = 0ul;
  outgoing = empty_bytes;
  outgoing_next_keys = None;
  outgoing_complete = false; }

val write_at_most: sto:send_state -> i:id -> max:nat -> send_state & outgoing i

val signals:
  sto:send_state ->
  option (bool & bool) ->
  bool ->
  send_state

module T = HSL.Transcript

inline_for_extraction
type transcript_state (a:EverCrypt.Hash.alg) = T.state a

inline_for_extraction
type transcript = Ghost.erased T.transcript_t

open FStar.HyperStack.ST
open TLSError

val send13
  (#a:EverCrypt.Hash.alg)
  (stt: transcript_state a)
  (t: transcript)
  (sto: send_state)
  (m: handshake13)
: Stack (result (send_state & transcript))
  (requires (fun h ->
    invariant sto h /\
    T.invariant stt (Ghost.reveal t) h /\
    B.loc_disjoint (footprint sto) (T.footprint stt) /\
    T.extensible (Ghost.reveal t) /\
    Some? (T.transition (Ghost.reveal t) (T.L_HSM13 m))
  ))
  (ensures (fun h res h' ->
    B.modifies (footprint sto `B.loc_union` T.footprint stt) h h' /\
    begin match res with
    | Correct (sto', t') ->
      invariant sto' h' /\
      sto'.out_slice == sto.out_slice /\
      sto'.out_pos >= sto.out_pos /\
//      LowParse.Low.Base.bytes_of_slice_from_to h' sto.out_slice sto.out_pos sto'.out_pos == LowParse.Spec.Base.serialize handshake13_serializer m /\ // TODO: is this needed? if so, then TR needs to enrich MITLS.Repr.* with the suitable lemmas
      T.invariant stt (Ghost.reveal t') h' /\
      T.transition (Ghost.reveal t) (T.L_HSM13 m) == Some (Ghost.reveal t')
    | _ -> True
    end
  ))
