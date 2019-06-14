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




noeq inline_for_extraction
type outbuffer = {
  base: Buffer.buffer UInt8.t;                        // provided by caller, filled by Send
  len: (len: UInt32.t{ v len = Buffer.length base }); // provided by caller
  pos: (pos: UInt32.t{ v pos <= Buffer.length base }); // updated by Send, QD-style
}

noeq type send_state = {
  // outgoing data, already formatted and hashed. Overflows are fatal.
  outgoing: bytes; // should become an [outbuffer]

  // still supporting the high-level API to TLS and Record;
  // as next_keys_use, with next fragment after CCS
  outgoing_next_keys: option (bool & option bytes & bool);
  outgoing_complete: bool;
}

// TODO we'll need an invariant, mostly stating that the output buffer
// is live.

let send_state0 = {
  outgoing = empty_bytes;
  outgoing_next_keys = None;
  outgoing_complete = false; }

val write_at_most: sto:send_state -> i:id -> max:nat -> send_state & outgoing i

val signals:
  sto:send_state ->
  option (bool & bool) ->
  bool ->
  send_state
