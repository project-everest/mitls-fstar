module TLS.Handshake.Send

/// towards separate high-level temporary HSL.Send
///
///
open FStar.Integers
open FStar.Bytes
open TLSError

open FStar.HyperStack.ST

// TODO may require switching from Tot to Stack
assume val trace: string -> unit

let mkfrange i min max: frange i =
  assume false;
  (min,max)

// For QUIC handshake interface
// do not do TLS fragmentation, support
// max output buffer size
let write_at_most sto i max
  =
  // do we have a fragment to send?
  let fragment, outgoing' =
    let o = sto.outgoing in
    let lo = length o in
    if lo = 0 then // nothing to send
       (None, empty_bytes)
    else // at most one fragment
    if (lo <= max) then
      let rg = mkfrange i lo lo in
      (Some (| rg, o |), empty_bytes)
    else // at least two fragments
      let (x,y) = split_ o max in
      let lx = length x in
      let rg = mkfrange i lx lx in
      (Some (| rg, x |), y) in
  if length outgoing' = 0 || max = 0
    then (
      // send signals only after flushing the output buffer
      let next_keys1, outgoing1 = match sto.outgoing_next_keys with
      | Some(a, Some finishedFragment, z) ->
        (if a || z then trace "unexpected 1.2 signals");
        Some({
          out_appdata = a;
          out_ccs_first = true;
          out_skip_0RTT = z}), finishedFragment
      | Some(a, None, z) ->
        Some({
          out_appdata = a;
          out_ccs_first = false;
          out_skip_0RTT = z}), outgoing'
      | None -> None, outgoing' in
      let sto = { outgoing = outgoing1; outgoing_next_keys = None; outgoing_complete = false } in
      sto, Outgoing #i fragment next_keys1 sto.outgoing_complete
      )
    else (
      let sto = { sto with outgoing = outgoing' } in
      sto, Outgoing #i fragment None false )

// TODO require or check that both flags are clear before the call
let signals sto next_keys1 complete1 =
  if Some? sto.outgoing_next_keys then trace "WARNING: dirty next-key flag -- use send_CCS instead";
  if sto.outgoing_complete then trace "WARNING: dirty complete flag";
  let outgoing_next_keys1 =
    match next_keys1 with
    | Some (enable_appdata,skip_0rtt) -> Some (enable_appdata, None, skip_0rtt)
    | None -> None in
  { sto with outgoing_next_keys = outgoing_next_keys1; outgoing_complete = complete1 }


/// The functions below are not used yet, will replace their counterpart in HandshakeLog

assume type transcript_state (a:EverCrypt.Hash.alg) //= UInt32.t
type transcript = unit

// usable also on the receiving side; later, we will use instead a
// lower-level caller-allocated output buffer.
val tag: #a:EverCrypt.Hash.alg -> transcript_state a -> transcript -> St bytes
let tag #a stt transcript =
  push_frame();
  let ltag =  EverCrypt.Hash.tagLen a in
  let btag = LowStar.Buffer.alloca 0uy ltag in
  // HSL.Transcript.extract stt btag transcript1;
  let tag = FStar.Bytes.of_buffer ltag btag in
  pop_frame();
  tag

/// Serializes and buffers a message to be sent, and extends the
/// transcript digest with it.

val send:
  #a:EverCrypt.Hash.alg ->
  transcript_state a -> transcript ->
  send_state -> msg ->
  St (result (send_state & transcript))

let send #a stt transcript0 sto msg =
  let b = msg_bytes msg in
  trace ("send "^hex_of_bytes b);
  // let repr = admit() in
  // let transcript1 = HSL.Transcript.extend stt repr transcript0 in

  // will make more sense with a bounded output buffer
  if UInt.fits (Bytes.length sto.outgoing + Bytes.length b) UInt32.n then
    ( let sto = { sto with outgoing = sto.outgoing @| b } in
    correct (sto, transcript0) )
  else
    fatal Internal_error "output buffer overflow"

val send_tag:
  #a:EverCrypt.Hash.alg ->
  transcript_state a -> transcript ->
  send_state -> msg ->
  St (result (send_state & transcript & bytes))

let send_tag #a stt transcript0 sto msg =
  let r = send #a stt transcript0 sto msg in
  match r with
  | Error z -> Error z
  | Correct (sto, transcript1) ->
    let tag1 = tag stt transcript1 in
    Correct (sto, transcript1, tag1)

// Missing variants for TCH and Binders
