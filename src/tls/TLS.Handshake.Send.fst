module TLS.Handshake.Send

/// towards separate high-level temporary HSL.Send
///
///
open FStar.Integers
open FStar.Bytes
open TLSError

open FStar.HyperStack.ST

module Repr = LowParse.Repr
module G = FStar.Ghost
module HS = FStar.HyperStack

// TODO may require switching from Tot to Stack
assume val trace: string -> unit

let mkfrange i min max: frange i =
  assume false;
  (min,max)

#push-options "--z3rlimit 32"
// For QUIC handshake interface
// do not do TLS fragmentation, support
// max output buffer size
let write_at_most sto i max
  =
  // do we have a fragment to send?
  let lo = sto.out_pos `op_Subtraction #(Unsigned W32)`  sto.out_start in
  // do we have an integer library?
  let lo = if lo <= max then lo else max in
  let fragment, sto =
    if lo = 0ul then
      None, sto
    else
      let lb = LowStar.Buffer.sub sto.out_slice.LowParse.Low.Base.base sto.out_start (G.hide lo) in
      let o = Bytes.of_buffer lo lb in
      let rg = mkfrange i (v lo) (v lo) in
      Some (| rg, o |), { sto with out_start = sto.out_start + lo } in
  if sto.out_start = sto.out_pos || max = 0ul // why this other case?
    then (
      // send signals only after flushing the output buffer
      // annoyingly, we may have to re-populate the buffer with
      // delayed bytes to be sent after we signal a key change.
      let next_keys1  =
        match sto.outgoing_next_keys with
        | None -> None
        | Some(a, delayed_fragment, z) -> (
          if Some? delayed_fragment then (
            (if a || z then trace "unexpected 1.2 signals");
            trace "TODO re-buffer delayed send for TLS 1.2" );
          Some({
            out_appdata = a;
            out_ccs_first = false;
            out_skip_0RTT = z})) in
      let sto = { sto with outgoing_next_keys = None; outgoing_complete = false } in
      sto, Outgoing #i fragment next_keys1 sto.outgoing_complete
      )
    else (
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

// usable also on the receiving side; later, we will use instead a
// lower-level caller-allocated output buffer.
val tag: #a:EverCrypt.Hash.alg -> st:Transcript.state a ->
  ST bytes
  (requires fun h0 -> Transcript.invariant st h0)
  (ensures fun h0 b h1 -> True)

let tag #a stt =
  let h0 = get () in
  Transcript.elim_invariant stt h0;
  push_frame();
  let ltag =  Hashing.Spec.hash_len a in
  let btag = LowStar.Buffer.alloca 0uy ltag in
  let h1 = get () in
  Transcript.frame_invariant stt h0 h1 B.loc_none;
  Transcript.extract_hash stt btag;
  let tag = FStar.Bytes.of_buffer ltag btag in
  pop_frame();
  tag

let send_tch sto m =
  let h0 = get () in
  let r = MITLS.Repr.Handshake.serialize sto.out_slice sto.out_pos (HSM.M_client_hello m) in
  match r with
  | None ->
    fatal Internal_error "send_tch: output buffer overflow"
  | Some r ->
    let rp = Repr.as_ptr r in
    let b = Repr.to_bytes rp r.Repr.length in
    trace ("send (truncated) CH "^hex_of_bytes b);
    let sto = { sto with out_pos = Repr.end_pos r } in
    correct sto

// FIXME(adl) required for PSK and 0-RTT to work!
let patch_binders #a stt sto binders
=
  admit()

let send_ch
  #a stt sto m
= let h0 = get () in
  let r = MITLS.Repr.Handshake.serialize sto.out_slice sto.out_pos m in
  let h1 = get () in
  Transcript.frame_invariant stt h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
  match r with
  | None ->
    fatal Internal_error "send_ch: output buffer overflow"
  | Some r ->
    Transcript.extend stt (Transcript.LR_ClientHello r);
    let h2 = get () in
    let b = Repr.to_bytes (Repr.as_ptr r) r.Repr.length in
    let h3 = get () in
    Transcript.frame_invariant stt h2 h3 B.loc_none;
    trace ("send CH "^hex_of_bytes b);
    let sto = { sto with out_pos = Repr.end_pos r } in
    correct sto

let send_sh #a stt sto m =
  let h0 = get () in
  let r = MITLS.Repr.Handshake.serialize sto.out_slice sto.out_pos m in
  let h1 = get () in
  Transcript.frame_invariant stt h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
  match r with
  | None ->
    fatal Internal_error "send_sh: output buffer overflow"
  | Some r ->
    Transcript.extend stt (Transcript.LR_ServerHello r);
    let h2 = get () in
    let b = Repr.to_bytes (Repr.as_ptr r) r.Repr.length in
    let h3 = get () in
    Transcript.frame_invariant stt h2 h3 B.loc_none;
    trace ("send SH "^hex_of_bytes b);
    let sto = { sto with out_pos = Repr.end_pos r } in
    correct sto

#push-options "--z3rlimit 32"

let send_tag_sh #a stt sto m tag =
  match send_sh stt sto m with
  | Correct (sto) ->
    Transcript.extract_hash stt tag;
    correct (sto)
  | Error z -> Error z

let send_hrr #a stt sto tag hrr =
  let h0 = get () in
  let r = MITLS.Repr.Handshake.serialize sto.out_slice sto.out_pos tag in
  match r with
  | None ->
    fatal Internal_error "send_hrr: output buffer overflow for tag"
  | Some r_tag ->
    let r = MITLS.Repr.Handshake.serialize sto.out_slice (Repr.end_pos r_tag) hrr in
    begin match r with
    | None ->
      fatal Internal_error "output_buffer_overflow for hrr"
    | Some r_hrr ->
      let h1 = get () in
      Transcript.frame_invariant stt h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
      Transcript.extend stt (Transcript.LR_HRR r_tag r_hrr);
      let h2 = get () in
      let b1 = Repr.to_bytes (Repr.as_ptr r_tag) r_tag.Repr.length in
      let b2 = Repr.to_bytes (Repr.as_ptr r_hrr) r_hrr.Repr.length in
      let h3 = get () in
      trace ("send "^hex_of_bytes (b1 @| b2));
      let sto = { sto with out_pos = Repr.end_pos r_hrr } in
      correct sto
    end

#pop-options

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 32"

assume val any_hash_tag_of_buffer (b:B.buffer Lib.IntTypes.uint8) : Tot Transcript.any_hash_tag

let extend_hrr #ha sending di retry msg =
  let h0 = get() in
  // Need to call elim_invariant with initial memory to conclude that the footprint
  // is disjoint from the new frame
  (**) Transcript.elim_invariant di h0;
  push_frame();
  let ltag = EverCrypt.Hash.Incremental.hash_len ha in
  let btag = LowStar.Buffer.alloca 0uy ltag in
  let h = get() in
  Transcript.frame_invariant di h0 h B.loc_none;
  Transcript.extract_hash di btag;
  Transcript.reset di;

  // TODO: Do this the correct way. How do we get a repr out of a buffer of bytes?
  // Once this is done, we can take only the second part of send_hrr (i.e. parse sh0)
  // before calling extend
  let tag = any_hash_tag_of_buffer btag in
//  let h1 = get() in
//  assume (tag == HSM.M_message_hash (Bytes.hide
//    (Transcript.transcript_hash ha (Transcript.ClientHello None retry.ch0))));
  let result = send_hrr di sending tag (HSM.M_server_hello retry.sh0) in
  pop_frame();
  let h1 = get () in
  // FIXME any_hash_tag_of_buffer (see commented assume)
  assume(Transcript.transcript di h1 == Transcript.Start(Some (retry_info_digest retry)));
  result

#pop-options

// FIXME(adl) prove in Transcript.fsti
let lemma_valid_transition #a (s:Transcript.state a) h l
  : Lemma (requires (
    let t = Transcript.transcript s h in
    Transcript.extensible t /\
    ((Transcript.Transcript13? t /\ Transcript.LR_HSM13? l)
    \/ (Transcript.Transcript12? t /\ Transcript.LR_HSM12? l))))
    (ensures Some? (Transcript.transition
      (Transcript.transcript s h) (Transcript.label_of_label_repr l)))
  = admit () // This should be automatic? is extensible not strong enough?
  
let send13 #a stt sto m
= let h0 = get () in
  let r = MITLS.Repr.Handshake13.serialize sto.out_slice sto.out_pos m in
  let h1 = get () in
  Transcript.frame_invariant stt h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
  match r with
  | None ->
    fatal Internal_error "send13: output buffer overflow"
  | Some r ->
    lemma_valid_transition stt h1 (Transcript.LR_HSM13 r);
    Transcript.extend stt (Transcript.LR_HSM13 r);
    let h2 = get () in
    let b = Repr.to_bytes (Repr.as_ptr r) r.Repr.length in
    let h3 = get () in
    Transcript.frame_invariant stt h2 h3 B.loc_none;
    trace ("send "^hex_of_bytes b);
    let sto = { sto with out_pos = Repr.end_pos r} in
    correct sto

/// Serializes and buffers a message to be sent, and extends the
/// transcript digest with it. Also returns the current hash of the transcript
let send_tag13 #a stt sto m tag =
  match send13 stt sto m with
  | Correct sto ->
    Transcript.extract_hash stt tag;
    correct sto
  | Error z -> Error z

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 32"

let send_extract13 #ha stt sto m =
  (**) let h0 = get() in
  // Need to call elim_invariant with initial memory to conclude that the footprint
  // is disjoint from the new frame
  (**) Transcript.elim_invariant stt h0;
  push_frame();
  let ltag = EverCrypt.Hash.Incremental.hash_len ha in
  let btag = LowStar.Buffer.alloca 0uy ltag in
  let h = get () in
  Transcript.frame_invariant stt h0 h B.loc_none;
  match send_tag13 stt sto m btag with
  | Error z -> pop_frame(); Error z
  | Correct sto ->
  (**) let h1 = get() in
  let tag = FStar.Bytes.of_buffer ltag btag in
  pop_frame();
  (**) let h2 = get() in
  (**) Transcript.frame_invariant stt h1 h2 (B.loc_region_only false (FStar.HyperStack.get_tip h1));
  Correct(sto,tag)

#pop-options

inline_for_extraction
noextract
let msg_type (msg: msg)
: Tot Type
= match msg with
| Msg m -> HSM.valid_handshake
| Msg12 _ -> HSM.handshake12
| Msg13 _ -> HSM.handshake13

inline_for_extraction
let msg_repr_type (msg: msg) (b: Repr.const_slice)
: Tot Type
= match msg with
| Msg _ -> MITLS.Repr.Handshake.pos b
| Msg12 _ -> MITLS.Repr.Handshake12.pos b
| Msg13 _ -> MITLS.Repr.Handshake13.pos b

val send:
  #a:EverCrypt.Hash.alg ->
  Transcript.state a ->
  send_state -> msg ->
  St (result send_state)

//#push-options "--z3rlimit 32"
let send #a stt (sto:send_state) msg =
  let h0 = get () in
  assume (LowParse.Low.Base.live_slice h0 sto.out_slice);
  assume (Transcript.invariant stt h0);
  assume (B.loc_disjoint (B.loc_buffer sto.out_slice.LowParse.Low.Base.base) (Transcript.footprint stt));
  let r : option (msg_repr_type msg (Repr.of_slice sto.out_slice)) =
    match msg with
    | Msg m ->
      MITLS.Repr.Handshake.serialize sto.out_slice sto.out_pos m
    | Msg12 m -> MITLS.Repr.Handshake12.serialize sto.out_slice sto.out_pos m
    | Msg13 m -> MITLS.Repr.Handshake13.serialize sto.out_slice sto.out_pos m
  in  
  match r with
  | None ->
    fatal Internal_error "send: output buffer overflow"
  | Some r ->
    //19-09-05
    // regression possibly due to the valid_sh refinement; no obvious fix.
    assume(False);
    let r : Repr.repr_pos (msg_type msg) (Repr.of_slice sto.out_slice) = r in
    let olabel : option Transcript.label_repr = match msg with
    | Msg (Parsers.Handshake.M_client_hello _) -> Some (Transcript.LR_ClientHello r) (* TODO: LR_TCH? *)
    | Msg (Parsers.Handshake.M_server_hello sh) ->
      Some (Transcript.LR_ServerHello r)
    | Msg12 _ -> Some (Transcript.LR_HSM12 r)
    | Msg13 _ -> Some (Transcript.LR_HSM13 r)
    | _ -> None
    in
    begin match olabel with
    | Some label ->
      let h1 = get () in
      Transcript.frame_invariant stt h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
      assume (Transcript.extensible (Transcript.transcript stt h1));
      assume (Some? (Transcript.transition (Transcript.transcript stt h1) (Transcript.label_of_label_repr label)));
      Transcript.extend stt label;
      let b = Repr.to_bytes (Repr.as_ptr r) r.Repr.length in
      trace ("send "^hex_of_bytes b);
      let sto = { sto with out_pos = Repr.end_pos r } in
      correct sto
    | _ -> fatal Internal_error "unsupported?"
    end

val send_tag:
  #a:EverCrypt.Hash.alg ->
  st:Transcript.state a ->
  send_state ->
  msg ->
  ST (result (send_state & bytes))
  (requires fun h0 -> Transcript.invariant st h0)
  (ensures fun h0 _ h1 -> True)

let send_tag #a stt sto msg =
  let h0 = get () in
  let r = send #a stt sto msg in
  match r with
  | Error z -> Error z
  | Correct sto ->
    let h1 = get () in 
    Transcript.frame_invariant stt h0 h1 (admit());
    let tag1 = tag stt in
    Correct (sto, tag1)

// Missing variants for TCH and Binders
