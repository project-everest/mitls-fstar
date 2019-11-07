module TLS.Handshake.Send

/// towards separate high-level temporary HSL.Send
///
///
open FStar.Integers
open FStar.Bytes
open TLSError

open FStar.HyperStack.ST
module HS = FStar.HyperStack

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
      let sto = { sto with outgoing = outgoing1; outgoing_next_keys = None; outgoing_complete = false } in
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

// usable also on the receiving side; later, we will use instead a
// lower-level caller-allocated output buffer.
val tag: #a:EverCrypt.Hash.alg -> Transcript.state a -> Transcript.transcript_t -> St bytes
let tag #a stt transcript =
  let h0 = get () in
  assume (Transcript.invariant stt transcript h0);
  Transcript.elim_invariant stt transcript h0;
  push_frame();
  let ltag =  Hashing.Spec.hash_len a in
  let btag = LowStar.Buffer.alloca 0uy ltag in
  let h1 = get () in
  Transcript.frame_invariant stt transcript h0 h1 B.loc_none;
  Transcript.extract_hash stt btag transcript;
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
    let b = MITLS.Repr.to_bytes r in
    trace ("send "^hex_of_bytes b);
    let sto = { sto with out_pos = r.MITLS.Repr.end_pos; outgoing = sto.outgoing @| b } in
    correct sto

let patch_binders
  #a stt t sto binders
=
  admit()

let send_ch
  #a stt #_ t sto m
= let h0 = get () in
  let r = MITLS.Repr.Handshake.serialize sto.out_slice sto.out_pos m in
  let h1 = get () in
  Transcript.frame_invariant stt t h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
  match r with
  | None ->
    fatal Internal_error "send_ch: output buffer overflow"
  | Some r ->
    let t' = Transcript.extend stt (Transcript.LR_ClientHello r) t in
    let b = MITLS.Repr.to_bytes r in
    trace ("send "^hex_of_bytes b);
    let sto = { sto with out_pos = r.MITLS.Repr.end_pos; outgoing = sto.outgoing @| b } in
    correct (sto, t')

let send_sh
  #a stt #_ t sto m
=
  let h0 = get () in
  let r = MITLS.Repr.Handshake.serialize sto.out_slice sto.out_pos m in
  let h1 = get () in
  Transcript.frame_invariant stt t h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
  match r with
  | None ->
    fatal Internal_error "send_sh: output buffer overflow"
  | Some r ->
    let t' = Transcript.extend stt (Transcript.LR_ServerHello r) t in
    let b = MITLS.Repr.to_bytes r in
    trace ("send "^hex_of_bytes b);
    let sto = { sto with out_pos = r.MITLS.Repr.end_pos; outgoing = sto.outgoing @| b } in
    correct (sto, t')

#push-options "--z3rlimit 32"

let send_tag_sh #a stt #_ t sto m tag =
  match send_sh stt t sto m with
  | Correct (sto, t') ->
    Transcript.extract_hash stt tag t';
    correct (sto, t')
  | Error z -> Error z

let send_hrr
  #a stt #_ t sto tag hrr
= let h0 = get () in
  let r = MITLS.Repr.Handshake.serialize sto.out_slice sto.out_pos tag in
  match r with
  | None ->
    fatal Internal_error "send_hrr: output buffer overflow for tag"
  | Some r_tag ->
    let r = MITLS.Repr.Handshake.serialize sto.out_slice r_tag.MITLS.Repr.end_pos hrr in
    begin match r with
    | None ->
      fatal Internal_error "output_buffer_overflow for hrr"
    | Some r_hrr ->
      let h1 = get () in
      Transcript.frame_invariant stt t h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
      let t' = Transcript.extend stt (Transcript.LR_HRR r_tag r_hrr) t in
      let b = MITLS.Repr.to_bytes r_tag @| MITLS.Repr.to_bytes r_hrr in
      trace ("send "^hex_of_bytes b);
      let sto = { sto with out_pos = r_hrr.MITLS.Repr.end_pos; outgoing = sto.outgoing @| b } in
      correct (sto, t')
    end

#pop-options

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 32"

assume val any_hash_tag_of_buffer (b:B.buffer Lib.IntTypes.uint8) : Tot Transcript.any_hash_tag

let extend_hrr #ha sending di retry msg #n tx0 =
  let h0 = get() in
  // Need to call elim_invariant with initial memory to conclude that the footprint
  // is disjoint from the new frame
  (**) Transcript.elim_invariant di tx0 h0;
  push_frame();
  let ltag = EverCrypt.Hash.Incremental.hash_len ha in
  let btag = LowStar.Buffer.alloca 0uy ltag in

  Transcript.extract_hash di btag tx0;
  let tx1 = Transcript.reset di tx0 in

  // TODO: Do this the correct way. How do we get a repr out of a buffer of bytes?
  // Once this is done, we can take only the second part of send_hrr (i.e. parse sh0)
  // before calling extend
  let tag = any_hash_tag_of_buffer btag in
  let h1 = get() in
  assume (tag == HSM.M_message_hash (Bytes.hide (B.as_seq h1 btag)));
  let result = send_hrr di tx1 sending tag (HSM.M_server_hello retry.sh0) in

  pop_frame();
  result

#pop-options

let send13
  #a stt #_ t sto m
= let h0 = get () in
  let r = MITLS.Repr.Handshake13.serialize sto.out_slice sto.out_pos m in
  let h1 = get () in
  Transcript.frame_invariant stt t h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
  match r with
  | None ->
    fatal Internal_error "send13: output buffer overflow"
  | Some r ->
//    let t : Ghost.erased Transcript.transcript_t = Ghost.hide (Ghost.reveal t) in
    List.lemma_snoc_length (Transcript.Transcript13?.rest t, m);
    let t' = Transcript.extend stt (Transcript.LR_HSM13 r) t in
    let b = MITLS.Repr.to_bytes r in
    trace ("send "^hex_of_bytes b);
    let sto = { sto with out_pos = r.MITLS.Repr.end_pos; outgoing = sto.outgoing @| b } in
    correct (sto, t')


/// Serializes and buffers a message to be sent, and extends the
/// transcript digest with it. Also returns the current hash of the transcript
let send_tag13 #a stt #_ t sto m tag =
  match send13 stt t sto m with
  | Correct (sto, t') ->
    Transcript.extract_hash stt tag t';
    correct (sto, t')
  | Error z -> Error z

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 32"

let send_extract13 #ha stt #_ t sto m =
  (**) let h0 = get() in
  // Need to call elim_invariant with initial memory to conclude that the footprint
  // is disjoint from the new frame
  (**) Transcript.elim_invariant stt t h0;
  push_frame();
  let ltag = EverCrypt.Hash.Incremental.hash_len ha in
  let btag = LowStar.Buffer.alloca 0uy ltag in
  match send_tag13 stt t sto m btag with
  | Error z -> pop_frame(); Error z
  | Correct (sto, tr) ->
  (**) let h1 = get() in
  let tag = FStar.Bytes.of_buffer ltag btag in
  pop_frame();
  (**) let h2 = get() in
  (**) Transcript.frame_invariant stt tr h1 h2 (B.loc_region_only false (FStar.HyperStack.get_tip h1));
  Correct(sto,tag,tr)

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
let msg_repr_type (msg: msg) (b: MITLS.Repr.const_slice)
: Tot Type
= match msg with
| Msg _ -> MITLS.Repr.Handshake.repr b
| Msg12 _ -> MITLS.Repr.Handshake12.repr b
| Msg13 _ -> MITLS.Repr.Handshake13.repr b

val send:
  #a:EverCrypt.Hash.alg ->
  Transcript.state a -> Transcript.transcript_t ->
  send_state -> msg ->
  St (result (send_state & Transcript.transcript_t))

//#push-options "--z3rlimit 32"
let send #a stt transcript0 sto msg =
  let h0 = get () in
  assume (LowParse.Low.Base.live_slice h0 sto.out_slice);
  assume (Transcript.invariant stt transcript0 h0);
  assume (B.loc_disjoint (B.loc_buffer sto.out_slice.LowParse.Low.Base.base) (Transcript.footprint stt));
  let r : option (msg_repr_type msg (MITLS.Repr.of_slice sto.out_slice)) =
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
    let r : MITLS.Repr.repr (msg_type msg) (MITLS.Repr.of_slice sto.out_slice) = r in
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
      Transcript.frame_invariant stt transcript0 h0 h1 (B.loc_buffer sto.out_slice.LowParse.Low.Base.base);
      assume (Transcript.extensible transcript0);
      assume (Some? (Transcript.transition transcript0 (Transcript.label_of_label_repr label)));
      let transcript1 = Transcript.extend stt label transcript0 in
      let b = MITLS.Repr.to_bytes r in
      trace ("send "^hex_of_bytes b);
      assume (FStar.Bytes.len sto.outgoing <= sto.out_pos);
      let sto = { sto with out_pos = r.MITLS.Repr.end_pos; outgoing = sto.outgoing @| b } in
      correct (sto, transcript1)
    | _ -> fatal Internal_error "unsupported?"
    end

val send_tag:
  #a:EverCrypt.Hash.alg ->
  Transcript.state a -> Transcript.transcript_t ->
  send_state -> msg ->
  St (result (send_state & Transcript.transcript_t & bytes))

let send_tag #a stt transcript0 sto msg =
  let r = send #a stt transcript0 sto msg in
  match r with
  | Error z -> Error z
  | Correct (sto, transcript1) ->
    let tag1 = tag stt transcript1 in
    Correct (sto, transcript1, tag1)

// Missing variants for TCH and Binders