module TLS.Handshake.Messaging

open Mem
open TLSError
open TLSInfo
open TLSConstants

module HS = FStar.HyperStack
module B = FStar.Bytes
module C = LowStar.ConstBuffer
module LB = LowStar.Buffer
module LP = LowParse.Low.Base
module M = LowStar.Modifies
module R = LowParse.Repr

module HSM = HandshakeMessages
module Epochs = Old.Epochs
module Transcript = TLS.Handshake.Transcript
module PF = TLS.Handshake.ParseFlights // only for flight names
module Recv = TLS.Handshake.Receive
module Send = TLS.Handshake.Send

inline_for_extraction noextract
let trace = MITLS.Tracing.mk_trace "HS"

/// * We keep [epochs] for now, to be replaced by multistreams.
///
/// * We keep the Receive state, includiong a connection-allocated
///   input slice, also used by a stub to exchange bytes with the TLS
///   record.  [I wish we could pass fewer indexes.]
///
///   This state is indexed by the incoming flight type.
///
/// * We keep a digest, indexed by its hash algorith. We recompute the
///   transcript from the handshake state (with a state-dependent
///   bound on its length) and state that it is currently-hased in the
///   digest in the stateful machine invariant. This requires that the
///   machine state keep message contents, at least ghostly. (Good to
///   try out erasure.)
///
/// * We keep the Send state, including a connection-allocated output
///   slice.
///
/// The resulting record of sub-states is dynamically allocated in the
/// handshake, and kept in most subsequent states of the machine:


// QUICified API proposal
noeq type msg_state0 (region: rgn) (inflight: PF.in_progress_flt_t) random ha  = {
  digest: Transcript.state ha;
  sending: Send.send_state;
  receiving: Recv.(r:state {
    PF.length_parsed_bytes r.pf_st == 0 \/ in_progress r == inflight });
  epochs: Epochs.epochs region random; }


// TODO complete regional refinements
// TODO stateful epochs (or wait for their refactoring?)
noeq type msg_state' (region: rgn) (inflight: PF.in_progress_flt_t) random ha  = {
  digest: Transcript.state ha;
  sending: Send.send_state;
  receiving: Recv.(r:state {
    PF.length_parsed_bytes r.pf_st == 0 \/ in_progress r == inflight });
  epochs: Epochs.epochs region random; }

let msg_state (region: rgn) (inflight: PF.in_progress_flt_t) random ha  =
  ms:msg_state' region inflight random ha{
     M.loc_disjoint (Transcript.footprint ms.digest) (Send.footprint ms.sending) /\
     M.loc_disjoint (Transcript.footprint ms.digest) (Recv.loc_recv ms.receiving) /\
     M.loc_disjoint (Send.footprint ms.sending) (Recv.loc_recv ms.receiving) }

let msg_invariant #region #inflight #random #ha (ms:msg_state region inflight random ha) transcript h =
    Transcript.invariant ms.digest h /\
    Send.invariant ms.sending h /\
    Receive.invariant ms.receiving h

let msg_state_footprint #region #inflight #random #ha (ms:msg_state region inflight random ha) =
  (Transcript.footprint ms.digest)
  `M.loc_union` (Send.footprint ms.sending)
  `M.loc_union` (Recv.loc_recv ms.receiving)

// In some cases, the transcript state and input buffers must be created in advance
let create_msg_state (region: rgn) (inflight: PF.in_progress_flt_t)
  random ha (di0:option (Transcript.state ha)) (in0:option Recv.state) :
  ST (msg_state region inflight random ha)
  (requires fun h0 -> True)
  (ensures fun h0 mst h1 -> msg_invariant mst (Transcript.Start None) h1)
= assume false;
  // TODO. Who should allocate this receive buffer?
  let out_buf_len = 16000ul in
  let b_out = LB.malloc region 0z out_buf_len in
  let recv =
    match in0 with
    | None -> 
      let in_buf_len = 16000ul in
      let b_in = LB.malloc region 0z in_buf_len in
      Receive.create (LP.make_slice b_in in_buf_len)
    | Some st -> st in
  let d = match di0 with
    | None -> Transcript.create region ha
    | Some di -> di in
  { digest = d;
    sending = {Send.send_state0 with Send.out_slice = LP.make_slice b_out out_buf_len};
    receiving = recv;
    epochs = Epochs.create region random }

(**** Transcript Bytes Wrappers ***)

// FIXME(adl) add bytes wrapper to Transcript interface?
// Temporarily moved here to share between client and server
#push-options "--max_fuel 0 --max_fuel 0 --z3rlimit 32"
let transcript_extract #ha (di:Transcript.state ha)
  : ST B.bytes
  (requires fun h0 -> Transcript.invariant di h0)
  (ensures fun h0 t h1 ->
    let tx = Transcript.transcript di h0 in
    let tx' = Transcript.transcript di h1 in
    Transcript.invariant di h1 /\
    tx == tx' /\
    M.(modifies (
      Transcript.footprint di `loc_union`
      Mem.loc_tables_region ()) h0 h1) /\
    B.reveal t == Transcript.transcript_hash ha tx /\
    Transcript.hashed ha tx)
  =
  // Show that the transcript state is disjoint from the new frame since it's not unused
  (**) let h0 = get() in
  (**) Transcript.elim_invariant di h0;
  push_frame();
  let ltag = EverCrypt.Hash.Incremental.hash_len ha in
  // AF: Why not allocate directly with size ltag?
  let btag0 = LB.alloca 0uy 64ul in // big enough for all tags
  let btag = LB.sub btag0 0ul ltag in
  let h1 = get () in
  Transcript.frame_invariant di h0 h1 LB.loc_none;
  Transcript.extract_hash di btag;
  let h2 = get () in
  let tag = B.of_buffer ltag btag in
  let h3 = get () in
  Transcript.frame_invariant di h2 h3 LB.loc_none;
  trace "Extracted a transcript hash: %xuy" ltag btag LowStar.Printf.done;
  pop_frame();
  let h4 = get () in
  Transcript.frame_invariant di h3 h4 (LB.loc_region_only false (FStar.HyperStack.get_tip h1));
  tag
#pop-options

// 19-09-05 Much overhead for calling Transcript
// let extend_ch #ha
//   (sending: Send.send_state)
//   (di:Transcript.state ha)
//   (msg: HSM.ch)
//   (tx0: Ghost.erased Transcript.transcript_t):
//   ST (result (Ghost.erased Transcript.transcript_t ))
//   (requires fun h0 ->
//     let tx0 = Ghost.reveal tx0 in Transcript.Start? tx0 /\
//     B.loc_disjoint (Send.footprint sending) (Transcript.footprint di) /\
//     Send.invariant sending h0 /\
//     Transcript.invariant di tx0 h0)
//   (ensures fun h0 r h1 ->
//     B.(modifies (Send.footprint sending `loc_union` Transcript.footprint di) h0 h1) /\
//     Send.invariant sending h1 /\ (
//     match r with
//     | Error _ -> True
//     | Correct tx1 ->
//       let Transcript.Start r = Ghost.reveal tx0 in
//       let tx1 = Ghost.reveal tx1 in
//       Transcript.invariant di tx1 h1 /\
//       tx1 == Transcript.ClientHello r msg ))
// =
//   admit()

#push-options "--max_fuel 0 --max_fuel 0 --z3rlimit 100"
// Adapted from Send.send13, using [sending] as scratch space;
// temporary. We may need similar functions for the Hello messages.
open FStar.Integers
let extend13
  #ha
  (sending: Send.send_state)
  (di:Transcript.state ha)
  (msg: HSM.handshake13)
  : ST (result unit)
  (requires fun h0 ->
    let tx = Transcript.transcript di h0 in
    Transcript.Transcript13? tx /\
    Transcript.extensible tx /\
    Send.footprint sending `M.loc_disjoint` Transcript.footprint di /\
    Send.invariant sending h0 /\
    Transcript.invariant di h0)
  (ensures fun h0 r h1 ->
    let tx = Transcript.transcript di h0 in
    let tx' = Transcript.transcript di h1 in
    M.modifies (Send.footprint sending `M.loc_union` Transcript.footprint di) h0 h1 /\
    Send.invariant sending h1 /\ (
    match r with
    | Error _ -> True
    | Correct () ->
      Transcript.invariant di h1 /\
      tx' == Transcript.snoc13 tx msg ))
  =
  let h0 = get () in
  let r = MITLS.Repr.Handshake13.serialize sending.Send.out_slice sending.Send.out_pos msg in
  let h1 = get () in
  Transcript.frame_invariant di h0 h1
    (LB.loc_buffer sending.Send.out_slice.LP.base);
  match r with
  | None -> fatal Internal_error "output buffer overflow"
  | Some r ->
    List.lemma_snoc_length (Transcript.Transcript13?.rest (Transcript.transcript di h1), msg);
    Transcript.extend di (Transcript.LR_HSM13 r);
    let h2 = get () in
    let b = R.to_bytes (R.as_ptr r) r.R.length in
    let h3 = get () in
    Transcript.frame_invariant di h2 h3 LB.loc_none;
    let workaround = MITLS.Tracing.mbuf_of_repr r in
    trace "extended transcript with %xuy" r.R.length workaround LowStar.Printf.done;
    Correct ()
#pop-options
