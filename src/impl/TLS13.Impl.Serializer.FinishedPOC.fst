module TLS13.Impl.Serializer.FinishedPOC

#lang-pulse

(* Proof-of-concept: the BUILD direction (serialize) via the generated copyful
   l2r writer [GHS.write_handshake], for the simplest message (Finished).
   Establishes the template: build the [_low] repr from the L mirror, fold the
   sum [handshake_vmatch], bridge array->slice, call the writer, read the bytes
   == [WS.serialize_handshake (M.Finished fin)] from the safe-writer postcond. *)

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module S = Pulse.Lib.Slice
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Seq = FStar.Seq
module T = TLS13.Types
module B = TLS13.Bytes
module L = TLS13.Impl.Messages
module M = TLS13.Messages
module WS = TLS13.Wire.Spec
module Sem = TLS13.Wire.Semantics
module GHS = TLS13.Wire.Generated.Handshake
module GFin = TLS13.Wire.Generated.Finished
module PPB = LowParse.PulseParse.Base
module PPBY = LowParse.PulseParse.Bytes
module LSeqB = LowParse.Pulse.SeqBytes
module LP = LowParse.Spec

(* Intro the sum vmatch for a Finished body, reverse of Impl.Parser.elim_vmatch_finished. *)
ghost
fn intro_handshake_finished_vmatch
  (lv: PPBY.lvec U8.t)
  (cm: Ghost.erased (Seq.seq U8.t))
  requires V.pts_to lv.PPBY.lvec_vec cm ** pure (V.is_full_vec lv.PPBY.lvec_vec)
  ensures GHS.handshake_vmatch (GHS.Body_finished_low lv) (GHS.Body_finished_mid (Ghost.reveal cm))
{
  fold (LSeqB.vmatch_copy_seqbytes lv (Ghost.reveal cm));
  rewrite (LSeqB.vmatch_copy_seqbytes lv (Ghost.reveal cm))
       as (GHS.handshake_body_finished_vmatch lv (Ghost.reveal cm));
  fold (GHS.handshake_vmatch (GHS.Body_finished_low lv) (GHS.Body_finished_mid (Ghost.reveal cm)));
}

fn serialize_finished_handshake_poc
  (#fin: erased GFin.finished)
  (lfin: L.finished)
  (handshake_out: A.array U8.t)
  (handshake_out_len: SZ.t)
  requires L.is_valid_finished lfin (Ghost.reveal fin) **
           A.pts_to handshake_out 'old_handshake **
           pure (B.length 'old_handshake == SZ.v handshake_out_len /\
                 SZ.v handshake_out_len == 36)
  returns written: (n:SZ.t{SZ.v n <= SZ.v handshake_out_len})
  ensures exists* handshake_bytes.
          L.is_valid_finished lfin (Ghost.reveal fin) **
          A.pts_to handshake_out handshake_bytes **
          pure (B.length handshake_bytes == 36 /\
                SZ.v written == 36 /\
                Seq.equal handshake_bytes
                  (WS.serialize_handshake (M.Finished (Ghost.reveal fin))) /\
                WS.parse_tls_message T.Handshake handshake_bytes ==
                  Some (M.TlsHandshake (M.Finished (Ghost.reveal fin))))
{
  unfold (L.is_valid_finished lfin (Ghost.reveal fin));
  with verify_data. assert (V.pts_to lfin.L.finished_verify_data verify_data);
  let lv : PPBY.lvec U8.t = { PPBY.lvec_vec = lfin.L.finished_verify_data; PPBY.lvec_len = 32sz };
  rewrite (V.pts_to lfin.L.finished_verify_data verify_data)
       as (V.pts_to lv.PPBY.lvec_vec verify_data);
  intro_handshake_finished_vmatch lv verify_data;
  A.pts_to_len handshake_out;
  let s = S.from_array handshake_out handshake_out_len;
  let mut perr = false;
  let sz = GHS.write_handshake (GHS.Body_finished_low lv)
             #(Ghost.hide (GHS.Body_finished_mid verify_data))
             s perr;
  with v'. assert (S.pts_to s v');
  (* serialized length of a 32-byte Finished handshake message is exactly 36 *)
  assert (pure (Seq.length verify_data == 32));
  GHS.handshake_bytesize_eq (GHS.Body_finished verify_data);
  assert (pure (GHS.handshake_conv (GHS.Body_finished_mid verify_data)
                  == Some (GHS.Body_finished verify_data)));
  (* recover the array and the L mirror vec from the writer-preserved vmatch *)
  S.to_array s;
  A.pts_to_len handshake_out;
  assert (pure (SZ.v sz == 36));
  WS.lemma_serialize_handshake_finished (Ghost.reveal fin);
  Seq.lemma_eq_elim verify_data (Ghost.reveal fin);
  WS.lemma_parse_serialize_handshake_finished (Ghost.reveal fin);
  unfold (GHS.handshake_vmatch (GHS.Body_finished_low lv) (GHS.Body_finished_mid verify_data));
  rewrite (GHS.handshake_body_finished_vmatch lv verify_data)
       as (LSeqB.vmatch_copy_seqbytes lv verify_data);
  unfold (LSeqB.vmatch_copy_seqbytes lv verify_data);
  rewrite (V.pts_to lv.PPBY.lvec_vec verify_data)
       as (V.pts_to lfin.L.finished_verify_data verify_data);
  fold (L.is_valid_finished lfin (Ghost.reveal fin));
  sz
}
