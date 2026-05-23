module TLS13.Handshake.Framing

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn build_server_certificate_verify_input
  (transcript_hash: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to transcript_hash 'hash_bytes **
           pts_to out 'old_bytes **
           pure (B.length 'hash_bytes == 32 /\
                 B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 130)
  ensures exists* out_bytes.
          pts_to transcript_hash 'hash_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 130)
{
  pts_to_len transcript_hash;
  pts_to_len out;
  out.(0sz) <- 0x20uy; out.(1sz) <- 0x20uy; out.(2sz) <- 0x20uy; out.(3sz) <- 0x20uy;
  out.(4sz) <- 0x20uy; out.(5sz) <- 0x20uy; out.(6sz) <- 0x20uy; out.(7sz) <- 0x20uy;
  out.(8sz) <- 0x20uy; out.(9sz) <- 0x20uy; out.(10sz) <- 0x20uy; out.(11sz) <- 0x20uy;
  out.(12sz) <- 0x20uy; out.(13sz) <- 0x20uy; out.(14sz) <- 0x20uy; out.(15sz) <- 0x20uy;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 130));
  out.(16sz) <- 0x20uy; out.(17sz) <- 0x20uy; out.(18sz) <- 0x20uy; out.(19sz) <- 0x20uy;
  out.(20sz) <- 0x20uy; out.(21sz) <- 0x20uy; out.(22sz) <- 0x20uy; out.(23sz) <- 0x20uy;
  out.(24sz) <- 0x20uy; out.(25sz) <- 0x20uy; out.(26sz) <- 0x20uy; out.(27sz) <- 0x20uy;
  out.(28sz) <- 0x20uy; out.(29sz) <- 0x20uy; out.(30sz) <- 0x20uy; out.(31sz) <- 0x20uy;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 130));
  out.(32sz) <- 0x20uy; out.(33sz) <- 0x20uy; out.(34sz) <- 0x20uy; out.(35sz) <- 0x20uy;
  out.(36sz) <- 0x20uy; out.(37sz) <- 0x20uy; out.(38sz) <- 0x20uy; out.(39sz) <- 0x20uy;
  out.(40sz) <- 0x20uy; out.(41sz) <- 0x20uy; out.(42sz) <- 0x20uy; out.(43sz) <- 0x20uy;
  out.(44sz) <- 0x20uy; out.(45sz) <- 0x20uy; out.(46sz) <- 0x20uy; out.(47sz) <- 0x20uy;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 130));
  out.(48sz) <- 0x20uy; out.(49sz) <- 0x20uy; out.(50sz) <- 0x20uy; out.(51sz) <- 0x20uy;
  out.(52sz) <- 0x20uy; out.(53sz) <- 0x20uy; out.(54sz) <- 0x20uy; out.(55sz) <- 0x20uy;
  out.(56sz) <- 0x20uy; out.(57sz) <- 0x20uy; out.(58sz) <- 0x20uy; out.(59sz) <- 0x20uy;
  out.(60sz) <- 0x20uy; out.(61sz) <- 0x20uy; out.(62sz) <- 0x20uy; out.(63sz) <- 0x20uy;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 130));

  out.(64sz) <- 0x54uy; out.(65sz) <- 0x4cuy; out.(66sz) <- 0x53uy; out.(67sz) <- 0x20uy;
  out.(68sz) <- 0x31uy; out.(69sz) <- 0x2euy; out.(70sz) <- 0x33uy; out.(71sz) <- 0x2cuy;
  out.(72sz) <- 0x20uy; out.(73sz) <- 0x73uy; out.(74sz) <- 0x65uy; out.(75sz) <- 0x72uy;
  out.(76sz) <- 0x76uy; out.(77sz) <- 0x65uy; out.(78sz) <- 0x72uy; out.(79sz) <- 0x20uy;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 130));
  out.(80sz) <- 0x43uy; out.(81sz) <- 0x65uy; out.(82sz) <- 0x72uy; out.(83sz) <- 0x74uy;
  out.(84sz) <- 0x69uy; out.(85sz) <- 0x66uy; out.(86sz) <- 0x69uy; out.(87sz) <- 0x63uy;
  out.(88sz) <- 0x61uy; out.(89sz) <- 0x74uy; out.(90sz) <- 0x65uy; out.(91sz) <- 0x56uy;
  out.(92sz) <- 0x65uy; out.(93sz) <- 0x72uy; out.(94sz) <- 0x69uy; out.(95sz) <- 0x66uy;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 130));
  out.(96sz) <- 0x79uy; out.(97sz) <- 0uy;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 130));

  out.(98sz) <- transcript_hash.(0sz); out.(99sz) <- transcript_hash.(1sz);
  out.(100sz) <- transcript_hash.(2sz); out.(101sz) <- transcript_hash.(3sz);
  out.(102sz) <- transcript_hash.(4sz); out.(103sz) <- transcript_hash.(5sz);
  out.(104sz) <- transcript_hash.(6sz); out.(105sz) <- transcript_hash.(7sz);
  out.(106sz) <- transcript_hash.(8sz); out.(107sz) <- transcript_hash.(9sz);
  out.(108sz) <- transcript_hash.(10sz); out.(109sz) <- transcript_hash.(11sz);
  out.(110sz) <- transcript_hash.(12sz); out.(111sz) <- transcript_hash.(13sz);
  out.(112sz) <- transcript_hash.(14sz); out.(113sz) <- transcript_hash.(15sz);
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 130));
  out.(114sz) <- transcript_hash.(16sz); out.(115sz) <- transcript_hash.(17sz);
  out.(116sz) <- transcript_hash.(18sz); out.(117sz) <- transcript_hash.(19sz);
  out.(118sz) <- transcript_hash.(20sz); out.(119sz) <- transcript_hash.(21sz);
  out.(120sz) <- transcript_hash.(22sz); out.(121sz) <- transcript_hash.(23sz);
  out.(122sz) <- transcript_hash.(24sz); out.(123sz) <- transcript_hash.(25sz);
  out.(124sz) <- transcript_hash.(26sz); out.(125sz) <- transcript_hash.(27sz);
  out.(126sz) <- transcript_hash.(28sz); out.(127sz) <- transcript_hash.(29sz);
  out.(128sz) <- transcript_hash.(30sz); out.(129sz) <- transcript_hash.(31sz);
  with out_s. assert (pts_to out out_s);
  pts_to_len out;
  assert (pure (Seq.length out_s == 130));
}
