module TLS13.Handshake.Framing

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Cast = FStar.Int.Cast
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U16 = FStar.UInt16
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

fn serialize_client_hello_record_header
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to out 'old_bytes **
           pure (B.length 'old_bytes == SZ.v out_len /\
                 SZ.v out_len == 5)
  ensures exists* out_bytes.
          pts_to out out_bytes **
          pure (B.length out_bytes == 5)
{
  pts_to_len out;
  out.(0sz) <- 0x16uy;
  out.(1sz) <- 0x03uy;
  out.(2sz) <- 0x01uy;
  out.(3sz) <- 0uy;
  out.(4sz) <- 0x82uy;
}

fn build_supported_client_hello_localhost
  (random: array U8.t)
  (key_share: array U8.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires pts_to random 'random_bytes **
           pts_to key_share 'key_share_bytes **
           pts_to out 'old_bytes **
           pure (B.length 'random_bytes == 32 /\
                 B.length 'key_share_bytes == 32 /\
                 B.length 'old_bytes == SZ.v out_len)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to random 'random_bytes **
          pts_to key_share 'key_share_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_len /\
                (ok ==> SZ.v out_len >= 130))
{
  pts_to_len random;
  pts_to_len key_share;
  pts_to_len out;
  if SZ.(out_len <^ 130sz) {
    false
  } else {
    out.(0sz) <- 0x01uy; out.(1sz) <- 0uy; out.(2sz) <- 0uy; out.(3sz) <- 0x7euy;
    out.(4sz) <- 0x03uy; out.(5sz) <- 0x03uy;
    out.(6sz) <- random.(0sz); out.(7sz) <- random.(1sz);
    out.(8sz) <- random.(2sz); out.(9sz) <- random.(3sz);
    out.(10sz) <- random.(4sz); out.(11sz) <- random.(5sz);
    out.(12sz) <- random.(6sz); out.(13sz) <- random.(7sz);
    out.(14sz) <- random.(8sz); out.(15sz) <- random.(9sz);
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == SZ.v out_len));
    out.(16sz) <- random.(10sz); out.(17sz) <- random.(11sz);
    out.(18sz) <- random.(12sz); out.(19sz) <- random.(13sz);
    out.(20sz) <- random.(14sz); out.(21sz) <- random.(15sz);
    out.(22sz) <- random.(16sz); out.(23sz) <- random.(17sz);
    out.(24sz) <- random.(18sz); out.(25sz) <- random.(19sz);
    out.(26sz) <- random.(20sz); out.(27sz) <- random.(21sz);
    out.(28sz) <- random.(22sz); out.(29sz) <- random.(23sz);
    out.(30sz) <- random.(24sz); out.(31sz) <- random.(25sz);
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == SZ.v out_len));
    out.(32sz) <- random.(26sz); out.(33sz) <- random.(27sz);
    out.(34sz) <- random.(28sz); out.(35sz) <- random.(29sz);
    out.(36sz) <- random.(30sz); out.(37sz) <- random.(31sz);
    out.(38sz) <- 0uy; out.(39sz) <- 0uy; out.(40sz) <- 0x02uy;
    out.(41sz) <- 0x13uy; out.(42sz) <- 0x03uy;
    out.(43sz) <- 0x01uy; out.(44sz) <- 0uy;
    out.(45sz) <- 0uy; out.(46sz) <- 0x53uy;
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == SZ.v out_len));

    out.(47sz) <- 0uy; out.(48sz) <- 0uy; out.(49sz) <- 0uy; out.(50sz) <- 0x0euy;
    out.(51sz) <- 0uy; out.(52sz) <- 0x0cuy; out.(53sz) <- 0uy; out.(54sz) <- 0uy;
    out.(55sz) <- 0x09uy;
    out.(56sz) <- 0x6cuy; out.(57sz) <- 0x6fuy; out.(58sz) <- 0x63uy; out.(59sz) <- 0x61uy;
    out.(60sz) <- 0x6cuy; out.(61sz) <- 0x68uy; out.(62sz) <- 0x6fuy; out.(63sz) <- 0x73uy;
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == SZ.v out_len));
    out.(64sz) <- 0x74uy;
    out.(65sz) <- 0uy; out.(66sz) <- 0x0auy; out.(67sz) <- 0uy; out.(68sz) <- 0x04uy;
    out.(69sz) <- 0uy; out.(70sz) <- 0x02uy; out.(71sz) <- 0uy; out.(72sz) <- 0x1duy;
    out.(73sz) <- 0uy; out.(74sz) <- 0x0duy; out.(75sz) <- 0uy; out.(76sz) <- 0x04uy;
    out.(77sz) <- 0uy; out.(78sz) <- 0x02uy; out.(79sz) <- 0x08uy; out.(80sz) <- 0x04uy;
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == SZ.v out_len));

    out.(81sz) <- 0uy; out.(82sz) <- 0x33uy; out.(83sz) <- 0uy; out.(84sz) <- 0x26uy;
    out.(85sz) <- 0uy; out.(86sz) <- 0x24uy; out.(87sz) <- 0uy; out.(88sz) <- 0x1duy;
    out.(89sz) <- 0uy; out.(90sz) <- 0x20uy;
    out.(91sz) <- key_share.(0sz); out.(92sz) <- key_share.(1sz);
    out.(93sz) <- key_share.(2sz); out.(94sz) <- key_share.(3sz);
    out.(95sz) <- key_share.(4sz); out.(96sz) <- key_share.(5sz);
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == SZ.v out_len));
    out.(97sz) <- key_share.(6sz); out.(98sz) <- key_share.(7sz);
    out.(99sz) <- key_share.(8sz); out.(100sz) <- key_share.(9sz);
    out.(101sz) <- key_share.(10sz); out.(102sz) <- key_share.(11sz);
    out.(103sz) <- key_share.(12sz); out.(104sz) <- key_share.(13sz);
    out.(105sz) <- key_share.(14sz); out.(106sz) <- key_share.(15sz);
    out.(107sz) <- key_share.(16sz); out.(108sz) <- key_share.(17sz);
    out.(109sz) <- key_share.(18sz); out.(110sz) <- key_share.(19sz);
    out.(111sz) <- key_share.(20sz); out.(112sz) <- key_share.(21sz);
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == SZ.v out_len));
    out.(113sz) <- key_share.(22sz); out.(114sz) <- key_share.(23sz);
    out.(115sz) <- key_share.(24sz); out.(116sz) <- key_share.(25sz);
    out.(117sz) <- key_share.(26sz); out.(118sz) <- key_share.(27sz);
    out.(119sz) <- key_share.(28sz); out.(120sz) <- key_share.(29sz);
    out.(121sz) <- key_share.(30sz); out.(122sz) <- key_share.(31sz);
    out.(123sz) <- 0uy; out.(124sz) <- 0x2buy; out.(125sz) <- 0uy; out.(126sz) <- 0x03uy;
    out.(127sz) <- 0x02uy; out.(128sz) <- 0x03uy; out.(129sz) <- 0x04uy;
    pts_to_len out;
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == SZ.v out_len));
    true
  }
}

fn parse_handshake_header
  (input: array U8.t)
  (input_len: SZ.t)
  (msg_type_out: array U8.t)
  (msg_type_out_len: SZ.t)
  (body_len_out: array U8.t)
  (body_len_out_len: SZ.t)
  requires pts_to input 'input_bytes **
           pts_to msg_type_out 'old_msg_type **
           pts_to body_len_out 'old_body_len **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 B.length 'old_msg_type == SZ.v msg_type_out_len /\
                 B.length 'old_body_len == SZ.v body_len_out_len /\
                 SZ.v msg_type_out_len == 1 /\
                 SZ.v body_len_out_len == 3)
  returns ok: bool
  ensures exists* msg_type_bytes body_len_bytes.
          pts_to input 'input_bytes **
          pts_to msg_type_out msg_type_bytes **
          pts_to body_len_out body_len_bytes **
          pure (B.length msg_type_bytes == 1 /\
                B.length body_len_bytes == 3 /\
                (ok ==> SZ.v input_len >= 4) /\
                (not ok ==> SZ.v input_len < 4))
{
  pts_to_len input;
  pts_to_len msg_type_out;
  pts_to_len body_len_out;
  if SZ.(input_len <^ 4sz) {
    false
  } else {
    let b0 = input.(0sz);
    let b1 = input.(1sz);
    let b2 = input.(2sz);
    let b3 = input.(3sz);
    msg_type_out.(0sz) <- b0;
    body_len_out.(0sz) <- b1;
    body_len_out.(1sz) <- b2;
    body_len_out.(2sz) <- b3;
    true
  }
}

fn copy_server_hello_random
  (input: array U8.t)
  (random_out: array U8.t)
  requires pts_to input 'input_bytes **
           pts_to random_out 'old_random **
           pure (B.length 'input_bytes == 90 /\ B.length 'old_random == 32)
  ensures exists* random_bytes.
          pts_to input 'input_bytes **
          pts_to random_out random_bytes **
          pure (B.length random_bytes == 32)
{
  random_out.(0sz) <- input.(6sz); random_out.(1sz) <- input.(7sz);
  random_out.(2sz) <- input.(8sz); random_out.(3sz) <- input.(9sz);
  random_out.(4sz) <- input.(10sz); random_out.(5sz) <- input.(11sz);
  random_out.(6sz) <- input.(12sz); random_out.(7sz) <- input.(13sz);
  random_out.(8sz) <- input.(14sz); random_out.(9sz) <- input.(15sz);
  random_out.(10sz) <- input.(16sz); random_out.(11sz) <- input.(17sz);
  random_out.(12sz) <- input.(18sz); random_out.(13sz) <- input.(19sz);
  random_out.(14sz) <- input.(20sz); random_out.(15sz) <- input.(21sz);
  with random_s. assert (pts_to random_out random_s);
  assert (pure (Seq.length random_s == 32));
  random_out.(16sz) <- input.(22sz); random_out.(17sz) <- input.(23sz);
  random_out.(18sz) <- input.(24sz); random_out.(19sz) <- input.(25sz);
  random_out.(20sz) <- input.(26sz); random_out.(21sz) <- input.(27sz);
  random_out.(22sz) <- input.(28sz); random_out.(23sz) <- input.(29sz);
  random_out.(24sz) <- input.(30sz); random_out.(25sz) <- input.(31sz);
  random_out.(26sz) <- input.(32sz); random_out.(27sz) <- input.(33sz);
  random_out.(28sz) <- input.(34sz); random_out.(29sz) <- input.(35sz);
  random_out.(30sz) <- input.(36sz); random_out.(31sz) <- input.(37sz);
}

fn copy_server_key_share_at_52
  (input: array U8.t)
  (key_share_out: array U8.t)
  requires pts_to input 'input_bytes **
           pts_to key_share_out 'old_key_share **
           pure (B.length 'input_bytes == 90 /\ B.length 'old_key_share == 32)
  ensures exists* key_share_bytes.
          pts_to input 'input_bytes **
          pts_to key_share_out key_share_bytes **
          pure (B.length key_share_bytes == 32)
{
  key_share_out.(0sz) <- input.(52sz); key_share_out.(1sz) <- input.(53sz);
  key_share_out.(2sz) <- input.(54sz); key_share_out.(3sz) <- input.(55sz);
  key_share_out.(4sz) <- input.(56sz); key_share_out.(5sz) <- input.(57sz);
  key_share_out.(6sz) <- input.(58sz); key_share_out.(7sz) <- input.(59sz);
  key_share_out.(8sz) <- input.(60sz); key_share_out.(9sz) <- input.(61sz);
  key_share_out.(10sz) <- input.(62sz); key_share_out.(11sz) <- input.(63sz);
  key_share_out.(12sz) <- input.(64sz); key_share_out.(13sz) <- input.(65sz);
  key_share_out.(14sz) <- input.(66sz); key_share_out.(15sz) <- input.(67sz);
  with key_share_s. assert (pts_to key_share_out key_share_s);
  assert (pure (Seq.length key_share_s == 32));
  key_share_out.(16sz) <- input.(68sz); key_share_out.(17sz) <- input.(69sz);
  key_share_out.(18sz) <- input.(70sz); key_share_out.(19sz) <- input.(71sz);
  key_share_out.(20sz) <- input.(72sz); key_share_out.(21sz) <- input.(73sz);
  key_share_out.(22sz) <- input.(74sz); key_share_out.(23sz) <- input.(75sz);
  key_share_out.(24sz) <- input.(76sz); key_share_out.(25sz) <- input.(77sz);
  key_share_out.(26sz) <- input.(78sz); key_share_out.(27sz) <- input.(79sz);
  key_share_out.(28sz) <- input.(80sz); key_share_out.(29sz) <- input.(81sz);
  key_share_out.(30sz) <- input.(82sz); key_share_out.(31sz) <- input.(83sz);
}

fn copy_server_key_share_at_58
  (input: array U8.t)
  (key_share_out: array U8.t)
  requires pts_to input 'input_bytes **
           pts_to key_share_out 'old_key_share **
           pure (B.length 'input_bytes == 90 /\ B.length 'old_key_share == 32)
  ensures exists* key_share_bytes.
          pts_to input 'input_bytes **
          pts_to key_share_out key_share_bytes **
          pure (B.length key_share_bytes == 32)
{
  key_share_out.(0sz) <- input.(58sz); key_share_out.(1sz) <- input.(59sz);
  key_share_out.(2sz) <- input.(60sz); key_share_out.(3sz) <- input.(61sz);
  key_share_out.(4sz) <- input.(62sz); key_share_out.(5sz) <- input.(63sz);
  key_share_out.(6sz) <- input.(64sz); key_share_out.(7sz) <- input.(65sz);
  key_share_out.(8sz) <- input.(66sz); key_share_out.(9sz) <- input.(67sz);
  key_share_out.(10sz) <- input.(68sz); key_share_out.(11sz) <- input.(69sz);
  key_share_out.(12sz) <- input.(70sz); key_share_out.(13sz) <- input.(71sz);
  key_share_out.(14sz) <- input.(72sz); key_share_out.(15sz) <- input.(73sz);
  with key_share_s. assert (pts_to key_share_out key_share_s);
  assert (pure (Seq.length key_share_s == 32));
  key_share_out.(16sz) <- input.(74sz); key_share_out.(17sz) <- input.(75sz);
  key_share_out.(18sz) <- input.(76sz); key_share_out.(19sz) <- input.(77sz);
  key_share_out.(20sz) <- input.(78sz); key_share_out.(21sz) <- input.(79sz);
  key_share_out.(22sz) <- input.(80sz); key_share_out.(23sz) <- input.(81sz);
  key_share_out.(24sz) <- input.(82sz); key_share_out.(25sz) <- input.(83sz);
  key_share_out.(26sz) <- input.(84sz); key_share_out.(27sz) <- input.(85sz);
  key_share_out.(28sz) <- input.(86sz); key_share_out.(29sz) <- input.(87sz);
  key_share_out.(30sz) <- input.(88sz); key_share_out.(31sz) <- input.(89sz);
}

fn parse_supported_server_hello
  (input: array U8.t)
  (input_len: SZ.t)
  (random_out: array U8.t)
  (random_out_len: SZ.t)
  (key_share_out: array U8.t)
  (key_share_out_len: SZ.t)
  requires pts_to input 'input_bytes **
           pts_to random_out 'old_random **
           pts_to key_share_out 'old_key_share **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 B.length 'old_random == SZ.v random_out_len /\
                 B.length 'old_key_share == SZ.v key_share_out_len /\
                 SZ.v random_out_len == 32 /\
                 SZ.v key_share_out_len == 32)
  returns ok: bool
  ensures exists* random_bytes key_share_bytes.
          pts_to input 'input_bytes **
          pts_to random_out random_bytes **
          pts_to key_share_out key_share_bytes **
          pure (B.length random_bytes == 32 /\
                B.length key_share_bytes == 32 /\
                (ok ==> SZ.v input_len == 90))
{
  pts_to_len input;
  pts_to_len random_out;
  pts_to_len key_share_out;
  if SZ.(input_len =^ 90sz) {
    let header_ok =
      (input.(0sz) = 0x02uy) && (input.(1sz) = 0uy) &&
      (input.(2sz) = 0uy) && (input.(3sz) = 0x56uy) &&
      (input.(4sz) = 0x03uy) && (input.(5sz) = 0x03uy) &&
      (input.(38sz) = 0uy) &&
      (input.(39sz) = 0x13uy) && (input.(40sz) = 0x03uy) &&
      (input.(41sz) = 0uy) &&
      (input.(42sz) = 0uy) && (input.(43sz) = 0x2euy);
    let hrr =
      (input.(6sz) = 0xcfuy) && (input.(7sz) = 0x21uy) &&
      (input.(8sz) = 0xaduy) && (input.(9sz) = 0x74uy) &&
      (input.(10sz) = 0xe5uy) && (input.(11sz) = 0x9auy) &&
      (input.(12sz) = 0x61uy) && (input.(13sz) = 0x11uy) &&
      (input.(14sz) = 0xbeuy) && (input.(15sz) = 0x1duy) &&
      (input.(16sz) = 0x8cuy) && (input.(17sz) = 0x02uy) &&
      (input.(18sz) = 0x1euy) && (input.(19sz) = 0x65uy) &&
      (input.(20sz) = 0xb8uy) && (input.(21sz) = 0x91uy) &&
      (input.(22sz) = 0xc2uy) && (input.(23sz) = 0xa2uy) &&
      (input.(24sz) = 0x11uy) && (input.(25sz) = 0x16uy) &&
      (input.(26sz) = 0x7auy) && (input.(27sz) = 0xbbuy) &&
      (input.(28sz) = 0x8cuy) && (input.(29sz) = 0x5euy) &&
      (input.(30sz) = 0x07uy) && (input.(31sz) = 0x9euy) &&
      (input.(32sz) = 0x09uy) && (input.(33sz) = 0xe2uy) &&
      (input.(34sz) = 0xc8uy) && (input.(35sz) = 0xa8uy) &&
      (input.(36sz) = 0x33uy) && (input.(37sz) = 0x9cuy);
    let key_share_first =
      (input.(44sz) = 0uy) && (input.(45sz) = 0x33uy) &&
      (input.(46sz) = 0uy) && (input.(47sz) = 0x24uy) &&
      (input.(48sz) = 0uy) && (input.(49sz) = 0x1duy) &&
      (input.(50sz) = 0uy) && (input.(51sz) = 0x20uy) &&
      (input.(84sz) = 0uy) && (input.(85sz) = 0x2buy) &&
      (input.(86sz) = 0uy) && (input.(87sz) = 0x02uy) &&
      (input.(88sz) = 0x03uy) && (input.(89sz) = 0x04uy);
    let supported_versions_first =
      (input.(44sz) = 0uy) && (input.(45sz) = 0x2buy) &&
      (input.(46sz) = 0uy) && (input.(47sz) = 0x02uy) &&
      (input.(48sz) = 0x03uy) && (input.(49sz) = 0x04uy) &&
      (input.(50sz) = 0uy) && (input.(51sz) = 0x33uy) &&
      (input.(52sz) = 0uy) && (input.(53sz) = 0x24uy) &&
      (input.(54sz) = 0uy) && (input.(55sz) = 0x1duy) &&
      (input.(56sz) = 0uy) && (input.(57sz) = 0x20uy);
    if (header_ok && (not hrr)) {
      copy_server_hello_random input random_out;
      if key_share_first {
        copy_server_key_share_at_52 input key_share_out;
        true
      } else if supported_versions_first {
        copy_server_key_share_at_58 input key_share_out;
        true
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}

fn parse_certificate_verify_body
  (input: array U8.t)
  (input_len: SZ.t)
  (signature_scheme_out: array U8.t)
  (signature_scheme_out_len: SZ.t)
  (signature_len_out: array U8.t)
  (signature_len_out_len: SZ.t)
  requires pts_to input 'input_bytes **
           pts_to signature_scheme_out 'old_signature_scheme **
           pts_to signature_len_out 'old_signature_len **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 B.length 'old_signature_scheme == SZ.v signature_scheme_out_len /\
                 B.length 'old_signature_len == SZ.v signature_len_out_len /\
                 SZ.v signature_scheme_out_len == 2 /\
                 SZ.v signature_len_out_len == 2)
  returns ok: bool
  ensures exists* signature_scheme_bytes signature_len_bytes.
          pts_to input 'input_bytes **
          pts_to signature_scheme_out signature_scheme_bytes **
          pts_to signature_len_out signature_len_bytes **
          pure (B.length signature_scheme_bytes == 2 /\
                B.length signature_len_bytes == 2 /\
                (ok ==> SZ.v input_len >= 4))
{
  pts_to_len input;
  pts_to_len signature_scheme_out;
  pts_to_len signature_len_out;
  if SZ.(input_len <^ 4sz) {
    false
  } else {
    let b0 = input.(0sz);
    let b1 = input.(1sz);
    let b2 = input.(2sz);
    let b3 = input.(3sz);
    signature_scheme_out.(0sz) <- b0;
    signature_scheme_out.(1sz) <- b1;
    signature_len_out.(0sz) <- b2;
    signature_len_out.(1sz) <- b3;
    let sig_len_hi = Cast.uint8_to_uint16 b2;
    let sig_len_lo = Cast.uint8_to_uint16 b3;
    let sig_len = U16.logor (U16.shift_left sig_len_hi 8ul) sig_len_lo;
    let expected_payload_len = SZ.uint16_to_sizet sig_len;
    let actual_payload_len = SZ.(input_len -^ 4sz);
    SZ.(actual_payload_len =^ expected_payload_len)
  }
}

fn parse_certificate_leaf_der_offsets
  (input: array U8.t)
  (input_len: SZ.t)
  (leaf_offset_out: array U8.t)
  (leaf_offset_out_len: SZ.t)
  (leaf_len_out: array U8.t)
  (leaf_len_out_len: SZ.t)
  requires pts_to input 'input_bytes **
           pts_to leaf_offset_out 'old_leaf_offset **
           pts_to leaf_len_out 'old_leaf_len **
           pure (B.length 'input_bytes == SZ.v input_len /\
                 B.length 'old_leaf_offset == SZ.v leaf_offset_out_len /\
                 B.length 'old_leaf_len == SZ.v leaf_len_out_len /\
                 SZ.v leaf_offset_out_len == 2 /\
                 SZ.v leaf_len_out_len == 2)
  returns ok: bool
  ensures exists* leaf_offset_bytes leaf_len_bytes.
          pts_to input 'input_bytes **
          pts_to leaf_offset_out leaf_offset_bytes **
          pts_to leaf_len_out leaf_len_bytes **
          pure (B.length leaf_offset_bytes == 2 /\
                B.length leaf_len_bytes == 2 /\
                (ok ==> SZ.v input_len >= 9))
{
  pts_to_len input;
  pts_to_len leaf_offset_out;
  pts_to_len leaf_len_out;
  if SZ.(input_len <^ 9sz) {
    false
  } else {
    let request_context_len = input.(0sz);
    let list_len_hi = input.(1sz);
    let list_len_b0 = input.(2sz);
    let list_len_b1 = input.(3sz);
    let cert_len_hi = input.(4sz);
    let cert_len_b0 = input.(5sz);
    let cert_len_b1 = input.(6sz);
    if ((request_context_len = 0uy) && (list_len_hi = 0uy) && (cert_len_hi = 0uy)) {
      let list_len_hi16 = Cast.uint8_to_uint16 list_len_b0;
      let list_len_lo16 = Cast.uint8_to_uint16 list_len_b1;
      let list_len16 = U16.logor (U16.shift_left list_len_hi16 8ul) list_len_lo16;
      let list_len = SZ.uint16_to_sizet list_len16;
      let actual_list_len = SZ.(input_len -^ 4sz);
      if SZ.(actual_list_len =^ list_len) {
        let cert_len_hi16 = Cast.uint8_to_uint16 cert_len_b0;
        let cert_len_lo16 = Cast.uint8_to_uint16 cert_len_b1;
        let cert_len16 = U16.logor (U16.shift_left cert_len_hi16 8ul) cert_len_lo16;
        let cert_len = SZ.uint16_to_sizet cert_len16;
        let payload_after_cert_header = SZ.(input_len -^ 7sz);
        if (SZ.(cert_len =^ 0sz) || SZ.(payload_after_cert_header <^ cert_len)) {
          false
        } else {
          let rest_after_cert = SZ.(payload_after_cert_header -^ cert_len);
          if SZ.(rest_after_cert <^ 2sz) {
            false
          } else {
            let rest_after_first_ext_len_byte = SZ.(rest_after_cert -^ 1sz);
            let ext_len_b0 = input.(SZ.(input_len -^ rest_after_cert));
            let ext_len_b1 = input.(SZ.(input_len -^ rest_after_first_ext_len_byte));
            let ext_len_hi16 = Cast.uint8_to_uint16 ext_len_b0;
            let ext_len_lo16 = Cast.uint8_to_uint16 ext_len_b1;
            let ext_len16 = U16.logor (U16.shift_left ext_len_hi16 8ul) ext_len_lo16;
            let ext_len = SZ.uint16_to_sizet ext_len16;
            let actual_ext_len = SZ.(rest_after_cert -^ 2sz);
            if SZ.(actual_ext_len =^ ext_len) {
              leaf_offset_out.(0sz) <- 0uy;
              leaf_offset_out.(1sz) <- 7uy;
              leaf_len_out.(0sz) <- cert_len_b0;
              leaf_len_out.(1sz) <- cert_len_b1;
              true
            } else {
              false
            }
          }
        }
      } else {
        false
      }
    } else {
      false
    }
  }
}
