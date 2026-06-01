module TLS13.Handshake.FlightState

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module Cast = FStar.Int.Cast
module Crypto = TLS13.Crypto
module HF = TLS13.Handshake.Framing
module KS = TLS13.KeySchedule
module Rec = TLS13.Record
module RF = TLS13.Record.Framing
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Transcript = TLS13.Handshake.Transcript
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

noeq
type flight_state = {
  handshake_len_box: box SZ.t;
  parsed_len_box: box SZ.t;
  client_hello_len_box: box SZ.t;
  server_hello_len_box: box SZ.t;
  client_hello: V.vec U8.t;
  client_hello_random: V.vec U8.t;
  client_hello_key_share: V.vec U8.t;
  server_hello: V.vec U8.t;
  server_handshake_messages: V.vec U8.t;
  certificate_verify_offset_box: box SZ.t;
  certificate_leaf_offset_box: box SZ.t;
  certificate_leaf_len_box: box SZ.t;
  certificate_verify_signature_scheme_box: box U16.t;
  certificate_verify_signature_offset_box: box SZ.t;
  certificate_verify_signature_len_box: box SZ.t;
  handshake_secret: V.vec U8.t;
  client_handshake_traffic_secret: V.vec U8.t;
  client_handshake_key: V.vec U8.t;
  client_handshake_iv: V.vec U8.t;
  server_handshake_traffic_secret: V.vec U8.t;
  server_handshake_key: V.vec U8.t;
  server_handshake_iv: V.vec U8.t;
  server_handshake_record_state: Rec.record_state;
  server_finished_verify_data: V.vec U8.t;
  client_finished_verify_data: V.vec U8.t;
  before_finished_len_box: box SZ.t;
  through_finished_len_box: box SZ.t;
  saw_encrypted_extensions_box: box bool;
  saw_certificate_box: box bool;
  saw_certificate_verify_box: box bool;
  certificate_verify_verified_box: box bool;
  saw_finished_box: box bool;
}

let is_flight_state ([@@@mkey] st: flight_state) : slprop =
  exists* handshake_len parsed_len client_hello_len server_hello_len client_hello client_hello_random client_hello_key_share server_hello server_handshake_messages
          certificate_verify_offset certificate_leaf_offset certificate_leaf_len
          certificate_verify_signature_scheme certificate_verify_signature_offset certificate_verify_signature_len
          handshake_secret client_handshake_traffic_secret client_handshake_key client_handshake_iv server_handshake_traffic_secret
          server_handshake_key server_handshake_iv server_handshake_record_state server_finished_verify_data client_finished_verify_data
          before_finished_len through_finished_len
          saw_encrypted_extensions saw_certificate saw_certificate_verify certificate_verify_verified saw_finished.
    Box.pts_to st.handshake_len_box handshake_len **
    Box.pts_to st.parsed_len_box parsed_len **
    Box.pts_to st.client_hello_len_box client_hello_len **
    Box.pts_to st.server_hello_len_box server_hello_len **
    V.pts_to st.client_hello client_hello **
    V.pts_to st.client_hello_random client_hello_random **
    V.pts_to st.client_hello_key_share client_hello_key_share **
    V.pts_to st.server_hello server_hello **
    V.pts_to st.server_handshake_messages server_handshake_messages **
    Box.pts_to st.certificate_verify_offset_box certificate_verify_offset **
    Box.pts_to st.certificate_leaf_offset_box certificate_leaf_offset **
    Box.pts_to st.certificate_leaf_len_box certificate_leaf_len **
    Box.pts_to st.certificate_verify_signature_scheme_box certificate_verify_signature_scheme **
    Box.pts_to st.certificate_verify_signature_offset_box certificate_verify_signature_offset **
    Box.pts_to st.certificate_verify_signature_len_box certificate_verify_signature_len **
    V.pts_to st.handshake_secret handshake_secret **
    V.pts_to st.client_handshake_traffic_secret client_handshake_traffic_secret **
    V.pts_to st.client_handshake_key client_handshake_key **
    V.pts_to st.client_handshake_iv client_handshake_iv **
    V.pts_to st.server_handshake_traffic_secret server_handshake_traffic_secret **
    V.pts_to st.server_handshake_key server_handshake_key **
    V.pts_to st.server_handshake_iv server_handshake_iv **
    Rec.is_record_state st.server_handshake_record_state server_handshake_record_state **
    V.pts_to st.server_finished_verify_data server_finished_verify_data **
    V.pts_to st.client_finished_verify_data client_finished_verify_data **
    Box.pts_to st.before_finished_len_box before_finished_len **
    Box.pts_to st.through_finished_len_box through_finished_len **
    Box.pts_to st.saw_encrypted_extensions_box saw_encrypted_extensions **
    Box.pts_to st.saw_certificate_box saw_certificate **
    Box.pts_to st.saw_certificate_verify_box saw_certificate_verify **
    Box.pts_to st.certificate_verify_verified_box certificate_verify_verified **
    Box.pts_to st.saw_finished_box saw_finished **
    pure (V.is_full_vec st.client_hello /\
    V.is_full_vec st.client_hello_random /\
    V.is_full_vec st.client_hello_key_share /\
    V.is_full_vec st.server_hello /\
    V.is_full_vec st.server_handshake_messages /\
    V.is_full_vec st.handshake_secret /\
          V.is_full_vec st.client_handshake_traffic_secret /\
    V.is_full_vec st.client_handshake_key /\
    V.is_full_vec st.client_handshake_iv /\
    V.is_full_vec st.server_handshake_traffic_secret /\
          V.is_full_vec st.server_handshake_key /\
          V.is_full_vec st.server_handshake_iv /\
          V.is_full_vec st.server_finished_verify_data /\
          V.is_full_vec st.client_finished_verify_data /\
          V.length st.client_hello == 512 /\
          V.length st.client_hello_random == 32 /\
          V.length st.client_hello_key_share == 32 /\
          V.length st.server_hello == 4096 /\
          V.length st.server_handshake_messages == 32768 /\
          V.length st.handshake_secret == 32 /\
          V.length st.client_handshake_traffic_secret == 32 /\
          V.length st.client_handshake_key == 32 /\
          V.length st.client_handshake_iv == 12 /\
          V.length st.server_handshake_traffic_secret == 32 /\
          V.length st.server_handshake_key == 32 /\
          V.length st.server_handshake_iv == 12 /\
          V.length st.server_finished_verify_data == 32 /\
          V.length st.client_finished_verify_data == 32 /\
          SZ.v client_hello_len <= 512 /\
          SZ.v server_hello_len <= 4096 /\
          SZ.v handshake_len <= 32768 /\
          SZ.v parsed_len <= SZ.v handshake_len /\
          SZ.v before_finished_len <= SZ.v handshake_len /\
          SZ.v through_finished_len <= SZ.v handshake_len /\
          SZ.v certificate_leaf_len <= 32768 /\
          SZ.v certificate_verify_signature_len <= 32768)

let flight_state_exactly ([@@@mkey] st: flight_state) (view: flight_view) : slprop =
  exists* handshake_len parsed_len client_hello_len server_hello_len client_hello client_hello_random client_hello_key_share server_hello server_handshake_messages
          certificate_verify_offset certificate_leaf_offset certificate_leaf_len
          certificate_verify_signature_scheme certificate_verify_signature_offset certificate_verify_signature_len
          handshake_secret client_handshake_traffic_secret client_handshake_key client_handshake_iv server_handshake_traffic_secret
          server_handshake_key server_handshake_iv server_handshake_record_state server_finished_verify_data client_finished_verify_data
          before_finished_len through_finished_len
          saw_encrypted_extensions saw_certificate saw_certificate_verify certificate_verify_verified saw_finished.
    Box.pts_to st.handshake_len_box handshake_len **
    Box.pts_to st.parsed_len_box parsed_len **
    Box.pts_to st.client_hello_len_box client_hello_len **
    Box.pts_to st.server_hello_len_box server_hello_len **
    V.pts_to st.client_hello client_hello **
    V.pts_to st.client_hello_random client_hello_random **
    V.pts_to st.client_hello_key_share client_hello_key_share **
    V.pts_to st.server_hello server_hello **
    V.pts_to st.server_handshake_messages server_handshake_messages **
    Box.pts_to st.certificate_verify_offset_box certificate_verify_offset **
    Box.pts_to st.certificate_leaf_offset_box certificate_leaf_offset **
    Box.pts_to st.certificate_leaf_len_box certificate_leaf_len **
    Box.pts_to st.certificate_verify_signature_scheme_box certificate_verify_signature_scheme **
    Box.pts_to st.certificate_verify_signature_offset_box certificate_verify_signature_offset **
    Box.pts_to st.certificate_verify_signature_len_box certificate_verify_signature_len **
    V.pts_to st.handshake_secret handshake_secret **
    V.pts_to st.client_handshake_traffic_secret client_handshake_traffic_secret **
    V.pts_to st.client_handshake_key client_handshake_key **
    V.pts_to st.client_handshake_iv client_handshake_iv **
    V.pts_to st.server_handshake_traffic_secret server_handshake_traffic_secret **
    V.pts_to st.server_handshake_key server_handshake_key **
    V.pts_to st.server_handshake_iv server_handshake_iv **
    Rec.is_record_state st.server_handshake_record_state server_handshake_record_state **
    V.pts_to st.server_finished_verify_data server_finished_verify_data **
    V.pts_to st.client_finished_verify_data client_finished_verify_data **
    Box.pts_to st.before_finished_len_box before_finished_len **
    Box.pts_to st.through_finished_len_box through_finished_len **
    Box.pts_to st.saw_encrypted_extensions_box saw_encrypted_extensions **
    Box.pts_to st.saw_certificate_box saw_certificate **
    Box.pts_to st.saw_certificate_verify_box saw_certificate_verify **
    Box.pts_to st.certificate_verify_verified_box certificate_verify_verified **
    Box.pts_to st.saw_finished_box saw_finished **
    pure (V.is_full_vec st.client_hello /\
    V.is_full_vec st.client_hello_random /\
    V.is_full_vec st.client_hello_key_share /\
    V.is_full_vec st.server_hello /\
          V.is_full_vec st.server_handshake_messages /\
          V.is_full_vec st.handshake_secret /\
          V.is_full_vec st.client_handshake_traffic_secret /\
          V.is_full_vec st.client_handshake_key /\
          V.is_full_vec st.client_handshake_iv /\
          V.is_full_vec st.server_handshake_traffic_secret /\
          V.is_full_vec st.server_handshake_key /\
          V.is_full_vec st.server_handshake_iv /\
          V.is_full_vec st.server_finished_verify_data /\
          V.is_full_vec st.client_finished_verify_data /\
          V.length st.client_hello == 512 /\
          V.length st.client_hello_random == 32 /\
          V.length st.client_hello_key_share == 32 /\
          V.length st.server_hello == 4096 /\
          V.length st.server_handshake_messages == 32768 /\
          V.length st.handshake_secret == 32 /\
          V.length st.client_handshake_traffic_secret == 32 /\
          V.length st.client_handshake_key == 32 /\
          V.length st.client_handshake_iv == 12 /\
          V.length st.server_handshake_traffic_secret == 32 /\
          V.length st.server_handshake_key == 32 /\
          V.length st.server_handshake_iv == 12 /\
          V.length st.server_finished_verify_data == 32 /\
          V.length st.client_finished_verify_data == 32 /\
          SZ.v client_hello_len <= 512 /\
          SZ.v server_hello_len <= 4096 /\
          SZ.v handshake_len <= 32768 /\
          SZ.v parsed_len <= SZ.v handshake_len /\
          SZ.v before_finished_len <= SZ.v handshake_len /\
          SZ.v through_finished_len <= SZ.v handshake_len /\
          SZ.v certificate_leaf_len <= 32768 /\
          SZ.v certificate_verify_signature_len <= 32768 /\
          view.client_hello_len == client_hello_len /\
          view.server_hello_len == server_hello_len /\
          view.server_handshake_len == handshake_len /\
          view.server_handshake_parsed_len == parsed_len /\
          view.certificate_verify_offset == certificate_verify_offset /\
          view.certificate_leaf_offset == certificate_leaf_offset /\
          view.certificate_leaf_len == certificate_leaf_len /\
          view.certificate_verify_signature_scheme == certificate_verify_signature_scheme /\
          view.certificate_verify_signature_offset == certificate_verify_signature_offset /\
          view.certificate_verify_signature_len == certificate_verify_signature_len /\
          view.client_hello_bytes == client_hello /\
          view.client_hello_random == client_hello_random /\
          view.client_hello_key_share == client_hello_key_share /\
          view.server_hello_bytes == server_hello /\
          view.server_handshake_bytes == server_handshake_messages /\
          view.server_finished_verify_data == server_finished_verify_data /\
          view.client_finished_verify_data == client_finished_verify_data /\
          view.saw_encrypted_extensions == saw_encrypted_extensions /\
          view.saw_certificate == saw_certificate /\
          view.saw_certificate_verify == saw_certificate_verify /\
          view.certificate_verify_verified == certificate_verify_verified /\
          view.saw_finished == saw_finished /\
          view.server_before_finished_len == before_finished_len /\
          view.server_through_finished_len == through_finished_len)

ghost
fn reveal_flight_view (st: flight_state)
  requires is_flight_state st
  ensures exists* view. flight_state_exactly st view
{
  unfold (is_flight_state st);
  with handshake_len. assert (Box.pts_to st.handshake_len_box handshake_len);
  with parsed_len. assert (Box.pts_to st.parsed_len_box parsed_len);
  with client_hello_len. assert (Box.pts_to st.client_hello_len_box client_hello_len);
  with server_hello_len. assert (Box.pts_to st.server_hello_len_box server_hello_len);
  with client_hello. assert (V.pts_to st.client_hello client_hello);
  with client_hello_random. assert (V.pts_to st.client_hello_random client_hello_random);
  V.pts_to_len st.client_hello_random;
  assert (pure (B.length client_hello_random == 32));
  with client_hello_key_share. assert (V.pts_to st.client_hello_key_share client_hello_key_share);
  V.pts_to_len st.client_hello_key_share;
  assert (pure (B.length client_hello_key_share == 32));
  with server_hello. assert (V.pts_to st.server_hello server_hello);
  with server_handshake_messages. assert (V.pts_to st.server_handshake_messages server_handshake_messages);
  with certificate_verify_offset. assert (Box.pts_to st.certificate_verify_offset_box certificate_verify_offset);
  with certificate_leaf_offset. assert (Box.pts_to st.certificate_leaf_offset_box certificate_leaf_offset);
  with certificate_leaf_len. assert (Box.pts_to st.certificate_leaf_len_box certificate_leaf_len);
  with certificate_verify_signature_scheme. assert (Box.pts_to st.certificate_verify_signature_scheme_box certificate_verify_signature_scheme);
  with certificate_verify_signature_offset. assert (Box.pts_to st.certificate_verify_signature_offset_box certificate_verify_signature_offset);
  with certificate_verify_signature_len. assert (Box.pts_to st.certificate_verify_signature_len_box certificate_verify_signature_len);
  with server_finished_verify_data. assert (V.pts_to st.server_finished_verify_data server_finished_verify_data);
  V.pts_to_len st.server_finished_verify_data;
  assert (pure (B.length server_finished_verify_data == 32));
  with client_finished_verify_data. assert (V.pts_to st.client_finished_verify_data client_finished_verify_data);
  V.pts_to_len st.client_finished_verify_data;
  assert (pure (B.length client_finished_verify_data == 32));
  with before_finished_len. assert (Box.pts_to st.before_finished_len_box before_finished_len);
  with through_finished_len. assert (Box.pts_to st.through_finished_len_box through_finished_len);
  with saw_encrypted_extensions. assert (Box.pts_to st.saw_encrypted_extensions_box saw_encrypted_extensions);
  with saw_certificate. assert (Box.pts_to st.saw_certificate_box saw_certificate);
  with saw_certificate_verify. assert (Box.pts_to st.saw_certificate_verify_box saw_certificate_verify);
  with certificate_verify_verified. assert (Box.pts_to st.certificate_verify_verified_box certificate_verify_verified);
  with saw_finished. assert (Box.pts_to st.saw_finished_box saw_finished);
  let view = {
    client_hello_bytes = client_hello;
    client_hello_random = client_hello_random;
    client_hello_key_share = client_hello_key_share;
    server_hello_bytes = server_hello;
    server_handshake_bytes = server_handshake_messages;
    server_finished_verify_data = server_finished_verify_data;
    client_finished_verify_data = client_finished_verify_data;
    client_hello_len;
    server_hello_len;
    server_handshake_len = handshake_len;
    server_handshake_parsed_len = parsed_len;
    certificate_verify_offset;
    certificate_leaf_offset;
    certificate_leaf_len;
    certificate_verify_signature_scheme;
    certificate_verify_signature_offset;
    certificate_verify_signature_len;
    saw_encrypted_extensions;
    saw_certificate;
    saw_certificate_verify;
    certificate_verify_verified;
    saw_finished;
    server_before_finished_len = before_finished_len;
    server_through_finished_len = through_finished_len
  };
  fold (flight_state_exactly st view);
}

ghost
fn hide_flight_view (st: flight_state)
  requires flight_state_exactly st 'view
  ensures is_flight_state st
{
  unfold (flight_state_exactly st 'view);
  fold (is_flight_state st);
}

fn flight_state_new ()
  returns st: flight_state
  ensures is_flight_state st
{
  let handshake_len_box = Box.alloc 0sz;
  let parsed_len_box = Box.alloc 0sz;
  let client_hello_len_box = Box.alloc 0sz;
  let server_hello_len_box = Box.alloc 0sz;
  let client_hello = V.alloc 0uy 512sz;
  let server_hello = V.alloc 0uy 4096sz;
  let client_hello_random = V.alloc 0uy 32sz;
  let client_hello_key_share = V.alloc 0uy 32sz;
  let server_handshake_messages = V.alloc 0uy 32768sz;
  let certificate_verify_offset_box = Box.alloc 0sz;
  let certificate_leaf_offset_box = Box.alloc 0sz;
  let certificate_leaf_len_box = Box.alloc 0sz;
  let certificate_verify_signature_scheme_box = Box.alloc 0us;
  let certificate_verify_signature_offset_box = Box.alloc 0sz;
  let certificate_verify_signature_len_box = Box.alloc 0sz;
  let handshake_secret = V.alloc 0uy 32sz;
  let client_handshake_traffic_secret = V.alloc 0uy 32sz;
  let client_handshake_key = V.alloc 0uy 32sz;
  let client_handshake_iv = V.alloc 0uy 12sz;
  let server_handshake_traffic_secret = V.alloc 0uy 32sz;
  let server_handshake_key = V.alloc 0uy 32sz;
  let server_handshake_iv = V.alloc 0uy 12sz;
  let server_handshake_record_state = Rec.record_state_new ();
  let server_finished_verify_data = V.alloc 0uy 32sz;
  let client_finished_verify_data = V.alloc 0uy 32sz;
  let before_finished_len_box = Box.alloc 0sz;
  let through_finished_len_box = Box.alloc 0sz;
  let saw_encrypted_extensions_box = Box.alloc false;
  let saw_certificate_box = Box.alloc false;
  let saw_certificate_verify_box = Box.alloc false;
  let certificate_verify_verified_box = Box.alloc false;
  let saw_finished_box = Box.alloc false;
  let st = {
    handshake_len_box;
    parsed_len_box;
    client_hello_len_box;
    server_hello_len_box;
    client_hello;
    client_hello_random;
    client_hello_key_share;
    server_hello;
    server_handshake_messages;
    certificate_verify_offset_box;
    certificate_leaf_offset_box;
    certificate_leaf_len_box;
    certificate_verify_signature_scheme_box;
    certificate_verify_signature_offset_box;
    certificate_verify_signature_len_box;
    handshake_secret;
    client_handshake_traffic_secret;
    client_handshake_key;
    client_handshake_iv;
    server_handshake_traffic_secret;
    server_handshake_key;
    server_handshake_iv;
    server_handshake_record_state;
    server_finished_verify_data;
    client_finished_verify_data;
    before_finished_len_box;
    through_finished_len_box;
    saw_encrypted_extensions_box;
    saw_certificate_box;
    saw_certificate_verify_box;
    certificate_verify_verified_box;
    saw_finished_box
  };
  with v. rewrite (Box.pts_to handshake_len_box v) as (Box.pts_to st.handshake_len_box v);
  with v. rewrite (Box.pts_to parsed_len_box v) as (Box.pts_to st.parsed_len_box v);
  with v. rewrite (Box.pts_to client_hello_len_box v) as (Box.pts_to st.client_hello_len_box v);
  with v. rewrite (Box.pts_to server_hello_len_box v) as (Box.pts_to st.server_hello_len_box v);
  with v. rewrite (V.pts_to client_hello v) as (V.pts_to st.client_hello v);
  with v. rewrite (V.pts_to client_hello_random v) as (V.pts_to st.client_hello_random v);
  with v. rewrite (V.pts_to client_hello_key_share v) as (V.pts_to st.client_hello_key_share v);
  with v. rewrite (V.pts_to server_hello v) as (V.pts_to st.server_hello v);
  with v. rewrite (V.pts_to server_handshake_messages v) as (V.pts_to st.server_handshake_messages v);
  with v. rewrite (Box.pts_to certificate_verify_offset_box v) as (Box.pts_to st.certificate_verify_offset_box v);
  with v. rewrite (Box.pts_to certificate_leaf_offset_box v) as (Box.pts_to st.certificate_leaf_offset_box v);
  with v. rewrite (Box.pts_to certificate_leaf_len_box v) as (Box.pts_to st.certificate_leaf_len_box v);
  with v. rewrite (Box.pts_to certificate_verify_signature_scheme_box v) as (Box.pts_to st.certificate_verify_signature_scheme_box v);
  with v. rewrite (Box.pts_to certificate_verify_signature_offset_box v) as (Box.pts_to st.certificate_verify_signature_offset_box v);
  with v. rewrite (Box.pts_to certificate_verify_signature_len_box v) as (Box.pts_to st.certificate_verify_signature_len_box v);
  with v. rewrite (V.pts_to handshake_secret v) as (V.pts_to st.handshake_secret v);
  with v. rewrite (V.pts_to client_handshake_traffic_secret v) as (V.pts_to st.client_handshake_traffic_secret v);
  with v. rewrite (V.pts_to client_handshake_key v) as (V.pts_to st.client_handshake_key v);
  with v. rewrite (V.pts_to client_handshake_iv v) as (V.pts_to st.client_handshake_iv v);
  with v. rewrite (V.pts_to server_handshake_traffic_secret v) as (V.pts_to st.server_handshake_traffic_secret v);
  with v. rewrite (V.pts_to server_handshake_key v) as (V.pts_to st.server_handshake_key v);
  with v. rewrite (V.pts_to server_handshake_iv v) as (V.pts_to st.server_handshake_iv v);
  with v. rewrite (Rec.is_record_state server_handshake_record_state v) as (Rec.is_record_state st.server_handshake_record_state v);
  with v. rewrite (V.pts_to server_finished_verify_data v) as (V.pts_to st.server_finished_verify_data v);
  with v. rewrite (V.pts_to client_finished_verify_data v) as (V.pts_to st.client_finished_verify_data v);
  with v. rewrite (Box.pts_to before_finished_len_box v) as (Box.pts_to st.before_finished_len_box v);
  with v. rewrite (Box.pts_to through_finished_len_box v) as (Box.pts_to st.through_finished_len_box v);
  with v. rewrite (Box.pts_to saw_encrypted_extensions_box v) as (Box.pts_to st.saw_encrypted_extensions_box v);
  with v. rewrite (Box.pts_to saw_certificate_box v) as (Box.pts_to st.saw_certificate_box v);
  with v. rewrite (Box.pts_to saw_certificate_verify_box v) as (Box.pts_to st.saw_certificate_verify_box v);
  with v. rewrite (Box.pts_to certificate_verify_verified_box v) as (Box.pts_to st.certificate_verify_verified_box v);
  with v. rewrite (Box.pts_to saw_finished_box v) as (Box.pts_to st.saw_finished_box v);
  fold (is_flight_state st);
  st
}

fn flight_state_free (st: flight_state)
  requires is_flight_state st
  ensures emp
{
  unfold (is_flight_state st);
  Box.free st.handshake_len_box;
  Box.free st.parsed_len_box;
  Box.free st.client_hello_len_box;
  Box.free st.server_hello_len_box;
  V.free st.client_hello;
  V.free st.client_hello_random;
  V.free st.client_hello_key_share;
  V.free st.server_hello;
  V.free st.server_handshake_messages;
  Box.free st.certificate_verify_offset_box;
  Box.free st.certificate_leaf_offset_box;
  Box.free st.certificate_leaf_len_box;
  Box.free st.certificate_verify_signature_scheme_box;
  Box.free st.certificate_verify_signature_offset_box;
  Box.free st.certificate_verify_signature_len_box;
  V.free st.handshake_secret;
  V.free st.client_handshake_traffic_secret;
  V.free st.client_handshake_key;
  V.free st.client_handshake_iv;
  V.free st.server_handshake_traffic_secret;
  V.free st.server_handshake_key;
  V.free st.server_handshake_iv;
  Rec.record_state_free st.server_handshake_record_state;
  V.free st.server_finished_verify_data;
  V.free st.client_finished_verify_data;
  Box.free st.before_finished_len_box;
  Box.free st.through_finished_len_box;
  Box.free st.saw_encrypted_extensions_box;
  Box.free st.saw_certificate_box;
  Box.free st.saw_certificate_verify_box;
  Box.free st.certificate_verify_verified_box;
  Box.free st.saw_finished_box;
}

fn reset (st: flight_state)
  requires is_flight_state st
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  st.handshake_len_box := 0sz;
  st.parsed_len_box := 0sz;
  st.certificate_verify_offset_box := 0sz;
  st.certificate_leaf_offset_box := 0sz;
  st.certificate_leaf_len_box := 0sz;
  st.certificate_verify_signature_scheme_box := 0us;
  st.certificate_verify_signature_offset_box := 0sz;
  st.certificate_verify_signature_len_box := 0sz;
  st.before_finished_len_box := 0sz;
  st.through_finished_len_box := 0sz;
  st.saw_encrypted_extensions_box := false;
  st.saw_certificate_box := false;
  st.saw_certificate_verify_box := false;
  st.certificate_verify_verified_box := false;
  st.saw_finished_box := false;
  fold (is_flight_state st);
}

fn set_client_hello
  (st: flight_state)
  (hello: array U8.t)
  (hello_capacity: SZ.t)
  (hello_len: SZ.t)
  requires is_flight_state st **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_capacity /\
                 SZ.v hello_capacity == 512 /\
                 SZ.v hello_len <= SZ.v hello_capacity)
  ensures is_flight_state st **
          pts_to hello 'hello_bytes
{
  unfold (is_flight_state st);
  pts_to_len hello;
  V.pts_to_len st.client_hello;
  assert (pure (V.length st.client_hello == 512));
  V.to_array_pts_to st.client_hello;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_hello) == 512));
  Arr.memcpy 512sz hello (V.vec_to_array st.client_hello);
  V.to_vec_pts_to st.client_hello;
  st.client_hello_len_box := hello_len;
  fold (is_flight_state st);
}

fn copy_client_hello
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 512)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 512)
{
  unfold (is_flight_state st);
  pts_to_len out;
  V.pts_to_len st.client_hello;
  assert (pure (V.length st.client_hello == 512));
  V.to_array_pts_to st.client_hello;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_hello) == 512));
  Arr.memcpy 512sz (V.vec_to_array st.client_hello) out;
  V.to_vec_pts_to st.client_hello;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 512));
  fold (is_flight_state st);
}

fn client_hello_len (st: flight_state)
  requires is_flight_state st
  returns len: (l:SZ.t{SZ.v l <= 512})
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.client_hello_len_box;
  fold (is_flight_state st);
  len
}

fn client_hello_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 512})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.client_hello_len)
{
  unfold (flight_state_exactly st 'view);
  let len = !st.client_hello_len_box;
  assert (pure (len == 'view.client_hello_len));
  fold (flight_state_exactly st 'view);
  len
}

fn set_server_hello
  (st: flight_state)
  (hello: array U8.t)
  (hello_capacity: SZ.t)
  (hello_len: SZ.t)
  requires is_flight_state st **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_capacity /\
                 SZ.v hello_capacity == 4096 /\
                 SZ.v hello_len <= SZ.v hello_capacity)
  ensures is_flight_state st **
          pts_to hello 'hello_bytes
{
  unfold (is_flight_state st);
  pts_to_len hello;
  V.pts_to_len st.server_hello;
  assert (pure (V.length st.server_hello == 4096));
  V.to_array_pts_to st.server_hello;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_hello) == 4096));
  Arr.memcpy 4096sz hello (V.vec_to_array st.server_hello);
  V.to_vec_pts_to st.server_hello;
  st.server_hello_len_box := hello_len;
  fold (is_flight_state st);
}

fn copy_server_hello
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 4096)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 4096)
{
  unfold (is_flight_state st);
  pts_to_len out;
  V.pts_to_len st.server_hello;
  assert (pure (V.length st.server_hello == 4096));
  V.to_array_pts_to st.server_hello;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_hello) == 4096));
  Arr.memcpy 4096sz (V.vec_to_array st.server_hello) out;
  V.to_vec_pts_to st.server_hello;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 4096));
  fold (is_flight_state st);
}

fn server_hello_len (st: flight_state)
  requires is_flight_state st
  returns len: (l:SZ.t{SZ.v l <= 4096})
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.server_hello_len_box;
  fold (is_flight_state st);
  len
}

fn server_hello_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 4096})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.server_hello_len)
{
  unfold (flight_state_exactly st 'view);
  let len = !st.server_hello_len_box;
  assert (pure (len == 'view.server_hello_len));
  fold (flight_state_exactly st 'view);
  len
}

inline_for_extraction
fn write_fixed_client_private_key (sk: array U8.t)
  requires pts_to sk 'old **
           pure (B.length 'old == 32)
  ensures exists* sk_bytes.
          pts_to sk sk_bytes **
          pure (B.length sk_bytes == 32)
{
  pts_to_len sk;
  sk.(0sz) <- 0x49uy;
  sk.(1sz) <- 0xafuy;
  sk.(2sz) <- 0x42uy;
  sk.(3sz) <- 0xbauy;
  sk.(4sz) <- 0x7fuy;
  sk.(5sz) <- 0x79uy;
  sk.(6sz) <- 0x94uy;
  sk.(7sz) <- 0x85uy;
  sk.(8sz) <- 0x2duy;
  sk.(9sz) <- 0x71uy;
  sk.(10sz) <- 0x3euy;
  sk.(11sz) <- 0xf2uy;
  sk.(12sz) <- 0x78uy;
  sk.(13sz) <- 0x4buy;
  sk.(14sz) <- 0xcbuy;
  sk.(15sz) <- 0xcauy;
  sk.(16sz) <- 0xa7uy;
  sk.(17sz) <- 0x91uy;
  sk.(18sz) <- 0x1duy;
  pts_to_len sk;
  with sk_mid. assert (pts_to sk sk_mid);
  assert (pure (B.length sk_mid == 32));
  sk.(19sz) <- 0xe2uy;
  sk.(20sz) <- 0x6auy;
  sk.(21sz) <- 0xdcuy;
  sk.(22sz) <- 0x56uy;
  sk.(23sz) <- 0x42uy;
  sk.(24sz) <- 0xcbuy;
  sk.(25sz) <- 0x63uy;
  sk.(26sz) <- 0x45uy;
  sk.(27sz) <- 0x40uy;
  sk.(28sz) <- 0xe7uy;
  sk.(29sz) <- 0xeauy;
  sk.(30sz) <- 0x50uy;
  sk.(31sz) <- 0x05uy;
  pts_to_len sk;
  with sk_bytes. assert (pts_to sk sk_bytes);
  assert (pure (B.length sk_bytes == 32));
}

fn set_server_handshake
  (st: flight_state)
  (messages: array U8.t)
  (messages_capacity: SZ.t)
  requires is_flight_state st **
           pts_to messages 'messages_bytes **
           pure (B.length 'messages_bytes == SZ.v messages_capacity /\
                 SZ.v messages_capacity == 32768)
  ensures is_flight_state st **
          pts_to messages 'messages_bytes
{
  unfold (is_flight_state st);
  pts_to_len messages;
  V.pts_to_len st.server_handshake_messages;
  assert (pure (V.length st.server_handshake_messages == 32768));
  V.to_array_pts_to st.server_handshake_messages;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
  Arr.memcpy 32768sz messages (V.vec_to_array st.server_handshake_messages);
  V.to_vec_pts_to st.server_handshake_messages;
  fold (is_flight_state st);
}

fn copy_server_handshake
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768)
{
  unfold (is_flight_state st);
  pts_to_len out;
  V.pts_to_len st.server_handshake_messages;
  assert (pure (V.length st.server_handshake_messages == 32768));
  V.to_array_pts_to st.server_handshake_messages;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
  Arr.memcpy 32768sz (V.vec_to_array st.server_handshake_messages) out;
  V.to_vec_pts_to st.server_handshake_messages;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 32768));
  fold (is_flight_state st);
}

let lemma_copied_range_slice
  (payload: B.bytes)
  (bytes: B.bytes)
  (src: nat)
  (dst: nat)
  (len: nat)
  : Lemma
      (requires src + len <= B.length payload /\
                dst + len <= B.length bytes /\
                (forall (i:nat{i < len}).
                  Seq.index bytes (dst + i) == Seq.index payload (src + i)))
      (ensures Seq.equal
        (Seq.slice bytes dst (dst + len))
        (Seq.slice payload src (src + len)))
  =
  Seq.lemma_len_slice bytes dst (dst + len);
  Seq.lemma_len_slice payload src (src + len);
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice bytes dst (dst + len)) i ==
            Seq.index bytes (dst + i));
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice payload src (src + len)) i ==
            Seq.index payload (src + i));
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice bytes dst (dst + len)) i ==
            Seq.index (Seq.slice payload src (src + len)) i);
  Seq.lemma_eq_intro
    (Seq.slice bytes dst (dst + len))
    (Seq.slice payload src (src + len))

let lemma_slice_equal_range
  (payload: B.bytes)
  (bytes: B.bytes)
  (src: nat)
  (dst: nat)
  (len: nat)
  : Lemma
      (requires src + len <= B.length payload /\
                dst + len <= B.length bytes /\
                Seq.equal
                  (Seq.slice bytes dst (dst + len))
                  (Seq.slice payload src (src + len)))
      (ensures (forall (i:nat{i < len}).
        Seq.index bytes (dst + i) == Seq.index payload (src + i)))
  =
  Seq.lemma_eq_elim
    (Seq.slice bytes dst (dst + len))
    (Seq.slice payload src (src + len));
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice bytes dst (dst + len)) i ==
            Seq.index (Seq.slice payload src (src + len)) i);
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice bytes dst (dst + len)) i ==
            Seq.index bytes (dst + i));
  assert (forall (i:nat{i < len}).
            Seq.index (Seq.slice payload src (src + len)) i ==
            Seq.index payload (src + i));
  assert (forall (i:nat{i < len}).
            Seq.index bytes (dst + i) == Seq.index payload (src + i))

let lemma_copy_step_range
  (payload: B.bytes)
  (mid: B.bytes)
  (final: B.bytes)
  (src: nat)
  (dst: nat)
  (remaining: nat)
  (src_next: nat)
  (dst_next: nat)
  (remaining_next: nat)
  : Lemma
      (requires remaining > 0 /\
                src_next == src + 1 /\
                dst_next == dst + 1 /\
                remaining_next == remaining - 1 /\
                src + remaining <= B.length payload /\
                dst + remaining <= B.length final /\
                B.length final == B.length mid /\
                Seq.index mid dst == Seq.index payload src /\
                (forall (i:nat{i < dst_next}).
                  Seq.index final i == Seq.index mid i) /\
                (forall (i:nat{i < remaining_next}).
                  Seq.index final (dst_next + i) ==
                  Seq.index payload (src_next + i)))
      (ensures (forall (i:nat{i < remaining}).
        Seq.index final (dst + i) == Seq.index payload (src + i)))
  =
  introduce forall (i:nat{i < remaining}).
    Seq.index final (dst + i) == Seq.index payload (src + i)
  with (
    if i = 0 then (
      assert (dst + i == dst);
      assert (src + i == src);
      assert (dst < dst_next);
      assert (Seq.index final dst == Seq.index mid dst)
    ) else (
      assert (i > 0);
      assert (i - 1 < remaining_next);
      assert (dst + i == dst_next + (i - 1));
      assert (src + i == src_next + (i - 1))
    )
  )

let lemma_copy_step_prefix
  (old: B.bytes)
  (mid: B.bytes)
  (final: B.bytes)
  (dst: nat)
  (dst_next: nat)
  : Lemma
      (requires dst <= B.length old /\
                dst_next == dst + 1 /\
                dst_next <= B.length old /\
                B.length mid == B.length old /\
                B.length final == B.length old /\
                (forall (i:nat{i < dst_next}).
                  Seq.index final i == Seq.index mid i) /\
                (forall (i:nat{i < dst}).
                  Seq.index mid i == Seq.index old i))
      (ensures (forall (i:nat{i < dst}).
        Seq.index final i == Seq.index old i))
  =
  ()

fn rec copy_fragment_to_buffer_loop
  (fragment: array U8.t)
  (fragment_total_len: SZ.t)
  (out: array U8.t)
  (out_capacity: SZ.t)
  (src_index: SZ.t)
  (dst_index: SZ.t)
  (remaining: SZ.t)
  requires pts_to fragment 'fragment_bytes **
           pts_to out 'old **
           pure (B.length 'fragment_bytes == SZ.v fragment_total_len /\
                 B.length 'old == SZ.v out_capacity /\
                 SZ.v src_index + SZ.v remaining <= SZ.v fragment_total_len /\
                 SZ.v dst_index + SZ.v remaining <= SZ.v out_capacity)
  ensures exists* out_bytes.
          pts_to fragment 'fragment_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_capacity /\
                B.length 'fragment_bytes == SZ.v fragment_total_len /\
                B.length 'old == SZ.v out_capacity /\
                SZ.v src_index + SZ.v remaining <= SZ.v fragment_total_len /\
                SZ.v dst_index + SZ.v remaining <= SZ.v out_capacity /\
                Seq.equal
                  (Seq.slice out_bytes (SZ.v dst_index) (SZ.v dst_index + SZ.v remaining))
                  (Seq.slice 'fragment_bytes (SZ.v src_index) (SZ.v src_index + SZ.v remaining)) /\
                Seq.equal
                  (Seq.slice out_bytes 0 (SZ.v dst_index))
                  (Seq.slice 'old 0 (SZ.v dst_index)))
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    with out_bytes. assert (pts_to out out_bytes);
    assert (pure (B.length out_bytes == SZ.v out_capacity));
    lemma_copied_range_slice
      (Ghost.reveal 'fragment_bytes)
      (Ghost.reveal out_bytes)
      (SZ.v src_index)
      (SZ.v dst_index)
      (SZ.v remaining);
    assert (pure (Seq.equal
      (Seq.slice out_bytes (SZ.v dst_index) (SZ.v dst_index + SZ.v remaining))
      (Seq.slice 'fragment_bytes (SZ.v src_index) (SZ.v src_index + SZ.v remaining))));
    assert (pure (forall (i:nat{i < SZ.v dst_index}).
      Seq.index out_bytes i == Seq.index 'old i));
    lemma_copied_range_slice
      (Ghost.reveal 'old)
      (Ghost.reveal out_bytes)
      0
      0
      (SZ.v dst_index);
    assert (pure (Seq.equal
      (Seq.slice out_bytes 0 (SZ.v dst_index))
      (Seq.slice 'old 0 (SZ.v dst_index))));
  } else {
    assert (pure (SZ.v src_index < SZ.v fragment_total_len));
    assert (pure (SZ.v dst_index < SZ.v out_capacity));
    let b = fragment.(src_index);
    out.(dst_index) <- b;
    let src_index' = SZ.(src_index +^ 1sz);
    let dst_index' = SZ.(dst_index +^ 1sz);
    let remaining' = SZ.(remaining -^ 1sz);
    with out_bytes. assert (pts_to out out_bytes);
    assert (pure (B.length out_bytes == SZ.v out_capacity));
    assert (pure (Seq.index out_bytes (SZ.v dst_index) == Seq.index 'fragment_bytes (SZ.v src_index)));
    assert (pure (forall (i:nat{i < SZ.v dst_index}).
      Seq.index out_bytes i == Seq.index 'old i));
    assert (pure (SZ.v remaining' < SZ.v remaining));
    assert (pure (SZ.v src_index' + SZ.v remaining' <= SZ.v fragment_total_len));
    assert (pure (SZ.v dst_index' + SZ.v remaining' <= SZ.v out_capacity));
    copy_fragment_to_buffer_loop
      fragment fragment_total_len out out_capacity src_index' dst_index' remaining'
    ;
    with final_bytes. assert (pts_to out final_bytes);
    assert (pure (B.length final_bytes == SZ.v out_capacity));
    assert (pure (SZ.v src_index' == SZ.v src_index + 1));
    assert (pure (SZ.v dst_index' == SZ.v dst_index + 1));
    assert (pure (SZ.v remaining' == SZ.v remaining - 1));
    lemma_slice_equal_range
      (Ghost.reveal out_bytes)
      (Ghost.reveal final_bytes)
      0
      0
      (SZ.v dst_index');
    lemma_slice_equal_range
      (Ghost.reveal 'fragment_bytes)
      (Ghost.reveal final_bytes)
      (SZ.v src_index')
      (SZ.v dst_index')
      (SZ.v remaining');
    lemma_copy_step_range
      (Ghost.reveal 'fragment_bytes)
      (Ghost.reveal out_bytes)
      (Ghost.reveal final_bytes)
      (SZ.v src_index)
      (SZ.v dst_index)
      (SZ.v remaining)
      (SZ.v src_index')
      (SZ.v dst_index')
      (SZ.v remaining');
    assert (pure (forall (i:nat{i < SZ.v remaining}).
      Seq.index final_bytes (SZ.v dst_index + i) ==
      Seq.index 'fragment_bytes (SZ.v src_index + i)));
    lemma_copied_range_slice
      (Ghost.reveal 'fragment_bytes)
      (Ghost.reveal final_bytes)
      (SZ.v src_index)
      (SZ.v dst_index)
      (SZ.v remaining);
    lemma_copy_step_prefix
      (Ghost.reveal 'old)
      (Ghost.reveal out_bytes)
      (Ghost.reveal final_bytes)
      (SZ.v dst_index)
      (SZ.v dst_index');
    assert (pure (forall (i:nat{i < SZ.v dst_index}).
      Seq.index final_bytes i == Seq.index 'old i));
    lemma_copied_range_slice
      (Ghost.reveal 'old)
      (Ghost.reveal final_bytes)
      0
      0
      (SZ.v dst_index);
    assert (pure (Seq.equal
      (Seq.slice final_bytes 0 (SZ.v dst_index))
      (Seq.slice 'old 0 (SZ.v dst_index))))
  }
}

fn copy_fragment_to_buffer
  (fragment: array U8.t)
  (fragment_total_len: SZ.t)
  (copy_len: SZ.t)
  (out: array U8.t)
  (out_capacity: SZ.t)
  (offset: SZ.t)
  requires pts_to fragment 'fragment_bytes **
           pts_to out 'old **
           pure (B.length 'fragment_bytes == SZ.v fragment_total_len /\
                 B.length 'old == SZ.v out_capacity /\
                 SZ.v copy_len <= SZ.v fragment_total_len /\
                 SZ.v offset + SZ.v copy_len <= SZ.v out_capacity)
  ensures exists* out_bytes.
          pts_to fragment 'fragment_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v out_capacity)
{
  copy_fragment_to_buffer_loop fragment fragment_total_len out out_capacity 0sz offset copy_len
}

fn set_client_hello_fragment
  (st: flight_state)
  (hello: array U8.t)
  (hello_len: SZ.t)
  requires is_flight_state st **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_len /\
                 SZ.v hello_len <= 512)
  ensures is_flight_state st **
          pts_to hello 'hello_bytes
{
  unfold (is_flight_state st);
  pts_to_len hello;
  V.pts_to_len st.client_hello;
  assert (pure (V.length st.client_hello == 512));
  V.to_array_pts_to st.client_hello;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_hello) == 512));
  copy_fragment_to_buffer_loop hello hello_len (V.vec_to_array st.client_hello) 512sz 0sz 0sz hello_len;
  V.to_vec_pts_to st.client_hello;
  st.client_hello_len_box := hello_len;
  fold (is_flight_state st);
}

fn set_client_hello_parameters
  (st: flight_state)
  (random: array U8.t)
  (key_share: array U8.t)
  requires is_flight_state st **
           pts_to random 'random_bytes **
           pts_to key_share 'key_share_bytes **
           pure (B.length 'random_bytes == 32 /\
                 B.length 'key_share_bytes == 32)
  ensures is_flight_state st **
          pts_to random 'random_bytes **
          pts_to key_share 'key_share_bytes
{
  unfold (is_flight_state st);
  pts_to_len random;
  pts_to_len key_share;
  V.pts_to_len st.client_hello_random;
  V.pts_to_len st.client_hello_key_share;
  assert (pure (V.length st.client_hello_random == 32));
  assert (pure (V.length st.client_hello_key_share == 32));
  V.to_array_pts_to st.client_hello_random;
  V.to_array_pts_to st.client_hello_key_share;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_hello_random) == 32));
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_hello_key_share) == 32));
  Arr.memcpy 32sz random (V.vec_to_array st.client_hello_random);
  Arr.memcpy 32sz key_share (V.vec_to_array st.client_hello_key_share);
  V.to_vec_pts_to st.client_hello_random;
  V.to_vec_pts_to st.client_hello_key_share;
  fold (is_flight_state st);
}

fn set_server_hello_fragment
  (st: flight_state)
  (hello: array U8.t)
  (hello_len: SZ.t)
  requires is_flight_state st **
           pts_to hello 'hello_bytes **
           pure (B.length 'hello_bytes == SZ.v hello_len /\
                 SZ.v hello_len <= 4096)
  ensures is_flight_state st **
          pts_to hello 'hello_bytes
{
  unfold (is_flight_state st);
  pts_to_len hello;
  V.pts_to_len st.server_hello;
  assert (pure (V.length st.server_hello == 4096));
  V.to_array_pts_to st.server_hello;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_hello) == 4096));
  copy_fragment_to_buffer_loop hello hello_len (V.vec_to_array st.server_hello) 4096sz 0sz 0sz hello_len;
  V.to_vec_pts_to st.server_hello;
  st.server_hello_len_box := hello_len;
  fold (is_flight_state st);
}

fn append_server_handshake_fragment
  (st: flight_state)
  (fragment: array U8.t)
  (fragment_total_len: SZ.t)
  (fragment_len: SZ.t)
  requires is_flight_state st **
           pts_to fragment 'fragment_bytes **
           pure (B.length 'fragment_bytes == SZ.v fragment_total_len /\
                 SZ.v fragment_len <= SZ.v fragment_total_len)
  returns ok: bool
  ensures is_flight_state st **
          pts_to fragment 'fragment_bytes
{
  unfold (is_flight_state st);
  let current = !st.handshake_len_box;
  if SZ.(fragment_len <=^ 32768sz) {
    let remaining_capacity = SZ.(32768sz -^ fragment_len);
    if SZ.(current <=^ remaining_capacity) {
      V.pts_to_len st.server_handshake_messages;
      assert (pure (V.length st.server_handshake_messages == 32768));
      V.to_array_pts_to st.server_handshake_messages;
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      assert (pure (SZ.v current + SZ.v fragment_len <= 32768));
      copy_fragment_to_buffer
        fragment
        fragment_total_len
        fragment_len
        (V.vec_to_array st.server_handshake_messages)
        32768sz
        current;
      V.to_vec_pts_to st.server_handshake_messages;
      st.handshake_len_box := SZ.(current +^ fragment_len);
      fold (is_flight_state st);
      true
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn set_handshake_secret
  (st: flight_state)
  (secret: array U8.t)
  (secret_len: SZ.t)
  requires is_flight_state st **
           pts_to secret 'secret_bytes **
           pure (B.length 'secret_bytes == SZ.v secret_len /\
                 SZ.v secret_len == 32)
  ensures is_flight_state st **
          pts_to secret 'secret_bytes
{
  unfold (is_flight_state st);
  pts_to_len secret;
  V.pts_to_len st.handshake_secret;
  assert (pure (V.length st.handshake_secret == 32));
  V.to_array_pts_to st.handshake_secret;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.handshake_secret) == 32));
  Arr.memcpy 32sz secret (V.vec_to_array st.handshake_secret);
  V.to_vec_pts_to st.handshake_secret;
  fold (is_flight_state st);
}

fn copy_handshake_secret
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 32)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32)
{
  unfold (is_flight_state st);
  pts_to_len out;
  V.pts_to_len st.handshake_secret;
  assert (pure (V.length st.handshake_secret == 32));
  V.to_array_pts_to st.handshake_secret;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.handshake_secret) == 32));
  Arr.memcpy 32sz (V.vec_to_array st.handshake_secret) out;
  V.to_vec_pts_to st.handshake_secret;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 32));
  fold (is_flight_state st);
}

fn set_client_handshake_traffic_secret
  (st: flight_state)
  (secret: array U8.t)
  (secret_len: SZ.t)
  requires is_flight_state st **
           pts_to secret 'secret_bytes **
           pure (B.length 'secret_bytes == SZ.v secret_len /\
                 SZ.v secret_len == 32)
  ensures is_flight_state st **
          pts_to secret 'secret_bytes
{
  unfold (is_flight_state st);
  pts_to_len secret;
  V.pts_to_len st.client_handshake_traffic_secret;
  assert (pure (V.length st.client_handshake_traffic_secret == 32));
  V.to_array_pts_to st.client_handshake_traffic_secret;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_handshake_traffic_secret) == 32));
  Arr.memcpy 32sz secret (V.vec_to_array st.client_handshake_traffic_secret);
  V.to_vec_pts_to st.client_handshake_traffic_secret;
  fold (is_flight_state st);
}

fn copy_client_handshake_traffic_secret
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 32)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32)
{
  unfold (is_flight_state st);
  pts_to_len out;
  V.pts_to_len st.client_handshake_traffic_secret;
  assert (pure (V.length st.client_handshake_traffic_secret == 32));
  V.to_array_pts_to st.client_handshake_traffic_secret;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_handshake_traffic_secret) == 32));
  Arr.memcpy 32sz (V.vec_to_array st.client_handshake_traffic_secret) out;
  V.to_vec_pts_to st.client_handshake_traffic_secret;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 32));
  fold (is_flight_state st);
}

fn set_client_handshake_key_iv
  (st: flight_state)
  (key: array U8.t)
  (key_len: SZ.t)
  (iv: array U8.t)
  (iv_len: SZ.t)
  requires is_flight_state st **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == SZ.v key_len /\
                 B.length 'iv_bytes == SZ.v iv_len /\
                 SZ.v key_len == 32 /\
                 SZ.v iv_len == 12)
  ensures is_flight_state st **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_flight_state st);
  pts_to_len key;
  pts_to_len iv;
  V.pts_to_len st.client_handshake_key;
  V.pts_to_len st.client_handshake_iv;
  assert (pure (V.length st.client_handshake_key == 32));
  assert (pure (V.length st.client_handshake_iv == 12));
  V.to_array_pts_to st.client_handshake_key;
  V.to_array_pts_to st.client_handshake_iv;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_handshake_key) == 32));
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_handshake_iv) == 12));
  Arr.memcpy 32sz key (V.vec_to_array st.client_handshake_key);
  Arr.memcpy 12sz iv (V.vec_to_array st.client_handshake_iv);
  V.to_vec_pts_to st.client_handshake_key;
  V.to_vec_pts_to st.client_handshake_iv;
  fold (is_flight_state st);
}

fn copy_client_handshake_key_iv
  (st: flight_state)
  (key_out: array U8.t)
  (key_out_len: SZ.t)
  (iv_out: array U8.t)
  (iv_out_len: SZ.t)
  requires is_flight_state st **
           pts_to key_out 'old_key **
           pts_to iv_out 'old_iv **
           pure (B.length 'old_key == SZ.v key_out_len /\
                 B.length 'old_iv == SZ.v iv_out_len /\
                 SZ.v key_out_len == 32 /\
                 SZ.v iv_out_len == 12)
  ensures exists* key_bytes iv_bytes.
          is_flight_state st **
          pts_to key_out key_bytes **
          pts_to iv_out iv_bytes **
          pure (B.length key_bytes == 32 /\
                B.length iv_bytes == 12)
{
  unfold (is_flight_state st);
  pts_to_len key_out;
  pts_to_len iv_out;
  V.pts_to_len st.client_handshake_key;
  V.pts_to_len st.client_handshake_iv;
  assert (pure (V.length st.client_handshake_key == 32));
  assert (pure (V.length st.client_handshake_iv == 12));
  V.to_array_pts_to st.client_handshake_key;
  V.to_array_pts_to st.client_handshake_iv;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_handshake_key) == 32));
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_handshake_iv) == 12));
  Arr.memcpy 32sz (V.vec_to_array st.client_handshake_key) key_out;
  Arr.memcpy 12sz (V.vec_to_array st.client_handshake_iv) iv_out;
  V.to_vec_pts_to st.client_handshake_key;
  V.to_vec_pts_to st.client_handshake_iv;
  with key_s. assert (pts_to key_out key_s);
  with iv_s. assert (pts_to iv_out iv_s);
  assert (pure (Seq.length key_s == 32));
  assert (pure (Seq.length iv_s == 12));
  fold (is_flight_state st);
}

fn seal_client_handshake_record
  (st: flight_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires is_flight_state st **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old_out **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old_out == SZ.v plain_len + 16)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == B.length 'old_out)
{
  unfold (is_flight_state st);
  let record_state = Rec.record_state_new ();
  V.pts_to_len st.client_handshake_key;
  V.pts_to_len st.client_handshake_iv;
  assert (pure (V.length st.client_handshake_key == 32));
  assert (pure (V.length st.client_handshake_iv == 12));
  V.to_array_pts_to st.client_handshake_key;
  V.to_array_pts_to st.client_handshake_iv;
  Rec.install_handshake_keys_runtime
    record_state
    (V.vec_to_array st.client_handshake_key)
    (V.vec_to_array st.client_handshake_iv);
  V.to_vec_pts_to st.client_handshake_key;
  V.to_vec_pts_to st.client_handshake_iv;
  let ok = Rec.seal_application_runtime record_state aad aad_len plain plain_len out;
  with out_s. assert (pts_to out out_s);
  assert (pure (B.length out_s == B.length 'old_out));
  Rec.record_state_free record_state;
  fold (is_flight_state st);
  ok
}

fn set_server_handshake_traffic_secret
  (st: flight_state)
  (secret: array U8.t)
  (secret_len: SZ.t)
  requires is_flight_state st **
           pts_to secret 'secret_bytes **
           pure (B.length 'secret_bytes == SZ.v secret_len /\
                 SZ.v secret_len == 32)
  ensures is_flight_state st **
          pts_to secret 'secret_bytes
{
  unfold (is_flight_state st);
  pts_to_len secret;
  V.pts_to_len st.server_handshake_traffic_secret;
  assert (pure (V.length st.server_handshake_traffic_secret == 32));
  V.to_array_pts_to st.server_handshake_traffic_secret;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_traffic_secret) == 32));
  Arr.memcpy 32sz secret (V.vec_to_array st.server_handshake_traffic_secret);
  V.to_vec_pts_to st.server_handshake_traffic_secret;
  fold (is_flight_state st);
}

fn copy_server_handshake_traffic_secret
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 32)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32)
{
  unfold (is_flight_state st);
  pts_to_len out;
  V.pts_to_len st.server_handshake_traffic_secret;
  assert (pure (V.length st.server_handshake_traffic_secret == 32));
  V.to_array_pts_to st.server_handshake_traffic_secret;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_traffic_secret) == 32));
  Arr.memcpy 32sz (V.vec_to_array st.server_handshake_traffic_secret) out;
  V.to_vec_pts_to st.server_handshake_traffic_secret;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 32));
  fold (is_flight_state st);
}

fn set_server_handshake_key_iv
  (st: flight_state)
  (key: array U8.t)
  (key_len: SZ.t)
  (iv: array U8.t)
  (iv_len: SZ.t)
  requires is_flight_state st **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == SZ.v key_len /\
                 B.length 'iv_bytes == SZ.v iv_len /\
                 SZ.v key_len == 32 /\
                 SZ.v iv_len == 12)
  ensures is_flight_state st **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_flight_state st);
  pts_to_len key;
  pts_to_len iv;
  V.pts_to_len st.server_handshake_key;
  V.pts_to_len st.server_handshake_iv;
  assert (pure (V.length st.server_handshake_key == 32));
  assert (pure (V.length st.server_handshake_iv == 12));
  V.to_array_pts_to st.server_handshake_key;
  V.to_array_pts_to st.server_handshake_iv;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_key) == 32));
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_iv) == 12));
  Arr.memcpy 32sz key (V.vec_to_array st.server_handshake_key);
  Arr.memcpy 12sz iv (V.vec_to_array st.server_handshake_iv);
  V.to_vec_pts_to st.server_handshake_key;
  V.to_vec_pts_to st.server_handshake_iv;
  fold (is_flight_state st);
}

fn copy_server_handshake_key_iv
  (st: flight_state)
  (key_out: array U8.t)
  (key_out_len: SZ.t)
  (iv_out: array U8.t)
  (iv_out_len: SZ.t)
  requires is_flight_state st **
           pts_to key_out 'old_key **
           pts_to iv_out 'old_iv **
           pure (B.length 'old_key == SZ.v key_out_len /\
                 B.length 'old_iv == SZ.v iv_out_len /\
                 SZ.v key_out_len == 32 /\
                 SZ.v iv_out_len == 12)
  ensures exists* key_bytes iv_bytes.
          is_flight_state st **
          pts_to key_out key_bytes **
          pts_to iv_out iv_bytes **
          pure (B.length key_bytes == 32 /\
                B.length iv_bytes == 12)
{
  unfold (is_flight_state st);
  pts_to_len key_out;
  pts_to_len iv_out;
  V.pts_to_len st.server_handshake_key;
  V.pts_to_len st.server_handshake_iv;
  assert (pure (V.length st.server_handshake_key == 32));
  assert (pure (V.length st.server_handshake_iv == 12));
  V.to_array_pts_to st.server_handshake_key;
  V.to_array_pts_to st.server_handshake_iv;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_key) == 32));
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_iv) == 12));
  Arr.memcpy 32sz (V.vec_to_array st.server_handshake_key) key_out;
  Arr.memcpy 12sz (V.vec_to_array st.server_handshake_iv) iv_out;
  V.to_vec_pts_to st.server_handshake_key;
  V.to_vec_pts_to st.server_handshake_iv;
  with key_s. assert (pts_to key_out key_s);
  with iv_s. assert (pts_to iv_out iv_s);
  assert (pure (Seq.length key_s == 32));
  assert (pure (Seq.length iv_s == 12));
  fold (is_flight_state st);
}

fn derive_server_handshake_keys_from_share
  (st: flight_state)
  (server_key_share: array U8.t)
  (server_key_share_len: SZ.t)
  requires is_flight_state st **
           pts_to server_key_share 'key_share_bytes **
           pure (B.length 'key_share_bytes == SZ.v server_key_share_len /\
                 SZ.v server_key_share_len == 32)
  returns ok: bool
  ensures is_flight_state st **
          pts_to server_key_share 'key_share_bytes
{
  let mut client_hello = [| 0uy; 512sz |];
  let mut server_hello = [| 0uy; 4096sz |];
  copy_client_hello st client_hello 512sz;
  copy_server_hello st server_hello 4096sz;
  let ch_len = client_hello_len st;
  let sh_len = server_hello_len st;
  assert (pure (SZ.v ch_len <= 512));
  assert (pure (SZ.v sh_len <= 4096));
  assert (pure (SZ.fits (SZ.v ch_len + SZ.v sh_len)));
  if SZ.(ch_len +^ sh_len <=^ 32768sz) {
    let mut client_hello_exact = [| 0uy; ch_len |];
    let mut server_hello_exact = [| 0uy; sh_len |];
    copy_fragment_to_buffer_loop client_hello 512sz client_hello_exact ch_len 0sz 0sz ch_len;
    copy_fragment_to_buffer_loop server_hello 4096sz server_hello_exact sh_len 0sz 0sz sh_len;
    let mut zero_secret = [| 0uy; 32sz |];
    let mut empty = [| 0uy; 0sz |];
    let mut early_secret = [| 0uy; 32sz |];
    Crypto.hkdf_extract empty 0sz zero_secret 32sz early_secret;
    let mut client_private_key = [| 0uy; 32sz |];
    write_fixed_client_private_key client_private_key;
    let mut shared_secret = [| 0uy; 32sz |];
    let shared_ok = Crypto.x25519_shared_runtime client_private_key server_key_share shared_secret;
    if shared_ok {
      with shared_secret_bytes. assert (pts_to shared_secret shared_secret_bytes);
      assert (pure (B.length shared_secret_bytes == 32));
      let mut transcript_hash = [| 0uy; 32sz |];
      let transcript_ok =
        Transcript.hash_client_server_hello
          client_hello_exact
          ch_len
          server_hello_exact
          sh_len
          transcript_hash;
      if transcript_ok {
        let mut handshake_secret_bytes = [| 0uy; 32sz |];
        let mut client_hs_secret = [| 0uy; 32sz |];
        let mut server_hs_secret = [| 0uy; 32sz |];
        let mut client_key = [| 0uy; 32sz |];
        let mut client_iv = [| 0uy; 12sz |];
        let mut server_key = [| 0uy; 32sz |];
        let mut server_iv = [| 0uy; 12sz |];
        KS.handshake_secret early_secret shared_secret 32sz handshake_secret_bytes;
        KS.client_handshake_traffic_secret handshake_secret_bytes transcript_hash client_hs_secret;
        KS.server_handshake_traffic_secret handshake_secret_bytes transcript_hash server_hs_secret;
        KS.derive_traffic_key client_hs_secret client_key;
        KS.derive_traffic_iv client_hs_secret client_iv;
        KS.derive_traffic_key server_hs_secret server_key;
        KS.derive_traffic_iv server_hs_secret server_iv;
        set_handshake_secret st handshake_secret_bytes 32sz;
        set_client_handshake_traffic_secret st client_hs_secret 32sz;
        set_client_handshake_key_iv st client_key 32sz client_iv 12sz;
        set_server_handshake_traffic_secret st server_hs_secret 32sz;
        set_server_handshake_key_iv st server_key 32sz server_iv 12sz;
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

fn install_server_handshake_record_keys
  (st: flight_state)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_flight_state st **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\
                 B.length 'iv_bytes == 12)
  ensures is_flight_state st **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_flight_state st);
  Rec.install_handshake_keys_runtime st.server_handshake_record_state key iv;
  fold (is_flight_state st);
}

fn open_server_handshake_record
  (st: flight_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires is_flight_state st **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old_out **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old_out + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == B.length 'old_out)
{
  unfold (is_flight_state st);
  let ok = Rec.open_application_runtime st.server_handshake_record_state aad aad_len cipher cipher_len out;
  with out_s. assert (pts_to out out_s);
  assert (pure (B.length out_s == B.length 'old_out));
  fold (is_flight_state st);
  ok
}

fn process_server_handshake_record
  (st: flight_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  requires is_flight_state st **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 SZ.v aad_len == 5 /\
                 16 < SZ.v cipher_len /\
                 SZ.v cipher_len <= 20000)
  returns ok: bool
  ensures is_flight_state st **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes
{
  let inner_len = SZ.(cipher_len -^ 16sz);
  assert (pure (SZ.v inner_len > 0));
  let mut inner = [| 0uy; inner_len |];
  let opened = open_server_handshake_record st aad aad_len cipher cipher_len inner;
  if opened {
    let mut inner_content_type_out = [| 0uy; 1sz |];
    let handshake_plaintext_len =
      RF.decode_inner_plaintext_no_padding inner inner_len inner_content_type_out 1sz;
    let inner_content_type = inner_content_type_out.(0sz);
    if (inner_content_type = 22uy) {
      append_server_handshake_fragment st inner inner_len handshake_plaintext_len
    } else {
      false
    }
  } else {
    false
  }
}

fn handshake_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.handshake_len_box;
  fold (is_flight_state st);
  len
}

fn handshake_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.server_handshake_len)
{
  unfold (flight_state_exactly st 'view);
  let len = !st.handshake_len_box;
  assert (pure (len == 'view.server_handshake_len));
  fold (flight_state_exactly st 'view);
  len
}

fn parsed_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.parsed_len_box;
  fold (is_flight_state st);
  len
}

fn parsed_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.server_handshake_parsed_len)
{
  unfold (flight_state_exactly st 'view);
  let len = !st.parsed_len_box;
  assert (pure (len == 'view.server_handshake_parsed_len));
  fold (flight_state_exactly st 'view);
  len
}

fn pending_handshake_message_complete (st: flight_state)
  requires is_flight_state st
  returns complete: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if SZ.(parsed <=^ hlen) {
    let remaining = SZ.(hlen -^ parsed);
    if SZ.(4sz <=^ remaining) {
      V.pts_to_len st.server_handshake_messages;
      assert (pure (V.length st.server_handshake_messages == 32768));
      V.to_array_pts_to st.server_handshake_messages;
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      assert (pure (SZ.v parsed + 3 < 32768));
      let len_hi = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 1sz));
      let len_mid = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 2sz));
      let len_lo = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 3sz));
      let len_mid16 = Cast.uint8_to_uint16 len_mid;
      let len_lo16 = Cast.uint8_to_uint16 len_lo;
      let body16 = U16.logor (U16.shift_left len_mid16 8ul) len_lo16;
      let body_len = SZ.uint16_to_sizet body16;
      let remaining_body_capacity = SZ.(remaining -^ 4sz);
      V.to_vec_pts_to st.server_handshake_messages;
      fold (is_flight_state st);
      (len_hi = 0uy) && SZ.(body_len <=^ remaining_body_capacity)
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn pending_handshake_message_type (st: flight_state)
  requires is_flight_state st
  returns msg_type: U8.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if SZ.(parsed <^ hlen) {
    V.pts_to_len st.server_handshake_messages;
    assert (pure (V.length st.server_handshake_messages == 32768));
    V.to_array_pts_to st.server_handshake_messages;
    assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
    assert (pure (SZ.v parsed < 32768));
    let msg_type = (V.vec_to_array st.server_handshake_messages).(parsed);
    V.to_vec_pts_to st.server_handshake_messages;
    fold (is_flight_state st);
    msg_type
  } else {
    fold (is_flight_state st);
    0uy
  }
}

fn append_handshake_len (st: flight_state) (fragment_len: SZ.t) (capacity: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  let _ = capacity;
  unfold (is_flight_state st);
  let current = !st.handshake_len_box;
  if SZ.(fragment_len <=^ 32768sz) {
    let remaining = SZ.(32768sz -^ fragment_len);
    if SZ.(current <=^ remaining) {
      st.handshake_len_box := SZ.(current +^ fragment_len);
      fold (is_flight_state st);
      true
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn accept_encrypted_extensions (st: flight_state) (message_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if (SZ.(parsed =^ 0sz) && SZ.(message_len <=^ hlen)) {
    st.saw_encrypted_extensions_box := true;
    st.parsed_len_box := message_len;
    fold (is_flight_state st);
    true
  } else {
    fold (is_flight_state st);
    false
  }
}

fn accept_pending_encrypted_extensions (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if (SZ.(parsed =^ 0sz) && SZ.(parsed <=^ hlen)) {
    let remaining = SZ.(hlen -^ parsed);
    if SZ.(4sz <=^ remaining) {
      V.pts_to_len st.server_handshake_messages;
      assert (pure (V.length st.server_handshake_messages == 32768));
      V.to_array_pts_to st.server_handshake_messages;
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      assert (pure (SZ.v parsed + 3 < 32768));
      let msg_type = (V.vec_to_array st.server_handshake_messages).(parsed);
      let len_hi = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 1sz));
      let len_mid = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 2sz));
      let len_lo = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 3sz));
      let len_mid16 = Cast.uint8_to_uint16 len_mid;
      let len_lo16 = Cast.uint8_to_uint16 len_lo;
      let body16 = U16.logor (U16.shift_left len_mid16 8ul) len_lo16;
      let body_len = SZ.uint16_to_sizet body16;
      let remaining_body_capacity = SZ.(remaining -^ 4sz);
      if ((msg_type = 0x08uy) && (len_hi = 0uy) && SZ.(body_len =^ 0sz) && SZ.(body_len <=^ remaining_body_capacity)) {
        assert (pure (SZ.fits (SZ.v parsed + 4)));
        let after_header = SZ.(parsed +^ 4sz);
        assert (pure (SZ.v after_header + SZ.v body_len <= SZ.v hlen));
        assert (pure (SZ.fits (SZ.v after_header + SZ.v body_len)));
        let next_parsed = SZ.(after_header +^ body_len);
        V.to_vec_pts_to st.server_handshake_messages;
        st.saw_encrypted_extensions_box := true;
        st.parsed_len_box := next_parsed;
        fold (is_flight_state st);
        true
      } else {
        V.to_vec_pts_to st.server_handshake_messages;
        fold (is_flight_state st);
        false
      }
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn accept_certificate (st: flight_state) (message_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if SZ.(parsed <=^ hlen) {
    let remaining = SZ.(hlen -^ parsed);
    if SZ.(message_len <=^ remaining) {
      st.saw_certificate_box := true;
      st.parsed_len_box := SZ.(parsed +^ message_len);
      fold (is_flight_state st);
      true
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn accept_pending_certificate (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if SZ.(parsed <=^ hlen) {
    let remaining = SZ.(hlen -^ parsed);
    if SZ.(4sz <=^ remaining) {
      V.pts_to_len st.server_handshake_messages;
      assert (pure (V.length st.server_handshake_messages == 32768));
      V.to_array_pts_to st.server_handshake_messages;
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      assert (pure (SZ.v parsed + 3 < 32768));
      let msg_type = (V.vec_to_array st.server_handshake_messages).(parsed);
      let len_hi = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 1sz));
      let len_mid = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 2sz));
      let len_lo = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 3sz));
      let len_mid16 = Cast.uint8_to_uint16 len_mid;
      let len_lo16 = Cast.uint8_to_uint16 len_lo;
      let body16 = U16.logor (U16.shift_left len_mid16 8ul) len_lo16;
      let body_len = SZ.uint16_to_sizet body16;
      let remaining_body_capacity = SZ.(remaining -^ 4sz);
      if ((msg_type = 0x0buy) && (len_hi = 0uy) && SZ.(body_len <=^ remaining_body_capacity) && not (SZ.(body_len <^ 9sz))) {
        assert (pure (SZ.fits (SZ.v parsed + 4)));
        let body_start = SZ.(parsed +^ 4sz);
        assert (pure (SZ.v body_start + SZ.v body_len <= SZ.v hlen));
        assert (pure (SZ.v body_start + 8 < 32768));
        let request_context_len = (V.vec_to_array st.server_handshake_messages).(body_start);
        let list_len_hi = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 1sz));
        let list_len_b0 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 2sz));
        let list_len_b1 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 3sz));
        let cert_len_hi = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 4sz));
        let cert_len_b0 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 5sz));
        let cert_len_b1 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 6sz));
        if ((request_context_len = 0uy) && (list_len_hi = 0uy) && (cert_len_hi = 0uy)) {
          let list_len_hi16 = Cast.uint8_to_uint16 list_len_b0;
          let list_len_lo16 = Cast.uint8_to_uint16 list_len_b1;
          let list_len16 = U16.logor (U16.shift_left list_len_hi16 8ul) list_len_lo16;
          let list_len = SZ.uint16_to_sizet list_len16;
          let actual_list_len = SZ.(body_len -^ 4sz);
          if SZ.(actual_list_len =^ list_len) {
            let cert_len_hi16 = Cast.uint8_to_uint16 cert_len_b0;
            let cert_len_lo16 = Cast.uint8_to_uint16 cert_len_b1;
            let cert_len16 = U16.logor (U16.shift_left cert_len_hi16 8ul) cert_len_lo16;
            let cert_len = SZ.uint16_to_sizet cert_len16;
            let payload_after_cert_header = SZ.(body_len -^ 7sz);
            if (SZ.(cert_len =^ 0sz) || SZ.(payload_after_cert_header <^ cert_len)) {
              V.to_vec_pts_to st.server_handshake_messages;
              fold (is_flight_state st);
              false
            } else {
              let rest_after_cert = SZ.(payload_after_cert_header -^ cert_len);
              if SZ.(rest_after_cert <^ 2sz) {
                V.to_vec_pts_to st.server_handshake_messages;
                fold (is_flight_state st);
                false
              } else {
                let rest_after_first_ext_len_byte = SZ.(rest_after_cert -^ 1sz);
                let ext0_offset = SZ.(body_len -^ rest_after_cert);
                let ext1_offset = SZ.(body_len -^ rest_after_first_ext_len_byte);
                assert (pure (SZ.v body_start + SZ.v ext1_offset < 32768));
                let ext_len_b0 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ ext0_offset));
                let ext_len_b1 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ ext1_offset));
                let ext_len_hi16 = Cast.uint8_to_uint16 ext_len_b0;
                let ext_len_lo16 = Cast.uint8_to_uint16 ext_len_b1;
                let ext_len16 = U16.logor (U16.shift_left ext_len_hi16 8ul) ext_len_lo16;
                let ext_len = SZ.uint16_to_sizet ext_len16;
                let actual_ext_len = SZ.(rest_after_cert -^ 2sz);
                if SZ.(actual_ext_len =^ ext_len) {
                  assert (pure (SZ.fits (SZ.v body_start + 7)));
                  let leaf_offset = SZ.(body_start +^ 7sz);
                  assert (pure (SZ.fits (SZ.v body_start + SZ.v body_len)));
                  let next_parsed = SZ.(body_start +^ body_len);
                  V.to_vec_pts_to st.server_handshake_messages;
                  st.certificate_leaf_offset_box := leaf_offset;
                  st.certificate_leaf_len_box := cert_len;
                  st.saw_certificate_box := true;
                  st.parsed_len_box := next_parsed;
                  fold (is_flight_state st);
                  true
                } else {
                  V.to_vec_pts_to st.server_handshake_messages;
                  fold (is_flight_state st);
                  false
                }
              }
            }
          } else {
            V.to_vec_pts_to st.server_handshake_messages;
            fold (is_flight_state st);
            false
          }
        } else {
          V.to_vec_pts_to st.server_handshake_messages;
          fold (is_flight_state st);
          false
        }
      } else {
        V.to_vec_pts_to st.server_handshake_messages;
        fold (is_flight_state st);
        false
      }
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn set_certificate_leaf (st: flight_state) (leaf_offset: SZ.t) (leaf_len: SZ.t)
  requires is_flight_state st **
           pure (SZ.v leaf_len <= 32768)
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  st.certificate_leaf_offset_box := leaf_offset;
  st.certificate_leaf_len_box := leaf_len;
  fold (is_flight_state st);
}

fn accept_certificate_verify (st: flight_state) (message_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if SZ.(parsed <=^ hlen) {
    let remaining = SZ.(hlen -^ parsed);
    if SZ.(message_len <=^ remaining) {
      st.certificate_verify_offset_box := parsed;
      st.saw_certificate_verify_box := true;
      st.parsed_len_box := SZ.(parsed +^ message_len);
      fold (is_flight_state st);
      true
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn accept_pending_certificate_verify (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if SZ.(parsed <=^ hlen) {
    let remaining = SZ.(hlen -^ parsed);
    if SZ.(4sz <=^ remaining) {
      V.pts_to_len st.server_handshake_messages;
      assert (pure (V.length st.server_handshake_messages == 32768));
      V.to_array_pts_to st.server_handshake_messages;
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      assert (pure (SZ.v parsed + 3 < 32768));
      let msg_type = (V.vec_to_array st.server_handshake_messages).(parsed);
      let len_hi = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 1sz));
      let len_mid = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 2sz));
      let len_lo = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 3sz));
      let len_mid16 = Cast.uint8_to_uint16 len_mid;
      let len_lo16 = Cast.uint8_to_uint16 len_lo;
      let body16 = U16.logor (U16.shift_left len_mid16 8ul) len_lo16;
      let body_len = SZ.uint16_to_sizet body16;
      let remaining_body_capacity = SZ.(remaining -^ 4sz);
      if ((msg_type = 0x0fuy) && (len_hi = 0uy) && SZ.(body_len <=^ remaining_body_capacity) && not (SZ.(body_len <^ 4sz))) {
        assert (pure (SZ.fits (SZ.v parsed + 4)));
        let body_start = SZ.(parsed +^ 4sz);
        assert (pure (SZ.v body_start + SZ.v body_len <= SZ.v hlen));
        assert (pure (SZ.v body_start + 3 < 32768));
        let scheme_b0 = (V.vec_to_array st.server_handshake_messages).(body_start);
        let scheme_b1 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 1sz));
        let sig_len_b0 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 2sz));
        let sig_len_b1 = (V.vec_to_array st.server_handshake_messages).(SZ.(body_start +^ 3sz));
        let scheme_hi16 = Cast.uint8_to_uint16 scheme_b0;
        let scheme_lo16 = Cast.uint8_to_uint16 scheme_b1;
        let scheme = U16.logor (U16.shift_left scheme_hi16 8ul) scheme_lo16;
        let sig_len_hi16 = Cast.uint8_to_uint16 sig_len_b0;
        let sig_len_lo16 = Cast.uint8_to_uint16 sig_len_b1;
        let sig_len16 = U16.logor (U16.shift_left sig_len_hi16 8ul) sig_len_lo16;
        let sig_len = SZ.uint16_to_sizet sig_len16;
        let actual_sig_len = SZ.(body_len -^ 4sz);
        if SZ.(actual_sig_len =^ sig_len) {
          assert (pure (SZ.fits (SZ.v body_start + 4)));
          let signature_offset = SZ.(body_start +^ 4sz);
          assert (pure (SZ.fits (SZ.v body_start + SZ.v body_len)));
          let next_parsed = SZ.(body_start +^ body_len);
          V.to_vec_pts_to st.server_handshake_messages;
          st.certificate_verify_offset_box := parsed;
          st.certificate_verify_signature_scheme_box := scheme;
          st.certificate_verify_signature_offset_box := signature_offset;
          st.certificate_verify_signature_len_box := sig_len;
          st.saw_certificate_verify_box := true;
          st.parsed_len_box := next_parsed;
          fold (is_flight_state st);
          true
        } else {
          V.to_vec_pts_to st.server_handshake_messages;
          fold (is_flight_state st);
          false
        }
      } else {
        V.to_vec_pts_to st.server_handshake_messages;
        fold (is_flight_state st);
        false
      }
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn set_certificate_verify_signature
  (st: flight_state)
  (signature_scheme: U16.t)
  (signature_offset: SZ.t)
  (signature_len: SZ.t)
  requires is_flight_state st **
           pure (SZ.v signature_len <= 32768)
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  st.certificate_verify_signature_scheme_box := signature_scheme;
  st.certificate_verify_signature_offset_box := signature_offset;
  st.certificate_verify_signature_len_box := signature_len;
  fold (is_flight_state st);
}

fn mark_certificate_verify_verified (st: flight_state)
  requires is_flight_state st
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  st.certificate_verify_verified_box := true;
  fold (is_flight_state st);
}

fn mark_certificate_verify_verified_exact (st: flight_state)
  requires flight_state_exactly st 'view
  ensures flight_state_exactly st (flight_view_with_certificate_verify_verified 'view)
{
  unfold (flight_state_exactly st 'view);
  st.certificate_verify_verified_box := true;
  assert (pure ((flight_view_with_certificate_verify_verified 'view).certificate_verify_verified == true));
  fold (flight_state_exactly st (flight_view_with_certificate_verify_verified 'view));
}

fn accept_finished (st: flight_state) (message_len: SZ.t) (body_len: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if (SZ.(body_len =^ 32sz) && SZ.(parsed <=^ hlen)) {
    let remaining = SZ.(hlen -^ parsed);
    if SZ.(message_len <=^ remaining) {
      let through = SZ.(parsed +^ message_len);
      st.before_finished_len_box := parsed;
      st.through_finished_len_box := through;
      st.saw_finished_box := true;
      st.parsed_len_box := through;
      fold (is_flight_state st);
      true
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn accept_pending_finished (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let parsed = !st.parsed_len_box;
  let hlen = !st.handshake_len_box;
  if SZ.(parsed <=^ hlen) {
    let remaining = SZ.(hlen -^ parsed);
    if SZ.(4sz <=^ remaining) {
      V.pts_to_len st.server_handshake_messages;
      assert (pure (V.length st.server_handshake_messages == 32768));
      V.to_array_pts_to st.server_handshake_messages;
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      V.pts_to_len st.server_finished_verify_data;
      assert (pure (V.length st.server_finished_verify_data == 32));
      assert (pure (SZ.v parsed + 3 < 32768));
      let msg_type = (V.vec_to_array st.server_handshake_messages).(parsed);
      let len_hi = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 1sz));
      let len_mid = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 2sz));
      let len_lo = (V.vec_to_array st.server_handshake_messages).(SZ.(parsed +^ 3sz));
      let len_mid16 = Cast.uint8_to_uint16 len_mid;
      let len_lo16 = Cast.uint8_to_uint16 len_lo;
      let body16 = U16.logor (U16.shift_left len_mid16 8ul) len_lo16;
      let body_len = SZ.uint16_to_sizet body16;
      let remaining_body_capacity = SZ.(remaining -^ 4sz);
      if ((msg_type = 0x14uy) && (len_hi = 0uy) && SZ.(body_len =^ 32sz) && SZ.(body_len <=^ remaining_body_capacity)) {
        assert (pure (SZ.fits (SZ.v parsed + 4)));
        let body_start = SZ.(parsed +^ 4sz);
        assert (pure (SZ.v body_start + 31 < 32768));
        assert (pure (SZ.v body_start + SZ.v body_len <= SZ.v hlen));
        V.to_array_pts_to st.server_finished_verify_data;
        assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_finished_verify_data) == 32));
        assert (pure (SZ.v body_start + 32 <= 32768));
        copy_fragment_to_buffer_loop
          (V.vec_to_array st.server_handshake_messages)
          32768sz
          (V.vec_to_array st.server_finished_verify_data)
          32sz
          body_start
          0sz
          32sz;
        V.to_vec_pts_to st.server_handshake_messages;
        V.to_vec_pts_to st.server_finished_verify_data;
        assert (pure (SZ.fits (SZ.v body_start + SZ.v body_len)));
        let through = SZ.(body_start +^ body_len);
        st.before_finished_len_box := parsed;
        st.through_finished_len_box := through;
        st.saw_finished_box := true;
        st.parsed_len_box := through;
        fold (is_flight_state st);
        true
      } else {
        V.to_vec_pts_to st.server_handshake_messages;
        fold (is_flight_state st);
        false
      }
    } else {
      fold (is_flight_state st);
      false
    }
  } else {
    fold (is_flight_state st);
    false
  }
}

fn set_server_finished_verify_data
  (st: flight_state)
  (verify_data: array U8.t)
  (verify_data_len: SZ.t)
  requires is_flight_state st **
           pts_to verify_data 'verify_data_bytes **
           pure (B.length 'verify_data_bytes == SZ.v verify_data_len /\
                 SZ.v verify_data_len == 32)
  ensures is_flight_state st **
          pts_to verify_data 'verify_data_bytes
{
  unfold (is_flight_state st);
  pts_to_len verify_data;
  V.pts_to_len st.server_finished_verify_data;
  assert (pure (V.length st.server_finished_verify_data == 32));
  V.to_array_pts_to st.server_finished_verify_data;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_finished_verify_data) == 32));
  Arr.memcpy 32sz verify_data (V.vec_to_array st.server_finished_verify_data);
  V.to_vec_pts_to st.server_finished_verify_data;
  fold (is_flight_state st);
}

fn set_client_finished_verify_data
  (st: flight_state)
  (verify_data: array U8.t)
  (verify_data_len: SZ.t)
  requires is_flight_state st **
           pts_to verify_data 'verify_data_bytes **
           pure (B.length 'verify_data_bytes == SZ.v verify_data_len /\
                 SZ.v verify_data_len == 32)
  ensures is_flight_state st **
          pts_to verify_data 'verify_data_bytes
{
  unfold (is_flight_state st);
  pts_to_len verify_data;
  V.pts_to_len st.client_finished_verify_data;
  assert (pure (V.length st.client_finished_verify_data == 32));
  V.to_array_pts_to st.client_finished_verify_data;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.client_finished_verify_data) == 32));
  Arr.memcpy 32sz verify_data (V.vec_to_array st.client_finished_verify_data);
  V.to_vec_pts_to st.client_finished_verify_data;
  fold (is_flight_state st);
}

fn copy_server_finished_verify_data
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 32)
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32)
{
  unfold (is_flight_state st);
  pts_to_len out;
  V.pts_to_len st.server_finished_verify_data;
  assert (pure (V.length st.server_finished_verify_data == 32));
  V.to_array_pts_to st.server_finished_verify_data;
  assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_finished_verify_data) == 32));
  Arr.memcpy 32sz (V.vec_to_array st.server_finished_verify_data) out;
  V.to_vec_pts_to st.server_finished_verify_data;
  with out_s. assert (pts_to out out_s);
  assert (pure (Seq.length out_s == 32));
  fold (is_flight_state st);
}

fn certificate_verify_offset (st: flight_state)
  requires is_flight_state st
  returns offset: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let offset = !st.certificate_verify_offset_box;
  fold (is_flight_state st);
  offset
}

fn certificate_verify_offset_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns offset: SZ.t
  ensures flight_state_exactly st 'view **
          pure (offset == 'view.certificate_verify_offset)
{
  unfold (flight_state_exactly st 'view);
  let offset = !st.certificate_verify_offset_box;
  assert (pure (offset == 'view.certificate_verify_offset));
  fold (flight_state_exactly st 'view);
  offset
}

fn copy_server_handshake_slice
  (st: flight_state)
  (slice_offset: SZ.t)
  (slice_len: SZ.t)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768)
{
  unfold (is_flight_state st);
  if SZ.(slice_offset <=^ 32768sz) {
    let available = SZ.(32768sz -^ slice_offset);
    if SZ.(slice_len <=^ available) {
      V.pts_to_len st.server_handshake_messages;
      V.to_array_pts_to st.server_handshake_messages;
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      assert (pure (SZ.v slice_offset + SZ.v slice_len <= 32768));
      copy_fragment_to_buffer_loop
        (V.vec_to_array st.server_handshake_messages)
        32768sz
        out
        out_capacity
        slice_offset
        0sz
        slice_len;
      V.to_vec_pts_to st.server_handshake_messages;
      with out_s. assert (pts_to out out_s);
      assert (pure (Seq.length out_s == 32768));
      fold (is_flight_state st);
      true
    } else {
      with out_s. assert (pts_to out out_s);
      assert (pure (Seq.length out_s == 32768));
      fold (is_flight_state st);
      false
    }
  } else {
    with out_s. assert (pts_to out out_s);
    assert (pure (Seq.length out_s == 32768));
    fold (is_flight_state st);
    false
  }
}

fn copy_server_handshake_slice_exact
  (st: flight_state)
  (slice_offset: SZ.t)
  (slice_len: SZ.t)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires flight_state_exactly st 'view **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  returns ok: bool
  ensures exists* out_bytes.
          flight_state_exactly st 'view **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768 /\
                (ok ==>
                  SZ.v slice_offset + SZ.v slice_len <= 32768 /\
                  Seq.equal
                    (flight_bytes_slice out_bytes 0 (SZ.v slice_len))
                    (flight_view_server_handshake_slice 'view slice_offset slice_len)))
{
  unfold (flight_state_exactly st 'view);
  if SZ.(slice_offset <=^ 32768sz) {
    let available = SZ.(32768sz -^ slice_offset);
    if SZ.(slice_len <=^ available) {
      assert (pure (SZ.v slice_offset + SZ.v slice_len <= 32768));
      V.pts_to_len st.server_handshake_messages;
      V.to_array_pts_to st.server_handshake_messages;
      with fragment_bytes.
        assert (pts_to (V.vec_to_array st.server_handshake_messages) fragment_bytes);
      assert (pure (fragment_bytes == 'view.server_handshake_bytes));
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      copy_fragment_to_buffer_loop
        (V.vec_to_array st.server_handshake_messages)
        32768sz
        out
        out_capacity
        slice_offset
        0sz
        slice_len;
      V.to_vec_pts_to st.server_handshake_messages;
      with out_s. assert (pts_to out out_s);
      assert (pure (B.length out_s == 32768));
      assert (pure (B.length 'view.server_handshake_bytes == 32768));
      assert (pure (flight_bytes_slice out_s 0 (SZ.v slice_len) ==
                    Seq.slice out_s 0 (SZ.v slice_len)));
      assert (pure (flight_view_server_handshake_slice 'view slice_offset slice_len ==
                    Seq.slice 'view.server_handshake_bytes
                      (SZ.v slice_offset)
                      (SZ.v slice_offset + SZ.v slice_len)));
      assert (pure (Seq.equal
        (flight_bytes_slice out_s 0 (SZ.v slice_len))
        (flight_view_server_handshake_slice 'view slice_offset slice_len)));
      fold (flight_state_exactly st 'view);
      true
    } else {
      with out_s. assert (pts_to out out_s);
      assert (pure (B.length out_s == 32768));
      fold (flight_state_exactly st 'view);
      false
    }
  } else {
    with out_s. assert (pts_to out out_s);
    assert (pure (B.length out_s == 32768));
    fold (flight_state_exactly st 'view);
    false
  }
}

fn copy_server_handshake_slice_exact_len
  (st: flight_state)
  (slice_offset: SZ.t)
  (slice_len: SZ.t)
  (out: array U8.t)
  (out_len: SZ.t)
  requires flight_state_exactly st 'view **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 out_len == slice_len)
  returns ok: bool
  ensures exists* out_bytes.
          flight_state_exactly st 'view **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v slice_len /\
                (ok ==>
                  SZ.v slice_offset + SZ.v slice_len <= 32768 /\
                  Seq.equal out_bytes
                    (flight_view_server_handshake_slice 'view slice_offset slice_len)))
{
  unfold (flight_state_exactly st 'view);
  if SZ.(slice_offset <=^ 32768sz) {
    let available = SZ.(32768sz -^ slice_offset);
    if SZ.(slice_len <=^ available) {
      assert (pure (SZ.v slice_offset + SZ.v slice_len <= 32768));
      V.pts_to_len st.server_handshake_messages;
      V.to_array_pts_to st.server_handshake_messages;
      with fragment_bytes.
        assert (pts_to (V.vec_to_array st.server_handshake_messages) fragment_bytes);
      assert (pure (fragment_bytes == 'view.server_handshake_bytes));
      assert (pure (Pulse.Lib.Array.Core.length (V.vec_to_array st.server_handshake_messages) == 32768));
      copy_fragment_to_buffer_loop
        (V.vec_to_array st.server_handshake_messages)
        32768sz
        out
        out_len
        slice_offset
        0sz
        slice_len;
      V.to_vec_pts_to st.server_handshake_messages;
      with out_s. assert (pts_to out out_s);
      assert (pure (B.length out_s == SZ.v slice_len));
      assert (pure (B.length 'view.server_handshake_bytes == 32768));
      assert (pure (Seq.equal
        (Seq.slice out_s 0 (SZ.v slice_len))
        (Seq.slice 'view.server_handshake_bytes
          (SZ.v slice_offset)
          (SZ.v slice_offset + SZ.v slice_len))));
      Seq.lemma_len_slice out_s 0 (SZ.v slice_len);
      Seq.lemma_eq_elim
        (Seq.slice out_s 0 (SZ.v slice_len))
        (Seq.slice 'view.server_handshake_bytes
          (SZ.v slice_offset)
          (SZ.v slice_offset + SZ.v slice_len));
      assert (pure (Seq.length (Seq.slice out_s 0 (SZ.v slice_len)) == B.length out_s));
      Seq.lemma_eq_intro out_s (Seq.slice out_s 0 (SZ.v slice_len));
      assert (pure (flight_view_server_handshake_slice 'view slice_offset slice_len ==
                    Seq.slice 'view.server_handshake_bytes
                      (SZ.v slice_offset)
                      (SZ.v slice_offset + SZ.v slice_len)));
      assert (pure (Seq.equal out_s
        (flight_view_server_handshake_slice 'view slice_offset slice_len)));
      fold (flight_state_exactly st 'view);
      true
    } else {
      with out_s. assert (pts_to out out_s);
      assert (pure (B.length out_s == SZ.v slice_len));
      fold (flight_state_exactly st 'view);
      false
    }
  } else {
    with out_s. assert (pts_to out out_s);
    assert (pure (B.length out_s == SZ.v slice_len));
    fold (flight_state_exactly st 'view);
    false
  }
}

fn certificate_leaf_offset (st: flight_state)
  requires is_flight_state st
  returns offset: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let offset = !st.certificate_leaf_offset_box;
  fold (is_flight_state st);
  offset
}

fn certificate_leaf_offset_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns offset: SZ.t
  ensures flight_state_exactly st 'view **
          pure (offset == 'view.certificate_leaf_offset)
{
  unfold (flight_state_exactly st 'view);
  let offset = !st.certificate_leaf_offset_box;
  assert (pure (offset == 'view.certificate_leaf_offset));
  fold (flight_state_exactly st 'view);
  offset
}

fn certificate_leaf_len (st: flight_state)
  requires is_flight_state st
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.certificate_leaf_len_box;
  fold (is_flight_state st);
  len
}

fn certificate_leaf_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.certificate_leaf_len)
{
  unfold (flight_state_exactly st 'view);
  let len = !st.certificate_leaf_len_box;
  assert (pure (len == 'view.certificate_leaf_len));
  fold (flight_state_exactly st 'view);
  len
}

fn certificate_verify_signature_scheme (st: flight_state)
  requires is_flight_state st
  returns scheme: U16.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let scheme = !st.certificate_verify_signature_scheme_box;
  fold (is_flight_state st);
  scheme
}

fn certificate_verify_signature_scheme_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns scheme: U16.t
  ensures flight_state_exactly st 'view **
          pure (scheme == 'view.certificate_verify_signature_scheme)
{
  unfold (flight_state_exactly st 'view);
  let scheme = !st.certificate_verify_signature_scheme_box;
  assert (pure (scheme == 'view.certificate_verify_signature_scheme));
  fold (flight_state_exactly st 'view);
  scheme
}

fn certificate_verify_signature_offset (st: flight_state)
  requires is_flight_state st
  returns offset: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let offset = !st.certificate_verify_signature_offset_box;
  fold (is_flight_state st);
  offset
}

fn certificate_verify_signature_offset_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns offset: SZ.t
  ensures flight_state_exactly st 'view **
          pure (offset == 'view.certificate_verify_signature_offset)
{
  unfold (flight_state_exactly st 'view);
  let offset = !st.certificate_verify_signature_offset_box;
  assert (pure (offset == 'view.certificate_verify_signature_offset));
  fold (flight_state_exactly st 'view);
  offset
}

fn certificate_verify_signature_len (st: flight_state)
  requires is_flight_state st
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.certificate_verify_signature_len_box;
  fold (is_flight_state st);
  len
}

fn certificate_verify_signature_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.certificate_verify_signature_len)
{
  unfold (flight_state_exactly st 'view);
  let len = !st.certificate_verify_signature_len_box;
  assert (pure (len == 'view.certificate_verify_signature_len));
  fold (flight_state_exactly st 'view);
  len
}

fn copy_certificate_leaf_der
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768)
{
  let offset = certificate_leaf_offset st;
  let len = certificate_leaf_len st;
  copy_server_handshake_slice st offset len out out_capacity
}

fn copy_certificate_leaf_der_exact
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires flight_state_exactly st 'view **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  returns ok: bool
  ensures exists* out_bytes.
          flight_state_exactly st 'view **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768 /\
                (ok ==>
                  SZ.v 'view.certificate_leaf_offset + SZ.v 'view.certificate_leaf_len <= 32768 /\
                  Seq.equal
                    (flight_bytes_slice out_bytes 0 (SZ.v 'view.certificate_leaf_len))
                    (flight_view_certificate_leaf_der 'view)))
{
  let offset = certificate_leaf_offset_exact st;
  let len = certificate_leaf_len_exact st;
  let ok = copy_server_handshake_slice_exact st offset len out out_capacity;
  with out_s. assert (pts_to out out_s);
  assert (pure (offset == 'view.certificate_leaf_offset));
  assert (pure (len == 'view.certificate_leaf_len));
  assert (pure (flight_view_server_handshake_slice 'view offset len ==
                flight_view_certificate_leaf_der 'view));
  ok
}

fn copy_certificate_leaf_der_exact_len
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires flight_state_exactly st 'view **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 out_len == 'view.certificate_leaf_len)
  returns ok: bool
  ensures exists* out_bytes.
          flight_state_exactly st 'view **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v 'view.certificate_leaf_len /\
                (ok ==>
                  SZ.v 'view.certificate_leaf_offset + SZ.v 'view.certificate_leaf_len <= 32768 /\
                  Seq.equal out_bytes (flight_view_certificate_leaf_der 'view)))
{
  let offset = certificate_leaf_offset_exact st;
  let len = certificate_leaf_len_exact st;
  let ok = copy_server_handshake_slice_exact_len st offset len out out_len;
  with out_s. assert (pts_to out out_s);
  assert (pure (offset == 'view.certificate_leaf_offset));
  assert (pure (len == 'view.certificate_leaf_len));
  assert (pure (flight_view_server_handshake_slice 'view offset len ==
                flight_view_certificate_leaf_der 'view));
  ok
}

fn copy_certificate_verify_signature
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768)
{
  let offset = certificate_verify_signature_offset st;
  let len = certificate_verify_signature_len st;
  copy_server_handshake_slice st offset len out out_capacity
}

fn copy_certificate_verify_signature_exact
  (st: flight_state)
  (out: array U8.t)
  (out_capacity: SZ.t)
  requires flight_state_exactly st 'view **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_capacity /\
                 SZ.v out_capacity == 32768)
  returns ok: bool
  ensures exists* out_bytes.
          flight_state_exactly st 'view **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32768 /\
                (ok ==>
                  SZ.v 'view.certificate_verify_signature_offset + SZ.v 'view.certificate_verify_signature_len <= 32768 /\
                  Seq.equal
                    (flight_bytes_slice out_bytes 0 (SZ.v 'view.certificate_verify_signature_len))
                    (flight_view_certificate_verify_signature 'view)))
{
  let offset = certificate_verify_signature_offset_exact st;
  let len = certificate_verify_signature_len_exact st;
  let ok = copy_server_handshake_slice_exact st offset len out out_capacity;
  with out_s. assert (pts_to out out_s);
  assert (pure (offset == 'view.certificate_verify_signature_offset));
  assert (pure (len == 'view.certificate_verify_signature_len));
  assert (pure (flight_view_server_handshake_slice 'view offset len ==
                flight_view_certificate_verify_signature 'view));
  ok
}

fn copy_certificate_verify_signature_exact_len
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires flight_state_exactly st 'view **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 out_len == 'view.certificate_verify_signature_len)
  returns ok: bool
  ensures exists* out_bytes.
          flight_state_exactly st 'view **
          pts_to out out_bytes **
          pure (B.length out_bytes == SZ.v 'view.certificate_verify_signature_len /\
                (ok ==>
                  SZ.v 'view.certificate_verify_signature_offset + SZ.v 'view.certificate_verify_signature_len <= 32768 /\
                  Seq.equal out_bytes (flight_view_certificate_verify_signature 'view)))
{
  let offset = certificate_verify_signature_offset_exact st;
  let len = certificate_verify_signature_len_exact st;
  let ok = copy_server_handshake_slice_exact_len st offset len out out_len;
  with out_s. assert (pts_to out out_s);
  assert (pure (offset == 'view.certificate_verify_signature_offset));
  assert (pure (len == 'view.certificate_verify_signature_len));
  assert (pure (flight_view_server_handshake_slice 'view offset len ==
                flight_view_certificate_verify_signature 'view));
  ok
}

fn server_before_finished_len (st: flight_state)
  requires is_flight_state st
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.before_finished_len_box;
  fold (is_flight_state st);
  len
}

fn server_before_finished_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.server_before_finished_len)
{
  unfold (flight_state_exactly st 'view);
  let len = !st.before_finished_len_box;
  assert (pure (len == 'view.server_before_finished_len));
  fold (flight_state_exactly st 'view);
  len
}

fn server_through_finished_len (st: flight_state)
  requires is_flight_state st
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.through_finished_len_box;
  fold (is_flight_state st);
  len
}

fn server_through_finished_len_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns len: (l:SZ.t{SZ.v l <= 32768})
  ensures flight_state_exactly st 'view **
          pure (len == 'view.server_through_finished_len)
{
  unfold (flight_state_exactly st 'view);
  let len = !st.through_finished_len_box;
  assert (pure (len == 'view.server_through_finished_len));
  fold (flight_state_exactly st 'view);
  len
}

fn verify_server_finished (st: flight_state)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  let mut client_hello = [| 0uy; 512sz |];
  let mut server_hello = [| 0uy; 4096sz |];
  let mut server_handshake = [| 0uy; 32768sz |];
  let mut finished_verify_data = [| 0uy; 32sz |];
  let mut server_hs_secret = [| 0uy; 32sz |];
  copy_client_hello st client_hello 512sz;
  copy_server_hello st server_hello 4096sz;
  copy_server_handshake st server_handshake 32768sz;
  copy_server_finished_verify_data st finished_verify_data 32sz;
  copy_server_handshake_traffic_secret st server_hs_secret 32sz;
  let ch_len = client_hello_len st;
  let sh_len = server_hello_len st;
  let before_len = server_before_finished_len st;
  assert (pure (SZ.v ch_len <= 512));
  assert (pure (SZ.v sh_len <= 4096));
  assert (pure (SZ.v before_len <= 32768));
  assert (pure (SZ.fits (SZ.v ch_len + SZ.v sh_len)));
  if SZ.(ch_len +^ sh_len <=^ 32768sz) {
    let ch_sh_len = SZ.(ch_len +^ sh_len);
    assert (pure (SZ.v ch_sh_len <= 32768));
    if SZ.(before_len <=^ 32768sz) {
      let mut client_hello_exact = [| 0uy; ch_len |];
      let mut server_hello_exact = [| 0uy; sh_len |];
      let mut server_handshake_exact = [| 0uy; before_len |];
      copy_fragment_to_buffer_loop client_hello 512sz client_hello_exact ch_len 0sz 0sz ch_len;
      copy_fragment_to_buffer_loop server_hello 4096sz server_hello_exact sh_len 0sz 0sz sh_len;
      copy_fragment_to_buffer_loop server_handshake 32768sz server_handshake_exact before_len 0sz 0sz before_len;
      assert (pure (SZ.fits (SZ.v ch_sh_len + SZ.v before_len)));
      if SZ.(ch_sh_len +^ before_len <=^ 32768sz) {
        let mut transcript_hash = [| 0uy; 32sz |];
        let transcript_ok =
          Transcript.hash_client_server_handshake
            client_hello_exact
            ch_len
            server_hello_exact
            sh_len
            server_handshake_exact
            before_len
            transcript_hash;
        if transcript_ok {
          let mut expected = [| 0uy; 32sz |];
          KS.finished_verify_data server_hs_secret transcript_hash expected;
          Transcript.equal32 expected finished_verify_data
        } else {
          false
        }
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

fn build_client_finished_record
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 58)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 58)
{
  let mut client_hello = [| 0uy; 512sz |];
  let mut server_hello = [| 0uy; 4096sz |];
  let mut server_handshake = [| 0uy; 32768sz |];
  let mut client_hs_secret = [| 0uy; 32sz |];
  copy_client_hello st client_hello 512sz;
  copy_server_hello st server_hello 4096sz;
  copy_server_handshake st server_handshake 32768sz;
  copy_client_handshake_traffic_secret st client_hs_secret 32sz;
  let ch_len = client_hello_len st;
  let sh_len = server_hello_len st;
  let through_len = server_through_finished_len st;
  assert (pure (SZ.v ch_len <= 512));
  assert (pure (SZ.v sh_len <= 4096));
  assert (pure (SZ.v through_len <= 32768));
  assert (pure (SZ.fits (SZ.v ch_len + SZ.v sh_len)));
  if SZ.(ch_len +^ sh_len <=^ 32768sz) {
    let ch_sh_len = SZ.(ch_len +^ sh_len);
    assert (pure (SZ.v ch_sh_len <= 32768));
    if SZ.(through_len <=^ 32768sz) {
      let mut client_hello_exact = [| 0uy; ch_len |];
      let mut server_hello_exact = [| 0uy; sh_len |];
      let mut server_handshake_exact = [| 0uy; through_len |];
      copy_fragment_to_buffer_loop client_hello 512sz client_hello_exact ch_len 0sz 0sz ch_len;
      copy_fragment_to_buffer_loop server_hello 4096sz server_hello_exact sh_len 0sz 0sz sh_len;
      copy_fragment_to_buffer_loop server_handshake 32768sz server_handshake_exact through_len 0sz 0sz through_len;
      assert (pure (SZ.fits (SZ.v ch_sh_len + SZ.v through_len)));
      if SZ.(ch_sh_len +^ through_len <=^ 32768sz) {
        let mut transcript_hash = [| 0uy; 32sz |];
        let transcript_ok =
          Transcript.hash_client_server_handshake
            client_hello_exact
            ch_len
            server_hello_exact
            sh_len
            server_handshake_exact
            through_len
            transcript_hash;
        if transcript_ok {
          let mut verify_data = [| 0uy; 32sz |];
          let mut client_finished = [| 0uy; 36sz |];
          let mut header = [| 0uy; 5sz |];
          let mut inner = [| 0uy; 37sz |];
          let mut cipher = [| 0uy; 53sz |];
          client_finished.(0sz) <- 20uy;
          client_finished.(1sz) <- 0uy;
          client_finished.(2sz) <- 0uy;
          client_finished.(3sz) <- 32uy;
          KS.finished_verify_data client_hs_secret transcript_hash verify_data;
          set_client_finished_verify_data st verify_data 32sz;
          copy_fragment_to_buffer_loop verify_data 32sz client_finished 36sz 0sz 4sz 32sz;
          header.(0sz) <- 0x17uy;
          header.(1sz) <- 0x03uy;
          header.(2sz) <- 0x03uy;
          header.(3sz) <- 0uy;
          header.(4sz) <- 53uy;
          copy_fragment_to_buffer_loop client_finished 36sz inner 37sz 0sz 0sz 36sz;
          inner.(36sz) <- 22uy;
          pts_to_len inner;
          with header_bytes. assert (pts_to header header_bytes);
          with inner_bytes. assert (pts_to inner inner_bytes);
          with cipher_bytes. assert (pts_to cipher cipher_bytes);
          assert (pure (B.length header_bytes == 5));
          assert (pure (B.length inner_bytes == 37));
          assert (pure (B.length cipher_bytes == 53));
          let sealed = seal_client_handshake_record st header 5sz inner 37sz cipher;
          if sealed {
            copy_fragment_to_buffer_loop header 5sz out out_len 0sz 0sz 5sz;
            copy_fragment_to_buffer_loop cipher 53sz out out_len 0sz 5sz 53sz;
            with out_bytes. assert (pts_to out out_bytes);
            assert (pure (B.length out_bytes == 58));
            true
          } else {
            with out_bytes. assert (pts_to out out_bytes);
            assert (pure (B.length out_bytes == 58));
            false
          }
        } else {
          with out_bytes. assert (pts_to out out_bytes);
          assert (pure (B.length out_bytes == 58));
          false
        }
      } else {
        with out_bytes. assert (pts_to out out_bytes);
        assert (pure (B.length out_bytes == 58));
        false
      }
    } else {
      with out_bytes. assert (pts_to out out_bytes);
      assert (pure (B.length out_bytes == 58));
      false
    }
  } else {
    with out_bytes. assert (pts_to out out_bytes);
    assert (pure (B.length out_bytes == 58));
    false
  }
}

fn build_certificate_verify_input
  (st: flight_state)
  (out: array U8.t)
  (out_len: SZ.t)
  requires is_flight_state st **
           pts_to out 'old_out **
           pure (B.length 'old_out == SZ.v out_len /\
                 SZ.v out_len == 130)
  returns ok: bool
  ensures exists* out_bytes.
          is_flight_state st **
          pts_to out out_bytes **
          pure (B.length out_bytes == 130)
{
  let mut client_hello = [| 0uy; 512sz |];
  let mut server_hello = [| 0uy; 4096sz |];
  let mut server_handshake = [| 0uy; 32768sz |];
  copy_client_hello st client_hello 512sz;
  copy_server_hello st server_hello 4096sz;
  copy_server_handshake st server_handshake 32768sz;
  let ch_len = client_hello_len st;
  let sh_len = server_hello_len st;
  let cv_offset = certificate_verify_offset st;
  assert (pure (SZ.v ch_len <= 512));
  assert (pure (SZ.v sh_len <= 4096));
  assert (pure (SZ.fits (SZ.v ch_len + SZ.v sh_len)));
  if SZ.(ch_len +^ sh_len <=^ 32768sz) {
    let ch_sh_len = SZ.(ch_len +^ sh_len);
    assert (pure (SZ.v ch_sh_len <= 32768));
    if SZ.(cv_offset <=^ 32768sz) {
      let mut client_hello_exact = [| 0uy; ch_len |];
      let mut server_hello_exact = [| 0uy; sh_len |];
      let mut server_handshake_exact = [| 0uy; cv_offset |];
      copy_fragment_to_buffer_loop client_hello 512sz client_hello_exact ch_len 0sz 0sz ch_len;
      copy_fragment_to_buffer_loop server_hello 4096sz server_hello_exact sh_len 0sz 0sz sh_len;
      copy_fragment_to_buffer_loop server_handshake 32768sz server_handshake_exact cv_offset 0sz 0sz cv_offset;
      assert (pure (SZ.fits (SZ.v ch_sh_len + SZ.v cv_offset)));
      if SZ.(ch_sh_len +^ cv_offset <=^ 32768sz) {
        let mut transcript_hash = [| 0uy; 32sz |];
        let transcript_ok =
          Transcript.hash_client_server_handshake
            client_hello_exact
            ch_len
            server_hello_exact
            sh_len
            server_handshake_exact
            cv_offset
            transcript_hash;
        if transcript_ok {
          HF.build_server_certificate_verify_input transcript_hash out out_len;
          with out_bytes. assert (pts_to out out_bytes);
          assert (pure (B.length out_bytes == 130));
          true
        } else {
          with out_bytes. assert (pts_to out out_bytes);
          assert (pure (B.length out_bytes == 130));
          false
        }
      } else {
        with out_bytes. assert (pts_to out out_bytes);
        assert (pure (B.length out_bytes == 130));
        false
      }
    } else {
      with out_bytes. assert (pts_to out out_bytes);
      assert (pure (B.length out_bytes == 130));
      false
    }
  } else {
    with out_bytes. assert (pts_to out out_bytes);
    assert (pure (B.length out_bytes == 130));
    false
  }
}

fn derive_application_keys
  (st: flight_state)
  (client_key: array U8.t)
  (client_key_len: SZ.t)
  (client_iv: array U8.t)
  (client_iv_len: SZ.t)
  (server_key: array U8.t)
  (server_key_len: SZ.t)
  (server_iv: array U8.t)
  (server_iv_len: SZ.t)
  requires is_flight_state st **
           pts_to client_key 'old_client_key **
           pts_to client_iv 'old_client_iv **
           pts_to server_key 'old_server_key **
           pts_to server_iv 'old_server_iv **
           pure (B.length 'old_client_key == SZ.v client_key_len /\
                 B.length 'old_client_iv == SZ.v client_iv_len /\
                 B.length 'old_server_key == SZ.v server_key_len /\
                 B.length 'old_server_iv == SZ.v server_iv_len /\
                 SZ.v client_key_len == 32 /\
                 SZ.v client_iv_len == 12 /\
                 SZ.v server_key_len == 32 /\
                 SZ.v server_iv_len == 12)
  returns ok: bool
  ensures exists* client_key_bytes client_iv_bytes server_key_bytes server_iv_bytes.
          is_flight_state st **
          pts_to client_key client_key_bytes **
          pts_to client_iv client_iv_bytes **
          pts_to server_key server_key_bytes **
          pts_to server_iv server_iv_bytes **
          pure (B.length client_key_bytes == 32 /\
                B.length client_iv_bytes == 12 /\
                B.length server_key_bytes == 32 /\
                B.length server_iv_bytes == 12)
{
  let mut client_hello = [| 0uy; 512sz |];
  let mut server_hello = [| 0uy; 4096sz |];
  let mut server_handshake = [| 0uy; 32768sz |];
  let mut handshake_secret_bytes = [| 0uy; 32sz |];
  copy_client_hello st client_hello 512sz;
  copy_server_hello st server_hello 4096sz;
  copy_server_handshake st server_handshake 32768sz;
  copy_handshake_secret st handshake_secret_bytes 32sz;
  let ch_len = client_hello_len st;
  let sh_len = server_hello_len st;
  let through_len = server_through_finished_len st;
  assert (pure (SZ.v ch_len <= 512));
  assert (pure (SZ.v sh_len <= 4096));
  assert (pure (SZ.v through_len <= 32768));
  assert (pure (SZ.fits (SZ.v ch_len + SZ.v sh_len)));
  if SZ.(ch_len +^ sh_len <=^ 32768sz) {
    let ch_sh_len = SZ.(ch_len +^ sh_len);
    assert (pure (SZ.v ch_sh_len <= 32768));
    if SZ.(through_len <=^ 32768sz) {
      let mut client_hello_exact = [| 0uy; ch_len |];
      let mut server_hello_exact = [| 0uy; sh_len |];
      let mut server_handshake_exact = [| 0uy; through_len |];
      copy_fragment_to_buffer_loop client_hello 512sz client_hello_exact ch_len 0sz 0sz ch_len;
      copy_fragment_to_buffer_loop server_hello 4096sz server_hello_exact sh_len 0sz 0sz sh_len;
      copy_fragment_to_buffer_loop server_handshake 32768sz server_handshake_exact through_len 0sz 0sz through_len;
      assert (pure (SZ.fits (SZ.v ch_sh_len + SZ.v through_len)));
      if SZ.(ch_sh_len +^ through_len <=^ 32768sz) {
        let mut transcript_hash = [| 0uy; 32sz |];
        let transcript_ok =
          Transcript.hash_client_server_handshake
            client_hello_exact
            ch_len
            server_hello_exact
            sh_len
            server_handshake_exact
            through_len
            transcript_hash;
        if transcript_ok {
          let mut master_secret = [| 0uy; 32sz |];
          let mut client_application_traffic_secret = [| 0uy; 32sz |];
          let mut server_application_traffic_secret = [| 0uy; 32sz |];
          KS.master_secret handshake_secret_bytes master_secret;
          KS.client_application_traffic_secret master_secret transcript_hash client_application_traffic_secret;
          KS.server_application_traffic_secret master_secret transcript_hash server_application_traffic_secret;
          KS.derive_traffic_key client_application_traffic_secret client_key;
          KS.derive_traffic_iv client_application_traffic_secret client_iv;
          KS.derive_traffic_key server_application_traffic_secret server_key;
          KS.derive_traffic_iv server_application_traffic_secret server_iv;
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
  } else {
    false
  }
}

fn saw_certificate (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let saw = !st.saw_certificate_box;
  fold (is_flight_state st);
  saw
}

fn saw_certificate_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns saw: bool
  ensures flight_state_exactly st 'view **
          pure (saw == 'view.saw_certificate)
{
  unfold (flight_state_exactly st 'view);
  let saw = !st.saw_certificate_box;
  assert (pure (saw == 'view.saw_certificate));
  fold (flight_state_exactly st 'view);
  saw
}

fn saw_certificate_verify (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let saw = !st.saw_certificate_verify_box;
  fold (is_flight_state st);
  saw
}

fn saw_certificate_verify_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns saw: bool
  ensures flight_state_exactly st 'view **
          pure (saw == 'view.saw_certificate_verify)
{
  unfold (flight_state_exactly st 'view);
  let saw = !st.saw_certificate_verify_box;
  assert (pure (saw == 'view.saw_certificate_verify));
  fold (flight_state_exactly st 'view);
  saw
}

fn certificate_verify_verified (st: flight_state)
  requires is_flight_state st
  returns verified: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let verified = !st.certificate_verify_verified_box;
  fold (is_flight_state st);
  verified
}

fn certificate_verify_verified_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns verified: bool
  ensures flight_state_exactly st 'view **
          pure (verified == 'view.certificate_verify_verified)
{
  unfold (flight_state_exactly st 'view);
  let verified = !st.certificate_verify_verified_box;
  assert (pure (verified == 'view.certificate_verify_verified));
  fold (flight_state_exactly st 'view);
  verified
}

fn saw_finished (st: flight_state)
  requires is_flight_state st
  returns saw: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let saw = !st.saw_finished_box;
  fold (is_flight_state st);
  saw
}

fn saw_finished_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns saw: bool
  ensures flight_state_exactly st 'view **
          pure (saw == 'view.saw_finished)
{
  unfold (flight_state_exactly st 'view);
  let saw = !st.saw_finished_box;
  assert (pure (saw == 'view.saw_finished));
  fold (flight_state_exactly st 'view);
  saw
}

fn encrypted_handshake_complete (st: flight_state)
  requires is_flight_state st
  returns complete: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let saw_ee = !st.saw_encrypted_extensions_box;
  let saw_finished = !st.saw_finished_box;
  fold (is_flight_state st);
  saw_ee && saw_finished
}

fn encrypted_handshake_complete_exact (st: flight_state)
  requires flight_state_exactly st 'view
  returns complete: bool
  ensures flight_state_exactly st 'view **
          pure (complete == ('view.saw_encrypted_extensions && 'view.saw_finished))
{
  unfold (flight_state_exactly st 'view);
  let saw_ee = !st.saw_encrypted_extensions_box;
  let saw_finished = !st.saw_finished_box;
  assert (pure (saw_ee == 'view.saw_encrypted_extensions));
  assert (pure (saw_finished == 'view.saw_finished));
  fold (flight_state_exactly st 'view);
  saw_ee && saw_finished
}
