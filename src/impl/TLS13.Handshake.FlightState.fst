module TLS13.Handshake.FlightState

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Box { box, (!), (:=) }

module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module U16 = FStar.UInt16

noeq
type flight_state = {
  handshake_len_box: box SZ.t;
  parsed_len_box: box SZ.t;
  certificate_verify_offset_box: box SZ.t;
  certificate_leaf_offset_box: box SZ.t;
  certificate_leaf_len_box: box SZ.t;
  certificate_verify_signature_scheme_box: box U16.t;
  certificate_verify_signature_offset_box: box SZ.t;
  certificate_verify_signature_len_box: box SZ.t;
  before_finished_len_box: box SZ.t;
  through_finished_len_box: box SZ.t;
  saw_encrypted_extensions_box: box bool;
  saw_certificate_box: box bool;
  saw_certificate_verify_box: box bool;
  saw_finished_box: box bool;
}

let is_flight_state ([@@@mkey] st: flight_state) : slprop =
  exists* handshake_len parsed_len certificate_verify_offset certificate_leaf_offset certificate_leaf_len
          certificate_verify_signature_scheme certificate_verify_signature_offset certificate_verify_signature_len
          before_finished_len through_finished_len
          saw_encrypted_extensions saw_certificate saw_certificate_verify saw_finished.
    Box.pts_to st.handshake_len_box handshake_len **
    Box.pts_to st.parsed_len_box parsed_len **
    Box.pts_to st.certificate_verify_offset_box certificate_verify_offset **
    Box.pts_to st.certificate_leaf_offset_box certificate_leaf_offset **
    Box.pts_to st.certificate_leaf_len_box certificate_leaf_len **
    Box.pts_to st.certificate_verify_signature_scheme_box certificate_verify_signature_scheme **
    Box.pts_to st.certificate_verify_signature_offset_box certificate_verify_signature_offset **
    Box.pts_to st.certificate_verify_signature_len_box certificate_verify_signature_len **
    Box.pts_to st.before_finished_len_box before_finished_len **
    Box.pts_to st.through_finished_len_box through_finished_len **
    Box.pts_to st.saw_encrypted_extensions_box saw_encrypted_extensions **
    Box.pts_to st.saw_certificate_box saw_certificate **
    Box.pts_to st.saw_certificate_verify_box saw_certificate_verify **
    Box.pts_to st.saw_finished_box saw_finished

fn flight_state_new ()
  returns st: flight_state
  ensures is_flight_state st
{
  let handshake_len_box = Box.alloc 0sz;
  let parsed_len_box = Box.alloc 0sz;
  let certificate_verify_offset_box = Box.alloc 0sz;
  let certificate_leaf_offset_box = Box.alloc 0sz;
  let certificate_leaf_len_box = Box.alloc 0sz;
  let certificate_verify_signature_scheme_box = Box.alloc 0us;
  let certificate_verify_signature_offset_box = Box.alloc 0sz;
  let certificate_verify_signature_len_box = Box.alloc 0sz;
  let before_finished_len_box = Box.alloc 0sz;
  let through_finished_len_box = Box.alloc 0sz;
  let saw_encrypted_extensions_box = Box.alloc false;
  let saw_certificate_box = Box.alloc false;
  let saw_certificate_verify_box = Box.alloc false;
  let saw_finished_box = Box.alloc false;
  let st = {
    handshake_len_box;
    parsed_len_box;
    certificate_verify_offset_box;
    certificate_leaf_offset_box;
    certificate_leaf_len_box;
    certificate_verify_signature_scheme_box;
    certificate_verify_signature_offset_box;
    certificate_verify_signature_len_box;
    before_finished_len_box;
    through_finished_len_box;
    saw_encrypted_extensions_box;
    saw_certificate_box;
    saw_certificate_verify_box;
    saw_finished_box
  };
  with v. rewrite (Box.pts_to handshake_len_box v) as (Box.pts_to st.handshake_len_box v);
  with v. rewrite (Box.pts_to parsed_len_box v) as (Box.pts_to st.parsed_len_box v);
  with v. rewrite (Box.pts_to certificate_verify_offset_box v) as (Box.pts_to st.certificate_verify_offset_box v);
  with v. rewrite (Box.pts_to certificate_leaf_offset_box v) as (Box.pts_to st.certificate_leaf_offset_box v);
  with v. rewrite (Box.pts_to certificate_leaf_len_box v) as (Box.pts_to st.certificate_leaf_len_box v);
  with v. rewrite (Box.pts_to certificate_verify_signature_scheme_box v) as (Box.pts_to st.certificate_verify_signature_scheme_box v);
  with v. rewrite (Box.pts_to certificate_verify_signature_offset_box v) as (Box.pts_to st.certificate_verify_signature_offset_box v);
  with v. rewrite (Box.pts_to certificate_verify_signature_len_box v) as (Box.pts_to st.certificate_verify_signature_len_box v);
  with v. rewrite (Box.pts_to before_finished_len_box v) as (Box.pts_to st.before_finished_len_box v);
  with v. rewrite (Box.pts_to through_finished_len_box v) as (Box.pts_to st.through_finished_len_box v);
  with v. rewrite (Box.pts_to saw_encrypted_extensions_box v) as (Box.pts_to st.saw_encrypted_extensions_box v);
  with v. rewrite (Box.pts_to saw_certificate_box v) as (Box.pts_to st.saw_certificate_box v);
  with v. rewrite (Box.pts_to saw_certificate_verify_box v) as (Box.pts_to st.saw_certificate_verify_box v);
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
  Box.free st.certificate_verify_offset_box;
  Box.free st.certificate_leaf_offset_box;
  Box.free st.certificate_leaf_len_box;
  Box.free st.certificate_verify_signature_scheme_box;
  Box.free st.certificate_verify_signature_offset_box;
  Box.free st.certificate_verify_signature_len_box;
  Box.free st.before_finished_len_box;
  Box.free st.through_finished_len_box;
  Box.free st.saw_encrypted_extensions_box;
  Box.free st.saw_certificate_box;
  Box.free st.saw_certificate_verify_box;
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
  st.saw_finished_box := false;
  fold (is_flight_state st);
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

fn append_handshake_len (st: flight_state) (fragment_len: SZ.t) (capacity: SZ.t)
  requires is_flight_state st
  returns ok: bool
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let current = !st.handshake_len_box;
  if SZ.(fragment_len <=^ capacity) {
    let remaining = SZ.(capacity -^ fragment_len);
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

fn set_certificate_leaf (st: flight_state) (leaf_offset: SZ.t) (leaf_len: SZ.t)
  requires is_flight_state st
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

fn set_certificate_verify_signature
  (st: flight_state)
  (signature_scheme: U16.t)
  (signature_offset: SZ.t)
  (signature_len: SZ.t)
  requires is_flight_state st
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  st.certificate_verify_signature_scheme_box := signature_scheme;
  st.certificate_verify_signature_offset_box := signature_offset;
  st.certificate_verify_signature_len_box := signature_len;
  fold (is_flight_state st);
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

fn certificate_leaf_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.certificate_leaf_len_box;
  fold (is_flight_state st);
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

fn certificate_verify_signature_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.certificate_verify_signature_len_box;
  fold (is_flight_state st);
  len
}

fn server_before_finished_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.before_finished_len_box;
  fold (is_flight_state st);
  len
}

fn server_through_finished_len (st: flight_state)
  requires is_flight_state st
  returns len: SZ.t
  ensures is_flight_state st
{
  unfold (is_flight_state st);
  let len = !st.through_finished_len_box;
  fold (is_flight_state st);
  len
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
