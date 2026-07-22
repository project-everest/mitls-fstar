module TLS13.Record

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open Pulse.Lib.Box { box, (!), (:=) }

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module Box = Pulse.Lib.Box
module C = TLS13.Crypto.Spec
module Crypto = TLS13.Crypto
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module V = Pulse.Lib.Vec

noeq
type record_state = {
  key: V.vec U8.t;
  iv: V.vec U8.t;
  seq: box U64.t;
  installed: box bool;
}

let state_matches
  (installed:bool)
  (seq:U64.t)
  (key:B.bytes)
  (iv:B.bytes)
  (s:R.direction_state)
  : prop =
  B.length key == 32 /\
  B.length iv == 12 /\
  U64.v seq == s.R.seq /\
  ((installed /\ s.R.key == Some key /\ s.R.static_iv == Some iv) \/
   (not installed /\ s.R.key == None /\ s.R.static_iv == None))

let is_record_state ([@@@mkey] st:record_state) (s:R.direction_state) : slprop =
  exists* key iv seq installed.
    V.pts_to st.key key **
    V.pts_to st.iv iv **
    Box.pts_to st.seq seq **
    Box.pts_to st.installed installed **
    pure (V.is_full_vec st.key /\
          V.is_full_vec st.iv /\
          state_matches installed seq key iv s)

fn record_state_new ()
  returns st: record_state
  ensures is_record_state st R.initial_direction_state
{
  let key = V.alloc 0uy 32sz;
  let iv = V.alloc 0uy 12sz;
  let seq = Box.alloc 0UL;
  let installed = Box.alloc false;
  let st = { key; iv; seq; installed };
  with key_s. rewrite (V.pts_to key key_s) as (V.pts_to st.key key_s);
  with iv_s. rewrite (V.pts_to iv iv_s) as (V.pts_to st.iv iv_s);
  with seq_s. rewrite (Box.pts_to seq seq_s) as (Box.pts_to st.seq seq_s);
  with installed_s. rewrite (Box.pts_to installed installed_s) as (Box.pts_to st.installed installed_s);
  assert_norm (state_matches false 0UL (Seq.create 32 0uy) (Seq.create 12 0uy) R.initial_direction_state);
  assert (pure (state_matches false 0UL (Seq.create 32 0uy) (Seq.create 12 0uy) R.initial_direction_state));
  fold (is_record_state st R.initial_direction_state);
  st
}

fn record_state_free (st: record_state)
  requires is_record_state st 's
  ensures emp
{
  unfold (is_record_state st 's);
  V.free st.key;
  V.free st.iv;
  Box.free st.seq;
  Box.free st.installed;
}

let u64_max : U64.t = U64.uint_to_t 18446744073709551615

let seq_can_advance (seq:U64.t) : bool = U64.lt seq u64_max

let lemma_seq_can_advance_fits (seq:U64.t)
  : Lemma
      (requires seq_can_advance seq)
      (ensures U64.fits (U64.v seq + 1))
=
  assert (U64.v u64_max == 18446744073709551615);
  assert (U64.v seq < U64.v u64_max);
  assert (U64.v seq + 1 < 18446744073709551616)

fn can_advance_seq (st: record_state)
  requires is_record_state st 's
  returns ok: bool
  ensures is_record_state st 's **
          pure (ok ==> U64.fits ('s.R.seq + 1))
{
  unfold (is_record_state st 's);
  let seq = !st.seq;
  let ok = seq_can_advance seq;
  if ok {
    lemma_seq_can_advance_fits seq;
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with installed_s. assert (Box.pts_to st.installed installed_s);
    assert (pure (state_matches installed_s seq key_s iv_s 's));
    assert (pure (U64.fits ('s.R.seq + 1)));
    fold (is_record_state st 's);
    true
  } else {
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with installed_s. assert (Box.pts_to st.installed installed_s);
    assert (pure (state_matches installed_s seq key_s iv_s 's));
    fold (is_record_state st 's);
    false
  }
}

fn seq_eq (st: record_state) (expected: U64.t)
  requires is_record_state st 's
  returns ok: bool
  ensures is_record_state st 's **
          pure (ok ==> 's.R.seq == U64.v expected)
{
  unfold (is_record_state st 's);
  with key_b iv_b seq_b installed_b. _;
  let current_seq = !st.seq;
  assert (pure (current_seq == seq_b));
  assert (pure (U64.v current_seq == 's.R.seq));
  let ok = current_seq = expected;
  assert (pure (ok ==> current_seq == expected));
  assert (pure (ok ==> U64.v current_seq == U64.v expected));
  assert (pure (ok ==> 's.R.seq == U64.v expected));
  fold (is_record_state st 's);
  ok
}

fn application_keys_match (st: record_state) (key: array U8.t) (iv: array U8.t)
  requires is_record_state st 's **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\ B.length 'iv_bytes == 12)
  returns ok: bool
  ensures is_record_state st 's **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes **
          pure (ok ==>
            's.R.key == Some (Ghost.reveal 'key_bytes) /\
            's.R.static_iv == Some (Ghost.reveal 'iv_bytes))
{
  unfold (is_record_state st 's);
  with stored_key stored_iv stored_seq stored_installed.
    assert (V.pts_to st.key stored_key **
            V.pts_to st.iv stored_iv **
            Box.pts_to st.seq stored_seq **
            Box.pts_to st.installed stored_installed);
  pts_to_len key;
  pts_to_len iv;
  V.pts_to_len st.key;
  V.pts_to_len st.iv;
  assert (pure (B.length stored_key == 32));
  assert (pure (B.length stored_iv == 12));
  let installed = !st.installed;
  assert (pure (installed == stored_installed));
  V.to_array_pts_to st.key;
  let key_ok = Crypto.equal32 (V.vec_to_array st.key) key;
  V.to_vec_pts_to st.key;
  V.to_array_pts_to st.iv;
  let iv_ok = Crypto.equal12 (V.vec_to_array st.iv) iv;
  V.to_vec_pts_to st.iv;
  let ok = installed && key_ok && iv_ok;
  assert (pure (ok ==> stored_installed));
  assert (pure (ok ==> Seq.equal stored_key 'key_bytes));
  assert (pure (ok ==> Seq.equal stored_iv 'iv_bytes));
  assert (pure (ok ==> stored_key == Ghost.reveal 'key_bytes));
  assert (pure (ok ==> stored_iv == Ghost.reveal 'iv_bytes));
  assert (pure (ok ==> 's.R.key == Some (Ghost.reveal 'key_bytes)));
  assert (pure (ok ==> 's.R.static_iv == Some (Ghost.reveal 'iv_bytes)));
  fold (is_record_state st 's);
  ok
}

fn has_seal_keys (st: record_state) (#'s: erased R.direction_state)
  requires is_record_state st 's
  returns ok: bool
  ensures is_record_state st 's **
          pure (ok ==> (match 's.R.key, 's.R.static_iv with
                        | Some _, Some _ -> True
                        | _, _ -> False))
{
  unfold (is_record_state st 's);
  let installed = !st.installed;
  with key_s. assert (V.pts_to st.key key_s);
  with iv_s. assert (V.pts_to st.iv iv_s);
  with seq_s. assert (Box.pts_to st.seq seq_s);
  assert (pure (state_matches installed seq_s key_s iv_s 's));
  if installed {
    assert (pure ('s.R.key == Some key_s /\ 's.R.static_iv == Some iv_s));
    fold (is_record_state st 's);
    true
  } else {
    fold (is_record_state st 's);
    false
  }
}

fn advance_seq (st: record_state)
  requires is_record_state st 's **
           pure (U64.fits ('s.R.seq + 1))
  ensures is_record_state st (R.next_seq 's)
{
  unfold (is_record_state st 's);
  let seq = !st.seq;
  let next_seq = U64.add seq 1UL;
  st.seq := next_seq;
  with key_s. assert (V.pts_to st.key key_s);
  with iv_s. assert (V.pts_to st.iv iv_s);
  with installed_s. assert (Box.pts_to st.installed installed_s);
  assert (pure (state_matches installed_s seq key_s iv_s 's));
  assert (pure (U64.v next_seq == 's.R.seq + 1));
  assert (pure (state_matches installed_s next_seq key_s iv_s (R.next_seq 's)));
  fold (is_record_state st (R.next_seq 's));
}

fn install_keys
  (st: record_state)
  (#epoch: R.epoch)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_record_state st 's **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\ B.length 'iv_bytes == 12)
  ensures is_record_state st (R.install_keys 's epoch (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes)) **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_record_state st 's);
  pts_to_len key;
  pts_to_len iv;
  V.pts_to_len st.key;
  V.pts_to_len st.iv;
  V.to_array_pts_to st.key;
  V.to_array_pts_to st.iv;
  Arr.memcpy 32sz key (V.vec_to_array st.key);
  Arr.memcpy 12sz iv (V.vec_to_array st.iv);
  V.to_vec_pts_to st.key;
  V.to_vec_pts_to st.iv;
  st.seq := 0UL;
  st.installed := true;
  with key_s. assert (V.pts_to st.key key_s);
  with iv_s. assert (V.pts_to st.iv iv_s);
  assert (pure (key_s == 'key_bytes));
  assert (pure (iv_s == 'iv_bytes));
  assert_norm (state_matches true 0UL key_s iv_s (R.install_keys 's epoch (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes)));
  assert (pure (state_matches true 0UL key_s iv_s (R.install_keys 's epoch (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes))));
  fold (is_record_state st (R.install_keys 's epoch (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes)));
}

fn install_handshake_keys_runtime
  (st: record_state)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_record_state st 's **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\ B.length 'iv_bytes == 12)
  ensures is_record_state st (R.install_keys 's R.Handshake (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes)) **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_record_state st 's);
  pts_to_len key;
  pts_to_len iv;
  V.pts_to_len st.key;
  V.pts_to_len st.iv;
  V.to_array_pts_to st.key;
  V.to_array_pts_to st.iv;
  Arr.memcpy 32sz key (V.vec_to_array st.key);
  Arr.memcpy 12sz iv (V.vec_to_array st.iv);
  V.to_vec_pts_to st.key;
  V.to_vec_pts_to st.iv;
  st.seq := 0UL;
  st.installed := true;
  with key_s. assert (V.pts_to st.key key_s);
  with iv_s. assert (V.pts_to st.iv iv_s);
  assert (pure (key_s == 'key_bytes));
  assert (pure (iv_s == 'iv_bytes));
  assert (pure (state_matches true 0UL key_s iv_s (R.install_keys 's R.Handshake (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes))));
  fold (is_record_state st (R.install_keys 's R.Handshake (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes)));
}

fn install_application_keys_runtime
  (st: record_state)
  (key: array U8.t)
  (iv: array U8.t)
  requires is_record_state st 's **
           pts_to key 'key_bytes **
           pts_to iv 'iv_bytes **
           pure (B.length 'key_bytes == 32 /\ B.length 'iv_bytes == 12)
  ensures is_record_state st (R.install_keys 's R.Application (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes)) **
          pts_to key 'key_bytes **
          pts_to iv 'iv_bytes
{
  unfold (is_record_state st 's);
  pts_to_len key;
  pts_to_len iv;
  V.pts_to_len st.key;
  V.pts_to_len st.iv;
  V.to_array_pts_to st.key;
  V.to_array_pts_to st.iv;
  Arr.memcpy 32sz key (V.vec_to_array st.key);
  Arr.memcpy 12sz iv (V.vec_to_array st.iv);
  V.to_vec_pts_to st.key;
  V.to_vec_pts_to st.iv;
  st.seq := 0UL;
  st.installed := true;
  with key_s. assert (V.pts_to st.key key_s);
  with iv_s. assert (V.pts_to st.iv iv_s);
  assert (pure (key_s == 'key_bytes));
  assert (pure (iv_s == 'iv_bytes));
  assert (pure (state_matches true 0UL key_s iv_s (R.install_keys 's R.Application (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes))));
  fold (is_record_state st (R.install_keys 's R.Application (Ghost.reveal 'key_bytes) (Ghost.reveal 'iv_bytes)));
}

fn seal_application
  (st: record_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires is_record_state st 's **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16 /\
                 U64.fits ('s.R.seq + 1))
  returns ok: bool
  ensures exists* s' out_bytes.
          is_record_state st s' **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out out_bytes **
          pure ((ok ==> R.seal
                           's
                           (Ghost.reveal 'aad_bytes)
                           { R.content_type = T.Application_data;
                             R.fragment = Ghost.reveal 'plain_bytes } == Some (out_bytes, s') /\
                         B.length out_bytes == B.length 'old) /\
                (not ok ==> s' == 's /\
                            out_bytes == 'old /\
                            R.seal
                              's
                              (Ghost.reveal 'aad_bytes)
                              { R.content_type = T.Application_data;
                                R.fragment = Ghost.reveal 'plain_bytes } == None))
{
  unfold (is_record_state st 's);
  let installed = !st.installed;
  if installed {
    let seq = !st.seq;
    let mut nonce = [| 0uy; 12sz |];
    V.to_array_pts_to st.key;
    V.to_array_pts_to st.iv;
    let nonce_ok = Crypto.tls13_record_nonce (V.vec_to_array st.iv) seq nonce;
    assert (pure nonce_ok);
    Crypto.chacha20_poly1305_seal (V.vec_to_array st.key) nonce aad aad_len plain plain_len out;
    V.to_vec_pts_to st.key;
    V.to_vec_pts_to st.iv;
    let next_seq = U64.add seq 1UL;
    st.seq := next_seq;
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    assert (pure (state_matches true seq key_s iv_s 's));
    assert (pure ('s.R.key == Some key_s /\ 's.R.static_iv == Some iv_s /\
                  's.R.seq == U64.v seq));
    assert (pure (B.length (C.chacha20_poly1305_seal key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'plain_bytes)) == B.length 'old));
    assert (pure (R.seal 's (Ghost.reveal 'aad_bytes) { R.content_type = T.Application_data; R.fragment = Ghost.reveal 'plain_bytes } ==
                  Some ((C.chacha20_poly1305_seal key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'plain_bytes) <: B.bytes),
                        R.next_seq 's)));
    assert (pure (match R.seal 's (Ghost.reveal 'aad_bytes) { R.content_type = T.Application_data; R.fragment = Ghost.reveal 'plain_bytes } with
                  | Some (sealed, s') ->
                    sealed == (C.chacha20_poly1305_seal key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'plain_bytes) <: B.bytes) /\
                    s' == R.next_seq 's /\
                    B.length sealed == B.length 'old
                  | None -> False));
    assert (pure (state_matches true next_seq key_s iv_s (R.next_seq 's)));
    fold (is_record_state st (R.next_seq 's));
    true
  } else {
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with seq_s. assert (Box.pts_to st.seq seq_s);
    assert (pure (R.seal 's (Ghost.reveal 'aad_bytes) { R.content_type = T.Application_data; R.fragment = Ghost.reveal 'plain_bytes } == None));
    fold (is_record_state st 's);
    false
  }
}

fn seal_application_no_update
  (st: record_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires is_record_state st 's **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16)
  returns ok: bool
  ensures exists* out_bytes.
          is_record_state st 's **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out out_bytes **
          pure ((ok ==> R.seal
                           's
                           (Ghost.reveal 'aad_bytes)
                           { R.content_type = T.Application_data;
                             R.fragment = Ghost.reveal 'plain_bytes } ==
                           Some (out_bytes, R.next_seq 's) /\
                         B.length out_bytes == B.length 'old) /\
                (not ok ==> out_bytes == 'old /\
                            R.seal
                              's
                              (Ghost.reveal 'aad_bytes)
                              { R.content_type = T.Application_data;
                                R.fragment = Ghost.reveal 'plain_bytes } == None))
{
  unfold (is_record_state st 's);
  let installed = !st.installed;
  if installed {
    let seq = !st.seq;
    let mut nonce = [| 0uy; 12sz |];
    V.to_array_pts_to st.key;
    V.to_array_pts_to st.iv;
    let nonce_ok = Crypto.tls13_record_nonce (V.vec_to_array st.iv) seq nonce;
    assert (pure nonce_ok);
    Crypto.chacha20_poly1305_seal (V.vec_to_array st.key) nonce aad aad_len plain plain_len out;
    V.to_vec_pts_to st.key;
    V.to_vec_pts_to st.iv;
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with out_s. assert (pts_to out out_s);
    assert (pure (state_matches true seq key_s iv_s 's));
    assert (pure ('s.R.key == Some key_s /\ 's.R.static_iv == Some iv_s /\
                  's.R.seq == U64.v seq));
    assert (pure (B.length
      (C.chacha20_poly1305_seal
        key_s
        (C.tls13_record_nonce iv_s (U64.v seq))
        (Ghost.reveal 'aad_bytes)
        (Ghost.reveal 'plain_bytes)) == B.length 'old));
    assert (pure (R.seal
      's
      (Ghost.reveal 'aad_bytes)
      { R.content_type = T.Application_data; R.fragment = Ghost.reveal 'plain_bytes } ==
      Some ((C.chacha20_poly1305_seal
               key_s
               (C.tls13_record_nonce iv_s (U64.v seq))
               (Ghost.reveal 'aad_bytes)
               (Ghost.reveal 'plain_bytes) <: B.bytes),
            R.next_seq 's)));
    assert (pure (out_s ==
      C.chacha20_poly1305_seal
        key_s
        (C.tls13_record_nonce iv_s (U64.v seq))
        (Ghost.reveal 'aad_bytes)
        (Ghost.reveal 'plain_bytes)));
    assert (pure (R.seal
      's
      (Ghost.reveal 'aad_bytes)
      { R.content_type = T.Application_data; R.fragment = Ghost.reveal 'plain_bytes } ==
      Some ((out_s <: B.bytes), R.next_seq 's)));
    fold (is_record_state st 's);
    true
  } else {
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with seq_s. assert (Box.pts_to st.seq seq_s);
    with out_s. assert (pts_to out out_s);
    assert (pure (out_s == 'old));
    assert (pure (state_matches false seq_s key_s iv_s 's));
    assert (pure (R.seal
      's
      (Ghost.reveal 'aad_bytes)
      { R.content_type = T.Application_data; R.fragment = Ghost.reveal 'plain_bytes } == None));
    fold (is_record_state st 's);
    false
  }
}

fn seal_application_runtime
  (st: record_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (plain: array U8.t)
  (plain_len: SZ.t)
  (out: array U8.t)
  requires is_record_state st 's **
           pts_to aad 'aad_bytes **
           pts_to plain 'plain_bytes **
           pts_to out 'old **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'plain_bytes == SZ.v plain_len /\
                 B.length 'old == SZ.v plain_len + 16)
  returns ok: bool
  ensures exists* s' out_bytes.
          is_record_state st s' **
          pts_to aad 'aad_bytes **
          pts_to plain 'plain_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == B.length 'old /\
                (ok /\ U64.fits ('s.R.seq + 1) ==> s'.R.seq == 's.R.seq + 1) /\
                (not ok ==> s' == 's /\ out_bytes == 'old))
{
  unfold (is_record_state st 's);
  let installed = !st.installed;
  if installed {
    let seq = !st.seq;
    let mut nonce = [| 0uy; 12sz |];
    V.to_array_pts_to st.key;
    V.to_array_pts_to st.iv;
    let nonce_ok = Crypto.tls13_record_nonce (V.vec_to_array st.iv) seq nonce;
    assert (pure nonce_ok);
    Crypto.chacha20_poly1305_seal (V.vec_to_array st.key) nonce aad aad_len plain plain_len out;
    V.to_vec_pts_to st.key;
    V.to_vec_pts_to st.iv;
    let next_seq = U64.add_underspec seq 1UL;
    st.seq := next_seq;
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with out_s. assert (pts_to out out_s);
    assert (pure (state_matches true seq key_s iv_s 's));
    assert (pure (B.length out_s == B.length 'old));
    assert (pure (U64.fits ('s.R.seq + 1) ==> U64.v next_seq == 's.R.seq + 1));
    assert (pure (state_matches true next_seq key_s iv_s ({ 's with R.seq = U64.v next_seq })));
    fold (is_record_state st ({ 's with R.seq = U64.v next_seq }));
    true
  } else {
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with seq_s. assert (Box.pts_to st.seq seq_s);
    with out_s. assert (pts_to out out_s);
    assert (pure (out_s == 'old));
    fold (is_record_state st 's);
    false
  }
}

fn open_application
  (st: record_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires is_record_state st 's **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old + 16 == SZ.v cipher_len /\
                 U64.fits ('s.R.seq + 1))
  returns ok: bool
  ensures exists* s' out_bytes.
          is_record_state st s' **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure ((ok ==> Some? (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes)) /\
                         (let opened = Some?.v (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes)) in
                          out_bytes == fst opened /\ s' == snd opened /\ B.length out_bytes == B.length 'old)) /\
                (not ok ==> s' == 's /\
                            out_bytes == 'old /\
                            R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes) == None))
{
  unfold (is_record_state st 's);
  let installed = !st.installed;
  if installed {
    let seq = !st.seq;
    let mut nonce = [| 0uy; 12sz |];
    V.to_array_pts_to st.key;
    V.to_array_pts_to st.iv;
    let nonce_ok = Crypto.tls13_record_nonce (V.vec_to_array st.iv) seq nonce;
    assert (pure nonce_ok);
    let opened = Crypto.chacha20_poly1305_open (V.vec_to_array st.key) nonce aad aad_len cipher cipher_len out;
    V.to_vec_pts_to st.key;
    V.to_vec_pts_to st.iv;
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    assert (pure (state_matches true seq key_s iv_s 's));
    assert (pure ('s.R.key == Some key_s /\ 's.R.static_iv == Some iv_s /\
                  's.R.seq == U64.v seq));
    if opened {
      let next_seq = U64.add seq 1UL;
      st.seq := next_seq;
      with out_s. assert (pts_to out out_s);
      assert (pure (Some? (C.chacha20_poly1305_open key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes))));
      assert (pure (out_s == Some?.v (C.chacha20_poly1305_open key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes))));
      assert (pure (Some? (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes))));
      assert (pure (Some?.v (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes)) == (out_s, R.next_seq 's)));
      assert (pure (state_matches true next_seq key_s iv_s (R.next_seq 's)));
      fold (is_record_state st (R.next_seq 's));
      true
    } else {
      assert (pure (C.chacha20_poly1305_open key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes) == None));
      assert (pure (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes) == None));
      fold (is_record_state st 's);
      false
    }
  } else {
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with seq_s. assert (Box.pts_to st.seq seq_s);
    assert (pure (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes) == None));
    fold (is_record_state st 's);
    false
  }
}

fn peek_open_application
  (st: record_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires is_record_state st 's **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          is_record_state st 's **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == B.length 'old /\
                (ok ==> Some? (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes)) /\
                         (let opened = Some?.v (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes)) in
                          out_bytes == fst opened)) /\
                (not ok ==> out_bytes == 'old /\
                            R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes) == None))
{
  unfold (is_record_state st 's);
  let installed = !st.installed;
  if installed {
    let seq = !st.seq;
    let mut nonce = [| 0uy; 12sz |];
    V.to_array_pts_to st.key;
    V.to_array_pts_to st.iv;
    let nonce_ok = Crypto.tls13_record_nonce (V.vec_to_array st.iv) seq nonce;
    assert (pure nonce_ok);
    let opened = Crypto.chacha20_poly1305_open (V.vec_to_array st.key) nonce aad aad_len cipher cipher_len out;
    V.to_vec_pts_to st.key;
    V.to_vec_pts_to st.iv;
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with seq_s. assert (Box.pts_to st.seq seq_s);
    assert (pure (seq_s == seq));
    assert (pure (state_matches true seq key_s iv_s 's));
    assert (pure ('s.R.key == Some key_s /\ 's.R.static_iv == Some iv_s /\
                  's.R.seq == U64.v seq));
    if opened {
      with out_s. assert (pts_to out out_s);
      assert (pure (B.length out_s == B.length 'old));
      assert (pure (Some? (C.chacha20_poly1305_open key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes))));
      assert (pure (out_s == Some?.v (C.chacha20_poly1305_open key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes))));
      assert (pure (Some? (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes))));
      assert (pure (Some?.v (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes)) == (out_s, R.next_seq 's)));
      fold (is_record_state st 's);
      true
    } else {
      with out_s. assert (pts_to out out_s);
      assert (pure (B.length out_s == B.length 'old));
      assert (pure (out_s == 'old));
      assert (pure (C.chacha20_poly1305_open key_s (C.tls13_record_nonce iv_s (U64.v seq)) (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes) == None));
      assert (pure (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes) == None));
      fold (is_record_state st 's);
      false
    }
  } else {
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with seq_s. assert (Box.pts_to st.seq seq_s);
    with out_s. assert (pts_to out out_s);
    assert (pure (out_s == 'old));
    assert (pure (R.open_record 's (Ghost.reveal 'aad_bytes) (Ghost.reveal 'cipher_bytes) == None));
    fold (is_record_state st 's);
    false
  }
}

fn peek_open_application_suffix
  (st: record_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (raw: array U8.t)
  (raw_len: SZ.t)
  (cipher_offset: SZ.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires is_record_state st 's **
           pts_to aad 'aad_bytes **
           pts_to raw 'raw_bytes **
           pts_to out 'old **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'raw_bytes == SZ.v raw_len /\
                 SZ.fits (SZ.v raw_len) /\
                 SZ.v cipher_offset <= SZ.v raw_len /\
                 SZ.v cipher_offset + SZ.v cipher_len == SZ.v raw_len /\
                 B.length 'old + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* out_bytes.
          is_record_state st 's **
          pts_to aad 'aad_bytes **
          pts_to raw 'raw_bytes **
          pts_to out out_bytes **
          pure (B.length 'raw_bytes == SZ.v raw_len /\
                SZ.fits (SZ.v raw_len) /\
                SZ.v cipher_offset <= SZ.v raw_len /\
                B.length out_bytes == B.length 'old /\
                (ok ==> Some? (R.open_record 's
                                  (Ghost.reveal 'aad_bytes)
                                  (Seq.slice
                                    (Ghost.reveal 'raw_bytes)
                                    (SZ.v cipher_offset)
                                    (SZ.v raw_len))) /\
                         (let opened = Some?.v (R.open_record 's
                                                (Ghost.reveal 'aad_bytes)
                                                (Seq.slice
                                                  (Ghost.reveal 'raw_bytes)
                                                  (SZ.v cipher_offset)
                                                  (SZ.v raw_len))) in
                          out_bytes == fst opened)) /\
                (not ok ==> out_bytes == 'old /\
                            R.open_record 's
                              (Ghost.reveal 'aad_bytes)
                              (Seq.slice
                                (Ghost.reveal 'raw_bytes)
                                (SZ.v cipher_offset)
                                (SZ.v raw_len)) == None))
{
  Arr.pts_to_len raw;
  Arr.to_mask raw;
  with raw_mask.
    assert (Arr.pts_to_mask raw #1.0R raw_mask (fun _ -> True));
  let cipher = Arr.sub raw cipher_offset (SZ.v raw_len);
  Arr.from_mask cipher;
  with cipher_bytes. assert (pts_to cipher cipher_bytes);
  assert (pure (Seq.equal cipher_bytes
    (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v cipher_offset) (SZ.v raw_len))));
  Seq.lemma_eq_elim cipher_bytes
    (Seq.slice (Ghost.reveal 'raw_bytes) (SZ.v cipher_offset) (SZ.v raw_len));
  let ok = peek_open_application st aad aad_len cipher cipher_len out;
  Arr.to_mask cipher;
  with cipher_mask_after.
    assert (Arr.pts_to_mask
      (Arr.gsub raw (SZ.v cipher_offset) (SZ.v raw_len))
      #1.0R
      cipher_mask_after
      (fun _ -> True));
  Arr.return_sub
    raw
    #1.0R
    #raw_mask
    #cipher_mask_after
    #(fun k ->
      True /\ ~(SZ.v cipher_offset <= k /\ k < SZ.v raw_len))
    #(fun _ -> True)
    #(SZ.v cipher_offset)
    #(SZ.v raw_len);
  Arr.from_mask raw;
  with raw_after. assert (pts_to raw raw_after);
  assert (pure (Seq.length raw_after == Seq.length (Ghost.reveal 'raw_bytes)));
  assert (pure (forall (i:nat). i < Seq.length raw_after ==>
    Seq.index raw_after i == Seq.index (Ghost.reveal 'raw_bytes) i));
  Seq.lemma_eq_intro raw_after (Ghost.reveal 'raw_bytes);
  Seq.lemma_eq_elim raw_after (Ghost.reveal 'raw_bytes);
  rewrite (pts_to raw raw_after) as (pts_to raw 'raw_bytes);
  ok
}

fn open_application_runtime
  (st: record_state)
  (aad: array U8.t)
  (aad_len: SZ.t)
  (cipher: array U8.t)
  (cipher_len: SZ.t)
  (out: array U8.t)
  requires is_record_state st 's **
           pts_to aad 'aad_bytes **
           pts_to cipher 'cipher_bytes **
           pts_to out 'old **
           pure (B.length 'aad_bytes == SZ.v aad_len /\
                 B.length 'cipher_bytes == SZ.v cipher_len /\
                 B.length 'old + 16 == SZ.v cipher_len)
  returns ok: bool
  ensures exists* s' out_bytes.
          is_record_state st s' **
          pts_to aad 'aad_bytes **
          pts_to cipher 'cipher_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == B.length 'old /\
                (ok /\ U64.fits ('s.R.seq + 1) ==> s'.R.seq == 's.R.seq + 1) /\
                (not ok ==> s' == 's /\ out_bytes == 'old))
{
  unfold (is_record_state st 's);
  let installed = !st.installed;
  if installed {
    let seq = !st.seq;
    let mut nonce = [| 0uy; 12sz |];
    V.to_array_pts_to st.key;
    V.to_array_pts_to st.iv;
    let nonce_ok = Crypto.tls13_record_nonce (V.vec_to_array st.iv) seq nonce;
    assert (pure nonce_ok);
    let opened = Crypto.chacha20_poly1305_open (V.vec_to_array st.key) nonce aad aad_len cipher cipher_len out;
    V.to_vec_pts_to st.key;
    V.to_vec_pts_to st.iv;
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    assert (pure (state_matches true seq key_s iv_s 's));
    assert (pure (B.length key_s == 32 /\ B.length iv_s == 12));
    if opened {
      let next_seq = U64.add_underspec seq 1UL;
      st.seq := next_seq;
      with out_s. assert (pts_to out out_s);
      assert (pure (B.length out_s == B.length 'old));
      assert (pure (U64.fits ('s.R.seq + 1) ==> U64.v next_seq == 's.R.seq + 1));
      assert (pure (state_matches true next_seq key_s iv_s ({ 's with R.seq = U64.v next_seq })));
      fold (is_record_state st ({ 's with R.seq = U64.v next_seq }));
      true
    } else {
      with out_s. assert (pts_to out out_s);
      assert (pure (out_s == 'old));
      fold (is_record_state st 's);
      false
    }
  } else {
    with key_s. assert (V.pts_to st.key key_s);
    with iv_s. assert (V.pts_to st.iv iv_s);
    with seq_s. assert (Box.pts_to st.seq seq_s);
    with out_s. assert (pts_to out out_s);
    assert (pure (out_s == 'old));
    fold (is_record_state st 's);
    false
  }
}
