module TLS13.Record

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module R = TLS13.Record.Spec
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module U64 = FStar.UInt64

val record_state : Type0

val is_record_state: record_state -> R.direction_state -> slprop

fn record_state_new ()
  returns st: record_state
  ensures is_record_state st R.initial_direction_state

fn record_state_free (st: record_state)
  requires is_record_state st 's
  ensures emp

fn can_advance_seq (st: record_state)
  requires is_record_state st 's
  returns ok: bool
  ensures is_record_state st 's **
          pure (ok ==> U64.fits ('s.R.seq + 1))

fn advance_seq (st: record_state)
  requires is_record_state st 's **
           pure (U64.fits ('s.R.seq + 1))
  ensures is_record_state st (R.next_seq 's)

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
                           { R.content_type = T.ApplicationData;
                             R.fragment = Ghost.reveal 'plain_bytes } == Some (out_bytes, s') /\
                         B.length out_bytes == B.length 'old) /\
                (not ok ==> s' == 's /\
                            out_bytes == 'old /\
                            R.seal
                              's
                              (Ghost.reveal 'aad_bytes)
                              { R.content_type = T.ApplicationData;
                                R.fragment = Ghost.reveal 'plain_bytes } == None))

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
