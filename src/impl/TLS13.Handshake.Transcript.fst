module TLS13.Handshake.Transcript

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Arr = Pulse.Lib.Array
module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Crypto = TLS13.Crypto
module Ref = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module V = Pulse.Lib.Vec

noextract
let concat3 (a:B.bytes) (b:B.bytes) (c:B.bytes)
  : B.bytes_of_len (B.length a + B.length b + B.length c)
=
  Seq.lemma_len_append a b;
  Seq.lemma_len_append (B.append a b) c;
  B.append (B.append a b) c

noextract
let concat2 (a:B.bytes) (b:B.bytes)
  : B.bytes_of_len (B.length a + B.length b)
=
  Seq.lemma_create_len 0 0uy;
  Seq.lemma_len_append a b;
  Seq.lemma_len_append (B.append a b) B.empty;
  concat3 a b B.empty

let lemma_concat3_index_a
  (a:B.bytes)
  (b:B.bytes)
  (c:B.bytes)
  (i:nat{i < B.length a})
  : Lemma (Seq.index (concat3 a b c) i == Seq.index a i)
=
  Seq.lemma_len_append a b;
  Seq.lemma_index_app1 (B.append a b) c i;
  Seq.lemma_index_app1 a b i

let lemma_concat3_index_b
  (a:B.bytes)
  (b:B.bytes)
  (c:B.bytes)
  (i:nat{B.length a <= i /\ i < B.length a + B.length b})
  : Lemma (Seq.index (concat3 a b c) i == Seq.index b (i - B.length a))
=
  Seq.lemma_len_append a b;
  Seq.lemma_index_app1 (B.append a b) c i;
  Seq.lemma_index_app2 a b i

let lemma_concat3_index_c
  (a:B.bytes)
  (b:B.bytes)
  (c:B.bytes)
  (i:nat{B.length a + B.length b <= i /\ i < B.length a + B.length b + B.length c})
  : Lemma (Seq.index (concat3 a b c) i == Seq.index c (i - (B.length a + B.length b)))
=
  Seq.lemma_len_append a b;
  Seq.lemma_len_append (B.append a b) c;
  Seq.lemma_index_app2 (B.append a b) c i

let lemma_concat2_index_a
  (a:B.bytes)
  (b:B.bytes)
  (i:nat{i < B.length a})
  : Lemma (Seq.index (concat2 a b) i == Seq.index a i)
=
  lemma_concat3_index_a a b B.empty i

let lemma_concat2_index_b
  (a:B.bytes)
  (b:B.bytes)
  (i:nat{B.length a <= i /\ i < B.length a + B.length b})
  : Lemma (Seq.index (concat2 a b) i == Seq.index b (i - B.length a))
=
  lemma_concat3_index_b a b B.empty i

inline_for_extraction
fn hash_concat3
  (a: array U8.t)
  (a_len: SZ.t)
  (b: array U8.t)
  (b_len: SZ.t)
  (c: array U8.t)
  (c_len: SZ.t)
  (out: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pts_to c 'c_bytes **
           pts_to out 'old_out **
           pure (B.length 'a_bytes == SZ.v a_len /\
                 B.length 'b_bytes == SZ.v b_len /\
                 B.length 'c_bytes == SZ.v c_len /\
                 B.length 'old_out == 32 /\
                 SZ.v a_len + SZ.v b_len + SZ.v c_len <= 32768)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pts_to c 'c_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> out_bytes == C.sha256 (concat3 'a_bytes 'b_bytes 'c_bytes)))
{
  let ab_len = SZ.(a_len +^ b_len);
  let total_len = SZ.(ab_len +^ c_len);
  let transcript_vec = V.alloc 0uy total_len;
  V.to_array_pts_to transcript_vec;
  let transcript = V.vec_to_array transcript_vec;
  with s. rewrite (pts_to (V.vec_to_array transcript_vec) s) as (pts_to transcript s);
  pts_to_len transcript;
  let mut i = 0sz;
  while (SZ.lt !i a_len)
    invariant exists* vi transcript_bytes.
      Ref.pts_to i vi **
      pts_to a 'a_bytes **
      pts_to b 'b_bytes **
      pts_to c 'c_bytes **
      pts_to out 'old_out **
      pts_to transcript transcript_bytes **
      pure (B.length transcript_bytes == SZ.v total_len /\
            SZ.v total_len == B.length 'a_bytes + B.length 'b_bytes + B.length 'c_bytes /\
            SZ.v vi <= SZ.v a_len /\
            (forall (j:nat{j < SZ.v vi}).
              Seq.index transcript_bytes j == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) j))
  {
    let vi = !i;
    let byte = a.(vi);
    transcript.(vi) <- byte;
    with transcript_after. assert (pts_to transcript transcript_after);
    lemma_concat3_index_a 'a_bytes 'b_bytes 'c_bytes (SZ.v vi);
    assert (pure (Seq.index transcript_after (SZ.v vi) == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) (SZ.v vi)));
    assert (pure (forall (j:nat{j < SZ.v vi}).
      Seq.index transcript_after j == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) j));
    assert (pure (forall (j:nat{j < SZ.v vi + 1}).
      Seq.index transcript_after j == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) j));
    i := SZ.(vi +^ 1sz);
  };
  with i_after_a transcript_after_a. assert (Ref.pts_to i i_after_a ** pts_to transcript transcript_after_a);
  assert (pure (SZ.v i_after_a == SZ.v a_len));
  let mut j = 0sz;
  while (SZ.lt !j b_len)
    invariant exists* vj transcript_bytes.
      Ref.pts_to j vj **
      pts_to a 'a_bytes **
      pts_to b 'b_bytes **
      pts_to c 'c_bytes **
      pts_to out 'old_out **
      pts_to transcript transcript_bytes **
      pure (B.length transcript_bytes == SZ.v total_len /\
            SZ.v total_len == B.length 'a_bytes + B.length 'b_bytes + B.length 'c_bytes /\
            SZ.v vj <= SZ.v b_len /\
            (forall (k:nat{k < SZ.v a_len + SZ.v vj}).
              Seq.index transcript_bytes k == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) k))
  {
    let vj = !j;
    let dst = SZ.(a_len +^ vj);
    let byte = b.(vj);
    transcript.(dst) <- byte;
    with transcript_after. assert (pts_to transcript transcript_after);
    lemma_concat3_index_b 'a_bytes 'b_bytes 'c_bytes (SZ.v a_len + SZ.v vj);
    assert (pure (Seq.index transcript_after (SZ.v a_len + SZ.v vj) == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) (SZ.v a_len + SZ.v vj)));
    assert (pure (forall (k:nat{k < SZ.v a_len + SZ.v vj}).
      Seq.index transcript_after k == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) k));
    assert (pure (forall (k:nat{k < SZ.v a_len + SZ.v vj + 1}).
      Seq.index transcript_after k == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) k));
    j := SZ.(vj +^ 1sz);
  };
  with j_after_b transcript_after_b. assert (Ref.pts_to j j_after_b ** pts_to transcript transcript_after_b);
  assert (pure (SZ.v j_after_b == SZ.v b_len));
  let mut k = 0sz;
  while (SZ.lt !k c_len)
    invariant exists* vk transcript_bytes.
      Ref.pts_to k vk **
      pts_to a 'a_bytes **
      pts_to b 'b_bytes **
      pts_to c 'c_bytes **
      pts_to out 'old_out **
      pts_to transcript transcript_bytes **
      pure (B.length transcript_bytes == SZ.v total_len /\
            SZ.v total_len == B.length 'a_bytes + B.length 'b_bytes + B.length 'c_bytes /\
            SZ.v vk <= SZ.v c_len /\
            (forall (idx:nat{idx < SZ.v a_len + SZ.v b_len + SZ.v vk}).
              Seq.index transcript_bytes idx == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) idx))
  {
    let vk = !k;
    let dst = SZ.(ab_len +^ vk);
    let byte = c.(vk);
    transcript.(dst) <- byte;
    with transcript_after. assert (pts_to transcript transcript_after);
    lemma_concat3_index_c 'a_bytes 'b_bytes 'c_bytes (SZ.v a_len + SZ.v b_len + SZ.v vk);
    assert (pure (Seq.index transcript_after (SZ.v a_len + SZ.v b_len + SZ.v vk) == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) (SZ.v a_len + SZ.v b_len + SZ.v vk)));
    assert (pure (forall (idx:nat{idx < SZ.v a_len + SZ.v b_len + SZ.v vk}).
      Seq.index transcript_after idx == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) idx));
    assert (pure (forall (idx:nat{idx < SZ.v a_len + SZ.v b_len + SZ.v vk + 1}).
      Seq.index transcript_after idx == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) idx));
    k := SZ.(vk +^ 1sz);
  };
  with k_after_c transcript_bytes. assert (Ref.pts_to k k_after_c ** pts_to transcript transcript_bytes);
  assert (pure (SZ.v k_after_c == SZ.v c_len));
  assert (pure (forall (idx:nat{idx < B.length transcript_bytes}).
    Seq.index transcript_bytes idx == Seq.index (concat3 'a_bytes 'b_bytes 'c_bytes) idx));
  Seq.lemma_eq_intro transcript_bytes (concat3 'a_bytes 'b_bytes 'c_bytes);
  Seq.lemma_eq_elim transcript_bytes (concat3 'a_bytes 'b_bytes 'c_bytes);
  Crypto.sha256 transcript total_len out;
  with s. rewrite (pts_to transcript s) as (pts_to (V.vec_to_array transcript_vec) s);
  V.to_vec_pts_to transcript_vec;
  V.free transcript_vec;
  true
}

inline_for_extraction
fn hash_concat2
  (a: array U8.t)
  (a_len: SZ.t)
  (b: array U8.t)
  (b_len: SZ.t)
  (out: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pts_to out 'old_out **
           pure (B.length 'a_bytes == SZ.v a_len /\
                 B.length 'b_bytes == SZ.v b_len /\
                 B.length 'old_out == 32 /\
                 SZ.v a_len + SZ.v b_len <= 32768)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to a 'a_bytes **
          pts_to b 'b_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> out_bytes == C.sha256 (concat2 'a_bytes 'b_bytes)))
{
  let total_len = SZ.(a_len +^ b_len);
  let transcript_vec = V.alloc 0uy total_len;
  V.to_array_pts_to transcript_vec;
  let transcript = V.vec_to_array transcript_vec;
  with s. rewrite (pts_to (V.vec_to_array transcript_vec) s) as (pts_to transcript s);
  pts_to_len transcript;
  let mut i = 0sz;
  while (SZ.lt !i a_len)
    invariant exists* vi transcript_bytes.
      Ref.pts_to i vi **
      pts_to a 'a_bytes **
      pts_to b 'b_bytes **
      pts_to out 'old_out **
      pts_to transcript transcript_bytes **
      pure (B.length transcript_bytes == SZ.v total_len /\
            SZ.v total_len == B.length 'a_bytes + B.length 'b_bytes /\
            SZ.v vi <= SZ.v a_len /\
            (forall (idx:nat{idx < SZ.v vi}).
              Seq.index transcript_bytes idx == Seq.index (concat2 'a_bytes 'b_bytes) idx))
  {
    let vi = !i;
    let byte = a.(vi);
    transcript.(vi) <- byte;
    with transcript_after. assert (pts_to transcript transcript_after);
    lemma_concat2_index_a 'a_bytes 'b_bytes (SZ.v vi);
    assert (pure (Seq.index transcript_after (SZ.v vi) == Seq.index (concat2 'a_bytes 'b_bytes) (SZ.v vi)));
    assert (pure (forall (idx:nat{idx < SZ.v vi}).
      Seq.index transcript_after idx == Seq.index (concat2 'a_bytes 'b_bytes) idx));
    assert (pure (forall (idx:nat{idx < SZ.v vi + 1}).
      Seq.index transcript_after idx == Seq.index (concat2 'a_bytes 'b_bytes) idx));
    i := SZ.(vi +^ 1sz);
  };
  with i_after_a transcript_after_a. assert (Ref.pts_to i i_after_a ** pts_to transcript transcript_after_a);
  assert (pure (SZ.v i_after_a == SZ.v a_len));
  let mut j = 0sz;
  while (SZ.lt !j b_len)
    invariant exists* vj transcript_bytes.
      Ref.pts_to j vj **
      pts_to a 'a_bytes **
      pts_to b 'b_bytes **
      pts_to out 'old_out **
      pts_to transcript transcript_bytes **
      pure (B.length transcript_bytes == SZ.v total_len /\
            SZ.v total_len == B.length 'a_bytes + B.length 'b_bytes /\
            SZ.v vj <= SZ.v b_len /\
            (forall (idx:nat{idx < SZ.v a_len + SZ.v vj}).
              Seq.index transcript_bytes idx == Seq.index (concat2 'a_bytes 'b_bytes) idx))
  {
    let vj = !j;
    let dst = SZ.(a_len +^ vj);
    let byte = b.(vj);
    transcript.(dst) <- byte;
    with transcript_after. assert (pts_to transcript transcript_after);
    lemma_concat2_index_b 'a_bytes 'b_bytes (SZ.v a_len + SZ.v vj);
    assert (pure (Seq.index transcript_after (SZ.v a_len + SZ.v vj) == Seq.index (concat2 'a_bytes 'b_bytes) (SZ.v a_len + SZ.v vj)));
    assert (pure (forall (idx:nat{idx < SZ.v a_len + SZ.v vj}).
      Seq.index transcript_after idx == Seq.index (concat2 'a_bytes 'b_bytes) idx));
    assert (pure (forall (idx:nat{idx < SZ.v a_len + SZ.v vj + 1}).
      Seq.index transcript_after idx == Seq.index (concat2 'a_bytes 'b_bytes) idx));
    j := SZ.(vj +^ 1sz);
  };
  with j_after_b transcript_bytes. assert (Ref.pts_to j j_after_b ** pts_to transcript transcript_bytes);
  assert (pure (SZ.v j_after_b == SZ.v b_len));
  assert (pure (forall (idx:nat{idx < B.length transcript_bytes}).
    Seq.index transcript_bytes idx == Seq.index (concat2 'a_bytes 'b_bytes) idx));
  Seq.lemma_eq_intro transcript_bytes (concat2 'a_bytes 'b_bytes);
  Seq.lemma_eq_elim transcript_bytes (concat2 'a_bytes 'b_bytes);
  Crypto.sha256 transcript total_len out;
  with s. rewrite (pts_to transcript s) as (pts_to (V.vec_to_array transcript_vec) s);
  V.to_vec_pts_to transcript_vec;
  V.free transcript_vec;
  true
}

fn hash_client_server_handshake
  (client_hello: array U8.t)
  (client_hello_len: SZ.t)
  (server_hello: array U8.t)
  (server_hello_len: SZ.t)
  (server_handshake: array U8.t)
  (server_handshake_len: SZ.t)
  (out: array U8.t)
  requires pts_to client_hello 'client_hello_bytes **
           pts_to server_hello 'server_hello_bytes **
           pts_to server_handshake 'server_handshake_bytes **
           pts_to out 'old_out **
           pure (B.length 'client_hello_bytes == SZ.v client_hello_len /\
                 B.length 'server_hello_bytes == SZ.v server_hello_len /\
                 B.length 'server_handshake_bytes == SZ.v server_handshake_len /\
                 B.length 'old_out == 32 /\
                 SZ.v client_hello_len + SZ.v server_hello_len + SZ.v server_handshake_len <= 32768)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to client_hello 'client_hello_bytes **
          pts_to server_hello 'server_hello_bytes **
          pts_to server_handshake 'server_handshake_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> out_bytes == C.sha256 (B.append (B.append 'client_hello_bytes 'server_hello_bytes) 'server_handshake_bytes)))
{
  hash_concat3
    client_hello client_hello_len
    server_hello server_hello_len
    server_handshake server_handshake_len
    out
}

fn hash_client_server_hello
  (client_hello: array U8.t)
  (client_hello_len: SZ.t)
  (server_hello: array U8.t)
  (server_hello_len: SZ.t)
  (out: array U8.t)
  requires pts_to client_hello 'client_hello_bytes **
           pts_to server_hello 'server_hello_bytes **
           pts_to out 'old_out **
           pure (B.length 'client_hello_bytes == SZ.v client_hello_len /\
                 B.length 'server_hello_bytes == SZ.v server_hello_len /\
                 B.length 'old_out == 32 /\
                 SZ.v client_hello_len + SZ.v server_hello_len <= 32768)
  returns ok: bool
  ensures exists* out_bytes.
          pts_to client_hello 'client_hello_bytes **
          pts_to server_hello 'server_hello_bytes **
          pts_to out out_bytes **
          pure (B.length out_bytes == 32 /\
                (ok ==> out_bytes == C.sha256 (B.append (B.append 'client_hello_bytes 'server_hello_bytes) (Seq.create 0 0uy))))
{
  hash_concat2
    client_hello client_hello_len
    server_hello server_hello_len
    out;
}

fn equal32
  (a: array U8.t)
  (b: array U8.t)
  requires pts_to a 'a_bytes **
           pts_to b 'b_bytes **
           pure (B.length 'a_bytes == 32 /\ B.length 'b_bytes == 32)
  returns eq: bool
  ensures pts_to a 'a_bytes ** pts_to b 'b_bytes
{
  pts_to_len a;
  pts_to_len b;
  let a0 = a.(0sz); let b0 = b.(0sz);
  let a1 = a.(1sz); let b1 = b.(1sz);
  let a2 = a.(2sz); let b2 = b.(2sz);
  let a3 = a.(3sz); let b3 = b.(3sz);
  let a4 = a.(4sz); let b4 = b.(4sz);
  let a5 = a.(5sz); let b5 = b.(5sz);
  let a6 = a.(6sz); let b6 = b.(6sz);
  let a7 = a.(7sz); let b7 = b.(7sz);
  let a8 = a.(8sz); let b8 = b.(8sz);
  let a9 = a.(9sz); let b9 = b.(9sz);
  let a10 = a.(10sz); let b10 = b.(10sz);
  let a11 = a.(11sz); let b11 = b.(11sz);
  let a12 = a.(12sz); let b12 = b.(12sz);
  let a13 = a.(13sz); let b13 = b.(13sz);
  let a14 = a.(14sz); let b14 = b.(14sz);
  let a15 = a.(15sz); let b15 = b.(15sz);
  let a16 = a.(16sz); let b16 = b.(16sz);
  let a17 = a.(17sz); let b17 = b.(17sz);
  let a18 = a.(18sz); let b18 = b.(18sz);
  let a19 = a.(19sz); let b19 = b.(19sz);
  let a20 = a.(20sz); let b20 = b.(20sz);
  let a21 = a.(21sz); let b21 = b.(21sz);
  let a22 = a.(22sz); let b22 = b.(22sz);
  let a23 = a.(23sz); let b23 = b.(23sz);
  let a24 = a.(24sz); let b24 = b.(24sz);
  let a25 = a.(25sz); let b25 = b.(25sz);
  let a26 = a.(26sz); let b26 = b.(26sz);
  let a27 = a.(27sz); let b27 = b.(27sz);
  let a28 = a.(28sz); let b28 = b.(28sz);
  let a29 = a.(29sz); let b29 = b.(29sz);
  let a30 = a.(30sz); let b30 = b.(30sz);
  let a31 = a.(31sz); let b31 = b.(31sz);
  (a0 = b0) && (a1 = b1) && (a2 = b2) && (a3 = b3) &&
  (a4 = b4) && (a5 = b5) && (a6 = b6) && (a7 = b7) &&
  (a8 = b8) && (a9 = b9) && (a10 = b10) && (a11 = b11) &&
  (a12 = b12) && (a13 = b13) && (a14 = b14) && (a15 = b15) &&
  (a16 = b16) && (a17 = b17) && (a18 = b18) && (a19 = b19) &&
  (a20 = b20) && (a21 = b21) && (a22 = b22) && (a23 = b23) &&
  (a24 = b24) && (a25 = b25) && (a26 = b26) && (a27 = b27) &&
  (a28 = b28) && (a29 = b29) && (a30 = b30) && (a31 = b31)
}
