module TLS13.Wire.Spec.Reveal.ClientHello
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec
module RU = TLS13.Wire.Spec.Reveal.Util

#push-options "--z3rlimit 20"
let lemma_serialize_client_hello_reveal (hello:M.client_hello)
  : Lemma (Seq.equal
    (WS.serialize_handshake (M.ClientHello hello))
    (B.append
      (B.of_list [1uy])
      (B.append
        (WS.u24 (B.length (WS.serialize_client_hello hello)))
        (WS.serialize_client_hello hello))))
=
  let body = WS.serialize_client_hello hello in
  WS.lemma_byte_v 1;
  assert_norm (U8.v 1uy == 1);
  assert (U8.v (WS.byte 1) == U8.v 1uy);
  U8.v_inj (WS.byte 1) 1uy;
  RU.lemma_u8_reveal 1;
  assert (WS.byte 1 == 1uy);
  assert (B.singleton (WS.byte 1) == B.singleton 1uy);
  assert (Seq.equal (B.singleton (WS.byte 1)) (B.singleton 1uy));
  Seq.lemma_eq_elim (B.singleton (WS.byte 1)) (B.singleton 1uy);
  RU.lemma_singleton_of_list 1uy;
  assert (Seq.equal (B.singleton 1uy) (B.of_list [1uy]));
  Seq.lemma_eq_elim (B.singleton 1uy) (B.of_list [1uy])
#pop-options

let client_hello_byte (n:nat) : GTot B.byte =
  WS.byte n

let lemma_client_hello_byte_v n =
  WS.lemma_byte_v n

let client_hello_common_extensions_bytes (key_share:B.bytes) : GTot B.bytes =
  B.append
    (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])
    (B.append
      (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])
      (B.append
        (B.append
          (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
          key_share)
        (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy])))

let client_hello_server_name_extension_bytes (hostname:B.bytes) : GTot B.bytes =
  if B.length hostname = 0 then B.empty
  else
    B.append
      (B.of_list [
        0uy; 0uy;
        client_hello_byte ((5 + B.length hostname) / 256);
        client_hello_byte (5 + B.length hostname);
        client_hello_byte ((3 + B.length hostname) / 256);
        client_hello_byte (3 + B.length hostname);
        0uy;
        client_hello_byte (B.length hostname / 256);
        client_hello_byte (B.length hostname)])
      hostname

let client_hello_extensions_bytes (hostname:B.bytes) (key_share:B.bytes) : GTot B.bytes =
  B.append
    (client_hello_server_name_extension_bytes hostname)
    (client_hello_common_extensions_bytes key_share)

let client_hello_prefix_bytes (body_len:nat) (extensions_len:nat) (random:B.bytes) : GTot B.bytes =
  B.append
    (B.of_list [
      1uy;
      client_hello_byte (body_len / 65536);
      client_hello_byte (body_len / 256);
      client_hello_byte body_len;
      0x03uy; 0x03uy])
    (B.append
      random
      (B.of_list [
        0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
        client_hello_byte (extensions_len / 256);
        client_hello_byte extensions_len]))

let client_hello_body_bytes
  (random:B.bytes)
  (hostname:B.bytes)
  (key_share:B.bytes)
  : GTot B.bytes =
  let extensions = client_hello_extensions_bytes hostname key_share in
  B.append
    (B.of_list [0x03uy; 0x03uy])
    (B.append
      random
      (B.append
        (B.of_list [0uy])
        (B.append
          (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
          (B.append
            (B.of_list [0uy])
            (B.append
              (B.of_list [
                client_hello_byte (B.length extensions / 256);
                client_hello_byte (B.length extensions)])
              extensions)))))

let client_hello_handshake_bytes
  (random:B.bytes)
  (hostname:B.bytes)
  (key_share:B.bytes)
  : GTot B.bytes =
  let body = client_hello_body_bytes random hostname key_share in
  B.append
    (B.of_list [
      1uy;
      client_hello_byte (B.length body / 65536);
      client_hello_byte (B.length body / 256);
      client_hello_byte (B.length body)])
    body

let lemma_client_hello_common_extensions_bytes_reveal
  (key_share:B.bytes{B.length key_share == 32})
=
  assert_norm (client_hello_common_extensions_bytes key_share ==
    B.append
      (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])
      (B.append
        (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])
        (B.append
          (B.append
            (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
            key_share)
          (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))))

let lemma_client_hello_extensions_bytes_shape
  (hostname:B.bytes{B.length hostname <= 255})
  (key_share:B.bytes{B.length key_share == 32})
=
  assert_norm (client_hello_extensions_bytes hostname key_share ==
    B.append
      (client_hello_server_name_extension_bytes hostname)
      (client_hello_common_extensions_bytes key_share))

let lemma_client_hello_server_name_extension_bytes_reveal
  (hostname:B.bytes{0 < B.length hostname /\ B.length hostname <= 255})
=
  assert (not (B.length hostname = 0));
  assert_norm (client_hello_server_name_extension_bytes hostname ==
    B.append
      (B.of_list [
        0uy; 0uy;
        client_hello_byte ((5 + B.length hostname) / 256);
        client_hello_byte (5 + B.length hostname);
        client_hello_byte ((3 + B.length hostname) / 256);
        client_hello_byte (3 + B.length hostname);
        0uy;
        client_hello_byte (B.length hostname / 256);
        client_hello_byte (B.length hostname)])
      hostname)

let lemma_client_hello_server_name_extension_bytes_empty
  (hostname:B.bytes{B.length hostname == 0})
=
  assert_norm (client_hello_server_name_extension_bytes hostname == B.empty)

let lemma_client_hello_prefix_bytes_reveal
  (body_len:nat)
  (extensions_len:nat)
  (random:B.bytes{B.length random == 32})
=
  assert_norm (client_hello_prefix_bytes body_len extensions_len random ==
    B.append
      (B.of_list [
        1uy;
        client_hello_byte (body_len / 65536);
        client_hello_byte (body_len / 256);
        client_hello_byte body_len;
        0x03uy; 0x03uy])
      (B.append
        random
        (B.of_list [
          0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
          client_hello_byte (extensions_len / 256);
          client_hello_byte extensions_len])))

let lemma_add_65_comm (n:nat)
  : Lemma (ensures n + 65 == 65 + n)
=
  ()

#push-options "--initial_fuel 50 --max_fuel 50 --split_queries always --z3rlimit 80"
let lemma_client_hello_common_extensions_len
  (key_share:B.bytes{B.length key_share == 32})
=
  let supported_l : l:list B.byte{FStar.List.Tot.length l == 8} =
    [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy] in
  let supported = SeqP.createL supported_l in
  assert (supported == B.of_list supported_l);
  assert (B.length (B.of_list supported_l) == 8);
  let signature_l : l:list B.byte{FStar.List.Tot.length l == 8} =
    [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy] in
  let signature = SeqP.createL signature_l in
  assert (signature == B.of_list signature_l);
  assert (B.length (B.of_list signature_l) == 8);
  let key_header_l : l:list B.byte{FStar.List.Tot.length l == 10} =
    [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy] in
  let key_header = SeqP.createL key_header_l in
  assert (key_header == B.of_list key_header_l);
  assert (B.length (B.of_list key_header_l) == 10);
  let common_suffix_l : l:list B.byte{FStar.List.Tot.length l == 7} =
    [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy] in
  let common_suffix = SeqP.createL common_suffix_l in
  assert (common_suffix == B.of_list common_suffix_l);
  assert (B.length (B.of_list common_suffix_l) == 7);
  Seq.lemma_len_append (B.of_list key_header_l) key_share;
  Seq.lemma_len_append
    (B.append (B.of_list key_header_l) key_share)
    (B.of_list common_suffix_l);
  Seq.lemma_len_append
    (B.of_list signature_l)
    (B.append
      (B.append (B.of_list key_header_l) key_share)
      (B.of_list common_suffix_l));
  Seq.lemma_len_append
    (B.of_list supported_l)
    (B.append
      (B.of_list signature_l)
      (B.append
        (B.append (B.of_list key_header_l) key_share)
        (B.of_list common_suffix_l)))

let lemma_client_hello_server_name_extension_len
  (hostname:B.bytes{B.length hostname <= 255})
=
  if B.length hostname = 0 then
    assert_norm (B.length B.empty == 0)
  else
    let sni_prefix_l : l:list B.byte{FStar.List.Tot.length l == 9} = [
        0uy; 0uy;
        client_hello_byte ((5 + B.length hostname) / 256);
        client_hello_byte (5 + B.length hostname);
        client_hello_byte ((3 + B.length hostname) / 256);
        client_hello_byte (3 + B.length hostname);
        0uy;
        client_hello_byte (B.length hostname / 256);
        client_hello_byte (B.length hostname)] in
    let sni_prefix = SeqP.createL sni_prefix_l in
    assert (sni_prefix == B.of_list sni_prefix_l);
    assert (B.length (B.of_list sni_prefix_l) == 9);
    Seq.lemma_len_append
      (B.of_list sni_prefix_l)
      hostname

let lemma_client_hello_extensions_len
  (hostname:B.bytes{B.length hostname <= 255})
  (key_share:B.bytes{B.length key_share == 32})
=
  lemma_client_hello_common_extensions_len key_share;
  lemma_client_hello_server_name_extension_len hostname;
  assert_norm (client_hello_extensions_bytes hostname key_share ==
    B.append
      (client_hello_server_name_extension_bytes hostname)
      (client_hello_common_extensions_bytes key_share));
  Seq.lemma_len_append
    (client_hello_server_name_extension_bytes hostname)
    (client_hello_common_extensions_bytes key_share);
  assert (B.length (client_hello_common_extensions_bytes key_share) == 65);
  assert (B.length (client_hello_server_name_extension_bytes hostname) ==
    (if B.length hostname == 0 then 0 else 9 + B.length hostname));
  assert (B.length (client_hello_extensions_bytes hostname key_share) ==
    B.length (client_hello_server_name_extension_bytes hostname) +
    B.length (client_hello_common_extensions_bytes key_share));
  if B.length hostname == 0 then (
    assert (B.length (client_hello_server_name_extension_bytes hostname) == 0);
    assert (B.length (client_hello_extensions_bytes hostname key_share) == 65);
    assert ((if B.length hostname == 0 then 0 else 9 + B.length hostname) == 0);
    assert (B.length (client_hello_extensions_bytes hostname key_share) ==
      65 + (if B.length hostname == 0 then 0 else 9 + B.length hostname))
  ) else (
    assert (B.length (client_hello_server_name_extension_bytes hostname) ==
      9 + B.length hostname);
    assert (B.length (client_hello_extensions_bytes hostname key_share) ==
      (9 + B.length hostname) + 65);
    lemma_add_65_comm (9 + B.length hostname);
    assert ((if B.length hostname == 0 then 0 else 9 + B.length hostname) ==
      9 + B.length hostname);
    assert (B.length (client_hello_extensions_bytes hostname key_share) ==
      65 + (if B.length hostname == 0 then 0 else 9 + B.length hostname))
  )
#pop-options

private let client_hello_body_bytes_with_extensions
  (random:B.bytes)
  (extensions:B.bytes)
  : GTot B.bytes =
  B.append
    (B.of_list [0x03uy; 0x03uy])
    (B.append
      random
      (B.append
        (B.of_list [0uy])
        (B.append
          (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
          (B.append
            (B.of_list [0uy])
            (B.append
              (B.of_list [
                client_hello_byte (B.length extensions / 256);
                client_hello_byte (B.length extensions)])
              extensions)))))

private let client_hello_hostname (hello:M.client_hello) : GTot B.bytes =
  match hello.M.server_name with
  | Some h -> h
  | None -> B.empty

private let client_hello_expected_extensions (hello:M.client_hello) : GTot B.bytes =
  client_hello_extensions_bytes (client_hello_hostname hello) hello.M.key_share

private let client_hello_ws_body_bytes (hello:M.client_hello) : GTot B.bytes =
  let extensions = client_hello_expected_extensions hello in
  WS.append6
    (WS.u16 0x0303)
    hello.M.random
    (WS.u8 0)
    (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
    (WS.u8 0)
    (B.append (WS.u16 (B.length extensions)) extensions)

private let client_hello_impl_body_bytes (hello:M.client_hello) : GTot B.bytes =
  client_hello_body_bytes_with_extensions
    hello.M.random
    (client_hello_expected_extensions hello)

private let client_hello_public_body_bytes (hello:M.client_hello) : GTot B.bytes =
  client_hello_body_bytes
    hello.M.random
    (client_hello_hostname hello)
    hello.M.key_share

private let lemma_client_hello_byte_eq (n:nat) (b:U8.t{U8.v b == n % 256})
  : Lemma (client_hello_byte n == b) =
  WS.lemma_byte_v n;
  assert (U8.v (client_hello_byte n) == n % 256);
  assert (U8.v (client_hello_byte n) == U8.v b);
  U8.v_inj (client_hello_byte n) b

private let lemma_ws_u8_literal (n:nat) (b:U8.t{U8.v b == n % 256})
  : Lemma (Seq.equal (WS.u8 n) (B.of_list [b])) =
  lemma_client_hello_byte_eq n b;
  assert (WS.u8 n == B.singleton (client_hello_byte n));
  assert (B.singleton (client_hello_byte n) == B.singleton b);
  RU.lemma_singleton_of_list b;
  Seq.lemma_eq_elim (B.singleton b) (B.of_list [b])

private let lemma_ws_u16_literal
  (n:nat)
  (hi:U8.t{U8.v hi == (n / 256) % 256})
  (lo:U8.t{U8.v lo == n % 256})
  : Lemma (Seq.equal (WS.u16 n) (B.of_list [hi; lo])) =
  lemma_client_hello_byte_eq (n / 256) hi;
  lemma_client_hello_byte_eq n lo;
  assert (WS.u16 n == B.of_list [hi; lo]);
  assert (Seq.equal (WS.u16 n) (B.of_list [hi; lo]))

private let lemma_ws_u16_reveal (n:nat)
  : Lemma (Seq.equal
    (WS.u16 n)
    (B.of_list [client_hello_byte (n / 256); client_hello_byte n])) =
  ()

private let lemma_ws_u24_reveal (n:nat)
  : Lemma (Seq.equal
    (WS.u24 n)
    (B.of_list [
      client_hello_byte (n / 65536);
      client_hello_byte (n / 256);
      client_hello_byte n])) =
  ()

private let app_list (a b:list U8.t) : Tot (list U8.t) =
  FStar.List.Tot.append a b

private let lemma_of_list_append3 (a b c:list U8.t)
  : Lemma (Seq.equal
      (B.append (B.of_list a) (B.append (B.of_list b) (B.of_list c)))
      (B.of_list (app_list (app_list a b) c))) =
  RU.lemma_olcons a b (B.of_list c);
  RU.lemma_of_list_append (app_list a b) c

private let lemma_of_list_append4 (a b c d:list U8.t)
  : Lemma (Seq.equal
      (B.append (B.of_list a) (B.append (B.of_list b) (B.append (B.of_list c) (B.of_list d))))
      (B.of_list (app_list (app_list (app_list a b) c) d))) =
  RU.lemma_olcons a b (B.append (B.of_list c) (B.of_list d));
  lemma_of_list_append3 (app_list a b) c d

private let lemma_of_list_append5_seq (a b c d e:list U8.t) (s:B.bytes)
  : Lemma (Seq.equal
      (B.append (B.of_list a)
        (B.append (B.of_list b)
          (B.append (B.of_list c)
            (B.append (B.of_list d)
              (B.append (B.of_list e) s)))))
      (B.append (B.of_list (app_list (app_list (app_list (app_list a b) c) d) e)) s)) =
  RU.lemma_olcons a b
    (B.append (B.of_list c) (B.append (B.of_list d) (B.append (B.of_list e) s)));
  RU.lemma_olcons (app_list a b) c
    (B.append (B.of_list d) (B.append (B.of_list e) s));
  RU.lemma_olcons (app_list (app_list a b) c) d
    (B.append (B.of_list e) s);
  RU.lemma_olcons (app_list (app_list (app_list a b) c) d) e s

private let lemma_of_list_append4_seq (a b c d:list U8.t) (s:B.bytes)
  : Lemma (Seq.equal
      (B.append (B.of_list a)
        (B.append (B.of_list b)
          (B.append (B.of_list c)
            (B.append (B.of_list d) s))))
      (B.append (B.of_list (app_list (app_list (app_list a b) c) d)) s)) =
  RU.lemma_olcons a b
    (B.append (B.of_list c) (B.append (B.of_list d) s));
  RU.lemma_olcons (app_list a b) c
    (B.append (B.of_list d) s);
  RU.lemma_olcons (app_list (app_list a b) c) d s

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 20"
private let lemma_client_hello_body_bytes_with_extensions_reveal
  (random:B.bytes)
  (extensions:B.bytes)
  : Lemma (Seq.equal
    (WS.append6
      (WS.u16 0x0303)
      random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions))
    (client_hello_body_bytes_with_extensions random extensions))
=
  lemma_ws_u16_literal 0x0303 0x03uy 0x03uy;
  assert (Seq.equal (WS.u16 0x0303) (B.of_list [0x03uy; 0x03uy]));
  Seq.lemma_eq_elim (WS.u16 0x0303) (B.of_list [0x03uy; 0x03uy]);
  lemma_ws_u8_literal 0 0uy;
  assert (Seq.equal (WS.u8 0) (B.of_list [0uy]));
  Seq.lemma_eq_elim (WS.u8 0) (B.of_list [0uy]);
  lemma_ws_u16_literal 2 0uy 2uy;
  lemma_ws_u16_literal 0x1303 0x13uy 0x03uy;
  lemma_ws_u8_literal 1 1uy;
  RU.lemma_olcons [0uy; 2uy] [0x13uy; 0x03uy] (B.of_list [1uy]);
  RU.lemma_of_list_append [0uy; 2uy; 0x13uy; 0x03uy] [1uy];
  assert (Seq.equal
    (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
    (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]));
  Seq.lemma_eq_elim
    (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
    (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy]);
  lemma_ws_u16_reveal (B.length extensions);
  assert (Seq.equal
    (WS.u16 (B.length extensions))
    (B.of_list [
      client_hello_byte (B.length extensions / 256);
      client_hello_byte (B.length extensions)]));
  Seq.lemma_eq_elim
    (WS.u16 (B.length extensions))
    (B.of_list [
      client_hello_byte (B.length extensions / 256);
      client_hello_byte (B.length extensions)]);
  assert_norm (WS.append6
    (B.of_list [0x03uy; 0x03uy])
    random
    (B.of_list [0uy])
    (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
    (B.of_list [0uy])
    (B.append
      (B.of_list [
        client_hello_byte (B.length extensions / 256);
        client_hello_byte (B.length extensions)])
      extensions) ==
    client_hello_body_bytes_with_extensions random extensions);
  Seq.lemma_eq_elim
    (WS.append6
      (WS.u16 0x0303)
      random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions))
    (WS.append6
      (B.of_list [0x03uy; 0x03uy])
      random
      (B.of_list [0uy])
      (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
      (B.of_list [0uy])
      (B.append
        (B.of_list [
          client_hello_byte (B.length extensions / 256);
          client_hello_byte (B.length extensions)])
        extensions));
  Seq.lemma_eq_refl
    (WS.append6
      (WS.u16 0x0303)
      random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions))
    (client_hello_body_bytes_with_extensions random extensions)
#pop-options

private let lemma_seq_equal_trans (#a:Type) (x y z:Seq.seq a)
  : Lemma
      (requires Seq.equal x y /\ Seq.equal y z)
      (ensures Seq.equal x z)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_elim y z;
  Seq.lemma_eq_refl x z

private let lemma_seq_equal_sym (#a:Type) (x y:Seq.seq a)
  : Lemma
      (requires Seq.equal x y)
      (ensures Seq.equal y x)
=
  Seq.lemma_eq_elim x y;
  Seq.lemma_eq_refl y x

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 10"
private let lemma_client_hello_public_body_reveal
  (hello:M.client_hello)
  : Lemma (Seq.equal
      (client_hello_impl_body_bytes hello)
      (client_hello_public_body_bytes hello))
=
  assert_norm (client_hello_impl_body_bytes hello ==
    client_hello_public_body_bytes hello);
  Seq.lemma_eq_refl
    (client_hello_impl_body_bytes hello)
    (client_hello_public_body_bytes hello)
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --split_queries always --z3rlimit 50"
private let lemma_supported_groups_extension_bytes ()
  : Lemma (Seq.equal
      (WS.supported_groups_extension ())
      (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]))
=
  lemma_ws_u16_literal 0x000a 0uy 0x0auy;
  lemma_ws_u16_literal 4 0uy 4uy;
  lemma_ws_u16_literal 2 0uy 2uy;
  lemma_ws_u16_literal 0x001d 0uy 0x1duy;
  lemma_of_list_append4 [0uy; 0x0auy] [0uy; 4uy] [0uy; 2uy] [0uy; 0x1duy]

private let lemma_signature_algorithms_extension_bytes ()
  : Lemma (Seq.equal
      (WS.signature_algorithms_extension ())
      (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]))
=
  lemma_ws_u16_literal 0x000d 0uy 0x0duy;
  lemma_ws_u16_literal 4 0uy 4uy;
  lemma_ws_u16_literal 2 0uy 2uy;
  lemma_ws_u16_literal 0x0804 0x08uy 0x04uy;
  lemma_of_list_append4 [0uy; 0x0duy] [0uy; 4uy] [0uy; 2uy] [0x08uy; 0x04uy]

private let lemma_key_share_extension_bytes (key_share:B.bytes)
  : Lemma (Seq.equal
      (WS.key_share_extension key_share)
      (B.append
        (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
        key_share))
=
  lemma_ws_u16_literal 0x0033 0uy 0x33uy;
  lemma_ws_u16_literal 38 0uy 38uy;
  lemma_ws_u16_literal 36 0uy 36uy;
  lemma_ws_u16_literal 0x001d 0uy 0x1duy;
  lemma_ws_u16_literal 32 0uy 32uy;
  lemma_of_list_append5_seq
    [0uy; 0x33uy]
    [0uy; 38uy]
    [0uy; 36uy]
    [0uy; 0x1duy]
    [0uy; 32uy]
    key_share

private let lemma_supported_versions_extension_bytes ()
  : Lemma (Seq.equal
      (WS.supported_versions_extension ())
      (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))
=
  lemma_ws_u16_literal 0x002b 0uy 0x2buy;
  lemma_ws_u16_literal 3 0uy 3uy;
  lemma_ws_u8_literal 2 2uy;
  lemma_ws_u16_literal 0x0304 0x03uy 0x04uy;
  lemma_of_list_append4 [0uy; 0x2buy] [0uy; 3uy] [2uy] [0x03uy; 0x04uy]

private let lemma_server_name_extension_bytes (hostname:B.bytes{B.length hostname <= 255})
  : Lemma (Seq.equal
      (WS.server_name_extension hostname)
      (client_hello_server_name_extension_bytes hostname))
=
  if 0 < B.length hostname then (
    assert (0 < B.length hostname);
    assert (not (B.length hostname = 0));
    lemma_client_hello_server_name_extension_bytes_reveal hostname;
    lemma_ws_u16_literal 0 0uy 0uy;
    lemma_ws_u16_reveal (5 + B.length hostname);
    lemma_ws_u16_reveal (3 + B.length hostname);
    lemma_ws_u8_literal 0 0uy;
    lemma_ws_u16_reveal (B.length hostname);
    lemma_of_list_append5_seq
      [0uy; 0uy]
      [client_hello_byte ((5 + B.length hostname) / 256);
       client_hello_byte (5 + B.length hostname)]
      [client_hello_byte ((3 + B.length hostname) / 256);
       client_hello_byte (3 + B.length hostname)]
      [0uy]
      [client_hello_byte (B.length hostname / 256);
       client_hello_byte (B.length hostname)]
      hostname;
    Seq.lemma_eq_elim
      (client_hello_server_name_extension_bytes hostname)
      (B.append
        (B.of_list [
          0uy; 0uy;
          client_hello_byte ((5 + B.length hostname) / 256);
          client_hello_byte (5 + B.length hostname);
          client_hello_byte ((3 + B.length hostname) / 256);
          client_hello_byte (3 + B.length hostname);
          0uy;
          client_hello_byte (B.length hostname / 256);
          client_hello_byte (B.length hostname)])
        hostname)
  ) else (
    assert (B.length hostname = 0);
    assert_norm (client_hello_server_name_extension_bytes hostname == B.empty)
  )

private let lemma_client_hello_extensions_bytes_reveal
  (hello:M.client_hello{B.length hello.M.key_share == 32 /\
                        (match hello.M.server_name with
                         | Some h -> B.length h <= 255
                         | None -> True)})
  : Lemma (Seq.equal
    (WS.client_hello_extensions hello)
    (client_hello_extensions_bytes
      (match hello.M.server_name with
       | Some h -> h
       | None -> B.empty)
      hello.M.key_share))
=
  match hello.M.server_name with
  | Some h ->
    assert (B.length h <= 255);
    lemma_server_name_extension_bytes h;
    lemma_supported_groups_extension_bytes ();
    lemma_signature_algorithms_extension_bytes ();
    lemma_key_share_extension_bytes hello.M.key_share;
    lemma_supported_versions_extension_bytes ();
    lemma_client_hello_extensions_len h hello.M.key_share
  | None ->
    lemma_server_name_extension_bytes B.empty;
    lemma_supported_groups_extension_bytes ();
    lemma_signature_algorithms_extension_bytes ();
    lemma_key_share_extension_bytes hello.M.key_share;
    lemma_supported_versions_extension_bytes ();
    lemma_client_hello_extensions_len B.empty hello.M.key_share

#push-options "--initial_fuel 50 --max_fuel 50 --z3rlimit 20"
private let lemma_serialize_client_hello_ws_body_reveal
  (hello:M.client_hello{B.length hello.M.key_share == 32 /\
                        (match hello.M.server_name with
                         | Some h -> B.length h <= 255
                         | None -> True)})
  : Lemma (Seq.equal
      (WS.serialize_client_hello hello)
      (client_hello_ws_body_bytes hello))
=
  lemma_client_hello_extensions_bytes_reveal hello;
  let extensions = client_hello_expected_extensions hello in
  let ws_extensions = WS.client_hello_extensions hello in
  assert (Seq.equal
    ws_extensions
    extensions);
  Seq.lemma_eq_elim
    ws_extensions
    extensions;
  assert (ws_extensions == extensions);
  assert (B.length ws_extensions == B.length extensions);
  assert (B.append (WS.u16 (B.length ws_extensions)) ws_extensions ==
    B.append (WS.u16 (B.length extensions)) extensions);
  assert_norm (WS.serialize_client_hello hello ==
    WS.append6
      (WS.u16 0x0303)
      hello.M.random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append
        (WS.u16 (B.length (WS.client_hello_extensions hello)))
        (WS.client_hello_extensions hello)));
  assert (WS.serialize_client_hello hello ==
    WS.append6
      (WS.u16 0x0303)
      hello.M.random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions));
  assert_norm (client_hello_ws_body_bytes hello ==
    WS.append6
      (WS.u16 0x0303)
      hello.M.random
      (WS.u8 0)
      (WS.append3 (WS.u16 2) (WS.u16 0x1303) (WS.u8 1))
      (WS.u8 0)
      (B.append (WS.u16 (B.length extensions)) extensions));
  assert (WS.serialize_client_hello hello == client_hello_ws_body_bytes hello);
  Seq.lemma_eq_refl
    (WS.serialize_client_hello hello)
    (client_hello_ws_body_bytes hello)
#pop-options

let lemma_client_hello_body_bytes_reveal
  (hello:M.client_hello{B.length hello.M.random == 32 /\
                        B.length hello.M.key_share == 32 /\
                        (match hello.M.server_name with
                         | Some h -> B.length h <= 255
                         | None -> True)})
  : Lemma (Seq.equal
    (WS.serialize_client_hello hello)
    (client_hello_body_bytes
      hello.M.random
      (match hello.M.server_name with
       | Some h -> h
       | None -> B.empty)
      hello.M.key_share))
=
  let ws_body = client_hello_ws_body_bytes hello in
  let impl_body = client_hello_impl_body_bytes hello in
  let public_body = client_hello_public_body_bytes hello in
  lemma_serialize_client_hello_ws_body_reveal hello;
  lemma_client_hello_body_bytes_with_extensions_reveal
    hello.M.random
    (client_hello_expected_extensions hello);
  assert (Seq.equal ws_body impl_body);
  lemma_client_hello_public_body_reveal hello;
  assert (Seq.equal impl_body public_body);
  lemma_seq_equal_trans
    (WS.serialize_client_hello hello)
    ws_body
    impl_body;
  lemma_seq_equal_trans
    (WS.serialize_client_hello hello)
    impl_body
    public_body
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --split_queries always --z3rlimit 50"
let lemma_client_hello_handshake_bytes_prefix
  (random:B.bytes{B.length random == 32})
  (hostname:B.bytes{B.length hostname <= 255})
  (key_share:B.bytes{B.length key_share == 32})
=
  let extensions = client_hello_extensions_bytes hostname key_share in
  let body = client_hello_body_bytes random hostname key_share in
  lemma_client_hello_extensions_len hostname key_share;
  assert (body ==
    B.append
      (B.of_list [0x03uy; 0x03uy])
      (B.append
        random
        (B.append
          (B.of_list [0uy])
          (B.append
            (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
            (B.append
              (B.of_list [0uy])
              (B.append
                (B.of_list [
                  client_hello_byte (B.length extensions / 256);
                  client_hello_byte (B.length extensions)])
                extensions))))));
  assert (B.length body == 43 + B.length extensions);
  assert (client_hello_byte (B.length body / 65536) ==
    client_hello_byte ((43 + B.length extensions) / 65536));
  assert (client_hello_byte (B.length body / 256) ==
    client_hello_byte ((43 + B.length extensions) / 256));
  assert (client_hello_byte (B.length body) ==
    client_hello_byte (43 + B.length extensions));
  assert_norm (client_hello_handshake_bytes random hostname key_share ==
    B.append
      (B.of_list [
        1uy;
        client_hello_byte (B.length body / 65536);
        client_hello_byte (B.length body / 256);
        client_hello_byte (B.length body)])
      body);
  assert (B.of_list [
        1uy;
        client_hello_byte (B.length body / 65536);
        client_hello_byte (B.length body / 256);
        client_hello_byte (B.length body)] ==
      B.of_list [
        1uy;
        client_hello_byte ((43 + B.length extensions) / 65536);
        client_hello_byte ((43 + B.length extensions) / 256);
        client_hello_byte (43 + B.length extensions)]);
  assert (client_hello_handshake_bytes random hostname key_share ==
    B.append
      (B.of_list [
        1uy;
        client_hello_byte ((43 + B.length extensions) / 65536);
        client_hello_byte ((43 + B.length extensions) / 256);
        client_hello_byte (43 + B.length extensions)])
      body);
  assert (client_hello_prefix_bytes (43 + B.length extensions) (B.length extensions) random ==
    B.append
      (B.of_list [
        1uy;
        client_hello_byte ((43 + B.length extensions) / 65536);
        client_hello_byte ((43 + B.length extensions) / 256);
        client_hello_byte (43 + B.length extensions);
        0x03uy; 0x03uy])
      (B.append
        random
        (B.of_list [
          0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
          client_hello_byte (B.length extensions / 256);
          client_hello_byte (B.length extensions)])));
  Seq.append_assoc
    (B.of_list [
      1uy;
      client_hello_byte ((43 + B.length extensions) / 65536);
      client_hello_byte ((43 + B.length extensions) / 256);
      client_hello_byte (43 + B.length extensions)])
    (B.of_list [0x03uy; 0x03uy])
    (B.append
      random
      (B.append
        (B.of_list [0uy])
        (B.append
          (B.of_list [0uy; 2uy; 0x13uy; 0x03uy; 1uy])
          (B.append
            (B.of_list [0uy])
            (B.append
              (B.of_list [
                client_hello_byte (B.length extensions / 256);
                client_hello_byte (B.length extensions)])
              extensions)))));
  Seq.append_assoc
    (B.of_list [
      1uy;
      client_hello_byte ((43 + B.length extensions) / 65536);
      client_hello_byte ((43 + B.length extensions) / 256);
      client_hello_byte (43 + B.length extensions);
      0x03uy; 0x03uy])
    random
    (B.append
      (B.of_list [
        0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
        client_hello_byte (B.length extensions / 256);
        client_hello_byte (B.length extensions)])
      extensions);
  RU.lemma_of_list_append
    [
      1uy;
      client_hello_byte ((43 + B.length extensions) / 65536);
      client_hello_byte ((43 + B.length extensions) / 256);
      client_hello_byte (43 + B.length extensions)
    ]
    [0x03uy; 0x03uy];
  Seq.lemma_eq_elim
    (B.append
      (B.of_list [
      1uy;
      client_hello_byte ((43 + B.length extensions) / 65536);
      client_hello_byte ((43 + B.length extensions) / 256);
      client_hello_byte (43 + B.length extensions)
      ])
      (B.of_list [0x03uy; 0x03uy]))
    (B.of_list [
      1uy;
      client_hello_byte ((43 + B.length extensions) / 65536);
      client_hello_byte ((43 + B.length extensions) / 256);
      client_hello_byte (43 + B.length extensions);
      0x03uy; 0x03uy]);
  Seq.append_assoc
    random
    (B.of_list [
      0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
      client_hello_byte (B.length extensions / 256);
      client_hello_byte (B.length extensions)])
    extensions;
  Seq.append_assoc
    (B.of_list [
      1uy;
      client_hello_byte ((43 + B.length extensions) / 65536);
      client_hello_byte ((43 + B.length extensions) / 256);
      client_hello_byte (43 + B.length extensions);
      0x03uy; 0x03uy])
    (B.append
      random
      (B.of_list [
        0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
        client_hello_byte (B.length extensions / 256);
        client_hello_byte (B.length extensions)]))
    extensions;
  let normal =
    B.append
      (B.of_list [
        1uy;
        client_hello_byte ((43 + B.length extensions) / 65536);
        client_hello_byte ((43 + B.length extensions) / 256);
        client_hello_byte (43 + B.length extensions);
        0x03uy; 0x03uy])
      (B.append
        random
        (B.append
          (B.of_list [
            0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
            client_hello_byte (B.length extensions / 256);
            client_hello_byte (B.length extensions)])
          extensions)) in
  let rhs =
    B.append
      (client_hello_prefix_bytes
        (43 + B.length extensions)
        (B.length extensions)
        random)
      extensions in
  let header4 =
    B.of_list [
      1uy;
      client_hello_byte ((43 + B.length extensions) / 65536);
      client_hello_byte ((43 + B.length extensions) / 256);
      client_hello_byte (43 + B.length extensions)] in
  let body_norm =
    B.append
      (B.of_list [0x03uy; 0x03uy])
      (B.append
        random
        (B.append
          (B.of_list [
            0uy; 0uy; 2uy; 0x13uy; 0x03uy; 1uy; 0uy;
            client_hello_byte (B.length extensions / 256);
            client_hello_byte (B.length extensions)])
          extensions)) in
  lemma_of_list_append4_seq
    [0uy]
    [0uy; 2uy; 0x13uy; 0x03uy; 1uy]
    [0uy]
    [
      client_hello_byte (B.length extensions / 256);
      client_hello_byte (B.length extensions)
    ]
    extensions;
  assert (Seq.equal body body_norm);
  Seq.lemma_eq_elim body body_norm;
  assert (Seq.equal
    (client_hello_handshake_bytes random hostname key_share)
    (B.append header4 body_norm));
  assert (Seq.equal (client_hello_handshake_bytes random hostname key_share) normal);
  assert (Seq.equal rhs normal);
  lemma_seq_equal_sym rhs normal;
  lemma_seq_equal_trans
    (client_hello_handshake_bytes random hostname key_share)
    normal
    rhs;
  assert (Seq.equal
    (client_hello_handshake_bytes random hostname key_share)
    (B.append
      (client_hello_prefix_bytes
        (43 + B.length extensions)
        (B.length extensions)
        random)
      extensions))
#pop-options

#push-options "--initial_fuel 50 --max_fuel 50 --split_queries always --z3rlimit 50"
let lemma_client_hello_handshake_bytes_reveal
  (hello:M.client_hello{B.length hello.M.random == 32 /\
                       B.length hello.M.key_share == 32 /\
                       (match hello.M.server_name with
                        | Some h -> B.length h <= 255
                        | None -> True)})
=
  let key_share : (b:B.bytes{B.length b == 32}) = hello.M.key_share in
  let hostname : (b:B.bytes{B.length b <= 255}) =
    match hello.M.server_name with
    | Some h -> h
    | None -> B.empty in
  let body = client_hello_body_bytes hello.M.random hostname key_share in
  lemma_client_hello_body_bytes_reveal hello;
  Seq.lemma_eq_elim (WS.serialize_client_hello hello) body;
  lemma_serialize_client_hello_reveal hello;
  lemma_ws_u24_reveal (B.length body);
  Seq.lemma_eq_elim
    (WS.u24 (B.length body))
    (B.of_list [
      client_hello_byte (B.length body / 65536);
      client_hello_byte (B.length body / 256);
      client_hello_byte (B.length body)]);
  Seq.append_assoc
    (B.of_list [1uy])
    (B.of_list [
      client_hello_byte (B.length body / 65536);
      client_hello_byte (B.length body / 256);
      client_hello_byte (B.length body)])
    body;
  RU.lemma_of_list_append
    [1uy]
    [
      client_hello_byte (B.length body / 65536);
      client_hello_byte (B.length body / 256);
      client_hello_byte (B.length body)
    ];
  Seq.lemma_eq_elim
    (B.append
      (B.of_list [1uy])
      (B.of_list [
        client_hello_byte (B.length body / 65536);
        client_hello_byte (B.length body / 256);
        client_hello_byte (B.length body)]))
    (B.of_list [
      1uy;
      client_hello_byte (B.length body / 65536);
      client_hello_byte (B.length body / 256);
      client_hello_byte (B.length body)]);
  assert_norm (client_hello_handshake_bytes hello.M.random hostname key_share ==
    B.append
      (B.of_list [
        1uy;
        client_hello_byte (B.length body / 65536);
        client_hello_byte (B.length body / 256);
        client_hello_byte (B.length body)])
      body);
  assert (Seq.equal
    (WS.serialize_handshake (M.ClientHello hello))
    (client_hello_handshake_bytes hello.M.random hostname key_share))
#pop-options
