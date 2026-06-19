module TLS13.Wire.Spec.Reveal.ClientHello

module B = TLS13.Bytes
module M = TLS13.Messages
module Seq = FStar.Seq
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

val client_hello_byte:
  n:nat ->
  GTot B.byte

val lemma_client_hello_byte_v:
  n:nat ->
  Lemma (U8.v (client_hello_byte n) == n % 256)

val client_hello_common_extensions_bytes:
  key_share:B.bytes ->
  GTot B.bytes

val client_hello_server_name_extension_bytes:
  hostname:B.bytes ->
  GTot B.bytes

val client_hello_extensions_bytes:
  hostname:B.bytes ->
  key_share:B.bytes ->
  GTot B.bytes

val client_hello_prefix_bytes:
  body_len:nat ->
  extensions_len:nat ->
  random:B.bytes ->
  GTot B.bytes

val client_hello_body_bytes:
  random:B.bytes ->
  hostname:B.bytes ->
  key_share:B.bytes ->
  GTot B.bytes

val client_hello_handshake_bytes:
  random:B.bytes ->
  hostname:B.bytes ->
  key_share:B.bytes ->
  GTot B.bytes

val lemma_client_hello_body_bytes_shape:
  random:B.bytes ->
  hostname:B.bytes ->
  key_share:B.bytes ->
  Lemma (Seq.equal
    (client_hello_body_bytes random hostname key_share)
    (let extensions = client_hello_extensions_bytes hostname key_share in
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
                 extensions)))))))

val lemma_client_hello_common_extensions_bytes_reveal:
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (Seq.equal
    (client_hello_common_extensions_bytes key_share)
    (B.append
      (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy])
      (B.append
        (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy])
        (B.append
          (B.append
            (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy])
            key_share)
          (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy])))))

val lemma_client_hello_extensions_bytes_shape:
  hostname:B.bytes{B.length hostname <= 255} ->
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (Seq.equal
    (client_hello_extensions_bytes hostname key_share)
    (B.append
      (client_hello_server_name_extension_bytes hostname)
      (client_hello_common_extensions_bytes key_share)))

val lemma_client_hello_server_name_extension_bytes_reveal:
  hostname:B.bytes{0 < B.length hostname /\ B.length hostname <= 255} ->
  Lemma (Seq.equal
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
      hostname))

val lemma_client_hello_server_name_extension_bytes_empty:
  hostname:B.bytes{B.length hostname == 0} ->
  Lemma (Seq.equal (client_hello_server_name_extension_bytes hostname) B.empty)

val lemma_client_hello_prefix_bytes_reveal:
  body_len:nat ->
  extensions_len:nat ->
  random:B.bytes{B.length random == 32} ->
  Lemma (Seq.equal
    (client_hello_prefix_bytes body_len extensions_len random)
    (B.append
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
          client_hello_byte extensions_len]))))

val lemma_client_hello_common_extensions_len:
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (B.length (client_hello_common_extensions_bytes key_share) == 65)

val lemma_client_hello_server_name_extension_len:
  hostname:B.bytes{B.length hostname <= 255} ->
  Lemma (B.length (client_hello_server_name_extension_bytes hostname) ==
    (if B.length hostname == 0 then 0 else 9 + B.length hostname))

val lemma_client_hello_extensions_len:
  hostname:B.bytes{B.length hostname <= 255} ->
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (B.length (client_hello_extensions_bytes hostname key_share) ==
    65 + (if B.length hostname == 0 then 0 else 9 + B.length hostname))

val lemma_client_hello_body_bytes_reveal:
  hello:M.client_hello{B.length hello.M.random == 32 /\
                       B.length hello.M.key_share == 32 /\
                       (match hello.M.server_name with
                        | Some h -> B.length h <= 255
                        | None -> True)} ->
  Lemma (Seq.equal
    (WS.serialize_client_hello hello)
    (client_hello_body_bytes
      hello.M.random
      (match hello.M.server_name with
       | Some h -> h
       | None -> B.empty)
      hello.M.key_share))

val lemma_client_hello_handshake_bytes_prefix:
  random:B.bytes{B.length random == 32} ->
  hostname:B.bytes{B.length hostname <= 255} ->
  key_share:B.bytes{B.length key_share == 32} ->
  Lemma (Seq.equal
    (client_hello_handshake_bytes random hostname key_share)
    (B.append
      (client_hello_prefix_bytes
        (43 + B.length (client_hello_extensions_bytes hostname key_share))
        (B.length (client_hello_extensions_bytes hostname key_share))
        random)
      (client_hello_extensions_bytes hostname key_share)))

val lemma_client_hello_handshake_bytes_reveal:
  hello:M.client_hello{B.length hello.M.random == 32 /\
                       B.length hello.M.key_share == 32 /\
                       (match hello.M.server_name with
                        | Some h -> B.length h <= 255
                        | None -> True)} ->
  Lemma (Seq.equal
    (WS.serialize_handshake (M.ClientHello hello))
    (client_hello_handshake_bytes
      hello.M.random
      (match hello.M.server_name with
       | Some h -> h
       | None -> B.empty)
      hello.M.key_share))
