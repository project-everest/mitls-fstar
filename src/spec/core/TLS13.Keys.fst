module TLS13.Keys

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec

type traffic_secret = C.secret

let label_derived : B.bytes =
  Seq.upd
    (Seq.upd
      (Seq.upd
        (Seq.upd
          (Seq.upd
            (Seq.upd
              (Seq.upd (B.zeros 7) 0 0x64uy)
              1 0x65uy)
            2 0x72uy)
          3 0x69uy)
        4 0x76uy)
      5 0x65uy)
    6 0x64uy

let label_c_hs_traffic : B.bytes =
  Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd
  (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (B.zeros 12)
    0 0x63uy) 1 0x20uy) 2 0x68uy) 3 0x73uy) 4 0x20uy) 5 0x74uy)
    6 0x72uy) 7 0x61uy) 8 0x66uy) 9 0x66uy) 10 0x69uy) 11 0x63uy

let label_s_hs_traffic : B.bytes =
  Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd
  (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (B.zeros 12)
    0 0x73uy) 1 0x20uy) 2 0x68uy) 3 0x73uy) 4 0x20uy) 5 0x74uy)
    6 0x72uy) 7 0x61uy) 8 0x66uy) 9 0x66uy) 10 0x69uy) 11 0x63uy

let label_c_ap_traffic : B.bytes =
  Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd
  (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (B.zeros 12)
    0 0x63uy) 1 0x20uy) 2 0x61uy) 3 0x70uy) 4 0x20uy) 5 0x74uy)
    6 0x72uy) 7 0x61uy) 8 0x66uy) 9 0x66uy) 10 0x69uy) 11 0x63uy

let label_s_ap_traffic : B.bytes =
  Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd
  (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (B.zeros 12)
    0 0x73uy) 1 0x20uy) 2 0x61uy) 3 0x70uy) 4 0x20uy) 5 0x74uy)
    6 0x72uy) 7 0x61uy) 8 0x66uy) 9 0x66uy) 10 0x69uy) 11 0x63uy

let label_exp_master : B.bytes =
  B.of_list [0x65uy; 0x78uy; 0x70uy; 0x20uy; 0x6duy; 0x61uy;
             0x73uy; 0x74uy; 0x65uy; 0x72uy]

let label_res_master : B.bytes =
  B.of_list [0x72uy; 0x65uy; 0x73uy; 0x20uy; 0x6duy; 0x61uy;
             0x73uy; 0x74uy; 0x65uy; 0x72uy]

let label_finished : B.bytes =
  Seq.upd (Seq.upd (Seq.upd (Seq.upd
  (Seq.upd (Seq.upd (Seq.upd (Seq.upd (B.zeros 8)
    0 0x66uy) 1 0x69uy) 2 0x6euy) 3 0x69uy)
    4 0x73uy) 5 0x68uy) 6 0x65uy) 7 0x64uy

let label_key : B.bytes =
  Seq.upd (Seq.upd (Seq.upd (B.zeros 3) 0 0x6buy) 1 0x65uy) 2 0x79uy

let label_iv : B.bytes =
  Seq.upd (Seq.upd (B.zeros 2) 0 0x69uy) 1 0x76uy

let label_traffic_update : B.bytes =
  Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd
  (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (B.zeros 11)
    0 0x74uy) 1 0x72uy) 2 0x61uy) 3 0x66uy) 4 0x66uy) 5 0x69uy)
    6 0x63uy) 7 0x20uy) 8 0x75uy) 9 0x70uy) 10 0x64uy

let zero_secret : C.secret = B.zeros 32

let empty_hash : C.digest32 = C.sha256 B.empty

let derive_secret
  (secret:B.bytes)
  (label:B.bytes)
  (context:B.bytes)
  : traffic_secret =
  C.hkdf_expand_label secret label context 32

let early_secret (psk:B.bytes) : C.secret =
  C.hkdf_extract B.empty (if B.length psk = 0 then zero_secret else psk)

let derived_secret (secret:B.bytes) : C.secret =
  derive_secret secret label_derived empty_hash

let handshake_secret (early:B.bytes) (shared_secret:B.bytes) : C.secret =
  C.hkdf_extract (derived_secret early) shared_secret

let master_secret (handshake:B.bytes) : C.secret =
  C.hkdf_extract (derived_secret handshake) zero_secret

let client_handshake_traffic_secret
  (handshake:B.bytes)
  (transcript_hash:B.bytes)
  : traffic_secret =
  derive_secret handshake label_c_hs_traffic transcript_hash

let server_handshake_traffic_secret
  (handshake:B.bytes)
  (transcript_hash:B.bytes)
  : traffic_secret =
  derive_secret handshake label_s_hs_traffic transcript_hash

let client_application_traffic_secret
  (master:B.bytes)
  (transcript_hash:B.bytes)
  : traffic_secret =
  derive_secret master label_c_ap_traffic transcript_hash

let server_application_traffic_secret
  (master:B.bytes)
  (transcript_hash:B.bytes)
  : traffic_secret =
  derive_secret master label_s_ap_traffic transcript_hash

let application_traffic_secret_update
  (old_secret:B.bytes)
  : traffic_secret =
  C.hkdf_expand_label old_secret label_traffic_update B.empty 32

let exporter_master_secret
  (master:B.bytes)
  (transcript_hash:B.bytes)
  : C.secret =
  derive_secret master label_exp_master transcript_hash

let resumption_master_secret
  (master:B.bytes)
  (transcript_hash:B.bytes)
  : C.secret =
  derive_secret master label_res_master transcript_hash

let finished_key (base_key:B.bytes) : C.secret =
  derive_secret base_key label_finished B.empty

let finished_verify_data (base_key:B.bytes) (transcript_hash:B.bytes) : C.digest32 =
  C.hmac_sha256 (finished_key base_key) transcript_hash

(**
  The AEAD traffic key.  The expansion length is part of the HKDF-Expand-Label
  `info` string, so a 16-byte AES-128-GCM key is *not* a prefix of the 32-byte
  ChaCha20-Poly1305 key: the algorithm must be threaded here rather than
  recovered by truncation.
**)
let derive_aead_key (a:C.aead_alg) (secret:B.bytes) : C.aead_key a =
  C.hkdf_expand_label secret label_key B.empty (C.aead_key_len a)

let derive_aead_iv (secret:B.bytes) : C.aead_nonce =
  C.hkdf_expand_label secret label_iv B.empty 12

(**
  The derived traffic key recovers its own algorithm, because the two supported
  algorithms have distinct key lengths.  This is what lets the record layer
  dispatch on the key alone (see `TLS13.Crypto.Spec.aead_alg_of_key`), so that
  "the peer installed the same key" already implies "the peer uses the same
  algorithm".
**)
let lemma_aead_alg_of_derived_key (a:C.aead_alg) (secret:B.bytes)
  : Lemma (C.aead_alg_of_key (derive_aead_key a secret) == a)
          [SMTPat (C.aead_alg_of_key (derive_aead_key a secret))]
= ()
