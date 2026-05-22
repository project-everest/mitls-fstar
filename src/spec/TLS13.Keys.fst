module TLS13.Keys

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module U8 = FStar.UInt8

type traffic_secret = C.secret

let b (n:nat{n < 256}) : B.byte = U8.uint_to_t n

let label_derived : B.bytes =
  B.of_list [b 0x64; b 0x65; b 0x72; b 0x69; b 0x76; b 0x65; b 0x64]

let label_c_hs_traffic : B.bytes =
  B.of_list [b 0x63; b 0x20; b 0x68; b 0x73; b 0x20; b 0x74;
             b 0x72; b 0x61; b 0x66; b 0x66; b 0x69; b 0x63]

let label_s_hs_traffic : B.bytes =
  B.of_list [b 0x73; b 0x20; b 0x68; b 0x73; b 0x20; b 0x74;
             b 0x72; b 0x61; b 0x66; b 0x66; b 0x69; b 0x63]

let label_c_ap_traffic : B.bytes =
  B.of_list [b 0x63; b 0x20; b 0x61; b 0x70; b 0x20; b 0x74;
             b 0x72; b 0x61; b 0x66; b 0x66; b 0x69; b 0x63]

let label_s_ap_traffic : B.bytes =
  B.of_list [b 0x73; b 0x20; b 0x61; b 0x70; b 0x20; b 0x74;
             b 0x72; b 0x61; b 0x66; b 0x66; b 0x69; b 0x63]

let label_exp_master : B.bytes =
  B.of_list [b 0x65; b 0x78; b 0x70; b 0x20; b 0x6d; b 0x61;
             b 0x73; b 0x74; b 0x65; b 0x72]

let label_res_master : B.bytes =
  B.of_list [b 0x72; b 0x65; b 0x73; b 0x20; b 0x6d; b 0x61;
             b 0x73; b 0x74; b 0x65; b 0x72]

let label_finished : B.bytes =
  B.of_list [b 0x66; b 0x69; b 0x6e; b 0x69; b 0x73; b 0x68;
             b 0x65; b 0x64]

let label_key : B.bytes = B.of_list [b 0x6b; b 0x65; b 0x79]

let label_iv : B.bytes = B.of_list [b 0x69; b 0x76]

let zero_secret : C.secret = B.zeros 32

let empty_hash : C.digest32 = C.sha256 B.empty

let derive_secret
  (secret:B.bytes)
  (label:B.bytes)
  (context:B.bytes)
  : traffic_secret =
  C.hkdf_expand_label secret label context 32

let early_secret (psk:B.bytes) : C.secret =
  C.hkdf_extract B.empty psk

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

let derive_aead_key (secret:B.bytes) : C.aead_key =
  C.hkdf_expand_label secret label_key B.empty 32

let derive_aead_iv (secret:B.bytes) : C.aead_nonce =
  C.hkdf_expand_label secret label_iv B.empty 12
