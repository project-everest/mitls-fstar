module TLS13.Symbolic.Terms

module B = TLS13.Bytes
module DY = DY.Core
module H = TLS13.Handshake.Spec
module K = TLS13.Keys
module Profile = TLS13.Symbolic.Profile
module Seq = FStar.Seq
module T = TLS13.Types

type symbolic_role =
  | SymbolicClient
  | SymbolicServer

type endpoint_session = {
  session_principal: DY.principal;
  session_principal_term: DY.bytes;
  session_state_id: DY.state_id;
  session_id_term: DY.bytes;
  session_role: symbolic_role;
}

noeq
type session_context = {
  context_client: endpoint_session;
  context_server: endpoint_session;
  context_server_name: DY.bytes;
  context_cipher_suite:
    suite:T.cipher_suite{suite == Profile.profile_cipher_suite};
  context_named_group:
    group:T.named_group{group == Profile.profile_named_group};
  context_signature_scheme:
    scheme:T.signature_scheme{
      scheme == Profile.profile_signature_scheme
    };
  context_client_random: DY.bytes;
  context_server_random: DY.bytes;
  context_client_key_share: DY.bytes;
  context_server_key_share: DY.bytes;
  context_transcript: DY.bytes;
}

let public_bytes (value:B.bytes) : DY.bytes =
  DY.Literal value

let fresh_32 (time:DY.timestamp) : DY.bytes =
  DY.Rand 32 time

let fresh_signature_nonce (time:DY.timestamp) : DY.bytes =
  fresh_32 time

let x25519_public (secret:DY.bytes) : DY.bytes =
  DY.dh_pk secret

let x25519_shared (secret peer_public:DY.bytes) : DY.bytes =
  DY.dh secret peer_public

let empty_transcript : DY.bytes =
  public_bytes B.empty

let extend_transcript (transcript message:DY.bytes) : DY.bytes =
  DY.Concat transcript message

let transcript_hash (transcript:DY.bytes) : DY.bytes =
  DY.Hash transcript

let certificate_verify_prefix : B.bytes =
  B.append
    (B.append
      (Seq.create 64 0x20uy)
      H.certificate_verify_server_context)
    (B.singleton B.zero)

let certificate_verify_input (transcript:DY.bytes) : DY.bytes =
  DY.Concat
    (public_bytes certificate_verify_prefix)
    (transcript_hash transcript)

let certificate_verify
  (signing_key nonce transcript:DY.bytes)
  : DY.bytes =
  DY.Sign signing_key nonce (certificate_verify_input transcript)

let tls13_label (label:B.bytes) : B.bytes =
  B.append
    (B.of_list [0x74uy; 0x6cuy; 0x73uy; 0x31uy; 0x33uy; 0x20uy])
    label

let hkdf_info
  (output_length_high output_length_low label_length:B.byte)
  (label:B.bytes)
  (context_length:B.byte)
  (context:DY.bytes)
  : DY.bytes =
  DY.Concat
    (public_bytes
      (B.of_list
        [output_length_high; output_length_low; label_length]))
    (DY.Concat
      (public_bytes (tls13_label label))
      (DY.Concat
        (public_bytes (B.singleton context_length))
        context))

let derive_secret
  (secret:DY.bytes)
  (label:B.bytes)
  (label_length:B.byte)
  (context:DY.bytes)
  : DY.bytes =
  DY.KdfExpand
    secret
    (hkdf_info 0uy 32uy label_length label 32uy context)
    32

let public_zero_secret : DY.bytes =
  public_bytes K.zero_secret

let early_secret : DY.bytes =
  DY.KdfExtract (public_bytes B.empty) public_zero_secret

let derived_secret (secret:DY.bytes) : DY.bytes =
  derive_secret secret K.label_derived 13uy (transcript_hash empty_transcript)

let handshake_secret (shared_secret:DY.bytes) : DY.bytes =
  DY.KdfExtract (derived_secret early_secret) shared_secret

let master_secret (handshake:DY.bytes) : DY.bytes =
  DY.KdfExtract (derived_secret handshake) public_zero_secret

let client_handshake_traffic_secret
  (handshake transcript:DY.bytes)
  : DY.bytes =
  derive_secret
    handshake K.label_c_hs_traffic 18uy (transcript_hash transcript)

let server_handshake_traffic_secret
  (handshake transcript:DY.bytes)
  : DY.bytes =
  derive_secret
    handshake K.label_s_hs_traffic 18uy (transcript_hash transcript)

let client_application_traffic_secret
  (master transcript:DY.bytes)
  : DY.bytes =
  derive_secret
    master K.label_c_ap_traffic 18uy (transcript_hash transcript)

let server_application_traffic_secret
  (master transcript:DY.bytes)
  : DY.bytes =
  derive_secret
    master K.label_s_ap_traffic 18uy (transcript_hash transcript)

let finished_key (traffic_secret:DY.bytes) : DY.bytes =
  DY.KdfExpand
    traffic_secret
    (hkdf_info
      0uy 32uy 14uy K.label_finished 0uy (public_bytes B.empty))
    32

let finished_verify_data
  (traffic_secret transcript:DY.bytes)
  : DY.bytes =
  DY.Mac (finished_key traffic_secret) (transcript_hash transcript)

let record_key (traffic_secret:DY.bytes) : DY.bytes =
  DY.KdfExpand
    traffic_secret
    (hkdf_info 0uy 32uy 9uy K.label_key 0uy (public_bytes B.empty))
    32

let record_iv (traffic_secret:DY.bytes) : DY.bytes =
  DY.KdfExpand
    traffic_secret
    (hkdf_info 0uy 12uy 8uy K.label_iv 0uy (public_bytes B.empty))
    12

let public_record_nonce (nonce:B.bytes) : DY.bytes =
  public_bytes nonce

let protected_record
  (key nonce plaintext additional_data:DY.bytes)
  : DY.bytes =
  DY.AeadEnc key nonce plaintext additional_data

let protected_record_additional_data (header:B.bytes) : DY.bytes =
  public_bytes header

let application_plaintext
  (content:DY.bytes)
  (content_type_and_padding:B.bytes)
  : DY.bytes =
  DY.Concat content (public_bytes content_type_and_padding)

let verification_key (signing_key:DY.bytes) : DY.bytes =
  DY.Vk signing_key

let encode_symbolic_role (role:symbolic_role) : DY.bytes =
  match role with
  | SymbolicClient -> public_bytes (B.singleton 0uy)
  | SymbolicServer -> public_bytes (B.singleton 1uy)

let encode_endpoint_session (session:endpoint_session) : DY.bytes =
  DY.Concat
    session.session_principal_term
    (DY.Concat
      session.session_id_term
      (encode_symbolic_role session.session_role))

let profile_algorithms : DY.bytes =
  public_bytes
    (B.of_list [0x13uy; 0x03uy; 0x00uy; 0x1duy; 0x08uy; 0x04uy])

let encode_session_context (context:session_context) : DY.bytes =
  DY.Concat
    (encode_endpoint_session context.context_client)
    (DY.Concat
      (encode_endpoint_session context.context_server)
      (DY.Concat
        context.context_server_name
        (DY.Concat
          profile_algorithms
          (DY.Concat
            context.context_client_random
            (DY.Concat
              context.context_server_random
              (DY.Concat
                context.context_client_key_share
                (DY.Concat
                  context.context_server_key_share
                  context.context_transcript)))))))

let session_context_in_profile (context:session_context) : prop =
  context.context_client.session_role == SymbolicClient /\
  context.context_server.session_role == SymbolicServer /\
  context.context_cipher_suite == Profile.profile_cipher_suite /\
  context.context_named_group == Profile.profile_named_group /\
  context.context_signature_scheme == Profile.profile_signature_scheme

let profile_session_context
  (client server:endpoint_session)
  (server_name client_random server_random client_share server_share transcript:
    DY.bytes)
  : session_context = {
  context_client = client;
  context_server = server;
  context_server_name = server_name;
  context_cipher_suite = Profile.profile_cipher_suite;
  context_named_group = Profile.profile_named_group;
  context_signature_scheme = Profile.profile_signature_scheme;
  context_client_random = client_random;
  context_server_random = server_random;
  context_client_key_share = client_share;
  context_server_key_share = server_share;
  context_transcript = transcript;
}
