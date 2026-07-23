module TLS13.Symbolic.Terms

(*
 * TLS-specific vocabulary over the DY* term algebra.
 *
 * These smart constructors preserve protocol structure: sessions, transcripts,
 * CertificateVerify inputs, the TLS 1.3 key schedule, Finished data, and
 * protected records remain distinct symbolic terms instead of opaque byte
 * strings.  Constructor equality is symbolic syntax, not a computational
 * collision-resistance result.  Concrete bytes are related to these terms only
 * through TLS13.Symbolic.Bridge.
 *)

module B = TLS13.Bytes
module DY = DY.Core
module H = TLS13.Handshake.Spec
module K = TLS13.Keys
module Profile = TLS13.Symbolic.Profile
module Seq = FStar.Seq
module T = TLS13.Types

(* Endpoint role as represented inside symbolic sessions and event payloads. *)
type symbolic_role =
  | SymbolicClient
  | SymbolicServer

(*
 * Identity and state coordinates for one symbolic endpoint session.
 *
 * principal/state fields feed DY labels; principal_term/session_id_term are
 * bytes embedded in usages and event contents.  Their correspondence is an
 * explicit modeling obligation rather than a consequence of this record.
 *)
type endpoint_session = {
  session_principal: DY.principal;
  session_principal_term: DY.bytes;
  session_state_id: DY.state_id;
  session_id_term: DY.bytes;
  session_role: symbolic_role;
}

(*
 * Complete symbolic context shared by authentication and record events.
 *
 * Refinement types fix the algorithm profile.  The randoms, key shares, name,
 * transcript, and peer session are symbolic fields; Product currently ties the
 * local session and transcript to an endpoint but does not derive every field
 * from concrete handshake state.
 *)
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

(* Embed an exact public byte string as a DY literal. *)
let public_bytes (value:B.bytes) : DY.bytes =
  DY.Literal value

(* Name a 32-byte honest random value by its trace timestamp. *)
let fresh_32 (time:DY.timestamp) : DY.bytes =
  DY.Rand 32 time

(* Specialize the generic 32-byte random constructor to signing randomness. *)
let fresh_signature_nonce (time:DY.timestamp) : DY.bytes =
  fresh_32 time

(* Construct the ideal X25519 public key corresponding to a private term. *)
let x25519_public (secret:DY.bytes) : DY.bytes =
  DY.dh_pk secret

(* Construct the ideal DH result for a private term and peer public term. *)
let x25519_shared (secret peer_public:DY.bytes) : DY.bytes =
  DY.dh secret peer_public

(* Represent the initial empty transcript as an exact public literal. *)
let empty_transcript : DY.bytes =
  public_bytes B.empty

(* Extend a transcript structurally by concatenating one serialized message. *)
let extend_transcript (transcript message:DY.bytes) : DY.bytes =
  DY.Concat transcript message

(* Apply the ideal hash constructor to a structured transcript. *)
let transcript_hash (transcript:DY.bytes) : DY.bytes =
  DY.Hash transcript

(*
 * Exact public TLS 1.3 server CertificateVerify prefix:
 * 64 spaces, the server context string, and one zero separator byte.
 *)
let certificate_verify_prefix : B.bytes =
  B.append
    (B.append
      (Seq.create 64 0x20uy)
      H.certificate_verify_server_context)
    (B.singleton B.zero)

(* Build the signed CertificateVerify input from the prefix and transcript hash. *)
let certificate_verify_input (transcript:DY.bytes) : DY.bytes =
  DY.Concat
    (public_bytes certificate_verify_prefix)
    (transcript_hash transcript)

(* Construct the ideal randomized signature over the CertificateVerify input. *)
let certificate_verify
  (signing_key nonce transcript:DY.bytes)
  : DY.bytes =
  DY.Sign signing_key nonce (certificate_verify_input transcript)

(* Prefix an RFC 8446 HKDF label with the public ASCII string "tls13 ". *)
let tls13_label (label:B.bytes) : B.bytes =
  B.append
    (B.of_list [0x74uy; 0x6cuy; 0x73uy; 0x31uy; 0x33uy; 0x20uy])
    label

(*
 * Encode the structured HkdfLabel info term.
 *
 * Public length and label bytes remain literals while the context remains a
 * symbolic subterm, allowing derivations to retain transcript structure.
 *)
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

(*
 * Model Derive-Secret as a 32-byte HKDF expansion.
 *
 * The caller supplies the exact TLS label bytes/length and symbolic context;
 * concrete serialization correspondence belongs to Bridge.
 *)
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

(* Public all-zero 32-byte secret used by the TLS 1.3 schedule. *)
let public_zero_secret : DY.bytes =
  public_bytes K.zero_secret

(* TLS early secret for the non-PSK profile. *)
let early_secret : DY.bytes =
  DY.KdfExtract (public_bytes B.empty) public_zero_secret

(* Apply the TLS "derived" label to advance between extract stages. *)
let derived_secret (secret:DY.bytes) : DY.bytes =
  derive_secret secret K.label_derived 13uy (transcript_hash empty_transcript)

(* Extract the handshake secret from the derived early secret and DH secret. *)
let handshake_secret (shared_secret:DY.bytes) : DY.bytes =
  DY.KdfExtract (derived_secret early_secret) shared_secret

(* Extract the master secret from the derived handshake secret and zero input. *)
let master_secret (handshake:DY.bytes) : DY.bytes =
  DY.KdfExtract (derived_secret handshake) public_zero_secret

(* Derive the client handshake traffic secret at the supplied transcript. *)
let client_handshake_traffic_secret
  (handshake transcript:DY.bytes)
  : DY.bytes =
  derive_secret
    handshake K.label_c_hs_traffic 18uy (transcript_hash transcript)

(* Derive the server handshake traffic secret at the supplied transcript. *)
let server_handshake_traffic_secret
  (handshake transcript:DY.bytes)
  : DY.bytes =
  derive_secret
    handshake K.label_s_hs_traffic 18uy (transcript_hash transcript)

(* Derive generation-zero client application traffic at its transcript. *)
let client_application_traffic_secret
  (master transcript:DY.bytes)
  : DY.bytes =
  derive_secret
    master K.label_c_ap_traffic 18uy (transcript_hash transcript)

(* Derive generation-zero server application traffic at its transcript. *)
let server_application_traffic_secret
  (master transcript:DY.bytes)
  : DY.bytes =
  derive_secret
    master K.label_s_ap_traffic 18uy (transcript_hash transcript)

(* Derive the role-specific Finished MAC key from a traffic secret. *)
let finished_key (traffic_secret:DY.bytes) : DY.bytes =
  DY.KdfExpand
    traffic_secret
    (hkdf_info
      0uy 32uy 14uy K.label_finished 0uy (public_bytes B.empty))
    32

(* Construct Finished verify_data as an ideal MAC of the transcript hash. *)
let finished_verify_data
  (traffic_secret transcript:DY.bytes)
  : DY.bytes =
  DY.Mac (finished_key traffic_secret) (transcript_hash transcript)

(* Derive the 32-byte ChaCha20-Poly1305 traffic key. *)
let record_key (traffic_secret:DY.bytes) : DY.bytes =
  DY.KdfExpand
    traffic_secret
    (hkdf_info 0uy 32uy 9uy K.label_key 0uy (public_bytes B.empty))
    32

(* Derive the 12-byte TLS static IV associated with a traffic secret. *)
let record_iv (traffic_secret:DY.bytes) : DY.bytes =
  DY.KdfExpand
    traffic_secret
    (hkdf_info 0uy 12uy 8uy K.label_iv 0uy (public_bytes B.empty))
    12

(*
 * Encode a natural sequence number as a public, length-injective token.
 *
 * This is not the RFC wire encoding.  Its sole symbolic purpose is to give
 * distinct naturals distinct public terms for nonce identity.
 *)
let encode_record_sequence_number (sequence_number:nat) : DY.bytes =
  public_bytes (Seq.create sequence_number 0uy)

(*
 * Place a sequence token in an opaque constructor used as the symbolic nonce.
 *
 * Hash here is a public injective namespace, not a claim that TLS hashes its
 * sequence number.  As a non-Literal term it requires an execution binding to
 * the concrete XOR-derived nonce.
 *)
let record_nonce_from_sequence_token
  (sequence_number:DY.bytes)
  : DY.bytes =
  DY.Hash sequence_number

(*
 * Nonce-token injectivity.
 *
 * Requirement: the two Hash-based nonce terms are equal.
 * Guarantee: their sequence-token arguments are equal.
 *)
val record_nonce_from_sequence_token_injective:
  left:DY.bytes ->
  right:DY.bytes ->
  Lemma
    (requires
      record_nonce_from_sequence_token left ==
      record_nonce_from_sequence_token right)
    (ensures left == right)
(* Proof: follows from injectivity of the DY Hash constructor. *)
let record_nonce_from_sequence_token_injective left right = ()

(*
 * Symbolic nonce for one record sequence number.
 *
 * The static IV is intentionally absent from the symbolic identity; Product's
 * AEAD bridge binds this term to the exact concrete IV/sequence computation.
 * Freshness is therefore stated for each key/nonce pair.
 *)
let record_nonce
  (_static_iv:DY.bytes)
  (sequence_number:nat)
  : DY.bytes =
  record_nonce_from_sequence_token
    (encode_record_sequence_number sequence_number)

(*
 * Sequence-token injectivity.
 *
 * Requirement: two public sequence encodings are equal.
 * Guarantee: the original natural sequence numbers are equal.
 *)
val encode_record_sequence_number_injective:
  left:nat ->
  right:nat ->
  Lemma
    (requires
      encode_record_sequence_number left ==
      encode_record_sequence_number right)
    (ensures left == right)
(* Proof: equal Seq.create values have equal lengths, which are left and right. *)
let encode_record_sequence_number_injective left right =
  assert (Seq.length (Seq.create left 0uy) == left);
  assert (Seq.length (Seq.create right 0uy) == right)

(*
 * Per-IV symbolic nonce injectivity.
 *
 * Requirement: nonces built for two sequence numbers are equal.
 * Guarantee: the sequence numbers are equal.  The IV parameter documents the
 * TLS call site but does not participate in the symbolic nonce constructor.
 *)
val record_nonce_injective:
  static_iv:DY.bytes ->
  left:nat ->
  right:nat ->
  Lemma
    (requires
      record_nonce static_iv left ==
      record_nonce static_iv right)
    (ensures left == right)
(* Proof: reduce nonce equality to injectivity of the sequence encoding. *)
let record_nonce_injective static_iv left right =
  encode_record_sequence_number_injective left right

(* Embed already-computed concrete nonce bytes as public data when needed. *)
let public_record_nonce (nonce:B.bytes) : DY.bytes =
  public_bytes nonce

(* Construct the ideal AEAD ciphertext for key, nonce, plaintext, and AAD. *)
let protected_record
  (key nonce plaintext additional_data:DY.bytes)
  : DY.bytes =
  DY.AeadEnc key nonce plaintext additional_data

(*
 * Relate the TLS smart constructor to DY*'s public AEAD constructor function.
 *
 * Requirement: none.
 * Guarantee: protected_record is definitionally the same ideal AEAD term as
 * DY.aead_enc with the four arguments in the same order.
 *)
val protected_record_definition:
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (ensures
      protected_record key nonce plaintext additional_data ==
      DY.aead_enc key nonce plaintext additional_data)
(* Proof: normalize the DY convenience constructor. *)
let protected_record_definition key nonce plaintext additional_data =
  normalize_term_spec DY.aead_enc

(* Embed the exact five-byte TLS record header used as public AEAD AAD. *)
let protected_record_additional_data (header:B.bytes) : DY.bytes =
  public_bytes header

(*
 * Represent TLSInnerPlaintext as secret content followed by public type/padding.
 *)
let application_plaintext
  (content:DY.bytes)
  (content_type_and_padding:B.bytes)
  : DY.bytes =
  DY.Concat content (public_bytes content_type_and_padding)

(* Derive the ideal public verification key from a signing-key term. *)
let verification_key (signing_key:DY.bytes) : DY.bytes =
  DY.Vk signing_key

(* Encode endpoint role as a public, constructor-distinct byte literal. *)
let encode_symbolic_role (role:symbolic_role) : DY.bytes =
  match role with
  | SymbolicClient -> public_bytes (B.singleton 0uy)
  | SymbolicServer -> public_bytes (B.singleton 1uy)

(*
 * Encode a symbolic endpoint identity for usages and event payloads.
 *
 * The encoding includes the term-level principal, session identifier, and
 * role; state-label coordinates are deliberately not serialized here.
 *)
let encode_endpoint_session (session:endpoint_session) : DY.bytes =
  DY.Concat
    session.session_principal_term
    (DY.Concat
      session.session_id_term
      (encode_symbolic_role session.session_role))

(* Public compact encoding of the fixed protocol version and algorithm profile. *)
let profile_algorithms : DY.bytes =
  public_bytes
    (B.of_list [0x13uy; 0x03uy; 0x00uy; 0x1duy; 0x08uy; 0x04uy])

(*
 * Canonically encode all symbolic session-context fields into one DY term.
 *
 * Constructor structure makes the ordered sessions, name, algorithms, randoms,
 * key shares, and transcript available to event-origin reasoning.
 *)
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

(* Check role orientation and the refined fixed algorithms of a context. *)
let session_context_in_profile (context:session_context) : prop =
  context.context_client.session_role == SymbolicClient /\
  context.context_server.session_role == SymbolicServer /\
  context.context_cipher_suite == Profile.profile_cipher_suite /\
  context.context_named_group == Profile.profile_named_group /\
  context.context_signature_scheme == Profile.profile_signature_scheme

(*
 * Build an in-profile session context from symbolic handshake parameters.
 *
 * The algorithm fields are populated with the fixed profile constants; callers
 * provide endpoint identities, name, randoms, key shares, and transcript.
 *)
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
