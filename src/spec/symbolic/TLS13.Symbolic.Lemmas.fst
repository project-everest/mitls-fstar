module TLS13.Symbolic.Lemmas

(*
 * Structural facts about the TLS symbolic vocabulary.
 *
 * These lemmas expose constructor shape, well-formedness, labels, and usage
 * calculations to downstream SMT proofs.  They are algebraic facts about DY
 * terms, not protocol-origin, concrete-collision, or peer-agreement results.
 *)

module B = TLS13.Bytes
module DY = DY.Core
module Events = TLS13.Symbolic.Events
module Terms = TLS13.Symbolic.Terms
module Usages = TLS13.Symbolic.Usages

(*
 * Ideal X25519 shared-secret agreement.
 *
 * Requirement: none.
 * Guarantee: applying each private term to the other party's ideal public term
 * yields the same DY shared-secret term.
 *)
val x25519_shared_agreement:
  client_secret:DY.bytes ->
  server_secret:DY.bytes ->
  Lemma
    (Terms.x25519_shared
       client_secret
       (Terms.x25519_public server_secret) ==
     Terms.x25519_shared
       server_secret
       (Terms.x25519_public client_secret))
(* Proof: delegate to the commutativity lemma of DY's DH constructor. *)
let x25519_shared_agreement client_secret server_secret =
  DY.dh_shared_secret_lemma client_secret server_secret

(*
 * Public nonce shape.
 *
 * Requirement: none.
 * Guarantee: public_record_nonce is exactly a DY Literal of the concrete bytes.
 *)
val public_record_nonce_shape:
  nonce:B.bytes ->
  Lemma
    (Terms.public_record_nonce nonce == DY.Literal nonce)
(* Proof: unfold the public nonce and public_bytes smart constructors. *)
let public_record_nonce_shape nonce = ()

(*
 * Protected-record shape.
 *
 * Requirement: none.
 * Guarantee: the TLS constructor preserves the exact key, nonce, plaintext,
 * and AAD as arguments of one DY AeadEnc node.
 *)
val protected_record_shape:
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (Terms.protected_record key nonce plaintext additional_data ==
     DY.AeadEnc key nonce plaintext additional_data)
(* Proof: definitional unfolding. *)
let protected_record_shape key nonce plaintext additional_data = ()

(*
 * Handshake-event shape.
 *
 * Requirement: none.
 * Guarantee: the entry contains the supplied principal, injective event tag,
 * encoded session context, and details in the documented order.
 *)
val handshake_event_shape:
  principal:DY.principal ->
  kind:Events.event_kind ->
  context:Terms.session_context ->
  details:DY.bytes ->
  Lemma
    (Events.handshake_event_entry principal kind context details ==
     DY.Event
       principal
       (Events.event_tag kind)
       (DY.Concat (Terms.encode_session_context context) details))
(* Proof: unfold the event-entry and event-content constructors. *)
let handshake_event_shape principal kind context details = ()

(*
 * TLS known-peer DH usage.
 *
 * Requirement: none.
 * Guarantee: combining two TLS ephemeral session usages selects the common
 * shared-secret usage.
 *)
val tls_dh_usage_known_peer:
  client_session:Terms.endpoint_session ->
  server_session:Terms.endpoint_session ->
  Lemma
    (Usages.known_peer_dh_usage
       (Usages.ephemeral_dh_usage client_session)
       (Usages.ephemeral_dh_usage server_session) ==
     Usages.shared_dh_usage)
(* Proof: both usages match the TLS ephemeral branch of the classifier. *)
let tls_dh_usage_known_peer client_session server_session = ()

(*
 * Literal well-formedness.
 *
 * Requirement: none.
 * Guarantee: every exact public byte literal is well formed in every trace.
 *)
val public_bytes_well_formed:
  tr:DY.trace ->
  value:B.bytes ->
  Lemma (DY.bytes_well_formed tr (Terms.public_bytes value))
(* Proof: normalize the literal case of bytes_well_formed. *)
let public_bytes_well_formed tr value =
  normalize_term_spec DY.bytes_well_formed

(*
 * DH public-key well-formedness.
 *
 * Requirement: none.
 * Guarantee: an ideal public key is well formed exactly when its private input
 * term is well formed.
 *)
val x25519_public_well_formed:
  tr:DY.trace ->
  secret:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr (Terms.x25519_public secret) ==
     DY.bytes_well_formed tr secret)
(* Proof: apply DY's DhPub well-formedness equation. *)
let x25519_public_well_formed tr secret =
  DY.bytes_well_formed_dh_pk tr secret

(*
 * DH shared-secret well-formedness.
 *
 * Requirement: none.
 * Guarantee: the result is well formed iff both private and peer-public inputs
 * are well formed.
 *)
val x25519_shared_well_formed:
  tr:DY.trace ->
  secret:DY.bytes ->
  peer_public:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.x25519_shared secret peer_public)
     <==>
     DY.bytes_well_formed tr secret /\
     DY.bytes_well_formed tr peer_public)
(* Proof: apply DY's Dh well-formedness equation. *)
let x25519_shared_well_formed tr secret peer_public =
  DY.bytes_well_formed_dh tr secret peer_public

(*
 * HkdfLabel-info well-formedness.
 *
 * Requirement: none.
 * Guarantee: all public encoding fields are automatically well formed, so the
 * complete info term is well formed exactly when its symbolic context is.
 *)
val hkdf_info_well_formed:
  tr:DY.trace ->
  output_length_high:B.byte ->
  output_length_low:B.byte ->
  label_length:B.byte ->
  label:B.bytes ->
  context_length:B.byte ->
  context:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.hkdf_info
         output_length_high output_length_low label_length
         label context_length context)
     <==>
     DY.bytes_well_formed tr context)
(* Proof: normalize concatenations and literal well-formedness. *)
let hkdf_info_well_formed
  tr output_length_high output_length_low label_length
  label context_length context =
  normalize_term_spec DY.bytes_well_formed

(*
 * Derive-Secret well-formedness.
 *
 * Requirement: none.
 * Guarantee: the KDF result is well formed iff its secret and symbolic context
 * are well formed.
 *)
val derive_secret_well_formed:
  tr:DY.trace ->
  secret:DY.bytes ->
  label:B.bytes ->
  label_length:B.byte ->
  context:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.derive_secret secret label label_length context)
     <==>
     DY.bytes_well_formed tr secret /\
     DY.bytes_well_formed tr context)
(* Proof: normalize KdfExpand and hkdf_info well-formedness. *)
let derive_secret_well_formed
  tr secret label label_length context =
  normalize_term_spec DY.bytes_well_formed

(*
 * CertificateVerify term well-formedness.
 *
 * Requirement: none.
 * Guarantee: the signature is well formed iff signing key, signing nonce, and
 * transcript are all well formed.
 *)
val certificate_verify_well_formed:
  tr:DY.trace ->
  signing_key:DY.bytes ->
  nonce:DY.bytes ->
  transcript:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.certificate_verify signing_key nonce transcript)
     <==>
     DY.bytes_well_formed tr signing_key /\
     DY.bytes_well_formed tr nonce /\
     DY.bytes_well_formed tr transcript)
(* Proof: normalize the signature, prefix, hash, and concatenation structure. *)
let certificate_verify_well_formed tr signing_key nonce transcript =
  normalize_term_spec DY.bytes_well_formed

(*
 * Protected-record well-formedness.
 *
 * Requirement: none.
 * Guarantee: an AeadEnc record is well formed iff its key, nonce, plaintext,
 * and additional-data terms are all well formed.
 *)
val protected_record_well_formed:
  tr:DY.trace ->
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.protected_record key nonce plaintext additional_data)
     <==>
     DY.bytes_well_formed tr key /\
     DY.bytes_well_formed tr nonce /\
     DY.bytes_well_formed tr plaintext /\
     DY.bytes_well_formed tr additional_data)
(* Proof: normalize the AeadEnc well-formedness rule. *)
let protected_record_well_formed tr key nonce plaintext additional_data =
  normalize_term_spec DY.bytes_well_formed

(*
 * Finished verify-data well-formedness.
 *
 * Requirement: none.
 * Guarantee: the MAC term is well formed iff the traffic secret and transcript
 * inputs are well formed.
 *)
val finished_verify_data_well_formed:
  tr:DY.trace ->
  traffic_secret:DY.bytes ->
  transcript:DY.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.finished_verify_data traffic_secret transcript)
     <==>
     DY.bytes_well_formed tr traffic_secret /\
     DY.bytes_well_formed tr transcript)
(* Proof: normalize Finished-key derivation, transcript hash, and MAC rules. *)
let finished_verify_data_well_formed tr traffic_secret transcript =
  normalize_term_spec DY.bytes_well_formed

(*
 * Application plaintext well-formedness.
 *
 * Requirement: none.
 * Guarantee: public content-type/padding bytes add no obligation, so the
 * plaintext is well formed exactly when its secret content term is.
 *)
val application_plaintext_well_formed:
  tr:DY.trace ->
  content:DY.bytes ->
  content_type_and_padding:B.bytes ->
  Lemma
    (DY.bytes_well_formed tr
       (Terms.application_plaintext content content_type_and_padding)
     <==>
     DY.bytes_well_formed tr content)
(* Proof: normalize concatenation and literal well-formedness. *)
let application_plaintext_well_formed
  tr content content_type_and_padding =
  normalize_term_spec DY.bytes_well_formed

(*
 * Public literal label.
 *
 * Requirement: none.
 * Guarantee: exact public bytes always have the DY public label.
 *)
val public_bytes_label:
  tr:DY.trace ->
  value:B.bytes ->
  Lemma
    (DY.get_label tr (Terms.public_bytes value) == DY.public)
(* Proof: normalize the Literal case of get_label. *)
let public_bytes_label tr value =
  normalize_term_spec DY.get_label

(*
 * X25519 public-key label.
 *
 * Requirement: none.
 * Guarantee: ideal DH public keys are public regardless of the private term's
 * confidentiality label.
 *)
val x25519_public_label:
  tr:DY.trace ->
  secret:DY.bytes ->
  Lemma
    (DY.get_label tr (Terms.x25519_public secret) == DY.public)
(* Proof: apply DY's label rule for DhPub. *)
let x25519_public_label tr secret =
  DY.get_label_dh_pk tr secret

(*
 * Transcript-hash label.
 *
 * Requirement: none.
 * Guarantee: hashing preserves the confidentiality label of the transcript.
 *)
val transcript_hash_label:
  tr:DY.trace ->
  transcript:DY.bytes ->
  Lemma
    (DY.get_label tr (Terms.transcript_hash transcript) ==
     DY.get_label tr transcript)
(* Proof: normalize the Hash label rule. *)
let transcript_hash_label tr transcript =
  normalize_term_spec Terms.transcript_hash;
  normalize_term_spec DY.get_label

(*
 * X25519 shared-secret label.
 *
 * Requirement: none.
 * Guarantee: DH over the client's secret and server's public key is protected
 * by the join of both private-term labels.
 *)
val x25519_shared_label:
  tr:DY.trace ->
  client_secret:DY.bytes ->
  server_secret:DY.bytes ->
  Lemma
    (DY.get_label tr
       (Terms.x25519_shared
         client_secret
         (Terms.x25519_public server_secret)) ==
     DY.join
       (DY.get_label tr client_secret)
       (DY.get_label tr server_secret))
(* Proof: expand Dh/DhPub labels and normalize the DY DH label join. *)
let x25519_shared_label tr client_secret server_secret =
  normalize_term_spec Terms.x25519_shared;
  normalize_term_spec Terms.x25519_public;
  normalize_term_spec DY.get_label;
  normalize_term_spec DY.get_dh_label

(*
 * CertificateVerify label.
 *
 * Requirement: none.
 * Guarantee: a public signature carries the label of its signed message, not
 * the label of the signing key or random nonce.
 *)
val certificate_verify_label:
  tr:DY.trace ->
  signing_key:DY.bytes ->
  nonce:DY.bytes ->
  transcript:DY.bytes ->
  Lemma
    (DY.get_label tr
       (Terms.certificate_verify signing_key nonce transcript) ==
     DY.get_label tr (Terms.certificate_verify_input transcript))
(* Proof: normalize the Sign label rule. *)
let certificate_verify_label tr signing_key nonce transcript =
  normalize_term_spec Terms.certificate_verify;
  normalize_term_spec DY.get_label

(*
 * Protected-record label.
 *
 * Requirement: none.
 * Guarantee: an AEAD ciphertext term is public even when its plaintext is not.
 *)
val protected_record_label:
  tr:DY.trace ->
  key:DY.bytes ->
  nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  Lemma
    (DY.get_label tr
       (Terms.protected_record key nonce plaintext additional_data) ==
     DY.public)
(* Proof: normalize the AeadEnc label rule. *)
let protected_record_label tr key nonce plaintext additional_data =
  normalize_term_spec Terms.protected_record;
  normalize_term_spec DY.get_label

(*
 * Concrete public-record nonce label.
 *
 * Requirement: none.
 * Guarantee: literal nonce bytes are public in every trace.
 *)
val public_record_nonce_label:
  tr:DY.trace ->
  nonce:B.bytes ->
  Lemma
    (DY.get_label tr (Terms.public_record_nonce nonce) == DY.public)
(* Proof: reuse the public literal label lemma. *)
let public_record_nonce_label tr nonce =
  public_bytes_label tr nonce

(*
 * KDF expansion label propagation.
 *
 * Requirement: the requested output length is nonzero (refinement type).
 * Guarantee: the derived term inherits exactly the PRK's label.
 *)
val kdf_expand_label:
  tr:DY.trace ->
  prk:DY.bytes ->
  info:DY.bytes ->
  length:nat{length <> 0} ->
  Lemma
    (DY.get_label tr (DY.KdfExpand prk info length) ==
     DY.get_label tr prk)
(* Proof: normalize the configured KdfExpand label rule. *)
let kdf_expand_label tr prk info length =
  normalize_term_spec DY.get_label

(*
 * Constructor separation between records and signatures.
 *
 * Requirement: none.
 * Guarantee: no protected-record AeadEnc term equals a CertificateVerify Sign
 * term, regardless of their arguments.
 *)
val protected_record_not_certificate_verify:
  key:DY.bytes ->
  record_nonce:DY.bytes ->
  plaintext:DY.bytes ->
  additional_data:DY.bytes ->
  signing_key:DY.bytes ->
  signing_nonce:DY.bytes ->
  transcript:DY.bytes ->
  Lemma
    (Terms.protected_record
       key record_nonce plaintext additional_data
     =!=
     Terms.certificate_verify signing_key signing_nonce transcript)
(* Proof: AeadEnc and Sign are distinct constructors of DY.bytes. *)
let protected_record_not_certificate_verify
  key record_nonce plaintext additional_data
  signing_key signing_nonce transcript = ()

(*
 * Event-tag injectivity.
 *
 * Requirement: the two event-tag strings are equal.
 * Guarantee: the originating event_kind constructors are equal.
 *)
val event_tag_injective:
  left:Events.event_kind ->
  right:Events.event_kind ->
  Lemma
    (requires Events.event_tag left == Events.event_tag right)
    (ensures left == right)
(* Proof: exhaustive reduction of the distinct event-tag strings. *)
let event_tag_injective left right = ()
