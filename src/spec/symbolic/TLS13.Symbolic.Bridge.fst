module TLS13.Symbolic.Bridge

(*
 * Execution-indexed relation between concrete TLS bytes and DY terms.
 *
 * Literals are related by exact byte equality, concatenations by a concrete
 * split, and all cryptographic/non-structural terms by explicit bindings in the
 * current representation.  The relation is intentionally relational rather
 * than globally functional.  Primitive bridge predicates state the idealized
 * meaning expected of concrete crypto operations; only the consumers noted
 * below currently connect those predicates to headline theorems.
 *)

module B = TLS13.Bytes
module C = TLS13.Crypto.Spec
module Canonical = TLS13.Spec.StateMachine.Canonical
module DY = DY.Core
module K = TLS13.Keys
module M = TLS13.Messages
module SM = TLS13.Spec.StateMachine
module Seq = FStar.Seq
module T = TLS13.Types
module Terms = TLS13.Symbolic.Terms
module W = TLS13.Wire.Spec

(*
 * One execution-local association between concrete bytes and a symbolic term.
 * Multiple bindings may mention the same concrete or symbolic value.
 *)
noeq
type representation_binding = {
  binding_concrete: B.bytes;
  binding_symbolic: DY.bytes;
}

(*
 * Symbolic interpretation state for one execution.
 *
 * The DY trace provides time, labels, usages, and events; bindings interpret
 * non-literal terms without claiming a global concrete-to-symbolic function.
 *)
noeq
type representation = {
  representation_trace: DY.trace;
  representation_bindings: list representation_binding;
}

(* Recursively test membership of an exact concrete/symbolic binding pair. *)
let rec explicitly_bound
  (bindings:list representation_binding)
  (concrete:B.bytes)
  (symbolic:DY.bytes)
  : Tot prop (decreases bindings) =
  match bindings with
  | [] -> False
  | binding :: rest ->
    (binding.binding_concrete == concrete /\
     binding.binding_symbolic == symbolic) \/
    explicitly_bound rest concrete symbolic

(*
 * Relate concrete bytes to a symbolic term.
 *
 * Literals demand exact equality, Concat demands a matching concrete append,
 * and every other constructor demands an explicit execution binding.
 *)
let rec represents
  (execution:representation)
  (concrete:B.bytes)
  (symbolic:DY.bytes)
  : Tot prop (decreases symbolic) =
  match symbolic with
  | DY.Literal value ->
    concrete == value
  | DY.Concat left right ->
    exists concrete_left concrete_right.
      concrete == B.append concrete_left concrete_right /\
      represents execution concrete_left left /\
      represents execution concrete_right right
  | _ ->
    explicitly_bound execution.representation_bindings concrete symbolic

(* Classify terms whose representation cannot be derived structurally. *)
let requires_explicit_binding (symbolic:DY.bytes) : prop =
  match symbolic with
  | DY.Literal _ -> False
  | DY.Concat _ _ -> False
  | _ -> True

(*
 * Extend a representation with one binding while preserving its trace and all
 * prior bindings.
 *)
let bind
  (execution:representation)
  (concrete:B.bytes)
  (symbolic:DY.bytes)
  : representation =
  {
    representation_trace = execution.representation_trace;
    representation_bindings = {
      binding_concrete = concrete;
      binding_symbolic = symbolic;
    } :: execution.representation_bindings;
  }

(*
 * Literal representation introduction.
 *
 * Requirement: none.
 * Guarantee: exact concrete bytes represent the equal DY Literal in every
 * execution.
 *)
val literal_represents:
  execution:representation ->
  value:B.bytes ->
  Lemma (represents execution value (DY.Literal value))
(* Proof: reduce represents through its Literal branch. *)
let literal_represents execution value = ()

(*
 * Concatenation representation introduction.
 *
 * Requirements: each concrete component represents its symbolic component.
 * Guarantee: their concrete append represents the matching symbolic Concat.
 *)
val concat_represents:
  execution:representation ->
  concrete_left:B.bytes ->
  concrete_right:B.bytes ->
  symbolic_left:DY.bytes ->
  symbolic_right:DY.bytes ->
  Lemma
    (requires
      represents execution concrete_left symbolic_left /\
      represents execution concrete_right symbolic_right)
    (ensures
      represents
        execution
        (B.append concrete_left concrete_right)
        (DY.Concat symbolic_left symbolic_right))
(* Proof: witness the two supplied concrete components in the Concat branch. *)
let concat_represents
  execution concrete_left concrete_right symbolic_left symbolic_right = ()

(*
 * Explicit-binding representation introduction.
 *
 * Requirement: the symbolic term is neither Literal nor Concat.
 * Guarantee: adding its concrete/symbolic pair makes it represented.
 *)
val bind_represents:
  execution:representation ->
  concrete:B.bytes ->
  symbolic:DY.bytes ->
  Lemma
    (requires requires_explicit_binding symbolic)
    (ensures represents (bind execution concrete symbolic) concrete symbolic)
(* Proof: case analysis excludes structural representation branches. *)
let bind_represents execution concrete symbolic =
  match symbolic with
  | DY.Literal _ -> ()
  | DY.Concat _ _ -> ()
  | _ -> ()

(*
 * Bind one concrete byte string to two symbolic meanings.
 *
 * Requirements: both symbolic terms require explicit bindings.
 * Guarantee: after adding both pairs, the extended relation represents the
 * concrete bytes as either term.  This lemma makes the relation's intentional
 * non-functionality explicit.
 *)
val bind_two_represents:
  execution:representation ->
  concrete:B.bytes ->
  left:DY.bytes ->
  right:DY.bytes ->
  Lemma
    (requires
      requires_explicit_binding left /\
      requires_explicit_binding right)
    (ensures (
      let extended =
        bind (bind execution concrete left) concrete right in
      represents extended concrete left /\
      represents extended concrete right))
(* Proof: case analysis plus membership in the two-element binding prefix. *)
let bind_two_represents execution concrete left right =
  match left, right with
  | DY.Literal _, _ -> ()
  | DY.Concat _ _, _ -> ()
  | _, DY.Literal _ -> ()
  | _, DY.Concat _ _ -> ()
  | _, _ -> ()

(* Alias represents for a complete concrete/symbolic transcript pair. *)
let transcript_represents
  (execution:representation)
  (concrete_transcript:B.bytes)
  (symbolic_transcript:DY.bytes)
  : prop =
  represents execution concrete_transcript symbolic_transcript

(* Relate exact serialized handshake bytes to a symbolic message term. *)
let serialized_handshake_represents
  (execution:representation)
  (message:M.handshake_msg)
  (symbolic_message:DY.bytes)
  : prop =
  represents execution (W.serialize_handshake message) symbolic_message

(*
 * Compositional transcript extension.
 *
 * Requirements: the previous transcript and serialized next message are
 * represented.
 * Guarantee: appending the concrete serialization represents the symbolic
 * transcript extended by the same message term.
 *)
val extend_transcript_represents:
  execution:representation ->
  concrete_transcript:B.bytes ->
  symbolic_transcript:DY.bytes ->
  message:M.handshake_msg ->
  symbolic_message:DY.bytes ->
  Lemma
    (requires
      transcript_represents
        execution concrete_transcript symbolic_transcript /\
      serialized_handshake_represents
        execution message symbolic_message)
    (ensures
      transcript_represents
        execution
        (B.append concrete_transcript (W.serialize_handshake message))
        (Terms.extend_transcript symbolic_transcript symbolic_message))
(* Proof: apply concat_represents to the transcript and message witnesses. *)
let extend_transcript_represents
  execution concrete_transcript symbolic_transcript
  message symbolic_message =
  concat_represents
    execution
    concrete_transcript
    (W.serialize_handshake message)
    symbolic_transcript
    symbolic_message

(*
 * Intended freshness bridge.
 *
 * The concrete bytes must represent a Rand term whose timestamp indexes an
 * earlier RandGen trace entry with the exact usage, label, and nonzero length.
 * This predicate is currently defined for future realization completeness but
 * is not consumed by the headline product/secrecy chain.
 *)
let fresh_value_bridge
  (execution:representation)
  (concrete:B.bytes)
  (symbolic:DY.bytes)
  (usage:DY.usage)
  (label:DY.label)
  (length:nat{length <> 0})
  : prop =
  represents execution concrete symbolic /\
  exists time.
    symbolic == DY.Rand length time /\
    time < DY.trace_length execution.representation_trace /\
    DY.get_entry_at execution.representation_trace time ==
      DY.RandGen usage label length

(*
 * Intended X25519 public-key bridge.
 *
 * The concrete private bytes and concrete public-key computation must
 * represent a private symbolic term and its ideal DhPub.  This predicate is
 * currently not wired into Product refinement or secrecy lineage.
 *)
let x25519_public_bridge
  (execution:representation)
  (concrete_secret:C.x25519_private)
  (symbolic_secret:DY.bytes)
  : prop =
  represents execution concrete_secret symbolic_secret /\
  represents
    execution
    (C.x25519_public_from_private concrete_secret)
    (Terms.x25519_public symbolic_secret)

(*
 * Intended X25519 shared-secret bridge.
 *
 * Both concrete operands must be represented, concrete X25519 must succeed,
 * and its result must represent the corresponding ideal Dh term.  This
 * predicate is currently not wired into Product refinement or secrecy lineage.
 *)
let x25519_shared_bridge
  (execution:representation)
  (concrete_secret:C.x25519_private)
  (symbolic_secret:DY.bytes)
  (concrete_peer_public:C.x25519_public)
  (symbolic_peer_public:DY.bytes)
  : prop =
  represents execution concrete_secret symbolic_secret /\
  represents execution concrete_peer_public symbolic_peer_public /\
  (match C.x25519_shared concrete_secret concrete_peer_public with
   | Some concrete_shared ->
     represents
       execution
       concrete_shared
       (Terms.x25519_shared symbolic_secret symbolic_peer_public)
   | None -> False)

(*
 * Intended SHA-256 bridge.
 *
 * The exact concrete input and digest are related to a symbolic message and
 * Hash node.  This predicate is currently not consumed by the headline chain.
 *)
let hash_bridge
  (execution:representation)
  (concrete_message:B.bytes)
  (symbolic_message:DY.bytes)
  : prop =
  represents execution concrete_message symbolic_message /\
  represents
    execution
    (C.sha256 concrete_message)
    (DY.Hash symbolic_message)

(*
 * Intended HKDF-Extract bridge.
 *
 * Represented concrete salt and IKM must produce bytes represented by the
 * matching KdfExtract term.  This predicate is currently not wired into key
 * lineage.
 *)
let hkdf_extract_bridge
  (execution:representation)
  (concrete_salt concrete_ikm:B.bytes)
  (symbolic_salt symbolic_ikm:DY.bytes)
  : prop =
  represents execution concrete_salt symbolic_salt /\
  represents execution concrete_ikm symbolic_ikm /\
  represents
    execution
    (C.hkdf_extract concrete_salt concrete_ikm)
    (DY.KdfExtract symbolic_salt symbolic_ikm)

(*
 * Intended HKDF-Expand-Label bridge.
 *
 * Exact public lengths and TLS label bytes are checked, the concrete secret and
 * context are represented, and concrete expansion output is bound to the
 * structured symbolic KdfExpand.  This predicate is currently not wired into
 * key lineage.
 *)
let hkdf_expand_label_bridge
  (execution:representation)
  (concrete_secret:B.bytes)
  (symbolic_secret:DY.bytes)
  (label:B.bytes)
  (label_length:B.byte)
  (concrete_context:B.bytes)
  (symbolic_context:DY.bytes)
  (context_length:B.byte)
  (output_length:nat{output_length <> 0})
  (output_length_high output_length_low:B.byte)
  : prop =
  represents execution concrete_secret symbolic_secret /\
  represents execution concrete_context symbolic_context /\
  B.length (Terms.tls13_label label) == FStar.UInt8.v label_length /\
  B.length concrete_context == FStar.UInt8.v context_length /\
  output_length ==
    FStar.UInt8.v output_length_high * 256 +
    FStar.UInt8.v output_length_low /\
  represents
    execution
    (C.hkdf_expand_label
      concrete_secret label concrete_context output_length)
    (DY.KdfExpand
      symbolic_secret
      (Terms.hkdf_info
        output_length_high output_length_low label_length
        label context_length symbolic_context)
      output_length)

(*
 * Concrete HMAC bridge used by Finished authentication.
 *
 * Represented key/message bytes and the exact concrete HMAC output are related
 * to one ideal Mac term.
 *)
let hmac_bridge
  (execution:representation)
  (concrete_key concrete_message:B.bytes)
  (symbolic_key symbolic_message:DY.bytes)
  : prop =
  represents execution concrete_key symbolic_key /\
  represents execution concrete_message symbolic_message /\
  represents
    execution
    (C.hmac_sha256 concrete_key concrete_message)
    (DY.Mac symbolic_key symbolic_message)

(*
 * Concrete RSA-PSS bridge used by CertificateVerify authentication.
 *
 * It relates signing and verification keys, exact message/signature bytes, and
 * requires successful concrete RSA-PSS-RSAE-SHA256 verification of the same
 * signature represented by the ideal Sign term.
 *)
let signature_bridge
  (execution:representation)
  (concrete_signing_key concrete_verification_key:B.bytes)
  (symbolic_signing_key symbolic_nonce symbolic_message:DY.bytes)
  (concrete_message concrete_signature:B.bytes)
  : prop =
  represents execution concrete_signing_key symbolic_signing_key /\
  represents
    execution
    concrete_verification_key
    (Terms.verification_key symbolic_signing_key) /\
  represents execution concrete_message symbolic_message /\
  represents
    execution
    concrete_signature
    (DY.Sign symbolic_signing_key symbolic_nonce symbolic_message) /\
  C.verify_signature
    T.Rsa_pss_rsae_sha256
    concrete_verification_key
    concrete_message
    concrete_signature == true

(*
 * Registry entry trusted by named-server authentication.
 *
 * It binds a hostname and principal to both concrete and symbolic verification
 * keys.  Registry membership is an explicit trust boundary, not a WebPKI proof.
 *)
noeq
type trusted_server = {
  trusted_server_name: T.hostname;
  trusted_server_principal: DY.principal;
  trusted_server_verification_key: B.bytes;
  trusted_server_symbolic_key: DY.bytes;
}

(* Recursive exact-membership predicate for the trusted-server registry. *)
let rec registered_server
  (registry:list trusted_server)
  (server:trusted_server)
  : Tot prop (decreases registry) =
  match registry with
  | [] -> False
  | entry :: rest ->
    entry == server \/ registered_server rest server

(*
 * X.509 identity bridge consumed by authentication.
 *
 * The chosen registry entry must be present, the validated name and leaf key
 * must equal it, and the concrete leaf key must represent its symbolic key.
 *)
let x509_identity_bridge
  (execution:representation)
  (registry:list trusted_server)
  (server:trusted_server)
  (validated_server_name:T.hostname)
  (validated_leaf_key:B.bytes)
  : prop =
  registered_server registry server /\
  validated_server_name == server.trusted_server_name /\
  validated_leaf_key == server.trusted_server_verification_key /\
  represents
    execution
    validated_leaf_key
    server.trusted_server_symbolic_key

(*
 * AEAD sealing bridge consumed by sent-record realization.
 *
 * Exact concrete key, nonce, AAD, and plaintext must represent their symbolic
 * counterparts; concrete ChaCha20-Poly1305 output must represent the matching
 * protected_record term.
 *)
let aead_seal_bridge
  (execution:representation)
  (concrete_key:C.aead_key)
  (symbolic_key:DY.bytes)
  (concrete_nonce:C.aead_nonce)
  (symbolic_nonce:DY.bytes)
  (concrete_aad concrete_plaintext:B.bytes)
  (symbolic_aad symbolic_plaintext:DY.bytes)
  : prop =
  represents execution concrete_key symbolic_key /\
  represents execution concrete_nonce symbolic_nonce /\
  represents execution concrete_aad symbolic_aad /\
  represents execution concrete_plaintext symbolic_plaintext /\
  represents
    execution
    (C.chacha20_poly1305_seal
      concrete_key concrete_nonce concrete_aad concrete_plaintext)
    (Terms.protected_record
      symbolic_key symbolic_nonce symbolic_plaintext symbolic_aad)

(*
 * AEAD opening bridge consumed by accepted-record realization.
 *
 * Concrete open must succeed with the supplied length-refined plaintext, every
 * operand must be represented, and the accepted concrete ciphertext must
 * represent the matching protected_record term.
 *)
let aead_open_bridge
  (execution:representation)
  (concrete_key:C.aead_key)
  (symbolic_key:DY.bytes)
  (concrete_nonce:C.aead_nonce)
  (symbolic_nonce:DY.bytes)
  (concrete_aad concrete_ciphertext:B.bytes)
  (concrete_plaintext:B.bytes{
    B.length concrete_plaintext + 16 == B.length concrete_ciphertext
  })
  (symbolic_aad symbolic_plaintext:DY.bytes)
  : prop =
  C.chacha20_poly1305_open
    concrete_key concrete_nonce concrete_aad concrete_ciphertext ==
      Some concrete_plaintext /\
  represents execution concrete_key symbolic_key /\
  represents execution concrete_nonce symbolic_nonce /\
  represents execution concrete_aad symbolic_aad /\
  represents execution concrete_plaintext symbolic_plaintext /\
  represents
    execution
    concrete_ciphertext
    (Terms.protected_record
      symbolic_key symbolic_nonce symbolic_plaintext symbolic_aad)

(*
 * Package canonical concrete wire semantics with a symbolic raw-record view.
 *
 * The concrete transition must be canonical.  Each nonempty sent or received
 * byte string must represent the supplied record term.
 *)
let canonical_record_bridge
  (execution:representation)
  (before after:SM.connection_state)
  (event:SM.conn_event)
  (raw_sent raw_received:B.bytes)
  (symbolic_record:DY.bytes)
  : prop =
  Canonical.canonical_wire_step
    before after event raw_sent raw_received /\
  (B.length raw_sent <> 0 ==>
    represents execution raw_sent symbolic_record) /\
  (B.length raw_received <> 0 ==>
    represents execution raw_received symbolic_record)

(*
 * Names of all intended trust/idealization boundaries.
 *
 * This enumeration is documentation data, not a proof that every predicate is
 * connected to a consumer.
 *)
type bridge_assumption =
  | HonestFreshness
  | X25519Idealization
  | HashIdealization
  | HkdfIdealization
  | HmacIdealization
  | RsaPssIdealization
  | TrustedNameToLeafKeyRegistry
  | AeadIdealization

(* Exhaustive list used by tooling and documentation to enumerate boundaries. *)
let all_bridge_assumptions : list bridge_assumption = [
  HonestFreshness;
  X25519Idealization;
  HashIdealization;
  HkdfIdealization;
  HmacIdealization;
  RsaPssIdealization;
  TrustedNameToLeafKeyRegistry;
  AeadIdealization;
]

(*
 * Human-readable intended consumer for each bridge assumption.
 *
 * Some primitive bridges remain future wiring obligations, as documented
 * above and in SYMBOLIC_AUDIT.md; this string table does not establish use.
 *)
let bridge_assumption_consumer (assumption:bridge_assumption) : string =
  match assumption with
  | HonestFreshness -> "product-step lifting and injective agreement"
  | X25519Idealization -> "key-schedule lifting and shared-secret secrecy"
  | HashIdealization -> "transcript and key-schedule lifting"
  | HkdfIdealization -> "key-schedule lifting and traffic-key secrecy"
  | HmacIdealization -> "Finished lifting and origin"
  | RsaPssIdealization -> "CertificateVerify lifting and origin"
  | TrustedNameToLeafKeyRegistry -> "server-identity authentication"
  | AeadIdealization -> "record lifting, integrity, and confidentiality"
