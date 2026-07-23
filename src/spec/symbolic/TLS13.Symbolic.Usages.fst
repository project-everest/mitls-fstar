module TLS13.Symbolic.Usages

(*
 * Protocol-specific DY usages for TLS keys and derived material.
 *
 * Usages record cryptographic purpose independently of confidentiality labels.
 * The KDF classifier below inspects exact symbolic HkdfLabel structure to
 * distinguish roles, epochs, Finished keys, record keys, and IVs.  These are
 * symbolic domain-separation facts; concrete key installation is established
 * separately by Product and Secrecy premises.
 *)

module B = TLS13.Bytes
module DY = DY.Core
module K = TLS13.Keys
module Seq = FStar.Seq
module Terms = TLS13.Symbolic.Terms

(* Identify a server signing key by principal and credential term. *)
let signing_key_usage
  (server:DY.principal)
  (credential:DY.bytes)
  : DY.usage =
  DY.SigKey server credential

(* Usage assigned to honest randomized-signature nonces. *)
let signing_nonce_usage : DY.usage =
  DY.SigNonce

(* Usage descriptor for the non-PSK early-secret stage in one context. *)
let early_secret_usage (context:Terms.session_context) : DY.usage =
  DY.KdfExpandKey
    "TLS13.EarlySecret"
    (Terms.encode_session_context context)

(* Usage descriptor for the handshake-secret extract stage. *)
let handshake_secret_usage (context:Terms.session_context) : DY.usage =
  DY.KdfExpandKey
    "TLS13.HandshakeSecret"
    (Terms.encode_session_context context)

(* Usage descriptor for the master-secret extract stage. *)
let master_secret_usage (context:Terms.session_context) : DY.usage =
  DY.KdfExpandKey
    "TLS13.MasterSecret"
    (Terms.encode_session_context context)

(* Identify an endpoint's X25519 private value by its encoded session. *)
let ephemeral_dh_usage (session:Terms.endpoint_session) : DY.usage =
  DY.DhKey "TLS13.X25519Ephemeral" (Terms.encode_endpoint_session session)

(* Common usage of a shared secret produced from a TLS ephemeral DH key. *)
let shared_dh_usage : DY.usage =
  DY.KdfExpandKey
    "TLS13.X25519SharedSecret"
    (Terms.public_bytes B.empty)

(*
 * Select the result usage when both DH peer usages are known.
 *
 * A TLS ephemeral key on either side yields shared_dh_usage; unrelated DH
 * usages are rejected with NoUsage.
 *)
let known_peer_dh_usage
  (left:DY.usage{DY.DhKey? left})
  (right:DY.usage{DY.DhKey? right})
  : DY.usage =
  match left, right with
  | DY.DhKey "TLS13.X25519Ephemeral" _, _ -> shared_dh_usage
  | _, DY.DhKey "TLS13.X25519Ephemeral" _ -> shared_dh_usage
  | _, _ -> DY.NoUsage

(* Select the shared-secret usage when only one TLS private-key usage is known. *)
let unknown_peer_dh_usage
  (key_usage:DY.usage{DY.DhKey? key_usage})
  : DY.usage =
  match key_usage with
  | DY.DhKey "TLS13.X25519Ephemeral" _ -> shared_dh_usage
  | _ -> DY.NoUsage

(*
 * Symmetry of known-peer DH usage selection.
 *
 * Requirement: both inputs are well-formed DH-key usages (refinement types).
 * Guarantee: swapping the two peer usages does not change the result usage.
 *)
val known_peer_dh_usage_commutes:
  left:DY.usage{DY.DhKey? left} ->
  right:DY.usage{DY.DhKey? right} ->
  Lemma
    (known_peer_dh_usage left right ==
     known_peer_dh_usage right left)
(* Proof: exhaustive case analysis on the two DH usage constructors. *)
let known_peer_dh_usage_commutes left right =
  match left, right with
  | DY.DhKey "TLS13.X25519Ephemeral" _, _ -> ()
  | _, DY.DhKey "TLS13.X25519Ephemeral" _ -> ()
  | _, _ -> ()

(*
 * Compatibility of unknown- and known-peer usage selection.
 *
 * Requirement: the left private-key usage produces a non-NoUsage result when
 * the peer is unknown.
 * Guarantee: supplying any well-formed peer usage to known_peer_dh_usage gives
 * exactly that same result.
 *)
val unknown_peer_dh_usage_implies:
  left:DY.usage{DY.DhKey? left} ->
  right:DY.usage{DY.DhKey? right} ->
  Lemma
    (requires unknown_peer_dh_usage left =!= DY.NoUsage)
    (ensures
      known_peer_dh_usage left right ==
      unknown_peer_dh_usage left)
(* Proof: the requirement restricts left to the TLS ephemeral usage branch. *)
let unknown_peer_dh_usage_implies left right =
  match left with
  | DY.DhKey "TLS13.X25519Ephemeral" _ -> ()
  | _ -> ()

(*
 * Classify a KDF expansion from its exact symbolic HkdfLabel info.
 *
 * The output/label/context length bytes distinguish TLS derivations.  Traffic
 * direction and epoch select unique KdfExpandKey, MacKey, AeadKey, or IV
 * usages.  Any malformed or unsupported info shape maps to NoUsage.
 *)
let kdf_usage_for_info
  (prk_usage:DY.usage{DY.KdfExpandKey? prk_usage})
  (info:DY.bytes)
  : DY.usage =
  match info with
  | DY.Concat
      (DY.Literal output_and_label_length)
      (DY.Concat
        (DY.Literal label)
        (DY.Concat (DY.Literal context_length) context)) ->
    if
      Seq.eq output_and_label_length
        (B.of_list [0uy; 32uy; 13uy]) &&
      Seq.eq label (Terms.tls13_label K.label_derived) &&
      Seq.eq context_length (B.singleton 32uy)
    then DY.KdfExpandKey "TLS13.DerivedSecret" context
    else if
      Seq.eq output_and_label_length
        (B.of_list [0uy; 32uy; 18uy]) &&
      Seq.eq label (Terms.tls13_label K.label_c_hs_traffic) &&
      Seq.eq context_length (B.singleton 32uy)
    then DY.KdfExpandKey "TLS13.ClientHandshakeTrafficSecret" context
    else if
      Seq.eq output_and_label_length
        (B.of_list [0uy; 32uy; 18uy]) &&
      Seq.eq label (Terms.tls13_label K.label_s_hs_traffic) &&
      Seq.eq context_length (B.singleton 32uy)
    then DY.KdfExpandKey "TLS13.ServerHandshakeTrafficSecret" context
    else if
      Seq.eq output_and_label_length
        (B.of_list [0uy; 32uy; 18uy]) &&
      Seq.eq label (Terms.tls13_label K.label_c_ap_traffic) &&
      Seq.eq context_length (B.singleton 32uy)
    then DY.KdfExpandKey "TLS13.ClientApplicationTrafficSecret" context
    else if
      Seq.eq output_and_label_length
        (B.of_list [0uy; 32uy; 18uy]) &&
      Seq.eq label (Terms.tls13_label K.label_s_ap_traffic) &&
      Seq.eq context_length (B.singleton 32uy)
    then DY.KdfExpandKey "TLS13.ServerApplicationTrafficSecret" context
    else if
      Seq.eq output_and_label_length
        (B.of_list [0uy; 32uy; 14uy]) &&
      Seq.eq label (Terms.tls13_label K.label_finished) &&
      Seq.eq context_length (B.singleton 0uy)
    then
      (match prk_usage with
       | DY.KdfExpandKey "TLS13.ClientHandshakeTrafficSecret" data ->
         DY.MacKey "TLS13.ClientFinishedKey" data
       | DY.KdfExpandKey "TLS13.ServerHandshakeTrafficSecret" data ->
         DY.MacKey "TLS13.ServerFinishedKey" data
       | _ -> DY.NoUsage)
    else if
      Seq.eq output_and_label_length
        (B.of_list [0uy; 32uy; 9uy]) &&
      Seq.eq label (Terms.tls13_label K.label_key) &&
      Seq.eq context_length (B.singleton 0uy)
    then
      (match prk_usage with
       | DY.KdfExpandKey "TLS13.ClientHandshakeTrafficSecret" data ->
         DY.AeadKey "TLS13.ClientHandshakeRecordKey" data
       | DY.KdfExpandKey "TLS13.ServerHandshakeTrafficSecret" data ->
         DY.AeadKey "TLS13.ServerHandshakeRecordKey" data
       | DY.KdfExpandKey "TLS13.ClientApplicationTrafficSecret" data ->
         DY.AeadKey "TLS13.ClientApplicationRecordKey" data
       | DY.KdfExpandKey "TLS13.ServerApplicationTrafficSecret" data ->
         DY.AeadKey "TLS13.ServerApplicationRecordKey" data
       | _ -> DY.NoUsage)
    else if
      Seq.eq output_and_label_length
        (B.of_list [0uy; 12uy; 8uy]) &&
      Seq.eq label (Terms.tls13_label K.label_iv) &&
      Seq.eq context_length (B.singleton 0uy)
    then
      (match prk_usage with
       | DY.KdfExpandKey "TLS13.ClientHandshakeTrafficSecret" data ->
         DY.KdfExpandKey "TLS13.ClientHandshakeRecordIV" data
       | DY.KdfExpandKey "TLS13.ServerHandshakeTrafficSecret" data ->
         DY.KdfExpandKey "TLS13.ServerHandshakeRecordIV" data
       | DY.KdfExpandKey "TLS13.ClientApplicationTrafficSecret" data ->
         DY.KdfExpandKey "TLS13.ClientApplicationRecordIV" data
       | DY.KdfExpandKey "TLS13.ServerApplicationTrafficSecret" data ->
         DY.KdfExpandKey "TLS13.ServerApplicationRecordIV" data
       | _ -> DY.NoUsage)
    else DY.NoUsage
  | _ -> DY.NoUsage

(*
 * TLS crypto-usage instance consumed by the DY invariant.
 *
 * Guarantee: DH terms use the symmetric TLS selectors above, KDF expansion uses
 * the exact-label classifier, and every derived term inherits the PRK's
 * confidentiality label through a reflexive flow proof.
 *)
val tls_crypto_usages: DY.crypto_usages
(* Install the TLS overrides while retaining all unrelated DY default usages. *)
instance tls_crypto_usages = {
  DY.default_crypto_usages with
  dh_usage = {
    known_peer_usage = known_peer_dh_usage;
    unknown_peer_usage = unknown_peer_dh_usage;
    known_peer_usage_commutes = known_peer_dh_usage_commutes;
    unknown_peer_usage_implies = unknown_peer_dh_usage_implies;
  };
  kdf_expand_usage = {
    get_usage = kdf_usage_for_info;
    get_label = (fun prk_usage prk_label info -> prk_label);
    get_label_lemma =
      (fun tr prk_usage prk_label info ->
        DY.can_flow_reflexive tr prk_label);
  };
}
