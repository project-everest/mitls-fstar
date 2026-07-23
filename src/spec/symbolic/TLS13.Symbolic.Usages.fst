module TLS13.Symbolic.Usages

module B = TLS13.Bytes
module DY = DY.Core
module K = TLS13.Keys
module Seq = FStar.Seq
module Terms = TLS13.Symbolic.Terms

let signing_key_usage (credential:DY.bytes) : DY.usage =
  DY.SigKey "TLS13.ServerSigningKey" credential

let signing_nonce_usage : DY.usage =
  DY.SigNonce

let early_secret_usage (context:Terms.session_context) : DY.usage =
  DY.KdfExpandKey
    "TLS13.EarlySecret"
    (Terms.encode_session_context context)

let handshake_secret_usage (context:Terms.session_context) : DY.usage =
  DY.KdfExpandKey
    "TLS13.HandshakeSecret"
    (Terms.encode_session_context context)

let master_secret_usage (context:Terms.session_context) : DY.usage =
  DY.KdfExpandKey
    "TLS13.MasterSecret"
    (Terms.encode_session_context context)

let ephemeral_dh_usage (session:Terms.endpoint_session) : DY.usage =
  DY.DhKey "TLS13.X25519Ephemeral" (Terms.encode_endpoint_session session)

let shared_dh_usage : DY.usage =
  DY.KdfExpandKey
    "TLS13.X25519SharedSecret"
    (Terms.public_bytes B.empty)

let known_peer_dh_usage
  (left:DY.usage{DY.DhKey? left})
  (right:DY.usage{DY.DhKey? right})
  : DY.usage =
  match left, right with
  | DY.DhKey "TLS13.X25519Ephemeral" _, _ -> shared_dh_usage
  | _, DY.DhKey "TLS13.X25519Ephemeral" _ -> shared_dh_usage
  | _, _ -> DY.NoUsage

let unknown_peer_dh_usage
  (key_usage:DY.usage{DY.DhKey? key_usage})
  : DY.usage =
  match key_usage with
  | DY.DhKey "TLS13.X25519Ephemeral" _ -> shared_dh_usage
  | _ -> DY.NoUsage

val known_peer_dh_usage_commutes:
  left:DY.usage{DY.DhKey? left} ->
  right:DY.usage{DY.DhKey? right} ->
  Lemma
    (known_peer_dh_usage left right ==
     known_peer_dh_usage right left)
let known_peer_dh_usage_commutes left right =
  match left, right with
  | DY.DhKey "TLS13.X25519Ephemeral" _, _ -> ()
  | _, DY.DhKey "TLS13.X25519Ephemeral" _ -> ()
  | _, _ -> ()

val unknown_peer_dh_usage_implies:
  left:DY.usage{DY.DhKey? left} ->
  right:DY.usage{DY.DhKey? right} ->
  Lemma
    (requires unknown_peer_dh_usage left =!= DY.NoUsage)
    (ensures
      known_peer_dh_usage left right ==
      unknown_peer_dh_usage left)
let unknown_peer_dh_usage_implies left right =
  match left with
  | DY.DhKey "TLS13.X25519Ephemeral" _ -> ()
  | _ -> ()

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

val tls_crypto_usages: DY.crypto_usages
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
