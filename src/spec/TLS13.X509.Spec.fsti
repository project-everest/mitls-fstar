module TLS13.X509.Spec

module B = TLS13.Bytes
module T = TLS13.Types
module C = TLS13.Crypto.Spec

type certificate = B.bytes
type cert_chain = list certificate
type trust_store = {
  anchors: B.bytes;
}
type validation_time = {
  seconds_since_epoch: nat;
}

type peer_identity = {
  validated_hostname: T.hostname;
  leaf_public_key: C.public_key;
  permitted_signature_schemes: list T.signature_scheme;
}

val validate_chain:
  hostname:T.hostname ->
  validation_time:validation_time ->
  trust_store:trust_store ->
  certs:cert_chain ->
  Tot (option peer_identity)
