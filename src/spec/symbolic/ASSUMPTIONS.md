# Symbolic proof assumption ledger

The symbolic proof is conditional on execution-local bridge witnesses. It does
not assume a global injective interpretation of concrete bytes, hashes, HKDF,
signatures, or ciphertexts.

| Assumption | Source predicate | Consumers |
| --- | --- | --- |
| Honest fresh values have fresh `RandGen` witnesses | `fresh_value_bridge` | Product lifting, session injectivity |
| X25519 calls have `DhPub`/`Dh` witnesses | `x25519_public_bridge`, `x25519_shared_bridge` | Key-schedule lifting, shared-secret secrecy |
| SHA-256 calls have `Hash` witnesses | `hash_bridge` | Transcript and key-schedule lifting |
| HKDF calls have exact `KdfExtract`/`KdfExpand` witnesses | `hkdf_extract_bridge`, `hkdf_expand_label_bridge` | Key-schedule lifting, traffic-secret secrecy |
| HMAC-SHA256 calls have `Mac` witnesses | `hmac_bridge` | Finished lifting and origin |
| Accepted RSA-PSS signatures have `Sign`/`Vk` witnesses | `signature_bridge` | CertificateVerify lifting and origin |
| Server names bind to trusted leaf verification keys | `x509_identity_bridge` | Server-identity authentication |
| ChaCha20-Poly1305 calls have `AeadEnc` witnesses | `aead_seal_bridge`, `aead_open_bridge` | Record lifting, integrity, confidentiality |

Concrete functional correctness facts remain in `TLS13.Crypto.Spec` and the
existing state-machine/serializer lemmas. Those facts are reused only for
correctness and projection; they are not treated as cryptographic security
theorems.
