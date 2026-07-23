module TLS13.Symbolic.Profile

(*
 * Fixed TLS 1.3 profile used by the symbolic development.
 *
 * This module is deliberately only a classifier: it names the one cipher
 * suite, group, and signature scheme modeled by the proof and recognizes
 * compatible endpoint configurations.  It does not prove that an arbitrary
 * execution negotiated this profile; product realizations carry that
 * obligation explicitly.
 *)

module SM = TLS13.Spec.StateMachine
module T = TLS13.Types

(* The only modeled cipher suite: ChaCha20-Poly1305 with SHA-256. *)
let profile_cipher_suite : T.cipher_suite =
  T.TLS_CHACHA20_POLY1305_SHA256

(* The only modeled key-exchange group: X25519. *)
let profile_named_group : T.named_group =
  T.X25519

(* The only modeled CertificateVerify algorithm: RSA-PSS-RSAE-SHA256. *)
let profile_signature_scheme : T.signature_scheme =
  T.Rsa_pss_rsae_sha256

(* Decide whether a concrete cipher-suite identifier is the profile suite. *)
let is_profile_cipher_suite (suite:T.cipher_suite) : bool =
  match suite with
  | T.TLS_CHACHA20_POLY1305_SHA256 -> true
  | _ -> false

(* Decide whether a concrete named-group identifier is X25519. *)
let is_profile_named_group (group:T.named_group) : bool =
  match group with
  | T.X25519 -> true
  | _ -> false

(* Decide whether a signature identifier is RSA-PSS-RSAE-SHA256. *)
let is_profile_signature_scheme (scheme:T.signature_scheme) : bool =
  match scheme with
  | T.Rsa_pss_rsae_sha256 -> true
  | _ -> false

(*
 * Classify a client configuration.
 *
 * The role and offered cipher/signature lists are fixed exactly.  A client has
 * no embedded server configuration; its requested name remains in the normal
 * connection configuration.
 *)
let client_config_in_profile (cfg:SM.connection_config) : prop =
  cfg.SM.config_role == SM.ClientEndpoint /\
  cfg.SM.config_cipher_suites == [profile_cipher_suite] /\
  cfg.SM.config_signature_schemes == [profile_signature_scheme] /\
  (match cfg.SM.config_server with
   | None -> True
   | Some _ -> False)

(*
 * Classify a server configuration.
 *
 * The outer role and algorithm lists, and the embedded server's allowed
 * signature, cipher, and group lists, must all be the singleton profile lists.
 *)
let server_config_in_profile (cfg:SM.connection_config) : prop =
  cfg.SM.config_role == SM.ServerEndpoint /\
  cfg.SM.config_cipher_suites == [profile_cipher_suite] /\
  cfg.SM.config_signature_schemes == [profile_signature_scheme] /\
  (match cfg.SM.config_server with
   | None -> False
   | Some server ->
     server.SM.server_allowed_signature_schemes ==
       [profile_signature_scheme] /\
     server.SM.server_supported_cipher_suites == [profile_cipher_suite] /\
     server.SM.server_supported_groups == [profile_named_group])

(*
 * Check one requested hostname against the server's SNI policy.
 *
 * An absent policy accepts every name; a present policy accepts only its
 * configured hostname.  This is not an X.509 validation predicate.
 *)
let server_accepts_name
  (server:SM.server_config)
  (name:T.hostname)
  : prop =
  match server.SM.server_sni_policy with
  | None -> True
  | Some expected -> expected == name

(*
 * Relate a client/server configuration pair.
 *
 * Both endpoints must be individually in profile and the server must accept
 * the client's requested name.  Product refinement currently consumes the
 * individual predicates, so cross-endpoint SNI compatibility must be supplied
 * separately by clients of the proof.
 *)
let config_pair_in_profile
  (client:SM.connection_config)
  (server:SM.connection_config)
  : prop =
  client_config_in_profile client /\
  server_config_in_profile server /\
  (match server.SM.config_server with
   | None -> False
   | Some server_config ->
     server_accepts_name server_config client.SM.config_server_name)
