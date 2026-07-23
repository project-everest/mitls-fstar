module TLS13.Symbolic.Profile

module SM = TLS13.Spec.StateMachine
module T = TLS13.Types

let profile_cipher_suite : T.cipher_suite =
  T.TLS_CHACHA20_POLY1305_SHA256

let profile_named_group : T.named_group =
  T.X25519

let profile_signature_scheme : T.signature_scheme =
  T.Rsa_pss_rsae_sha256

let is_profile_cipher_suite (suite:T.cipher_suite) : bool =
  match suite with
  | T.TLS_CHACHA20_POLY1305_SHA256 -> true
  | _ -> false

let is_profile_named_group (group:T.named_group) : bool =
  match group with
  | T.X25519 -> true
  | _ -> false

let is_profile_signature_scheme (scheme:T.signature_scheme) : bool =
  match scheme with
  | T.Rsa_pss_rsae_sha256 -> true
  | _ -> false

let client_config_in_profile (cfg:SM.connection_config) : prop =
  cfg.SM.config_role == SM.ClientEndpoint /\
  cfg.SM.config_cipher_suites == [profile_cipher_suite] /\
  cfg.SM.config_signature_schemes == [profile_signature_scheme] /\
  (match cfg.SM.config_server with
   | None -> True
   | Some _ -> False)

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

let server_accepts_name
  (server:SM.server_config)
  (name:T.hostname)
  : prop =
  match server.SM.server_sni_policy with
  | None -> True
  | Some expected -> expected == name

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
