module TLS13.Wire.Spec.Reveal.Handshake

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module LP = LowParse.Spec
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV = TLS13.Wire.Generated.CertificateVerify
module GCS = TLS13.Wire.Generated.CipherSuite
module GSS = TLS13.Wire.Generated.SignatureScheme
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GNG = TLS13.Wire.Generated.NamedGroup
module GSN = TLS13.Wire.Generated.ServerName
module GHN = TLS13.Wire.Generated.HostName
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GESN = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GESA = TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
module GESK = TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
module GESV = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
module GESG = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GPN = TLS13.Wire.Generated.ProtocolName
module GCE = TLS13.Wire.Generated.CertificateEntry

(* ---- one-step reveals of the ClientHello scanners (delegated to WS) ------- *)

let lemma_reveal_synth_cipher_suites_nil () = WS.lemma_synth_cipher_suites_nil ()

let lemma_reveal_synth_cipher_suites_cons c tl = WS.lemma_synth_cipher_suites_cons c tl

let lemma_reveal_synth_sig_schemes_nil () = WS.lemma_synth_sig_schemes_nil ()

let lemma_reveal_synth_sig_schemes_cons s tl = WS.lemma_synth_sig_schemes_cons s tl

let lemma_reveal_ch_server_name_nil () = WS.lemma_ch_server_name_nil ()

let lemma_reveal_ch_server_name_host h tl = WS.lemma_ch_server_name_host h tl

let lemma_reveal_key_exchange_to_key32 ke = WS.lemma_key_exchange_to_key32 ke

let lemma_reveal_ch_find_key_share_nil () = WS.lemma_ch_find_key_share_nil ()

let lemma_reveal_ch_find_key_share_cons e tl = WS.lemma_ch_find_key_share_cons e tl

let lemma_reveal_ch_extensions_nil sn ks sv ss = WS.lemma_ch_extensions_nil sn ks sv ss

let lemma_reveal_ch_extensions_cons_sn snl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_sn snl tl sn ks sv ss

let lemma_reveal_ch_extensions_cons_sg sgl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_sg sgl tl sn ks sv ss

let lemma_reveal_ch_extensions_cons_sa ssl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_sa ssl tl sn ks sv ss

let lemma_reveal_ch_extensions_cons_ks kscl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_ks kscl tl sn ks sv ss

let lemma_reveal_ch_extensions_cons_sv svl tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_sv svl tl sn ks sv ss

let lemma_reveal_ch_extensions_cons_other e tl sn ks sv ss =
  WS.lemma_ch_extensions_cons_other e tl sn ks sv ss

let lemma_synth_signature_scheme s = WS.lemma_synth_signature_scheme s

let lemma_synth_client_hello_reveal c = WS.lemma_synth_client_hello c

(* ---- per-constructor reveals of [handshake_synth] (delegated to WS) ------- *)

let lemma_handshake_synth_finished b = WS.lemma_synth_handshake_msg_finished b

let lemma_handshake_synth_key_update b = WS.lemma_synth_handshake_msg_key_update b

let lemma_handshake_synth_client_hello b = WS.lemma_synth_handshake_msg_client_hello b

let lemma_handshake_synth_certificate b = WS.lemma_synth_handshake_msg_certificate b

let lemma_handshake_synth_certificate_verify b =
  WS.lemma_synth_handshake_msg_certificate_verify b

let lemma_handshake_synth_encrypted_extensions b =
  WS.lemma_synth_handshake_msg_encrypted_extensions b

let lemma_handshake_synth_server_hello_hrr b shb =
  WS.lemma_synth_handshake_msg_server_hello_hrr b shb

let lemma_handshake_synth_server_hello_sh b sf =
  WS.lemma_synth_handshake_msg_server_hello_sh b sf

let lemma_handshake_synth_server_hello_bad_version b =
  WS.lemma_synth_handshake_msg_server_hello_bad_version b

(* ---- pure list-suffix helper -------------------------------------------- *)

let rec list_drop (#a:Type) (n:nat) (l:list a) : Tot (list a) (decreases n) =
  if n <= 0 then l
  else (match l with
        | [] -> []
        | _ :: tl -> list_drop (n - 1) tl)

let lemma_list_drop_zero (#a:Type) (l:list a) = ()

let lemma_list_drop_cons_succ (#a:Type) (hd:a) (tl:list a) (n:nat)
  : Lemma (ensures list_drop (n + 1) (hd :: tl) == list_drop n tl)
  = ()

let lemma_list_index_cons_succ (#a:Type) (hd:a) (tl:list a) (i:nat)
  : Lemma (requires i < FStar.List.Tot.length tl)
          (ensures FStar.List.Tot.index (hd :: tl) (i + 1) == FStar.List.Tot.index tl i)
  = ()

let rec lemma_list_drop_index (#a:Type) (l:list a) (i:nat)
  : Lemma (requires i < FStar.List.Tot.length l)
          (ensures list_drop i l == FStar.List.Tot.index l i :: list_drop (i + 1) l)
          (decreases i)
  = if i <= 0 then
      (match l with
       | hd :: tl -> lemma_list_drop_cons_succ hd tl 0)
    else
      (match l with
       | hd :: tl ->
         lemma_list_drop_index tl (i - 1);
         lemma_list_drop_cons_succ hd tl (i - 1);
         lemma_list_index_cons_succ hd tl (i - 1);
         lemma_list_drop_cons_succ hd tl i)

let rec lemma_list_drop_length (#a:Type) (l:list a)
  : Lemma (ensures list_drop (FStar.List.Tot.length l) l == [])
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> lemma_list_drop_length tl

(* ---- ServerHello key-share scan ----------------------------------------- *)

let rec reveal_sh_key_share
  (l:list GESH.extensionServerHello)
  (saw_supported_versions:bool)
  (key_share:option (B.bytes_of_len 32))
  : GTot (option (B.bytes_of_len 32)) (decreases l)
  = match l with
    | [] -> if saw_supported_versions then key_share else None
    | e :: tl ->
      (match e with
       | GESH.Extension_data_supported_versions sv ->
         if GPV.TLS_1p3? sv then reveal_sh_key_share tl true key_share else None
       | GESH.Extension_data_key_share kse ->
         if GNG.X25519? kse.GKSE.group
         then (match reveal_key_exchange_to_key32 kse.GKSE.key_exchange with
               | Some k -> reveal_sh_key_share tl saw_supported_versions (Some k)
               | None -> None)
         else None
       | _ -> reveal_sh_key_share tl saw_supported_versions key_share)

let lemma_sh_key_share_nil saw_supported_versions key_share = ()

let lemma_sh_key_share_cons e tl saw_supported_versions key_share = ()

(* ---- certificate chain helpers ------------------------------------------ *)

let rec reveal_synth_cert_chain (l:list GCE.certificateEntry)
  : GTot (list B.bytes) (decreases l)
  = match l with
    | [] -> []
    | e :: tl -> (e.GCE.cert_data <: B.bytes) :: reveal_synth_cert_chain tl

let rec reveal_cert_chain_total_bytes (chain:list B.bytes)
  : GTot nat (decreases chain)
  = match chain with
    | [] -> 0
    | x :: tl -> B.length x + reveal_cert_chain_total_bytes tl

let lemma_synth_cert_chain_nil () = ()

let lemma_synth_cert_chain_cons e tl = ()

let rec lemma_synth_cert_chain_length l =
  match l with
  | [] -> ()
  | _ :: tl -> lemma_synth_cert_chain_length tl

let lemma_cert_chain_total_bytes_nil () = ()

let rec lemma_cert_chain_total_bytes_snoc chain x =
  match chain with
  | [] -> ()
  | _ :: tl -> lemma_cert_chain_total_bytes_snoc tl x

let rec lemma_cert_chain_total_bytes_prefix_le prefix x rest =
  match prefix with
  | [] -> ()
  | _ :: tl -> lemma_cert_chain_total_bytes_prefix_le tl x rest

(* ---- EncryptedExtensions ALPN scan -------------------------------------- *)

let reveal_alpn_first_name pnl =
  match (pnl <: list GPN.protocolName) with
  | [] -> None
  | n :: _ -> Some (n <: B.bytes)

let rec reveal_synth_encrypted_extensions (l:list GEEE.extensionEncryptedExtensions)
  : GTot (option (option B.bytes)) (decreases l)
  = match l with
    | [] -> Some None
    | e :: tl ->
      (match e with
       | GEEE.Extension_data_application_layer_protocol_negotiation pnl ->
         (match reveal_alpn_first_name pnl with
          | Some name -> Some (Some name)
          | None -> None)
       | _ -> reveal_synth_encrypted_extensions tl)

let lemma_synth_ee_nil () = ()

let lemma_synth_ee_cons_non_alpn e tl = ()

let lemma_synth_ee_cons_alpn pnl tl = ()

let lemma_alpn_first_name_index0 pnl = ()

(* ---- byte-level [parse_tls_message] arm reveals (delegated to WS) -------- *)

let lemma_ptm_alert fragment = WS.lemma_ptm_alert fragment

let lemma_ptm_handshake_some fragment v m = WS.lemma_ptm_handshake_some fragment v m

let lemma_ptm_handshake_fallback fragment = WS.lemma_ptm_handshake_fallback fragment

let lemma_parse_key_update_def input = WS.lemma_parse_key_update_def input

let lemma_parse_ignored_post_handshake_def input =
  WS.lemma_parse_ignored_post_handshake_def input

let lemma_parse_handshake_none_of_lp_none fragment =
  WS.lemma_parse_handshake_none_of_lp_none fragment

let lemma_parse_handshake_none_of_synth_none fragment v consumed =
  WS.lemma_parse_handshake_none_of_synth_none fragment v consumed
