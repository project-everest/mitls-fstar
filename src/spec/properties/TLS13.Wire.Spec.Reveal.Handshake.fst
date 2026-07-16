module TLS13.Wire.Spec.Reveal.Handshake

friend TLS13.Wire.Spec

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
module GFin = TLS13.Wire.Generated.Finished

(* ---- one-step reveals of the ClientHello scanners (delegated to WS) ------- *)

let lemma_reveal_synth_cipher_suites_nil () = WS.lemma_synth_cipher_suites_nil ()

let lemma_reveal_synth_cipher_suites_cons c tl = WS.lemma_synth_cipher_suites_cons c tl

let lemma_reveal_synth_sig_schemes_nil () = WS.lemma_synth_sig_schemes_nil ()

let lemma_reveal_synth_sig_schemes_cons s tl = WS.lemma_synth_sig_schemes_cons s tl

let rec lemma_reveal_synth_cipher_suites_id (l:list GCS.cipherSuite)
  : Lemma (ensures reveal_synth_cipher_suites l == l) (decreases l)
  = match l with
    | [] -> lemma_reveal_synth_cipher_suites_nil ()
    | c :: tl ->
      lemma_reveal_synth_cipher_suites_cons c tl;
      WS.lemma_synth_cipher_suite c;
      lemma_reveal_synth_cipher_suites_id tl

let rec lemma_reveal_synth_sig_schemes_id (l:list GSS.signatureScheme)
  : Lemma (ensures reveal_synth_sig_schemes l == l) (decreases l)
  = match l with
    | [] -> lemma_reveal_synth_sig_schemes_nil ()
    | s :: tl ->
      lemma_reveal_synth_sig_schemes_cons s tl;
      WS.lemma_synth_signature_scheme s;
      lemma_reveal_synth_sig_schemes_id tl

let lemma_reveal_ch_server_name_nil () = WS.lemma_ch_server_name_nil ()

let lemma_reveal_ch_server_name_host h tl = WS.lemma_ch_server_name_host h tl

let lemma_reveal_key_exchange_to_key32 ke = WS.lemma_key_exchange_to_key32 ke

let lemma_reveal_ch_find_key_share_nil () = WS.lemma_ch_find_key_share_nil ()

let lemma_reveal_ch_find_key_share_cons e tl = WS.lemma_ch_find_key_share_cons e tl

let lemma_reveal_kse_list_find_x25519_nil () = ()

let lemma_reveal_kse_list_find_x25519_cons e tl = ()

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

let lemma_reveal_clientHello_representable_scan c =
  WS.lemma_clientHello_representable_scan c

let lemma_reveal_ch_extensions_connect c =
  WS.lemma_ch_extensions_connect c

let lemma_reveal_ch_extensions_connect_valid c =
  lemma_reveal_ch_extensions_connect c;
  match reveal_ch_extensions (c.GCH.extensions <: list GECH.extensionClientHello)
                             None None false [] with
  | Some (sn, Some k, _, ss) ->
    (match TLS13.Wire.Semantics.clientHello_sig_algs c with
     | Some sas -> lemma_reveal_synth_sig_schemes_id sas
     | None -> ())
  | _ -> ()

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
  (decided:bool)
  (key_share:option (B.bytes_of_len 32))
  : GTot (option (B.bytes_of_len 32)) (decreases l)
  = if decided then key_share
    else match l with
      | [] -> None
      | e :: tl ->
        (match e with
         | GESH.Extension_data_key_share kse ->
           reveal_sh_key_share tl true
             (if GNG.X25519? kse.GKSE.group
              then reveal_key_exchange_to_key32 kse.GKSE.key_exchange
              else None)
         | _ -> reveal_sh_key_share tl false None)

let lemma_sh_key_share_nil decided key_share = ()

let lemma_sh_key_share_cons e tl decided key_share = ()

let lemma_sh_key_share_decided l key_share = ()

let rec lemma_reveal_sh_key_share_connect l =
  match l with
  | [] -> ()
  | GESH.Extension_data_key_share kse :: tl ->
      lemma_sh_key_share_cons (GESH.Extension_data_key_share kse) tl false None;
      lemma_sh_key_share_decided tl
        (if GNG.X25519? kse.GKSE.group
         then reveal_key_exchange_to_key32 kse.GKSE.key_exchange
         else None);
      lemma_reveal_key_exchange_to_key32 kse.GKSE.key_exchange
  | e :: tl ->
      lemma_sh_key_share_cons e tl false None;
      lemma_reveal_sh_key_share_connect tl

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

(* ---- Certificate representability connect (scan <-> synth) --------------- *)

(* [reveal_synth_cert_chain] and [Sem.cert_entries_data] are the same fold over
   the same field ([cert_data]); they differ only by which module names the
   [CertificateEntry] type.  Prove them equal by induction. *)
let rec lemma_reveal_cert_chain_eq_entries (l:list GCE.certificateEntry)
  : Lemma (ensures reveal_synth_cert_chain l == TLS13.Wire.Semantics.cert_entries_data l)
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: tl -> lemma_reveal_cert_chain_eq_entries tl

(* [reveal_cert_chain_total_bytes] and [WS.cert_chain_total_bytes] are the same
   fold; the latter is abstract, so unfold it via its revealed recursion. *)
let rec lemma_reveal_total_bytes_eq (ch:list B.bytes)
  : Lemma (ensures reveal_cert_chain_total_bytes ch == WS.cert_chain_total_bytes ch)
          (decreases ch)
  = match ch with
    | [] -> WS.lemma_cert_chain_total_bytes_nil ()
    | x :: tl -> WS.lemma_cert_chain_total_bytes_cons x tl;
                 lemma_reveal_total_bytes_eq tl

let lemma_handshake_synth_certificate_none b =
  lemma_handshake_synth_certificate b;
  WS.lemma_certificate_representable (b <: GCert.certificate);
  lemma_reveal_cert_chain_eq_entries (b.GCert.certificate_list);
  lemma_reveal_total_bytes_eq (reveal_synth_cert_chain (b.GCert.certificate_list))

let lemma_handshake_synth_certificate_some b =
  lemma_handshake_synth_certificate b;
  WS.lemma_certificate_representable (b <: GCert.certificate);
  lemma_reveal_cert_chain_eq_entries (b.GCert.certificate_list);
  lemma_reveal_total_bytes_eq (reveal_synth_cert_chain (b.GCert.certificate_list))

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

let lemma_alpn_first_name_nil pnl = ()

(* Bridge: when the EE ALPN scan succeeds ([Some?]), its payload equals the
   first-wins [Sem.encryptedExtensions_alpn], and the ALPN name (if any) is
   <= 255 bytes (wire-bounded [protocolName]) — i.e. the EE is representable. *)
let rec lemma_reveal_ee_connect_list (l:list GEEE.extensionEncryptedExtensions)
  : Lemma
    (requires Some? (reveal_synth_encrypted_extensions l))
    (ensures
      Some?.v (reveal_synth_encrypted_extensions l)
        == TLS13.Wire.Semantics.ee_find_alpn l /\
      (match TLS13.Wire.Semantics.ee_find_alpn l with
       | Some a -> B.length a <= M.client_hello_server_name_max_len
       | None -> true))
    (decreases l)
  = match l with
    | [] -> lemma_synth_ee_nil ()
    | e :: tl ->
      (match e with
       | GEEE.Extension_data_application_layer_protocol_negotiation pnl ->
         lemma_synth_ee_cons_alpn pnl tl;
         (match (pnl <: list GPN.protocolName) with
          | [] -> lemma_alpn_first_name_nil pnl
          | p :: _ -> lemma_alpn_first_name_index0 pnl)
       | _ ->
         lemma_synth_ee_cons_non_alpn e tl;
         lemma_reveal_ee_connect_list tl)

let lemma_reveal_ee_connect b =
  lemma_reveal_ee_connect_list (b <: list GEEE.extensionEncryptedExtensions)

(* ---- byte-level [parse_tls_message] arm reveals (delegated to WS) -------- *)

(* [lemma_ptm_alert] is intentionally NOT defined here: the branch provides it in
   TLS13.Wire.Spec.Reveal.Alert (re-exported by the aggregator).  [WS] does not
   expose a [lemma_ptm_alert]/[lemma_ptm_handshake_some] (the parse-direction
   [parse_tls_message] arm reveals live in this Reveal layer, not in Wire.Spec),
   so [lemma_ptm_handshake_some] is discharged directly here via [friend
   TLS13.Wire.Spec] (the [parse_tls_message] . [parse_handshake] definitional
   unfolding). *)
let lemma_ptm_handshake_some fragment v m = ()

let lemma_ptm_handshake_fallback fragment = WS.lemma_ptm_handshake_fallback fragment

let lemma_parse_key_update_def input = WS.lemma_parse_key_update_def input

let lemma_parse_ignored_post_handshake_def input =
  WS.lemma_parse_ignored_post_handshake_def input

let lemma_parse_handshake_none_of_lp_none fragment =
  WS.lemma_parse_handshake_none_of_lp_none fragment

let lemma_parse_handshake_none_of_synth_none fragment v consumed =
  WS.lemma_parse_handshake_none_of_synth_none fragment v consumed

(* ---- build-direction serialize reveals (branch-local) ------------------- *)
(* Definitional unfolding of [WS.serialize_handshake]'s per-constructor match
   arm, transparent via [friend TLS13.Wire.Spec]; consumed by the impl
   serializers (TLS13.Impl.Serializer.Handshake). *)

let lemma_serialize_handshake_client_hello ch = ()
let lemma_serialize_handshake_server_hello sh = ()
let lemma_serialize_handshake_encrypted_extensions ee = ()
let lemma_serialize_handshake_certificate cert = ()
let lemma_serialize_handshake_certificate_verify cv = ()
let lemma_serialize_handshake_finished fin = ()
