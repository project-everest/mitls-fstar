module TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module LP = LowParse.Spec
module GFinished = TLS13.Wire.Generated.Finished
module GCV = TLS13.Wire.Generated.CertificateVerify
module GSS = TLS13.Wire.Generated.SignatureScheme
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GSH = TLS13.Wire.Generated.ServerHello
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GCS = TLS13.Wire.Generated.CipherSuite
module GCert = TLS13.Wire.Generated.Certificate
module GCE = TLS13.Wire.Generated.CertificateEntry
module GCH = TLS13.Wire.Generated.ClientHello
module GHS = TLS13.Wire.Generated.Handshake
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GECH = TLS13.Wire.Generated.ExtensionClientHello
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GNG = TLS13.Wire.Generated.NamedGroup
module GSN = TLS13.Wire.Generated.ServerName
module M = TLS13.Messages
module ML = FStar.Math.Lemmas
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module Sem = TLS13.Wire.Semantics
module L = FStar.List.Tot
module GHN = TLS13.Wire.Generated.HostName
module GESN = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GESA = TLS13.Wire.Generated.ExtensionClientHello_extension_data_signature_algorithms
module GESK = TLS13.Wire.Generated.ExtensionClientHello_extension_data_key_share
module GESV = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_versions
module GESG = TLS13.Wire.Generated.ExtensionClientHello_extension_data_supported_groups
module SHC = TLS13.ServerHello.Checks

let byte (n:nat) : B.byte = U8.uint_to_t (n % 256)

let nat_of_byte (b:B.byte) : GTot nat = U8.v b

let lemma_byte_v (n:nat)
  : Lemma (nat_of_byte (byte n) == n % 256)
=
  U8.vu_inv (n % 256)

let u16 (n:nat) : GTot B.bytes =
  B.of_list [byte (n / 256); byte n]

let u24 (n:nat) : GTot B.bytes =
  B.of_list [byte (n / 65536); byte (n / 256); byte n]

let u8 (n:nat) : GTot B.bytes = B.singleton (byte n)

let append3 (a b c:B.bytes) : GTot B.bytes =
  B.append a (B.append b c)

let read_u16 (input:B.bytes) (pos:nat{pos + 2 <= B.length input}) : GTot (n:nat{n < 65536}) =
  nat_of_byte (Seq.index input pos) * 256 +
  nat_of_byte (Seq.index input (pos + 1))

let lemma_read_u16_u16 (n:nat{n <= 65535})
  : Lemma (read_u16 (u16 n) 0 == n)
=
  lemma_byte_v (n / 256);
  lemma_byte_v n;
  ML.lemma_div_mod n 256;
  ML.lemma_mod_lt n 256;
  ML.lemma_div_lt n 16 8;
  assert (n / 256 < 256);
  ML.small_mod (n / 256) 256;
  assert ((n / 256) % 256 == n / 256);
  assert (n == 256 * (n / 256) + n % 256);
  assert (read_u16 (u16 n) 0 == n)

let lemma_read_u16_definition
  (input:B.bytes)
  (pos:nat{pos + 2 <= B.length input})
  : Lemma (read_u16 input pos ==
           U8.v (Seq.index input pos) * 256 +
           U8.v (Seq.index input (pos + 1)))
=
  ()

let read_u24 (input:B.bytes) (pos:nat{pos + 3 <= B.length input}) : GTot nat =
  nat_of_byte (Seq.index input pos) * 65536 +
  nat_of_byte (Seq.index input (pos + 1)) * 256 +
  nat_of_byte (Seq.index input (pos + 2))

let lemma_read_u24_one (input:B.bytes{B.length input >= 4}) = ()

let take_range
  (input:B.bytes)
  (pos:nat)
  (len:nat)
  : GTot (option (b:B.bytes{B.length b == len})) =
  if pos + len <= B.length input
  then Some (Seq.slice input pos (pos + len))
  else None

let content_type_to_byte (ct:T.content_type) : GTot nat =
  match ct with
  | T.Invalid -> 0
  | T.Change_cipher_spec -> 20
  | T.Alert -> 21
  | T.Handshake -> 22
  | T.Application_data -> 23

let content_type_of_byte (b:B.byte) : GTot (option T.content_type) =
  match nat_of_byte b with
  | 0 -> Some T.Invalid
  | 20 -> Some T.Change_cipher_spec
  | 21 -> Some T.Alert
  | 22 -> Some T.Handshake
  | 23 -> Some T.Application_data
  | _ -> None

let alert_description_to_byte (alert:T.alert_description) : GTot nat =
  match alert with
  | T.Close_notify -> 0
  | T.Unexpected_message -> 10
  | T.Bad_record_mac -> 20
  | T.Handshake_failure -> 40
  | T.Decode_error -> 50
  | T.Decrypt_error -> 51
  | T.Protocol_version -> 70
  | T.Unsupported_extension -> 110
  | T.Certificate_unknown -> 46
  | T.Illegal_parameter -> 47

let alert_description_of_byte (b:B.byte) : GTot (option T.alert_description) =
  match nat_of_byte b with
  | 0 -> Some T.Close_notify
  | 10 -> Some T.Unexpected_message
  | 20 -> Some T.Bad_record_mac
  | 40 -> Some T.Handshake_failure
  | 50 -> Some T.Decode_error
  | 51 -> Some T.Decrypt_error
  | 70 -> Some T.Protocol_version
  | 110 -> Some T.Unsupported_extension
  | 46 -> Some T.Certificate_unknown
  | 47 -> Some T.Illegal_parameter
  | _ -> None

let parse_ignored_post_handshake (input:B.bytes) : GTot (option B.bytes) =
  if B.length input < 4 then None
  else
    let msg_type = nat_of_byte (Seq.index input 0) in
    let body_len = read_u24 input 1 in
    if msg_type == 4 && body_len + 4 == B.length input
    then Some (Seq.slice input 4 (body_len + 4))
    else None

let lemma_parse_ignored_post_handshake_def input = ()

let parse_key_update (input:B.bytes) : GTot (option M.key_update_request) =
  if B.length input == 5 &&
     nat_of_byte (Seq.index input 0) == 24 &&
     read_u24 input 1 == 1
  then
    let request = nat_of_byte (Seq.index input 4) in
    if request == 0 then Some M.UpdateNotRequested
    else if request == 1 then Some M.UpdateRequested
    else None
  else None

let lemma_parse_key_update_def input =
  if B.length input = 5 then lemma_read_u24_one input else ()

// Structural dispatch from a parsed QuackyDucky [handshake] record onto the high
// [M.handshake_msg], which now carries the generated wire records directly.
//
// Phase 3b read-direction FIX: the dispatch is VALIDATING.  A parsed body maps to
// [Some m] iff [m] is representable in the fixed-size impl-layer storage, i.e. it
// satisfies EXACTLY the field-support conditions the TLS13.Impl.Messages
// [is_valid_*] predicates enforce (stated over the TLS13.Wire.Semantics accessors
// [Sem.*]).  A parseable-but-unsupported message (no X25519 key share, no/oversized
// signature_algorithms, oversized certificate chain, ...) maps to [None] so that
// the Parser's [.fsti] contract ([Some l -> is_valid l m /\ parse == Some m];
// [None -> parse == None]) is satisfiable.  Profile-relevant fields are read via
// the [Sem.*] accessors and transcript exactness is the generated parse/serialize
// round-trip (see lemma_parse_tls_message_round_trip).
//
// A magic-random HelloRetryRequest is mapped to the dedicated M.HelloRetryRequest
// arm (it is not a normal ServerHello); key_update / new_session_ticket are not
// handshake messages in this profile and are rejected.
//
// NOTE the [max_alpn_len] bound (255) coincides numerically with
// [M.client_hello_server_name_max_len]; both mirror the impl-layer storage maxima.

(* --- cipher-suite / signature-scheme synths: identity on the shared enums. --- *)

let synth_cipher_suite (c:GCS.cipherSuite) : GTot T.cipher_suite = c

let lemma_synth_cipher_suite c = ()

let rec synth_cipher_suites (l:list GCS.cipherSuite)
  : GTot (list T.cipher_suite) (decreases l)
  = match l with
    | [] -> []
    | c :: tl -> synth_cipher_suite c :: synth_cipher_suites tl

let lemma_synth_cipher_suites_nil () = ()

let lemma_synth_cipher_suites_cons c tl = ()

let synth_signature_scheme (s:GSS.signatureScheme) : GTot T.signature_scheme = s

let rec synth_sig_schemes (l:list GSS.signatureScheme)
  : GTot (list T.signature_scheme) (decreases l)
  = match l with
    | [] -> []
    | s :: tl -> synth_signature_scheme s :: synth_sig_schemes tl

let lemma_synth_sig_schemes_nil () = ()

let lemma_synth_sig_schemes_cons s tl = ()

(* --- ClientHello field scanners --- *)

let key_exchange_to_key32 (ke:GKSE.keyShareEntry_key_exchange) : GTot (option (B.bytes_of_len 32)) =
  let b : B.bytes = (ke <: B.bytes) in
  if B.length b = 32 then Some (b <: B.bytes_of_len 32) else None

let lemma_key_exchange_to_key32 ke = ()

let rec ch_find_key_share (l:list GKSE.keyShareEntry)
  : GTot (option (B.bytes_of_len 32)) (decreases l) =
  match l with
  | [] -> None
  | e :: tl ->
    if GNG.X25519? e.GKSE.group
    then (match key_exchange_to_key32 e.GKSE.key_exchange with
          | Some k -> Some k
          | None -> ch_find_key_share tl)
    else ch_find_key_share tl

let lemma_ch_find_key_share_nil () = ()

let lemma_ch_find_key_share_cons e tl = ()

let ch_server_name (snl:list GSN.serverName) : GTot (option T.hostname) =
  match snl with
  | (GSN.Name_host_name h) :: _ -> Some ((h <: B.bytes) <: T.hostname)
  | _ -> None

let lemma_ch_server_name_nil () = ()

let lemma_ch_server_name_host h tl = ()

(* Commit-on-first scan of a ClientHello extension list, accumulating
   (server_name, key_share, saw_supported_versions, sig_schemes).  A field is
   only written when still unset (so the first offered value wins, matching the
   first-wins TLS13.Wire.Semantics finders). *)
let rec ch_extensions
  (l:list GECH.extensionClientHello)
  (server_name:option T.hostname)
  (key_share:option (B.bytes_of_len 32))
  (saw_supported_versions:bool)
  (signature_schemes:list T.signature_scheme)
  : GTot (option (option T.hostname & option (B.bytes_of_len 32) & bool & list T.signature_scheme))
       (decreases l)
  =
  match l with
  | [] ->
    if saw_supported_versions
    then Some (server_name, key_share, saw_supported_versions, signature_schemes)
    else None
  | e :: tl ->
    (match e with
     | GECH.Extension_data_server_name snl ->
       if Some? server_name
       then ch_extensions tl server_name key_share saw_supported_versions signature_schemes
       else (match ch_server_name snl with
             | Some name -> ch_extensions tl (Some name) key_share saw_supported_versions signature_schemes
             | None -> None)
     | GECH.Extension_data_supported_groups _ ->
       ch_extensions tl server_name key_share saw_supported_versions signature_schemes
     | GECH.Extension_data_signature_algorithms ssl ->
       ch_extensions tl server_name key_share saw_supported_versions
         (if Nil? signature_schemes then synth_sig_schemes ssl else signature_schemes)
     | GECH.Extension_data_key_share kscl ->
       if Some? key_share
       then ch_extensions tl server_name key_share saw_supported_versions signature_schemes
       else (match Sem.kse_list_find_x25519 (kscl <: list GKSE.keyShareEntry) with
             | Some raw ->
               if B.length raw = 32
               then ch_extensions tl server_name (Some (raw <: B.bytes_of_len 32)) saw_supported_versions signature_schemes
               else None
             | None -> None)
     | GECH.Extension_data_supported_versions svl ->
       if List.Tot.mem GPV.TLS_1p3 svl
       then ch_extensions tl server_name key_share true signature_schemes
       else None
     | _ -> ch_extensions tl server_name key_share saw_supported_versions signature_schemes)

let lemma_ch_extensions_nil sn ks sv ss = ()

let lemma_ch_extensions_cons_sn snl tl sn ks sv ss = ()

let lemma_ch_extensions_cons_sg sgl tl sn ks sv ss = ()

let lemma_ch_extensions_cons_sa ssl tl sn ks sv ss = ()

let lemma_ch_extensions_cons_ks kscl tl sn ks sv ss = ()

let lemma_ch_extensions_cons_sv svl tl sn ks sv ss = ()

let lemma_ch_extensions_cons_other e tl sn ks sv ss = ()

(* ---- One-step unfolding of the first-wins Sem finders on a cons (used to
       prove the connection lemmas below).  Private helpers. ---- *)

let lemma_sem_sn_cons (e:GECH.extensionClientHello) (tl:list GECH.extensionClientHello)
  : Lemma (ensures Sem.ch_find_server_name (e :: tl)
                   == (match e with
                       | GECH.Extension_data_server_name sn ->
                         (match (sn <: list GSN.serverName) with
                          | [] -> None
                          | GSN.Name_host_name h :: _ -> Some (h <: Seq.seq U8.t))
                       | _ -> Sem.ch_find_server_name tl))
  = ()

let lemma_sem_ks_cons (e:GECH.extensionClientHello) (tl:list GECH.extensionClientHello)
  : Lemma (ensures Sem.ch_find_key_share (e :: tl)
                   == (match e with
                       | GECH.Extension_data_key_share ks ->
                         Sem.kse_list_find_x25519 (ks <: list GKSE.keyShareEntry)
                       | _ -> Sem.ch_find_key_share tl))
  = ()

let lemma_sem_sa_cons (e:GECH.extensionClientHello) (tl:list GECH.extensionClientHello)
  : Lemma (ensures Sem.ch_find_sig_algs (e :: tl)
                   == (match e with
                       | GECH.Extension_data_signature_algorithms sa ->
                         Some (sa <: list GSS.signatureScheme)
                       | _ -> Sem.ch_find_sig_algs tl))
  = ()

(* ---- General connection lemmas: the [ch_extensions] commit-first accumulator
       components equal the corresponding first-wins [Sem] finders.  Private;
       exposed to the Parser via [lemma_ch_extensions_connect] below. ---- *)

let rec lemma_connect_sn
  (l:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (ensures
      (match ch_extensions l sn ks sv ss with
       | Some (sn', _, _, _) ->
         sn' == (if Some? sn then sn else Sem.ch_find_server_name l)
       | None -> True))
      (decreases l) =
  match l with
  | [] -> ()
  | e :: tl ->
    lemma_sem_sn_cons e tl; lemma_sem_ks_cons e tl; lemma_sem_sa_cons e tl;
    (match e with
     | GECH.Extension_data_server_name snl ->
       if Some? sn then lemma_connect_sn tl sn ks sv ss
       else (match ch_server_name snl with
             | Some name -> lemma_connect_sn tl (Some name) ks sv ss
             | None -> ())
     | GECH.Extension_data_signature_algorithms ssl ->
       lemma_connect_sn tl sn ks sv (if Nil? ss then synth_sig_schemes ssl else ss)
     | GECH.Extension_data_key_share kscl ->
       if Some? ks then lemma_connect_sn tl sn ks sv ss
       else (match Sem.kse_list_find_x25519 (kscl <: list GKSE.keyShareEntry) with
             | Some raw -> if B.length raw = 32 then lemma_connect_sn tl sn (Some (raw <: B.bytes_of_len 32)) sv ss else ()
             | None -> ())
     | GECH.Extension_data_supported_versions svl ->
       if List.Tot.mem GPV.TLS_1p3 svl then lemma_connect_sn tl sn ks true ss else ()
     | _ -> lemma_connect_sn tl sn ks sv ss)

let rec lemma_connect_ks
  (l:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (ensures
      (match ch_extensions l sn ks sv ss with
       | Some (_, ks', _, _) ->
         (if Some? ks then ks' == ks
          else (match ks' with
                | Some k -> Sem.ch_find_key_share l == Some ((k <: B.bytes) <: Seq.seq U8.t)
                | None -> Sem.ch_find_key_share l == None))
       | None -> True))
      (decreases l) =
  match l with
  | [] -> ()
  | e :: tl ->
    lemma_sem_sn_cons e tl; lemma_sem_ks_cons e tl; lemma_sem_sa_cons e tl;
    (match e with
     | GECH.Extension_data_server_name snl ->
       if Some? sn then lemma_connect_ks tl sn ks sv ss
       else (match ch_server_name snl with
             | Some name -> lemma_connect_ks tl (Some name) ks sv ss
             | None -> ())
     | GECH.Extension_data_signature_algorithms ssl ->
       lemma_connect_ks tl sn ks sv (if Nil? ss then synth_sig_schemes ssl else ss)
     | GECH.Extension_data_key_share kscl ->
       if Some? ks then lemma_connect_ks tl sn ks sv ss
       else (match Sem.kse_list_find_x25519 (kscl <: list GKSE.keyShareEntry) with
             | Some raw -> if B.length raw = 32 then lemma_connect_ks tl sn (Some (raw <: B.bytes_of_len 32)) sv ss else ()
             | None -> ())
     | GECH.Extension_data_supported_versions svl ->
       if List.Tot.mem GPV.TLS_1p3 svl then lemma_connect_ks tl sn ks true ss else ()
     | _ -> lemma_connect_ks tl sn ks sv ss)

let rec lemma_connect_sa
  (l:list GECH.extensionClientHello)
  (sn:option T.hostname) (ks:option (B.bytes_of_len 32)) (sv:bool) (ss:list T.signature_scheme)
  : Lemma (ensures
      (match ch_extensions l sn ks sv ss with
       | Some (_, _, _, ss') ->
         (if Cons? ss then ss' == ss
          else (match Sem.ch_find_sig_algs l with
                | Some sas -> ss' == synth_sig_schemes sas
                | None -> ss' == []))
       | None -> True))
      (decreases l) =
  match l with
  | [] -> ()
  | e :: tl ->
    lemma_sem_sn_cons e tl; lemma_sem_ks_cons e tl; lemma_sem_sa_cons e tl;
    (match e with
     | GECH.Extension_data_server_name snl ->
       if Some? sn then lemma_connect_sa tl sn ks sv ss
       else (match ch_server_name snl with
             | Some name -> lemma_connect_sa tl (Some name) ks sv ss
             | None -> ())
     | GECH.Extension_data_signature_algorithms ssl ->
       lemma_connect_sa tl sn ks sv (if Nil? ss then synth_sig_schemes ssl else ss)
     | GECH.Extension_data_key_share kscl ->
       if Some? ks then lemma_connect_sa tl sn ks sv ss
       else (match Sem.kse_list_find_x25519 (kscl <: list GKSE.keyShareEntry) with
             | Some raw -> if B.length raw = 32 then lemma_connect_sa tl sn (Some (raw <: B.bytes_of_len 32)) sv ss else ()
             | None -> ())
     | GECH.Extension_data_supported_versions svl ->
       if List.Tot.mem GPV.TLS_1p3 svl then lemma_connect_sa tl sn ks true ss else ()
     | _ -> lemma_connect_sa tl sn ks sv ss)

// The total byte size of a certificate chain (sum of the raw DER blob lengths),
// mirroring the contiguous layout the impl-layer certificate storage uses.
let rec cert_chain_total_bytes (l:list (Seq.seq U8.t)) : GTot nat (decreases l) =
  match l with
  | [] -> 0
  | c :: tl -> B.length c + cert_chain_total_bytes tl

// A ClientHello is representable iff the impl-layer extension scan [ch_extensions]
// accepts it (returns [Some] with an X25519 key share present, <= 16 signature
// schemes, and a server_name (if any) of <= 255 bytes) and it offers <= 16 cipher
// suites.  This is exactly the accept/reject gate the byte-level Parser computes
// (see [scan_ch_extensions] + the cipher-suite length bound), so representability
// is definitionally the Parser's success condition.  Because [ch_extensions] is a
// commit-on-first scan that mirrors the first-wins [TLS13.Wire.Semantics] finders,
// an accepted ClientHello's stored fields equal the [Sem.*] accessors
// (lemma_ch_extensions_connect), which is what [is_valid_client_hello] requires.
let clientHello_representable (b:GCH.clientHello) : GTot bool =
  (match ch_extensions (b.GCH.extensions <: list GECH.extensionClientHello)
                       None None false [] with
   | Some (server_name, Some key_share, _, sig_schemes) ->
     Cons? sig_schemes &&
     L.length sig_schemes <= M.client_hello_max_signature_schemes &&
     (match server_name with
      | Some hostname -> B.length hostname <= M.client_hello_server_name_max_len
      | None -> true)
   | _ -> false) &&
  L.length (Sem.clientHello_cipher_suites b) <= M.client_hello_max_cipher_suites

// Reveal the ClientHello accept/reject condition of [clientHello_representable]
// as the [ch_extensions] scan outcome + the cipher-suite bound.  Definitional;
// exposed so the byte-level Parser can relate its scan result to representability.
let lemma_clientHello_representable_scan (c:GCH.clientHello) = ()

(* The Parser bridge: under the commit-first [ch_extensions] scan, an accepted
   ClientHello's stored (server_name, key_share, sig_schemes) equal the first-wins
   [Sem] accessors that [is_valid_client_hello] compares against. *)
let lemma_ch_extensions_connect (c:GCH.clientHello) =
  lemma_connect_sn (c.GCH.extensions <: list GECH.extensionClientHello) None None false [];
  lemma_connect_ks (c.GCH.extensions <: list GECH.extensionClientHello) None None false [];
  lemma_connect_sa (c.GCH.extensions <: list GECH.extensionClientHello) None None false []

// A (non-HRR) ServerHello is representable iff it selects an X25519 key share (32
// bytes) and the CHACHA20_POLY1305_SHA256 cipher suite.  Matches
// is_valid_server_hello (Sem.serverHello_random is always Some on this arm).
let serverHello_representable (b:GSH.serverHello) : GTot bool =
  (match Sem.serverHello_key_share_x25519 b with
   | Some k -> B.length k = 32
   | None -> false) &&
  (match Sem.serverHello_cipher_suite b with
   | Some cs -> cs = T.TLS_CHACHA20_POLY1305_SHA256
   | None -> false)

// EncryptedExtensions is representable iff its ALPN protocol name (if any) is <=
// 255 bytes.  Matches is_valid_encrypted_extensions.
let encryptedExtensions_representable (b:GEE.encryptedExtensions) : GTot bool =
  (match Sem.encryptedExtensions_alpn b with
   | Some a -> B.length a <= M.client_hello_server_name_max_len
   | None -> true)

// A Certificate is representable iff it carries <= 8 entries whose raw DER blobs
// fit contiguously in the 32768-byte chain storage.  Matches
// is_valid_certificate_msg (which lays the blobs out at contiguous offsets).
let certificate_representable (b:GCert.certificate) : GTot bool =
  L.length (Sem.certificate_entries b) <= M.certificate_chain_max_entries &&
  cert_chain_total_bytes (Sem.certificate_entries b) <= M.certificate_chain_max_bytes

// A CertificateVerify is representable iff its signature is <= 4096 bytes.
// Matches is_valid_certificate_verify.
let certificateVerify_representable (b:GCV.certificateVerify) : GTot bool =
  B.length (Sem.certificateVerify_signature_bytes b) <= M.signature_max_len

(* Reveals of the opaque per-message representability predicates as their
   [Sem]-level accept conditions (the Parser's accept/reject branches need to
   compute these). *)
let lemma_certificateVerify_representable b = ()
let lemma_serverHello_representable b = ()
let lemma_encryptedExtensions_representable b = ()
let lemma_certificate_representable b = ()
let lemma_cert_chain_total_bytes_nil () = ()
let lemma_cert_chain_total_bytes_cons c tl = ()

let synth_handshake_msg_of (h:GHS.handshake) : GTot (option M.handshake_msg) =
  match h with
  | GHS.Body_client_hello b ->
    if clientHello_representable b then Some (M.ClientHello b) else None
  | GHS.Body_server_hello b ->
    (match b.GSH.body with
     | GSHB.HelloRetryRequest _ -> Some M.HelloRetryRequest
     | GSHB.ServerHello_body_false _ ->
       if serverHello_representable b then Some (M.ServerHello b) else None)
  | GHS.Body_encrypted_extensions b ->
    if encryptedExtensions_representable b then Some (M.EncryptedExtensions b) else None
  | GHS.Body_certificate b ->
    if certificate_representable (b <: GCert.certificate)
    then Some (M.Certificate (b <: GCert.certificate)) else None
  | GHS.Body_certificate_verify b ->
    if certificateVerify_representable b then Some (M.CertificateVerify b) else None
  | GHS.Body_finished b -> Some (M.Finished b)
  | GHS.Body_key_update _ -> None
  | GHS.Body_new_session_ticket _ -> None

let parse_handshake (input:B.bytes) : GTot (option (M.handshake_msg & nat)) =
  match LP.parse GHS.handshake_parser input with
  | Some (h, consumed) ->
    (match synth_handshake_msg_of h with
     | Some m -> Some (m, consumed)
     | None -> None)
  | None -> None

let parse_handshake_msg (input:B.bytes) : GTot (option (M.handshake_msg & nat)) =
  parse_handshake input

// Serialize a high handshake message by re-wrapping it into the generated
// [handshake] record and applying the QuackyDucky serializer (the single source
// of truth for the wire format).  This is the exact inverse of the structural
// [synth_handshake_msg_of] dispatch above.
//
// [M.Certificate] carries an unrestricted [GCert.certificate]; the generated
// [Body_certificate] arm requires [certificate_bytesize <= 16777215] (the u24
// body-length bound).  The certificate parser kind admits sizes up to 16777474,
// so an oversized certificate cannot be wrapped: we return [B.empty] for it
// (such a value never arises from parsing, and is never produced for sending).
//
// [M.HelloRetryRequest] returns [B.empty]: this profile never SENDS an HRR, and a
// received HRR is rejected before it can reach the transcript serializer.
let serialize_handshake (msg:M.handshake_msg) : GTot B.bytes =
  match msg with
  | M.ClientHello ch ->
    LP.serialize GHS.handshake_serializer (GHS.Body_client_hello ch)
  | M.ServerHello sh ->
    LP.serialize GHS.handshake_serializer (GHS.Body_server_hello sh)
  | M.EncryptedExtensions ee ->
    LP.serialize GHS.handshake_serializer (GHS.Body_encrypted_extensions ee)
  | M.Certificate cert ->
    if GCert.certificate_bytesize cert <= 16777215
    then LP.serialize GHS.handshake_serializer
           (GHS.Body_certificate (cert <: GHS.handshake_body_certificate))
    else B.empty
  | M.CertificateVerify cv ->
    LP.serialize GHS.handshake_serializer (GHS.Body_certificate_verify cv)
  | M.Finished fin ->
    LP.serialize GHS.handshake_serializer (GHS.Body_finished fin)
  | M.HelloRetryRequest -> B.empty

let serialize_handshake_msg (msg:M.handshake_msg) : GTot B.bytes =
  serialize_handshake msg

let serialize_server_certificate_verify_input (transcript_hash:B.bytes) : GTot B.bytes =
  if B.length transcript_hash == 32
  then H.certificate_verify_input transcript_hash
  else B.empty

let lemma_serialize_server_certificate_verify_input_len32
  (transcript_hash:B.bytes{B.length transcript_hash == 32})
  : Lemma (Seq.equal
      (serialize_server_certificate_verify_input transcript_hash)
      (H.certificate_verify_input transcript_hash))
=
  ()

let parse_record (input:B.bytes) : GTot (option (T.content_type & M.sealed_record & nat)) =
  if B.length input < 5 then None
  else
    match content_type_of_byte (Seq.index input 0) with
    | None -> None
    | Some content_type ->
      if read_u16 input 1 <> 0x0303 then None
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 || 5 + fragment_len > B.length input then None
        else
          match take_range input 5 fragment_len with
          | Some fragment -> Some (content_type, fragment, 5 + fragment_len)
          | None -> None

let parse_record_wire (input:B.bytes) : GTot (option (T.content_type & M.sealed_record & nat)) =
  let parsed = parse_record input in
  if Some? parsed then parsed
  else
    if B.length input < 5 then None
    else
      if Seq.index input 0 <> 0x16uy || read_u16 input 1 <> 0x0301 then None
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 || 5 + fragment_len > B.length input then None
        else Some (T.Handshake, Seq.slice input 5 (5 + fragment_len), 5 + fragment_len)

let lemma_parse_record_some_consumed_positive
  (input:B.bytes)
  (content_type:T.content_type)
  (fragment:M.sealed_record)
  (consumed:nat)
  : Lemma
    (requires parse_record input == Some (content_type, fragment, consumed))
    (ensures consumed > 0 /\ consumed <= B.length input)
=
  if B.length input < 5 then ()
  else
    match content_type_of_byte (Seq.index input 0) with
    | None -> ()
    | Some _ ->
      if read_u16 input 1 <> 0x0303 then ()
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 || 5 + fragment_len > B.length input then ()
        else
          match take_range input 5 fragment_len with
          | Some _ ->
            assert (consumed == 5 + fragment_len);
            assert (consumed > 0);
            assert (consumed <= B.length input)
          | None -> ()

let lemma_parse_record_implies_parse_record_wire (input:B.bytes)
  : Lemma
    (ensures (
      match parse_record input with
      | Some (content_type, fragment, consumed) ->
        parse_record_wire input == Some (content_type, fragment, consumed)
      | None -> True))
=
  ()

let lemma_parse_record_wire_some_consumed_positive
  (input:B.bytes)
  (content_type:T.content_type)
  (fragment:M.sealed_record)
  (consumed:nat)
  : Lemma
    (requires parse_record_wire input == Some (content_type, fragment, consumed))
    (ensures consumed > 0 /\ consumed <= B.length input)
=
  match parse_record input with
  | Some (ct, frag, consumed') ->
    assert (content_type == ct);
    assert (fragment == frag);
    assert (consumed == consumed');
    lemma_parse_record_some_consumed_positive input ct frag consumed'
  | None ->
    if B.length input < 5 then ()
    else
      if Seq.index input 0 <> 0x16uy || read_u16 input 1 <> 0x0301 then ()
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 || 5 + fragment_len > B.length input then ()
        else (
          assert (consumed == 5 + fragment_len);
          assert (consumed > 0);
          assert (consumed <= B.length input)
        )

// Parse just the 5-byte record header (without requiring the fragment data)
let parse_record_header (input:B.bytes) : GTot (option (T.content_type & nat)) =
  if B.length input < 5 then None
  else
    match content_type_of_byte (Seq.index input 0) with
    | None -> None
    | Some content_type ->
      if not (
           read_u16 input 1 == 0x0303 ||
           (content_type == T.Handshake && read_u16 input 1 == 0x0301))
      then None
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 then None
        else Some (content_type, fragment_len)

let lemma_parse_record_header_some_iff (input:B.bytes{B.length input == 5})
  : Lemma (Some? (parse_record_header input) <==>
    ((Seq.index input 0 = 0x00uy ||
      Seq.index input 0 = 0x14uy ||
      Seq.index input 0 = 0x15uy ||
      Seq.index input 0 = 0x16uy ||
      Seq.index input 0 = 0x17uy) &&
     Seq.index input 1 = 0x03uy &&
     (Seq.index input 2 = 0x03uy ||
      (Seq.index input 0 = 0x16uy && Seq.index input 2 = 0x01uy)) &&
     read_u16 input 3 <= 16640))
=
  ()

let serialize_record (content_type:T.content_type) (fragment:B.bytes) : GTot B.bytes =
  append3
    (u8 (content_type_to_byte content_type))
    (u16 0x0303)
    (B.append (u16 (B.length fragment)) fragment)

let lemma_parse_record_serialize_record
  (content_type:T.content_type)
  (fragment:B.bytes{B.length fragment <= 16640})
  : Lemma
      (B.length (serialize_record content_type fragment) == 5 + B.length fragment /\
       parse_record (serialize_record content_type fragment) ==
        Some (content_type, fragment, B.length (serialize_record content_type fragment)))
=
  let ct = u8 (content_type_to_byte content_type) in
  let ver = u16 0x0303 in
  let lenb = u16 (B.length fragment) in
  let tail2 = B.append lenb fragment in
  let tail1 = B.append ver tail2 in
  let raw = B.append ct tail1 in
  assert (raw == serialize_record content_type fragment);
  Seq.lemma_len_append ct tail1;
  Seq.lemma_len_append ver tail2;
  Seq.lemma_len_append lenb fragment;
  assert (B.length ct == 1);
  assert (B.length ver == 2);
  assert (B.length lenb == 2);
  assert (B.length raw == 5 + B.length fragment);

  Seq.lemma_index_app1 ct tail1 0;
  Seq.lemma_index_create 1 (byte (content_type_to_byte content_type)) 0;
  assert (Seq.index raw 0 == byte (content_type_to_byte content_type));
  lemma_byte_v (content_type_to_byte content_type);
  (match content_type with
   | T.Invalid -> ()
   | T.Change_cipher_spec -> ()
   | T.Alert -> ()
   | T.Handshake -> ()
   | T.Application_data -> ());
  assert (content_type_of_byte (Seq.index raw 0) == Some content_type);

  Seq.lemma_index_app2 ct tail1 1;
  Seq.lemma_index_app1 ver tail2 0;
  Seq.lemma_index_app2 ct tail1 2;
  Seq.lemma_index_app1 ver tail2 1;
  lemma_read_u16_u16 0x0303;
  assert (read_u16 raw 1 == read_u16 ver 0);
  assert (read_u16 raw 1 == 0x0303);

  Seq.lemma_index_app2 ct tail1 3;
  Seq.lemma_index_app2 ver tail2 2;
  Seq.lemma_index_app1 lenb fragment 0;
  Seq.lemma_index_app2 ct tail1 4;
  Seq.lemma_index_app2 ver tail2 3;
  Seq.lemma_index_app1 lenb fragment 1;
  lemma_read_u16_u16 (B.length fragment);
  assert (read_u16 raw 3 == read_u16 lenb 0);
  assert (read_u16 raw 3 == B.length fragment);

  assert (B.length fragment <= 16384 + 256);
  assert (5 + B.length fragment <= B.length raw);
  let frag_slice = Seq.slice raw 5 (5 + B.length fragment) in
  Seq.lemma_len_slice raw 5 (5 + B.length fragment);
  assert (forall (i:nat{i < B.length fragment}).
    Seq.index frag_slice i == Seq.index fragment i);
  Seq.lemma_eq_intro frag_slice fragment;
  assert (frag_slice == fragment);
  assert (take_range raw 5 (B.length fragment) == Some frag_slice);
  assert (take_range raw 5 (B.length fragment) == Some fragment);
  assert (parse_record raw ==
    Some (content_type, fragment, B.length raw))

let parse_plaintext (input:B.bytes) : GTot (option M.plaintext) =
  if B.length input == 0 then None
  else
    let content_type_pos = B.length input - 1 in
    match content_type_of_byte (Seq.index input content_type_pos) with
    | None -> None
    | Some content_type ->
      Some {
        M.content_type = content_type;
        M.fragment = Seq.slice input 0 content_type_pos
      }

let serialize_plaintext (pt:M.plaintext) : GTot B.bytes =
  B.append pt.M.fragment (u8 (content_type_to_byte pt.M.content_type))

let lemma_parse_plaintext_serialize_plaintext (pt:M.plaintext)
  : Lemma (parse_plaintext (serialize_plaintext pt) == Some pt)
=
  let input = serialize_plaintext pt in
  assert (B.length input == B.length pt.M.fragment + 1);
  assert (B.length input > 0);
  let content_type_pos = B.length input - 1 in
  assert (content_type_pos == B.length pt.M.fragment);
  lemma_byte_v (content_type_to_byte pt.M.content_type);
  assert (content_type_of_byte (Seq.index input content_type_pos) ==
    Some pt.M.content_type);
  assert (Seq.equal (Seq.slice input 0 content_type_pos) pt.M.fragment);
  Seq.lemma_eq_intro (Seq.slice input 0 content_type_pos) pt.M.fragment

(* --- Branch-specific (LTL/pairing) bespoke ServerHello field parser (see
       .fsti).  Self-contained on byte helpers (take_range) and the
       TLS13.ServerHello.Checks fixed-layout guards; independent of the generated
       handshake codec. --- *)
let parse_supported_server_hello_impl (input:B.bytes)
  : GTot (option supported_server_hello) =
  if SHC.server_hello_ok_52 input then
    match take_range input 6 32, take_range input 52 32 with
    | Some random, Some key_share ->
      Some {
        random = random;
        key_share = key_share;
        cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
      }
    | _, _ -> None
  else if SHC.server_hello_ok_58 input then
    match take_range input 6 32, take_range input 58 32 with
    | Some random, Some key_share ->
      Some {
        random = random;
        key_share = key_share;
        cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
      }
    | _, _ -> None
  else None

let parse_supported_server_hello (input:B.bytes)
  : GTot (option supported_server_hello) =
  parse_supported_server_hello_impl input

let lemma_parse_supported_server_hello_ok (input:B.bytes)
  : Lemma (Some? (parse_supported_server_hello input) <==>
           SHC.server_hello_ok input)
=
  ()

let lemma_parse_supported_server_hello_fields (input:B.bytes)
  : Lemma
      (requires SHC.server_hello_ok input)
      (ensures (
        match parse_supported_server_hello input with
        | Some sh ->
          sh.cipher_suite == T.TLS_CHACHA20_POLY1305_SHA256 /\
          Seq.equal sh.random (Seq.slice input 6 38) /\
          ((SHC.server_hello_ok_52 input /\
            Seq.equal sh.key_share (Seq.slice input 52 84)) \/
           (SHC.server_hello_ok_58 input /\
            Seq.equal sh.key_share (Seq.slice input 58 90)))
        | None -> False))
=
  if SHC.server_hello_ok_52 input then
    begin
      Seq.lemma_len_slice input 6 38;
      Seq.lemma_eq_intro (Seq.slice input 6 38) (Seq.slice input 6 38);
      Seq.lemma_len_slice input 52 84;
      Seq.lemma_eq_intro (Seq.slice input 52 84) (Seq.slice input 52 84)
    end
  else
    begin
      Seq.lemma_len_slice input 6 38;
      Seq.lemma_eq_intro (Seq.slice input 6 38) (Seq.slice input 6 38);
      Seq.lemma_len_slice input 58 90;
      Seq.lemma_eq_intro (Seq.slice input 58 90) (Seq.slice input 58 90)
    end

let parse_sealed_record (input:B.bytes) : GTot (option M.sealed_record) =
  Some input

let serialize_sealed_record (record:M.sealed_record) : GTot B.bytes =
  record

let parse_tls_message (content_type:T.content_type) (fragment:B.bytes) : GTot (option M.tls_message) =
  match content_type with
  | T.Invalid -> None
  | T.Handshake ->
    (match parse_handshake fragment with
     | Some (msg, consumed) ->
       if consumed == B.length fragment then Some (M.TlsHandshake msg) else None
     | None ->
       match parse_key_update fragment with
       | Some req -> Some (M.TlsKeyUpdate req)
       | None ->
         match parse_ignored_post_handshake fragment with
         | Some body -> Some (M.TlsIgnoredPostHandshake body)
         | None -> None)
  | T.Application_data -> Some (M.TlsApplicationData fragment)
  | T.Alert ->
    if B.length fragment == 2
    then
      match alert_description_of_byte (Seq.index fragment 1) with
      | Some alert -> Some (M.TlsAlert alert)
      | None -> None
    else None
  | T.Change_cipher_spec ->
    if B.length fragment == 1 && nat_of_byte (Seq.index fragment 0) == 1
    then Some M.TlsChangeCipherSpec
    else None

let lemma_parse_tls_message_invalid_none fragment = ()

let lemma_parse_handshake_none_of_lp_none fragment = ()

let lemma_parse_handshake_none_of_synth_none fragment v consumed = ()

let lemma_ptm_handshake_fallback fragment = ()

let serialize_tls_message (msg:M.tls_message) : GTot (T.content_type & B.bytes) =
  match msg with
  | M.TlsHandshake hs -> (T.Handshake, serialize_handshake hs)
  | M.TlsApplicationData data -> (T.Application_data, data)
  | M.TlsAlert alert -> (T.Alert, B.of_list [byte 2; byte (alert_description_to_byte alert)])
  | M.TlsChangeCipherSpec -> (T.Change_cipher_spec, B.singleton (byte 1))
  | M.TlsIgnoredPostHandshake body -> (T.Handshake, append3 (u8 4) (u24 (B.length body)) body)
  | M.TlsKeyUpdate req ->
    let request_byte =
      match req with
      | M.UpdateNotRequested -> 0
      | M.UpdateRequested -> 1 in
    (T.Handshake, append3 (u8 24) (u24 1) (u8 request_byte))

let lemma_serialize_tls_message_handshake (hs:M.handshake_msg)
  : Lemma (serialize_tls_message (M.TlsHandshake hs) == (T.Handshake, serialize_handshake hs))
=
  ()

let lemma_serialize_tls_message_application_data (data:B.bytes)
  : Lemma (serialize_tls_message (M.TlsApplicationData data) == (T.Application_data, data))
=
  ()

let lemma_serialize_tls_message_close_notify ()
  : Lemma (serialize_tls_message (M.TlsAlert T.Close_notify) ==
    (T.Alert, B.of_list [2uy; 0uy]))
=
  ()

let lemma_serialize_tls_message_change_cipher_spec ()
  : Lemma (serialize_tls_message M.TlsChangeCipherSpec ==
    (T.Change_cipher_spec, B.singleton 1uy))
=
  ()

let lemma_serialize_tls_message_key_update_not_requested ()
  : Lemma (serialize_tls_message (M.TlsKeyUpdate M.UpdateNotRequested) ==
    (T.Handshake, B.of_list [24uy; 0uy; 0uy; 1uy; 0uy]))
=
  let lhs = append3 (u8 24) (u24 1) (u8 0) in
  let rhs = B.of_list [24uy; 0uy; 0uy; 1uy; 0uy] in
  lemma_byte_v 24;
  lemma_byte_v 0;
  lemma_byte_v 1;
  assert (B.length lhs == 5);
  assert (B.length rhs == 5);
  assert (forall (i:nat{i < B.length lhs}). Seq.index lhs i == Seq.index rhs i);
  Seq.lemma_eq_intro lhs rhs;
  Seq.lemma_eq_elim lhs rhs;
  assert (serialize_tls_message (M.TlsKeyUpdate M.UpdateNotRequested) == (T.Handshake, lhs))

let parse_tls_record (input:B.bytes) : GTot (option (M.tls_record & nat)) =
  match parse_record input with
  | Some (content_type, fragment, consumed) ->
    Some ({ M.record_outer_type = content_type; M.record_fragment = fragment }, consumed)
  | None -> None

let serialize_tls_record (record:M.tls_record) : GTot B.bytes =
  serialize_record record.M.record_outer_type record.M.record_fragment

let lemma_parse_record_serializes (input:B.bytes)
  : Lemma
      (ensures (
        match parse_record input with
        | Some (content_type, fragment, consumed) ->
          consumed > 0 /\
          consumed <= B.length input /\
          consumed == B.length (serialize_record content_type fragment) /\
          Seq.equal (serialize_record content_type fragment)
                    (Seq.slice input 0 consumed)
        | None -> True))
  =
  if B.length input < 5 then ()
  else
    match content_type_of_byte (Seq.index input 0) with
    | None -> ()
    | Some content_type ->
      if read_u16 input 1 <> 0x0303 then ()
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 || 5 + fragment_len > B.length input then ()
        else
          match take_range input 5 fragment_len with
          | None -> ()
          | Some fragment ->
            assert (B.length fragment == fragment_len);
            assert (B.length (serialize_record content_type fragment) == 5 + fragment_len);
            assert (5 + fragment_len <= B.length input);
            assert (forall (i:nat{i < B.length (serialize_record content_type fragment)}).
                      Seq.index (serialize_record content_type fragment) i ==
                      Seq.index (Seq.slice input 0 (5 + fragment_len)) i);
            Seq.lemma_eq_intro
              (serialize_record content_type fragment)
              (Seq.slice input 0 (5 + fragment_len))

let lemma_parse_record_fragment_bound (input:B.bytes)
  : Lemma
      (ensures (
        match parse_record input with
        | Some (_, fragment, _) -> B.length fragment <= 16640
        | None -> True))
=
  if B.length input < 5 then ()
  else
    match content_type_of_byte (Seq.index input 0) with
    | None -> ()
    | Some _ ->
      if read_u16 input 1 <> 0x0303 then ()
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 || 5 + fragment_len > B.length input then ()
        else
          match take_range input 5 fragment_len with
          | Some fragment ->
            assert (B.length fragment == fragment_len);
            assert (B.length fragment <= 16640)
          | None -> ()

let lemma_parse_record_wire_fragment_bound (input:B.bytes)
  : Lemma
      (ensures (
        match parse_record_wire input with
        | Some (_, fragment, _) -> B.length fragment <= 16640
        | None -> True))
=
  if B.length input < 5 then ()
  else
    match content_type_of_byte (Seq.index input 0) with
    | None -> ()
    | Some _ ->
      if read_u16 input 1 <> 0x0303 then ()
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 || 5 + fragment_len > B.length input then ()
        else
          match take_range input 5 fragment_len with
          | Some fragment ->
            assert (B.length fragment == fragment_len);
            assert (B.length fragment <= 16640)
          | None -> ()

// Round-trip: a handshake message accepted by parse_tls_message re-serializes to
// exactly the input fragment, for the messages whose constructor carries a
// generated wire record (ClientHello, ServerHello, EncryptedExtensions,
// Certificate, CertificateVerify).
// This is the spec obligation a verified parser discharges for
// CT.parsed_message_wire_success_for.  Proof: synth_handshake_msg_of is the exact
// structural inverse of the re-wrapping in serialize_handshake, and LowParse's
// parsed_data_is_serialize gives `serialize handshake_serializer h == fragment`
// (exact consumption), so re-wrapping the synthesized message reproduces h.
let lemma_parse_tls_message_round_trip
  (content_type:T.content_type)
  (fragment:B.bytes)
  : Lemma
    (ensures (
      match parse_tls_message content_type fragment with
      | Some (M.TlsHandshake (M.ClientHello ch)) ->
        Seq.equal fragment (serialize_handshake (M.ClientHello ch))
      | Some (M.TlsHandshake (M.ServerHello sh)) ->
        Seq.equal fragment (serialize_handshake (M.ServerHello sh))
      | Some (M.TlsHandshake (M.EncryptedExtensions ee)) ->
        Seq.equal fragment (serialize_handshake (M.EncryptedExtensions ee))
      | Some (M.TlsHandshake (M.Certificate c)) ->
        Seq.equal fragment (serialize_handshake (M.Certificate c))
      | Some (M.TlsHandshake (M.CertificateVerify cv)) ->
        Seq.equal fragment (serialize_handshake (M.CertificateVerify cv))
      | _ -> True))
=
  match content_type with
  | T.Handshake ->
    (match LP.parse GHS.handshake_parser fragment with
     | Some (h, consumed) ->
       if consumed = B.length fragment then begin
         LP.parsed_data_is_serialize GHS.handshake_serializer fragment;
         Seq.lemma_eq_intro
           (Seq.slice fragment consumed (B.length fragment))
           B.empty;
         Seq.lemma_eq_intro
           (Seq.append (LP.serialize GHS.handshake_serializer h)
                       (Seq.slice fragment consumed (B.length fragment)))
           (LP.serialize GHS.handshake_serializer h);
         // Now `serialize handshake_serializer h == fragment`.  Case-split on h so
         // serialize_handshake of the structurally-synthesized message reduces to
         // `serialize handshake_serializer h` (the certificate arm additionally
         // needs the bytesize bound carried by handshake_body_certificate).
         (match h with
          | GHS.Body_server_hello b ->
            (match b.GSH.body with
             | GSHB.HelloRetryRequest _ -> ()
             | _ -> ())
          | GHS.Body_certificate b ->
            assert (GCert.certificate_bytesize (b <: GCert.certificate) <= 16777215)
          | _ -> ())
       end
       else ()
     | None -> ())
  | _ -> ()


(* --- synth_client_hello: accept/reject gate returning the wire record. --- *)

let synth_client_hello (c:GCH.clientHello) : GTot (option GCH.clientHello) =
  if clientHello_representable c then Some c else None

let lemma_synth_client_hello c = ()

(* --- Per-constructor reveals of the validating [synth_handshake_msg_of]. --- *)

let lemma_synth_handshake_msg_finished b = ()

let lemma_synth_handshake_msg_key_update b = ()

let lemma_synth_handshake_msg_client_hello b = ()

let lemma_synth_handshake_msg_certificate b = ()

let lemma_synth_handshake_msg_certificate_verify b = ()

let lemma_synth_handshake_msg_encrypted_extensions b = ()

let lemma_synth_handshake_msg_server_hello_hrr b shb = ()

let lemma_synth_handshake_msg_server_hello_sh b sf = ()

let lemma_synth_handshake_msg_server_hello_bad_version b = ()

let lemma_synth_signature_scheme s = ()
