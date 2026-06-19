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
module SHC = TLS13.ServerHello.Checks
module SP = FStar.Seq.Properties
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16

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

let append4 (a b c d:B.bytes) : GTot B.bytes =
  B.append a (B.append b (B.append c d))

let append5 (a b c d e:B.bytes) : GTot B.bytes =
  B.append a (B.append b (B.append c (B.append d e)))

let append6 (a b c d e f:B.bytes) : GTot B.bytes =
  B.append a (B.append b (B.append c (B.append d (B.append e f))))

let read_u16 (input:B.bytes) (pos:nat{pos + 2 <= B.length input}) : GTot nat =
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
  | T.ChangeCipherSpec -> 20
  | T.Alert -> 21
  | T.Handshake -> 22
  | T.ApplicationData -> 23

let content_type_of_byte (b:B.byte) : GTot (option T.content_type) =
  match nat_of_byte b with
  | 20 -> Some T.ChangeCipherSpec
  | 21 -> Some T.Alert
  | 22 -> Some T.Handshake
  | 23 -> Some T.ApplicationData
  | _ -> None

let signature_scheme_to_u16 (scheme:T.signature_scheme) : GTot nat =
  match scheme with
  | T.RsaPssRsaeSha256 -> 0x0804
  | T.EcdsaSecp256r1Sha256 -> 0x0403
  | T.Ed25519 -> 0x0807
  | T.UnsupportedSignatureScheme n -> n

let signature_scheme_of_u16 (scheme:nat) : GTot T.signature_scheme =
  match scheme with
  | 0x0804 -> T.RsaPssRsaeSha256
  | 0x0403 -> T.EcdsaSecp256r1Sha256
  | 0x0807 -> T.Ed25519
  | _ -> T.UnsupportedSignatureScheme scheme

let cipher_suite_to_u16 (suite:T.cipher_suite) : GTot nat =
  match suite with
  | T.TLS_CHACHA20_POLY1305_SHA256 -> 0x1303

let cipher_suite_of_u16 (suite:nat) : GTot (option T.cipher_suite) =
  match suite with
  | 0x1303 -> Some T.TLS_CHACHA20_POLY1305_SHA256
  | _ -> None

let alert_description_to_byte (alert:T.alert_description) : GTot nat =
  match alert with
  | T.CloseNotify -> 0
  | T.UnexpectedMessage -> 10
  | T.BadRecordMac -> 20
  | T.HandshakeFailure -> 40
  | T.DecodeError -> 50
  | T.DecryptError -> 51
  | T.ProtocolVersion -> 70
  | T.UnsupportedExtension -> 110
  | T.CertificateUnknown -> 46
  | T.IllegalParameter -> 47

let alert_description_of_byte (b:B.byte) : GTot (option T.alert_description) =
  match nat_of_byte b with
  | 0 -> Some T.CloseNotify
  | 10 -> Some T.UnexpectedMessage
  | 20 -> Some T.BadRecordMac
  | 40 -> Some T.HandshakeFailure
  | 50 -> Some T.DecodeError
  | 51 -> Some T.DecryptError
  | 70 -> Some T.ProtocolVersion
  | 110 -> Some T.UnsupportedExtension
  | 46 -> Some T.CertificateUnknown
  | 47 -> Some T.IllegalParameter
  | _ -> None

let rec bytes_equal_at
  (a:B.bytes)
  (b:B.bytes)
  (i:nat)
  (n:nat{n <= B.length a /\ n <= B.length b /\ i <= n})
  : GTot bool
        (decreases (n - i))
  =
  if i == n then true
  else
    nat_of_byte (Seq.index a i) == nat_of_byte (Seq.index b i) &&
    bytes_equal_at a b (i + 1) n

let bytes_equal (a:B.bytes) (b:B.bytes) : GTot bool =
  B.length a == B.length b && bytes_equal_at a b 0 (B.length a)

let is_hrr_random (random:B.bytes) : GTot bool =
  bytes_equal random
    (B.of_list [
      byte 0xcf; byte 0x21; byte 0xad; byte 0x74;
      byte 0xe5; byte 0x9a; byte 0x61; byte 0x11;
      byte 0xbe; byte 0x1d; byte 0x8c; byte 0x02;
      byte 0x1e; byte 0x65; byte 0xb8; byte 0x91;
      byte 0xc2; byte 0xa2; byte 0x11; byte 0x16;
      byte 0x7a; byte 0xbb; byte 0x8c; byte 0x5e;
      byte 0x07; byte 0x9e; byte 0x09; byte 0xe2;
      byte 0xc8; byte 0xa8; byte 0x33; byte 0x9c
    ])

let rec parse_server_hello_extensions
  (body:B.bytes)
  (pos:nat)
  (extensions_end:nat)
  (saw_supported_versions:bool)
  (key_share:option (B.bytes_of_len 32))
  : GTot (option (B.bytes_of_len 32))
        (decreases (extensions_end - pos))
  =
  if pos == extensions_end then
    if saw_supported_versions then key_share else None
  else if pos < extensions_end && pos + 4 <= extensions_end && extensions_end <= B.length body then
    let ext_type = read_u16 body pos in
    let ext_len = read_u16 body (pos + 2) in
    let ext_pos = pos + 4 in
    if ext_pos + ext_len > extensions_end then None
    else
      let next = ext_pos + ext_len in
      if ext_type == 0x002b then
        if ext_len == 2 && read_u16 body ext_pos == 0x0304
        then parse_server_hello_extensions body next extensions_end true key_share
        else None
      else if ext_type == 0x0033 then
        if ext_len == 36 &&
           read_u16 body ext_pos == 0x001d &&
           read_u16 body (ext_pos + 2) == 32
        then
          match take_range body (ext_pos + 4) 32 with
          | Some ks -> parse_server_hello_extensions body next extensions_end saw_supported_versions (Some ks)
          | None -> None
        else None
      else parse_server_hello_extensions body next extensions_end saw_supported_versions key_share
  else None

let rec parse_client_hello_extensions
  (body:B.bytes)
  (pos:nat)
  (extensions_end:nat)
  (server_name:option T.hostname)
  (key_share:option (B.bytes_of_len 32))
  (saw_supported_versions:bool)
  (signature_schemes:list T.signature_scheme)
  : GTot (option (option T.hostname & option (B.bytes_of_len 32) & bool & list T.signature_scheme))
        (decreases (extensions_end - pos))
  =
  if pos == extensions_end then
    if saw_supported_versions
    then Some (server_name, key_share, saw_supported_versions, signature_schemes)
    else None
  else if pos < extensions_end && pos + 4 <= extensions_end && extensions_end <= B.length body then
    let ext_type = read_u16 body pos in
    let ext_len = read_u16 body (pos + 2) in
    let ext_pos = pos + 4 in
    if ext_pos + ext_len > extensions_end then None
    else
      let next = ext_pos + ext_len in
      if ext_type == 0x0000 then
        if ext_len >= 5 &&
           read_u16 body ext_pos + 2 == ext_len &&
           nat_of_byte (Seq.index body (ext_pos + 2)) == 0 &&
           read_u16 body (ext_pos + 3) + 5 == ext_len
        then
          let name_len = read_u16 body (ext_pos + 3) in
          match take_range body (ext_pos + 5) name_len with
          | Some name ->
            parse_client_hello_extensions body next extensions_end
              (Some (name <: T.hostname)) key_share saw_supported_versions signature_schemes
          | None -> None
        else None
      else if ext_type == 0x000a then
        if ext_len == 4 &&
           read_u16 body ext_pos == 2 &&
           read_u16 body (ext_pos + 2) == 0x001d
        then parse_client_hello_extensions body next extensions_end server_name key_share saw_supported_versions signature_schemes
        else None
      else if ext_type == 0x000d then
        if ext_len == 4 && read_u16 body ext_pos == 2 then
          let scheme = signature_scheme_of_u16 (read_u16 body (ext_pos + 2)) in
          parse_client_hello_extensions body next extensions_end server_name key_share saw_supported_versions [scheme]
        else None
      else if ext_type == 0x0033 then
        if ext_len == 38 &&
           read_u16 body ext_pos == 36 &&
           read_u16 body (ext_pos + 2) == 0x001d &&
           read_u16 body (ext_pos + 4) == 32
        then
          match take_range body (ext_pos + 6) 32 with
          | Some ks -> parse_client_hello_extensions body next extensions_end server_name (Some ks) saw_supported_versions signature_schemes
          | None -> None
        else None
      else if ext_type == 0x002b then
        if ext_len == 3 &&
           nat_of_byte (Seq.index body ext_pos) == 2 &&
           read_u16 body (ext_pos + 1) == 0x0304
        then parse_client_hello_extensions body next extensions_end server_name key_share true signature_schemes
        else None
      else parse_client_hello_extensions body next extensions_end server_name key_share saw_supported_versions signature_schemes
  else None

let synth_cipher_suite (c:GCS.cipherSuite) : T.cipher_suite =
  match c with
  | GCS.TLS_CHACHA20_POLY1305_SHA256 -> T.TLS_CHACHA20_POLY1305_SHA256

let rec synth_cipher_suites (l:list GCS.cipherSuite)
  : GTot (list T.cipher_suite)
       (decreases l)
  =
  match l with
  | [] -> []
  | c :: tl -> synth_cipher_suite c :: synth_cipher_suites tl

let key_exchange_to_key32 (ke:GKSE.keyShareEntry_key_exchange) : GTot (option (B.bytes_of_len 32)) =
  let b : B.bytes = (ke <: B.bytes) in
  if B.length b = 32 then Some (b <: B.bytes_of_len 32) else None

let lemma_key_exchange_to_key32 ke = ()

// Find an x25519 entry carrying a 32-byte key in a ClientHello key_share list.
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

let synth_signature_scheme (s:GSS.signatureScheme) : T.signature_scheme =
  match s with
  | GSS.Ecdsa_secp256r1_sha256 -> T.EcdsaSecp256r1Sha256
  | GSS.Rsa_pss_rsae_sha256 -> T.RsaPssRsaeSha256
  | GSS.Ed25519 -> T.Ed25519
  | GSS.Unknown_signatureScheme v -> T.UnsupportedSignatureScheme (U16.v v)

let rec synth_sig_schemes (l:list GSS.signatureScheme) : GTot (list T.signature_scheme) (decreases l) =
  match l with
  | [] -> []
  | s :: tl -> synth_signature_scheme s :: synth_sig_schemes tl

// Hostname from the first host_name entry of a ClientHello server_name list.
let ch_server_name (snl:list GSN.serverName) : GTot (option T.hostname) =
  match snl with
  | (GSN.Name_host_name h) :: _ -> Some ((h <: B.bytes) <: T.hostname)
  | _ -> None

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
       (match ch_server_name snl with
        | Some name -> ch_extensions tl (Some name) key_share saw_supported_versions signature_schemes
        | None -> None)
     | GECH.Extension_data_supported_groups _ ->
       ch_extensions tl server_name key_share saw_supported_versions signature_schemes
     | GECH.Extension_data_signature_algorithms ssl ->
       ch_extensions tl server_name key_share saw_supported_versions (synth_sig_schemes ssl)
     | GECH.Extension_data_key_share kscl ->
       (match ch_find_key_share kscl with
        | Some ks -> ch_extensions tl server_name (Some ks) saw_supported_versions signature_schemes
        | None -> None)
     | GECH.Extension_data_supported_versions svl ->
       if List.Tot.mem GPV.TLS_1p3 svl
       then ch_extensions tl server_name key_share true signature_schemes
       else None
     | _ -> ch_extensions tl server_name key_share saw_supported_versions signature_schemes)

let synth_client_hello (c:GCH.clientHello) : GTot (option M.client_hello) =
  // RFC 8446 4.1.2: ClientHello.legacy_version MUST be 0x0303 (TLS_1p2). The high
  // M.client_hello has no version field, so requiring the canonical value here both
  // matches the original parser and keeps the wire<->M map injective on this field.
  if not (GPV.TLS_1p2? c.GCH.legacy_version) then None
  else
  match ch_extensions c.GCH.extensions None None false [] with
  | Some (server_name, Some key_share, _, signature_schemes) ->
    Some ({ M.random = (c.GCH.random <: B.bytes_of_len 32);
            M.server_name = server_name;
            M.key_share = key_share;
            M.cipher_suites = synth_cipher_suites c.GCH.cipher_suites;
            M.signature_schemes = signature_schemes })
  | _ -> None

let parse_client_hello (input:B.bytes) : GTot (option M.client_hello) =
  match LP.parse GCH.clientHello_parser input with
  | Some (ch, consumed) ->
    if consumed = B.length input then synth_client_hello ch else None
  | None -> None

let rec sh_key_share
  (l:list GESH.extensionServerHello)
  (saw_supported_versions:bool)
  (key_share:option (B.bytes_of_len 32))
  : GTot (option (B.bytes_of_len 32))
       (decreases l)
  =
  match l with
  | [] -> if saw_supported_versions then key_share else None
  | e :: tl ->
    (match e with
     | GESH.Extension_data_supported_versions sv ->
       // sv : protocolVersion (closed enum); RFC requires the selected version 0x0304.
       if GPV.TLS_1p3? sv then sh_key_share tl true key_share else None
     | GESH.Extension_data_key_share ks ->
       // ks : keyShareEntry; require x25519 + 32-byte key.
       if GNG.X25519? ks.GKSE.group
       then (match key_exchange_to_key32 ks.GKSE.key_exchange with
             | Some k -> sh_key_share tl saw_supported_versions (Some k)
             | None -> None)
       else None
     | _ -> sh_key_share tl saw_supported_versions key_share)

let lemma_sh_key_share_nil saw_supported_versions key_share = ()

let lemma_sh_key_share_cons e tl saw_supported_versions key_share = ()

let synth_server_hello (sh:GSH.serverHello) : GTot (option M.server_hello) =
  // A magic-random HelloRetryRequest is NOT a normal ServerHello: reject it here
  // (consistent with parse_supported_server_hello, which rejects HRR via
  // SHC.server_hello_ok).  parse_handshake maps the HRR arm to M.HelloRetryRequest
  // separately, so the modeled HelloRetryRequestRejected path is reachable.
  // RFC 8446 4.1.3: ServerHello.legacy_version MUST be 0x0303 (TLS_1p2); the high
  // M.server_hello has no version field, so requiring the canonical value here both
  // matches the original parser and keeps the wire<->M map injective on this field.
  if not (GPV.TLS_1p2? sh.GSH.legacy_version) then None
  else
  match sh.GSH.body with
  | GSHB.HelloRetryRequest _ -> None
  | GSHB.ServerHello_body_false sf ->
    let body = sf.GSHB.value in
    if U8.v body.GSHBody.legacy_compression_method <> 0 then None
    else
      match sh_key_share body.GSHBody.extensions false None with
      | Some ks ->
        Some ({ M.random = (sf.GSHB.tag <: B.bytes_of_len 32);
                M.key_share = ks;
                M.cipher_suite = synth_cipher_suite body.GSHBody.cipher_suite;
                // Overridden with the verbatim wire bytes in synth_handshake_msg_of;
                // this standalone entry point is unused by the round-trip path.
                M.body = B.empty })
      | None -> None

let parse_server_hello (input:B.bytes) : GTot (option M.server_hello) =
  match LP.parse GSH.serverHello_parser input with
  | Some (sh, consumed) ->
    if consumed = B.length input then synth_server_hello sh else None
  | None -> None

let parse_supported_server_hello_impl (input:B.bytes) : GTot (option M.server_hello) =
  if SHC.server_hello_ok_52 input then
    match take_range input 6 32, take_range input 52 32 with
    | Some random, Some key_share ->
      Some {
        M.random = random;
        M.key_share = key_share;
        M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
        M.body = B.empty
      }
    | _, _ -> None
  else if SHC.server_hello_ok_58 input then
    match take_range input 6 32, take_range input 58 32 with
    | Some random, Some key_share ->
      Some {
        M.random = random;
        M.key_share = key_share;
        M.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256;
        M.body = B.empty
      }
    | _, _ -> None
  else None

let parse_certificate_leaf_der_impl (input:B.bytes) : GTot (option B.bytes) =
  if B.length input < 4 then None
  else
    let request_context_len = nat_of_byte (Seq.index input 0) in
    let list_len_pos = 1 + request_context_len in
    if list_len_pos + 3 > B.length input then None
    else
      let cert_list_len = read_u24 input list_len_pos in
      let pos = list_len_pos + 3 in
      if cert_list_len == 0 || pos + cert_list_len <> B.length input then None
      else if pos + 5 > B.length input then None
      else
        let cert_data_len = read_u24 input pos in
        let cert_pos = pos + 3 in
        if cert_data_len == 0 || cert_pos + cert_data_len + 2 > B.length input then None
        else
          let extensions_len_pos = cert_pos + cert_data_len in
          let extensions_len = read_u16 input extensions_len_pos in
          if extensions_len_pos + 2 + extensions_len > B.length input then None
          else
            match take_range input cert_pos cert_data_len with
            | Some leaf -> Some (leaf <: B.bytes)
            | None -> None

let rec parse_certificate_entries
  (input:B.bytes)
  (pos:nat)
  (entries_end:nat)
  : GTot (option (list B.bytes))
        (decreases (entries_end - pos))
  =
  if pos == entries_end then Some []
  else if pos < entries_end && pos + 5 <= entries_end && entries_end <= B.length input then
    let cert_data_len = read_u24 input pos in
    let cert_pos = pos + 3 in
    let extensions_len_pos = cert_pos + cert_data_len in
    if cert_data_len == 0 || extensions_len_pos + 2 > entries_end then None
    else
      let extensions_len = read_u16 input extensions_len_pos in
      let next = extensions_len_pos + 2 + extensions_len in
      if next > entries_end then None
      else
        match take_range input cert_pos cert_data_len, parse_certificate_entries input next entries_end with
        | Some cert, Some rest -> Some ((cert <: B.bytes) :: rest)
        | _, _ -> None
  else None

let rec synth_cert_chain (l:list GCE.certificateEntry)
  : GTot (list B.bytes)
       (decreases l)
  =
  match l with
  | [] -> []
  | e :: tl -> (e.GCE.cert_data <: B.bytes) :: synth_cert_chain tl

// Total number of bytes of certificate data in a chain (concatenated cert_data,
// the layout the low-level certificate_msg representation stores).
let rec cert_chain_total_bytes (chain:list B.bytes) : GTot nat =
  match chain with
  | [] -> 0
  | c :: tl -> B.length c + cert_chain_total_bytes tl

// A chain fits the fixed-size low-level representation iff it has at most
// certificate_chain_max_entries certificates and their data fits in
// certificate_chain_max_bytes.
let cert_chain_fits (chain:list B.bytes) : GTot bool =
  FStar.List.Tot.length chain <= M.certificate_chain_max_entries &&
  cert_chain_total_bytes chain <= M.certificate_chain_max_bytes

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

let parse_certificate_msg (input:B.bytes) : GTot (option M.certificate_msg) =
  match LP.parse GCert.certificate_parser input with
  | Some (c, consumed) ->
    if consumed = B.length input
    then Some ({ M.chain = synth_cert_chain c.GCert.certificate_list; M.body = B.empty })
    else None
  | None -> None

let parse_certificate_verify_impl (input:B.bytes) : GTot (option M.certificate_verify) =
  if B.length input < 4 then None
  else
    let scheme = read_u16 input 0 in
    let sig_len = read_u16 input 2 in
    if sig_len + 4 <> B.length input then None
    else
      match take_range input 4 sig_len with
      | Some signature ->
        Some {
          M.scheme = signature_scheme_of_u16 scheme;
          M.signature = signature;
          M.body = B.empty
        }
      | None -> None

let rec parse_encrypted_extensions_entries
  (input:B.bytes)
  (pos:nat)
  (entries_end:nat)
  (alpn:option B.bytes)
  : GTot (option M.encrypted_extensions)
       (decreases (entries_end - pos))
  =
  if pos == entries_end then Some { M.negotiated_alpn = alpn; M.body = B.empty }
  else if pos < entries_end && pos + 4 <= entries_end && entries_end <= B.length input then
    let ext_type = read_u16 input pos in
    let ext_len = read_u16 input (pos + 2) in
    let ext_pos = pos + 4 in
    if ext_pos + ext_len > entries_end then None
    else
      let next = ext_pos + ext_len in
      if ext_type == 0x0010 then
       if ext_len >= 3 &&
          read_u16 input ext_pos + 2 == ext_len &&
          nat_of_byte (Seq.index input (ext_pos + 2)) + 3 == ext_len
       then
         let name_len = nat_of_byte (Seq.index input (ext_pos + 2)) in
         match take_range input (ext_pos + 3) name_len with
         | Some name -> parse_encrypted_extensions_entries input next entries_end (Some (name <: B.bytes))
         | None -> None
       else None
      else parse_encrypted_extensions_entries input next entries_end alpn
  else None

// First ALPN protocol name (as raw bytes) from a parsed protocol_name_list.
let alpn_first_name (pnl:GEEE.extensionEncryptedExtensions_extension_data_application_layer_protocol_negotiation)
  : GTot (option B.bytes) =
  match (pnl <: list TLS13.Wire.Generated.ProtocolName.protocolName) with
  | pn :: _ -> Some ((pn <: B.bytes))
  | [] -> None

let rec synth_encrypted_extensions (l:list GEEE.extensionEncryptedExtensions)
  : GTot (option M.encrypted_extensions)
       (decreases l)
  =
  match l with
  | [] -> Some ({ M.negotiated_alpn = None; M.body = B.empty })
  | e :: tl ->
    (match e with
     | GEEE.Extension_data_application_layer_protocol_negotiation pnl ->
       (match alpn_first_name pnl with
        | Some name -> Some ({ M.negotiated_alpn = Some name; M.body = B.empty })
        | None -> None)
     | _ -> synth_encrypted_extensions tl)

let lemma_synth_encrypted_extensions_nil () = ()

let lemma_synth_encrypted_extensions_cons_non_alpn e tl = ()

let lemma_synth_encrypted_extensions_cons_alpn pnl tl = ()

let parse_encrypted_extensions (input:B.bytes) : GTot (option M.encrypted_extensions) =
  match LP.parse GEE.encryptedExtensions_parser input with
  | Some (exts, consumed) ->
    if consumed = B.length input
    then synth_encrypted_extensions exts
    else None
  | None -> None

let parse_certificate_verify (input:B.bytes) : GTot (option M.certificate_verify) =
  match LP.parse GCV.certificateVerify_parser input with
  | Some (cv, consumed) ->
    if consumed = B.length input
    then Some ({ M.scheme = synth_signature_scheme cv.GCV.algorithm;
                 M.signature = (cv.GCV.signature <: B.bytes);
                 M.body = B.empty })
    else None
  | None -> None

let parse_finished (input:B.bytes) : GTot (option M.finished) =
  match LP.parse GFinished.finished_parser input with
  | Some (vd, consumed) ->
    if consumed = B.length input
    then Some ({ M.verify_data = vd })
    else None
  | None -> None

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

let synth_handshake_msg_of (h:GHS.handshake) : GTot (option M.handshake_msg) =
  // The verbatim wire bytes of this handshake message: the QuackyDucky
  // serializer applied to the parsed value.  By LowParse's parse/serialize
  // round-trip this equals the input fragment, so a parser can discharge
  // `fragment == serialize_handshake msg` (see lemma_synth_handshake_round_trip).
  let full = LP.serialize GHS.handshake_serializer h in
  match h with
  | GHS.Body_client_hello b ->
    // A TLS client never legitimately receives a ClientHello; the dispatcher
    // would reject it as an unexpected handshake message anyway.  Modelling it
    // as a parse failure (rather than Some (M.ClientHello _)) keeps the received
    // message space to what a client can actually accept, and lets the verified
    // parser reject it without the (never-exercised) ClientHello field copy.
    None
  | GHS.Body_server_hello b ->
    // legacy_version MUST be 0x0303 (matches synth_server_hello and the original
    // parser, which rejected non-0x0303 before inspecting random/body).
    if not (GPV.TLS_1p2? b.GSH.legacy_version) then None
    else
    (match b.GSH.body with
     | GSHB.HelloRetryRequest _ -> Some M.HelloRetryRequest
     | GSHB.ServerHello_body_false _ ->
       (match synth_server_hello b with
        | Some x ->
          // Bound the carried ServerHello to server_hello_max_len; oversized
          // ServerHellos are rejected (they cannot fit the fixed receive buffer).
          if B.length full <= M.server_hello_max_len
          then Some (M.ServerHello ({ x with M.body = full }))
          else None
        | None -> None))
  | GHS.Body_encrypted_extensions b ->
    (match synth_encrypted_extensions b with
     | Some x -> Some (M.EncryptedExtensions ({ x with M.body = full }))
     | None -> None)
  | GHS.Body_certificate b ->
    // Reject chains too large for the fixed-size low-level representation.
    let chain = synth_cert_chain b.GCert.certificate_list in
    if cert_chain_fits chain
    then Some (M.Certificate ({ M.chain = chain; M.body = full }))
    else None
  | GHS.Body_certificate_verify b ->
    // Reject signatures too large for the fixed-size low-level representation.
    if B.length b.GCV.signature <= M.signature_max_len
    then Some (M.CertificateVerify ({ M.scheme = synth_signature_scheme b.GCV.algorithm;
                                      M.signature = (b.GCV.signature <: B.bytes);
                                      M.body = full }))
    else None
  | GHS.Body_finished b ->
    Some (M.Finished ({ M.verify_data = (b <: B.bytes_of_len 32) }))
  | GHS.Body_key_update _ -> None
  | GHS.Body_new_session_ticket _ -> None

let lemma_synth_handshake_msg_finished b = ()

let lemma_synth_handshake_msg_certificate_verify b = ()

let lemma_synth_handshake_msg_key_update b = ()

let lemma_synth_handshake_msg_client_hello b = ()

let lemma_synth_handshake_msg_server_hello_bad_version b = ()

let lemma_synth_handshake_msg_server_hello_hrr b shb = ()

let lemma_synth_handshake_msg_server_hello_sh b sf = ()

let lemma_synth_handshake_msg_encrypted_extensions b = ()

let lemma_synth_handshake_msg_certificate b = ()

let parse_handshake (input:B.bytes) : GTot (option (M.handshake_msg & nat)) =
  match LP.parse GHS.handshake_parser input with
  | Some (h, consumed) ->
    (match synth_handshake_msg_of h with
     | Some m -> Some (m, consumed)
     | None -> None)
  | None -> None

let parse_handshake_msg (input:B.bytes) : GTot (option (M.handshake_msg & nat)) =
  parse_handshake input

let parse_supported_server_hello (input:B.bytes) : GTot (option M.server_hello) =
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
          Seq.equal sh.M.random (Seq.slice input 6 38) /\
          ((SHC.server_hello_ok_52 input /\
            Seq.equal sh.M.key_share (Seq.slice input 52 84)) \/
           (SHC.server_hello_ok_58 input /\
            Seq.equal sh.M.key_share (Seq.slice input 58 90)))
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

let parse_certificate_leaf_der (input:B.bytes) : GTot (option B.bytes) =
  parse_certificate_leaf_der_impl input

let server_name_extension (hostname:B.bytes) : GTot B.bytes =
  if B.length hostname == 0 then B.empty
  else
    append5
      (u16 0x0000)
      (u16 (5 + B.length hostname))
      (u16 (3 + B.length hostname))
      (u8 0)
      (B.append (u16 (B.length hostname)) hostname)

let supported_groups_extension (_:unit) : GTot B.bytes =
  append4 (u16 0x000a) (u16 4) (u16 2) (u16 0x001d)

let signature_algorithms_extension (_:unit) : GTot B.bytes =
  append4 (u16 0x000d) (u16 4) (u16 2) (u16 0x0804)

let key_share_extension (key_share:B.bytes) : GTot B.bytes =
  append6
    (u16 0x0033)
    (u16 38)
    (u16 36)
    (u16 0x001d)
    (u16 32)
    key_share

let server_key_share_extension (key_share:B.bytes) : GTot B.bytes =
  append5
    (u16 0x0033)
    (u16 36)
    (u16 0x001d)
    (u16 32)
    key_share

let supported_versions_extension (_:unit) : GTot B.bytes =
  append4 (u16 0x002b) (u16 3) (u8 2) (u16 0x0304)

let server_supported_versions_extension (_:unit) : GTot B.bytes =
  append3 (u16 0x002b) (u16 2) (u16 0x0304)

let client_hello_extensions (hello:M.client_hello) : GTot B.bytes =
  let hostname =
    match hello.M.server_name with
    | Some h -> h
    | None -> B.empty in
  append5
    (server_name_extension hostname)
    (supported_groups_extension ())
    (signature_algorithms_extension ())
    (key_share_extension hello.M.key_share)
    (supported_versions_extension ())

let serialize_client_hello (hello:M.client_hello) : GTot B.bytes =
  let extensions = client_hello_extensions hello in
  append6
    (u16 0x0303)
    hello.M.random
    (u8 0)
    (append3 (u16 2) (u16 0x1303) (u8 1))
    (u8 0)
    (B.append (u16 (B.length extensions)) extensions)

let serialize_server_hello (sh:M.server_hello) : GTot B.bytes =
  let extensions =
    B.append (server_key_share_extension sh.M.key_share) (server_supported_versions_extension ()) in
  append6
    (u16 0x0303)
    sh.M.random
    (u8 0)
    (u16 (cipher_suite_to_u16 sh.M.cipher_suite))
    (u8 0)
    (B.append (u16 (B.length extensions)) extensions)

let alpn_extension (alpn:B.bytes) : GTot B.bytes =
  append4
    (u16 0x0010)
    (u16 (3 + B.length alpn))
    (u16 (1 + B.length alpn))
    (B.append (u8 (B.length alpn)) alpn)

let serialize_encrypted_extensions (ee:M.encrypted_extensions) : GTot B.bytes =
  let extensions =
    match ee.M.negotiated_alpn with
    | None -> B.empty
    | Some alpn -> alpn_extension alpn in
  B.append (u16 (B.length extensions)) extensions

let rec serialize_certificate_entries (chain:list B.bytes) : GTot B.bytes =
  match chain with
  | [] -> B.empty
  | cert :: rest ->
    append3
      (u24 (B.length cert))
      cert
      (B.append (u16 0) (serialize_certificate_entries rest))

let serialize_certificate_msg (cert:M.certificate_msg) : GTot B.bytes =
  let chain_bytes = serialize_certificate_entries cert.M.chain in
  append3 (u8 0) (u24 (B.length chain_bytes)) chain_bytes

let serialize_certificate_verify (cv:M.certificate_verify) : GTot B.bytes =
  append3
    (u16 (signature_scheme_to_u16 cv.M.scheme))
    (u16 (B.length cv.M.signature))
    cv.M.signature

let serialize_finished (fin:M.finished) : GTot B.bytes =
  fin.M.verify_data

let serialize_supported_client_hello (hello:M.client_hello) : GTot B.bytes =
  let body = serialize_client_hello hello in
  append3 (u8 1) (u24 (B.length body)) body

let serialize_server_hello_from_selection_canonical (sh:M.server_hello) : GTot B.bytes =
  let body = serialize_server_hello sh in
  append3 (u8 2) (u24 (B.length body)) body

let serialize_empty_encrypted_extensions_canonical (_:unit) : GTot B.bytes =
  let body =
    serialize_encrypted_extensions
      { M.negotiated_alpn = None; M.body = B.empty } in
  append3 (u8 8) (u24 (B.length body)) body

let serialize_certificate_from_credential_canonical (cert:M.certificate_msg) : GTot B.bytes =
  let body = serialize_certificate_msg cert in
  append3 (u8 11) (u24 (B.length body)) body

let serialize_certificate_verify_from_signature_canonical (cv:M.certificate_verify) : GTot B.bytes =
  let body = serialize_certificate_verify cv in
  append3 (u8 15) (u24 (B.length body)) body

let serialize_server_finished_canonical (fin:M.finished) : GTot B.bytes =
  append3 (u8 20) (u24 (B.length fin.M.verify_data)) fin.M.verify_data

let serialize_handshake_body (msg:M.handshake_msg) : GTot (option (nat & B.bytes)) =
  match msg with
  | M.ClientHello hello -> Some (1, serialize_client_hello hello)
  | M.ServerHello sh -> Some (2, serialize_server_hello sh)
  | M.EncryptedExtensions ee -> Some (8, serialize_encrypted_extensions ee)
  | M.Certificate cert -> Some (11, serialize_certificate_msg cert)
  | M.CertificateVerify cv -> Some (15, serialize_certificate_verify cv)
  | M.Finished fin -> Some (20, serialize_finished fin)
  | M.HelloRetryRequest -> None

// Received messages that must round-trip exactly (ServerHello, Encrypted-
// Extensions, Certificate, CertificateVerify) carry the verbatim wire bytes in
// [body].  Server-generated messages use [body = B.empty] and fall back to the
// canonical server-side serializers backed by the C stubs.
let serialize_handshake (msg:M.handshake_msg) : GTot B.bytes =
  match msg with
  | M.ServerHello sh ->
    if B.length sh.M.body == 0 then serialize_server_hello_from_selection_canonical sh else sh.M.body
  | M.EncryptedExtensions ee ->
    if B.length ee.M.body == 0 then serialize_empty_encrypted_extensions_canonical () else ee.M.body
  | M.Certificate cert ->
    if B.length cert.M.body == 0 then serialize_certificate_from_credential_canonical cert else cert.M.body
  | M.CertificateVerify cv ->
    if B.length cv.M.body == 0 then serialize_certificate_verify_from_signature_canonical cv else cv.M.body
  | _ ->
    (match serialize_handshake_body msg with
     | Some (msg_type, body) -> append3 (u8 msg_type) (u24 (B.length body)) body
     | None -> B.empty)

let serialize_handshake_msg (msg:M.handshake_msg) : GTot B.bytes =
  serialize_handshake msg

let lemma_serialize_finished_len (fin:M.finished)
  : Lemma (B.length (serialize_finished fin) == 32 /\
           B.length (serialize_handshake (M.Finished fin)) == 36 /\
           B.length (serialize_handshake_msg (M.Finished fin)) == 36)
=
  ()

let lemma_serialize_server_hello_len (sh:M.server_hello)
  : Lemma (B.length (serialize_handshake (M.ServerHello sh)) <= M.server_hello_max_len /\
           B.length (serialize_handshake_msg (M.ServerHello sh)) <= M.server_hello_max_len)
=
  ()

let serialize_server_hello_from_selection (sh:M.server_hello) : GTot B.bytes =
  serialize_server_hello_from_selection_canonical sh

let lemma_serialize_server_hello_from_selection_len (sh:M.server_hello)
  : Lemma
    (requires B.length sh.M.random == 32 /\
              B.length sh.M.key_share == 32)
    (ensures B.length (serialize_server_hello_from_selection sh) == 90)
=
  ()

let serialize_empty_encrypted_extensions (_:unit) : GTot B.bytes =
  serialize_empty_encrypted_extensions_canonical ()

let serialize_certificate_from_credential (cert:M.certificate_msg) : GTot B.bytes =
  serialize_certificate_from_credential_canonical cert

let lemma_serialize_certificate_from_single_chain_len
  (certificate:B.bytes)
  : Lemma
    (B.length
      (serialize_certificate_msg { M.chain = [certificate]; M.body = B.empty }) ==
        9 + B.length certificate /\
     B.length
      (serialize_handshake (M.Certificate { M.chain = [certificate]; M.body = B.empty })) ==
        13 + B.length certificate /\
     B.length
      (serialize_certificate_from_credential { M.chain = [certificate]; M.body = B.empty }) ==
        13 + B.length certificate)
=
  ()

let serialize_certificate_verify_from_signature (cv:M.certificate_verify) : GTot B.bytes =
  serialize_certificate_verify_from_signature_canonical cv

let lemma_serialize_certificate_verify_from_signature_len
  (cv:M.certificate_verify)
  : Lemma
    (B.length (serialize_certificate_verify cv) == 4 + B.length cv.M.signature /\
     (B.length cv.M.body == 0 ==>
      B.length (serialize_handshake (M.CertificateVerify cv)) ==
        8 + B.length cv.M.signature) /\
     B.length (serialize_certificate_verify_from_signature cv) ==
       8 + B.length cv.M.signature)
=
  ()

let serialize_server_finished (fin:M.finished) : GTot B.bytes =
  serialize_server_finished_canonical fin

let lemma_fixed_server_handshake_serializers
  (sh:M.server_hello)
  (cert:M.certificate_msg)
  (cv:M.certificate_verify)
  (fin:M.finished)
  : Lemma
    (requires B.length sh.M.body == 0 /\
              B.length cert.M.body == 0 /\
              B.length cv.M.body == 0)
    (ensures Seq.equal
       (serialize_server_hello_from_selection sh)
       (serialize_handshake (M.ServerHello sh)) /\
     Seq.equal
       (serialize_empty_encrypted_extensions ())
       (serialize_handshake (M.EncryptedExtensions { M.negotiated_alpn = None; M.body = B.empty })) /\
     Seq.equal
       (serialize_certificate_from_credential cert)
       (serialize_handshake (M.Certificate cert)) /\
     Seq.equal
       (serialize_certificate_verify_from_signature cv)
       (serialize_handshake (M.CertificateVerify cv)) /\
     Seq.equal
       (serialize_server_finished fin)
       (serialize_handshake (M.Finished fin)))
=
  ()

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
  parse_record input

let lemma_parse_record_implies_parse_record_wire (input:B.bytes)
  : Lemma
    (ensures parse_record_wire input == parse_record input)
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

// Parse just the 5-byte record header (without requiring the fragment data)
let parse_record_header (input:B.bytes) : GTot (option (T.content_type & nat)) =
  if B.length input < 5 then None
  else
    match content_type_of_byte (Seq.index input 0) with
    | None -> None
    | Some content_type ->
      if read_u16 input 1 <> 0x0303 then None
      else
        let fragment_len = read_u16 input 3 in
        if fragment_len > 16384 + 256 then None
        else Some (content_type, fragment_len)

let lemma_parse_record_header_some_iff (input:B.bytes{B.length input == 5})
  : Lemma (Some? (parse_record_header input) <==>
    ((Seq.index input 0 = 0x14uy ||
      Seq.index input 0 = 0x15uy ||
      Seq.index input 0 = 0x16uy ||
      Seq.index input 0 = 0x17uy) &&
     Seq.index input 1 = 0x03uy &&
     Seq.index input 2 = 0x03uy &&
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
   | T.ChangeCipherSpec -> ()
   | T.Alert -> ()
   | T.Handshake -> ()
   | T.ApplicationData -> ());
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

let parse_sealed_record (input:B.bytes) : GTot (option M.sealed_record) =
  Some input

let serialize_sealed_record (record:M.sealed_record) : GTot B.bytes =
  record

let parse_tls_message (content_type:T.content_type) (fragment:B.bytes) : GTot (option M.tls_message) =
  match content_type with
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
  | T.ApplicationData -> Some (M.TlsApplicationData fragment)
  | T.Alert ->
    if B.length fragment == 2
    then
      match alert_description_of_byte (Seq.index fragment 1) with
      | Some alert -> Some (M.TlsAlert alert)
      | None -> None
    else None
  | T.ChangeCipherSpec ->
    if B.length fragment == 1 && nat_of_byte (Seq.index fragment 0) == 1
    then Some M.TlsChangeCipherSpec
    else None

let lemma_parse_handshake_none_of_lp_none fragment = ()

let lemma_parse_handshake_none_of_synth_none fragment v consumed = ()

let lemma_ptm_handshake_fallback fragment = ()

let serialize_tls_message (msg:M.tls_message) : GTot (T.content_type & B.bytes) =
  match msg with
  | M.TlsHandshake hs -> (T.Handshake, serialize_handshake hs)
  | M.TlsApplicationData data -> (T.ApplicationData, data)
  | M.TlsAlert alert -> (T.Alert, B.of_list [byte 2; byte (alert_description_to_byte alert)])
  | M.TlsChangeCipherSpec -> (T.ChangeCipherSpec, B.singleton (byte 1))
  | M.TlsIgnoredPostHandshake body -> (T.Handshake, append3 (u8 4) (u24 (B.length body)) body)
  | M.TlsKeyUpdate req ->
    let request_byte =
      match req with
      | M.UpdateNotRequested -> 0
      | M.UpdateRequested -> 1 in
    (T.Handshake, append3 (u8 24) (u24 1) (u8 request_byte))

let lemma_serialize_tls_message_application_data (data:B.bytes)
  : Lemma (serialize_tls_message (M.TlsApplicationData data) == (T.ApplicationData, data))
=
  ()

let lemma_serialize_tls_message_close_notify ()
  : Lemma (serialize_tls_message (M.TlsAlert T.CloseNotify) ==
    (T.Alert, B.of_list [2uy; 0uy]))
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
  Seq.lemma_eq_elim lhs rhs

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
// exactly the input fragment, for the messages whose M-value carries the verbatim
// wire body (ServerHello, EncryptedExtensions, Certificate, CertificateVerify).
// This is the spec obligation a verified parser discharges for
// CT.parsed_message_wire_success_for.  Proof: synth sets m.body to the QuackyDucky
// serialization of the parsed handshake value h, and LowParse's parsed_data_is_serialize
// gives `serialize handshake_serializer h == fragment` (exact consumption).
let lemma_parse_tls_message_round_trip
  (content_type:T.content_type)
  (fragment:B.bytes)
  : Lemma
    (ensures (
      match parse_tls_message content_type fragment with
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
           (LP.serialize GHS.handshake_serializer h)
       end
       else ()
     | None -> ())
  | _ -> ()
