module TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module R = TLS13.Record.Spec
module Seq = FStar.Seq
module T = TLS13.Types
module U8 = FStar.UInt8

let byte (n:nat) : B.byte = U8.uint_to_t (n % 256)

let nat_of_byte (b:B.byte) : GTot nat = U8.v b

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

let read_u24 (input:B.bytes) (pos:nat{pos + 3 <= B.length input}) : GTot nat =
  nat_of_byte (Seq.index input pos) * 65536 +
  nat_of_byte (Seq.index input (pos + 1)) * 256 +
  nat_of_byte (Seq.index input (pos + 2))

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

let parse_supported_server_hello_impl (input:B.bytes) : GTot (option H.server_hello) =
  if B.length input < 4 then None
  else
    let msg_type = nat_of_byte (Seq.index input 0) in
    let body_len = read_u24 input 1 in
    if msg_type <> 2 || body_len + 4 <> B.length input then None
    else
      let body = Seq.slice input 4 (B.length input) in
      if B.length body < 40 then None
      else if read_u16 body 0 <> 0x0303 then None
      else
        match take_range body 2 32 with
        | None -> None
        | Some random ->
          if is_hrr_random random then None
          else
            let session_id_len = nat_of_byte (Seq.index body 34) in
            let pos = 35 + session_id_len in
            if pos + 5 > B.length body then None
            else if read_u16 body pos <> 0x1303 then None
            else if nat_of_byte (Seq.index body (pos + 2)) <> 0 then None
            else
              let extensions_len = read_u16 body (pos + 3) in
              let extensions_pos = pos + 5 in
              if extensions_pos + extensions_len <> B.length body then None
              else
                match parse_server_hello_extensions body extensions_pos (extensions_pos + extensions_len) false None with
                | Some key_share ->
                  Some {
                    H.random = random;
                    H.key_share = key_share;
                    H.cipher_suite = T.TLS_CHACHA20_POLY1305_SHA256
                  }
                | None -> None

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

let parse_certificate_verify_impl (input:B.bytes) : GTot (option H.certificate_verify) =
  if B.length input < 4 then None
  else
    let scheme = read_u16 input 0 in
    let sig_len = read_u16 input 2 in
    if sig_len + 4 <> B.length input then None
    else
      match take_range input 4 sig_len with
      | Some signature ->
        Some {
          H.scheme = signature_scheme_of_u16 scheme;
          H.signature = signature
        }
      | None -> None

let parse_handshake (input:B.bytes) : GTot (option (H.handshake_msg & nat)) =
  if B.length input < 4 then None
  else
    let msg_type = nat_of_byte (Seq.index input 0) in
    let body_len = read_u24 input 1 in
    if body_len + 4 > B.length input then None
    else
      let consumed = body_len + 4 in
      let body = Seq.slice input 4 consumed in
      match msg_type with
      | 2 ->
        (match parse_supported_server_hello_impl (Seq.slice input 0 consumed) with
         | Some sh -> Some (H.ServerHello sh, consumed)
         | None -> None)
      | 8 -> Some (H.EncryptedExtensions { H.negotiated_alpn = None }, consumed)
      | 11 -> Some (H.Certificate { H.chain = [body] }, consumed)
      | 15 ->
        (match parse_certificate_verify_impl body with
         | Some cv -> Some (H.CertificateVerify cv, consumed)
         | None -> None)
      | 20 ->
        if B.length body == 32
        then Some (H.Finished { H.verify_data = body }, consumed)
        else None
      | _ -> None

let parse_supported_server_hello (input:B.bytes) : GTot (option H.server_hello) =
  parse_supported_server_hello_impl input

let parse_certificate_leaf_der (input:B.bytes) : GTot (option B.bytes) =
  parse_certificate_leaf_der_impl input

let parse_certificate_verify (input:B.bytes) : GTot (option H.certificate_verify) =
  parse_certificate_verify_impl input

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

let supported_versions_extension (_:unit) : GTot B.bytes =
  append4 (u16 0x002b) (u16 3) (u8 2) (u16 0x0304)

let client_hello_extensions (hello:H.client_hello) : GTot B.bytes =
  let hostname =
    match hello.H.server_name with
    | Some h -> h
    | None -> B.empty in
  append5
    (server_name_extension hostname)
    (supported_groups_extension ())
    (signature_algorithms_extension ())
    (key_share_extension hello.H.key_share)
    (supported_versions_extension ())

let serialize_supported_client_hello (hello:H.client_hello) : GTot B.bytes =
  let extensions = client_hello_extensions hello in
  let body =
    append6
      (u16 0x0303)
      hello.H.random
      (u8 0)
      (append3 (u16 2) (u16 0x1303) (u8 1))
      (u8 0)
      (B.append (u16 (B.length extensions)) extensions) in
  append3 (u8 1) (u24 (B.length body)) body

let serialize_handshake_body (msg:H.handshake_msg) : GTot (option (nat & B.bytes)) =
  match msg with
  | H.ClientHello hello ->
    let encoded = serialize_supported_client_hello hello in
    if B.length encoded >= 4 then Some (1, Seq.slice encoded 4 (B.length encoded)) else None
  | H.ServerHello sh ->
    let extensions =
      B.append (key_share_extension sh.H.key_share) (supported_versions_extension ()) in
    let body =
      append6
        (u16 0x0303)
        sh.H.random
        (u8 0)
        (u16 (cipher_suite_to_u16 sh.H.cipher_suite))
        (u8 0)
        (B.append (u16 (B.length extensions)) extensions) in
    Some (2, body)
  | H.EncryptedExtensions _ -> Some (8, u16 0)
  | H.Certificate cert ->
    let chain_bytes =
      match cert.H.chain with
      | [] -> B.empty
      | leaf :: _ -> append3 (u24 (B.length leaf)) leaf (u16 0) in
    Some (11, append3 (u8 0) (u24 (B.length chain_bytes)) chain_bytes)
  | H.CertificateVerify cv ->
    Some (15, append3
                (u16 (signature_scheme_to_u16 cv.H.scheme))
                (u16 (B.length cv.H.signature))
                cv.H.signature)
  | H.Finished fin -> Some (20, fin.H.verify_data)
  | H.HelloRetryRequest -> None

let serialize_handshake (msg:H.handshake_msg) : GTot B.bytes =
  match serialize_handshake_body msg with
  | Some (msg_type, body) -> append3 (u8 msg_type) (u24 (B.length body)) body
  | None -> B.empty

let serialize_server_certificate_verify_input (transcript_hash:B.bytes) : GTot B.bytes =
  if B.length transcript_hash == 32
  then H.certificate_verify_input transcript_hash
  else B.empty

let parse_record (input:B.bytes) : GTot (option (T.content_type & R.sealed_record & nat)) =
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

let serialize_record (content_type:T.content_type) (fragment:B.bytes) : GTot B.bytes =
  append3
    (u8 (content_type_to_byte content_type))
    (u16 0x0303)
    (B.append (u16 (B.length fragment)) fragment)
