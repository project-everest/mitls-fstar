module TLS13.Impl.Messages

#lang-pulse

open Pulse.Lib.Pervasives

module B = TLS13.Bytes
module L = FStar.List.Tot
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Sem = TLS13.Wire.Semantics
module T = TLS13.Types
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module V = Pulse.Lib.Vec

// Phase 5: handshake_msg payloads are now the QuackyDucky-generated wire
// records; profile-relevant fields are read through the TLS13.Wire.Semantics
// accessors instead of the deleted M.<record> projection fields.
module GCH   = TLS13.Wire.Generated.ClientHello
module GSH   = TLS13.Wire.Generated.ServerHello
module GEE   = TLS13.Wire.Generated.EncryptedExtensions
module GCert = TLS13.Wire.Generated.Certificate
module GCV   = TLS13.Wire.Generated.CertificateVerify
module GFin  = TLS13.Wire.Generated.Finished

(**
  Extraction-oriented low-level message layer.

  The types in this module are the L counterparts of TLS13.Messages.  Fixed
  wire discriminants and lengths use machine integers; variable-size payloads
  are represented by heap vectors plus explicit SizeT lengths.  The is_valid_*
  predicates are ghost-only ownership/correspondence predicates tying each L
  value to its pure M value.
**)

noextract
let max_server_name_len : nat = 255

noextract
let max_alpn_len : nat = 255

noextract
let max_cipher_suites : nat = 64

noextract
let max_signature_schemes : nat = 32

noextract
let max_certificate_chain_bytes : nat = 32768

(* [SZ.t] companion (sz literal) so executable [SZ.uint_to_t max_certificate_chain_bytes]
   positions extract to a plain C [size_t] constant instead of [FStar_SizeT_uint_to_t]. *)
inline_for_extraction let max_certificate_chain_bytes_sz : SZ.t = 32768sz

noextract
let max_certificate_chain_entries : nat = 8

noextract
let max_signature_len : nat = 4096

inline_for_extraction let max_signature_len_sz : SZ.t = 4096sz

noextract
let max_record_fragment_len : nat = 16640

noeq
type client_hello = {
  client_hello_random: V.vec U8.t;
  client_hello_session_id: V.vec U8.t;
  client_hello_server_name: V.vec U8.t;
  client_hello_server_name_len: SZ.t;
  client_hello_has_server_name: bool;
  client_hello_key_share: V.vec U8.t;
  client_hello_cipher_suites: V.vec U16.t;
  client_hello_cipher_suites_len: SZ.t;
  client_hello_signature_schemes: V.vec U16.t;
  client_hello_signature_schemes_len: SZ.t;
}

noeq
type server_hello = {
  server_hello_random: V.vec U8.t;
  server_hello_session_id: V.vec U8.t;
  server_hello_key_share: V.vec U8.t;
  server_hello_cipher_suite: U16.t;
}

noeq
type encrypted_extensions = {
  encrypted_extensions_alpn: V.vec U8.t;
  encrypted_extensions_alpn_len: SZ.t;
  encrypted_extensions_has_alpn: bool;
}

noeq
type certificate_msg = {
  certificate_msg_chain_bytes: V.vec U8.t;
  certificate_msg_chain_bytes_len: SZ.t;
  certificate_msg_cert_offsets: V.vec SZ.t;
  certificate_msg_cert_lens: V.vec SZ.t;
  certificate_msg_cert_count: SZ.t;
}

noeq
type certificate_verify = {
  certificate_verify_scheme: U16.t;
  certificate_verify_signature: V.vec U8.t;
  certificate_verify_signature_len: SZ.t;
}

noeq
type finished = {
  finished_verify_data: V.vec U8.t;
}

noeq
type handshake_msg =
  | LClientHello of client_hello
  | LServerHello of server_hello
  | LEncryptedExtensions of encrypted_extensions
  | LCertificate of certificate_msg
  | LCertificateVerify of certificate_verify
  | LFinished of finished
  | LHelloRetryRequest

noeq
type plaintext = {
  plaintext_content_type: U8.t;
  plaintext_fragment: V.vec U8.t;
  plaintext_fragment_len: SZ.t;
}

noeq
type sealed_record = {
  sealed_record_fragment: V.vec U8.t;
  sealed_record_fragment_len: SZ.t;
}

noeq
type application_data = {
  application_data_bytes: V.vec U8.t;
  application_data_len: SZ.t;
}

noeq
type tls_message =
  | LTlsHandshake of handshake_msg
  | LTlsApplicationData of application_data
  | LTlsAlert of U8.t
  | LTlsChangeCipherSpec
  | LTlsIgnoredPostHandshake of application_data
  | LTlsKeyUpdate of U8.t

let tls_message_is_handshake (l:tls_message) : bool =
  match l with
  | LTlsHandshake _ -> true
  | _ -> false

let tls_message_is_application_data (l:tls_message) : bool =
  match l with
  | LTlsApplicationData _ -> true
  | _ -> false

let tls_message_is_alert (l:tls_message) : bool =
  match l with
  | LTlsAlert _ -> true
  | _ -> false

let tls_message_is_change_cipher_spec (l:tls_message) : bool =
  match l with
  | LTlsChangeCipherSpec -> true
  | _ -> false

let tls_message_is_ignored_post_handshake (l:tls_message) : bool =
  match l with
  | LTlsIgnoredPostHandshake _ -> true
  | _ -> false

let tls_message_is_key_update (l:tls_message) : bool =
  match l with
  | LTlsKeyUpdate _ -> true
  | _ -> false

let lemma_tls_message_classifier_complete (l:tls_message)
  : Lemma (
      tls_message_is_handshake l \/
      tls_message_is_application_data l \/
      tls_message_is_alert l \/
      tls_message_is_change_cipher_spec l \/
      tls_message_is_ignored_post_handshake l \/
      tls_message_is_key_update l)
  =
  match l with
  | LTlsHandshake _ -> ()
  | LTlsApplicationData _ -> ()
  | LTlsAlert _ -> ()
  | LTlsChangeCipherSpec -> ()
  | LTlsIgnoredPostHandshake _ -> ()
  | LTlsKeyUpdate _ -> ()

noeq
type tls_record = {
  tls_record_outer_type: U8.t;
  tls_record_fragment: sealed_record;
}

noeq
type decoded_network_record = {
  decoded_record_content_type: U8.t;
  decoded_record_fragment: V.vec U8.t;
  decoded_record_fragment_len: SZ.t;
  decoded_record_parsed: option tls_message;
}

noeq
type decoded_network_record_result =
  | NetworkRecordNeedMoreInput
  | NetworkRecordDecodeError
  | NetworkRecordOk of decoded_network_record

noeq
type parsed_handshake_prefix = {
  parsed_handshake_message: tls_message;
  parsed_handshake_consumed: SZ.t;
  parsed_handshake_fragment: V.vec U8.t;
}

noeq
type decoded_network_buffer = {
  decoded_buffer_raw_record: V.vec U8.t;
  decoded_buffer_raw_record_len: SZ.t;
  decoded_buffer_consumed_len: SZ.t;
  decoded_buffer_content_type: U8.t;
  decoded_buffer_fragment: V.vec U8.t;
  decoded_buffer_fragment_len: SZ.t;
  decoded_buffer_parsed: option tls_message;
  decoded_buffer_protected: bool;
}

noeq
type decoded_network_buffer_result =
  | NetworkBufferNeedMoreInput
  | NetworkBufferDecodeError
  | NetworkBufferOk of decoded_network_buffer

noextract
let content_type_matches (wire:U8.t) (ct:T.content_type) : prop =
  match ct with
  | T.Invalid -> U8.v wire == 0x00
  | T.Change_cipher_spec -> U8.v wire == 0x14
  | T.Alert -> U8.v wire == 0x15
  | T.Handshake -> U8.v wire == 0x16
  | T.Application_data -> U8.v wire == 0x17

noextract
let alert_description_matches (wire:U8.t) (alert:T.alert_description) : prop =
  match alert with
  | T.Close_notify -> U8.v wire == 0
  | T.Unexpected_message -> U8.v wire == 10
  | T.Bad_record_mac -> U8.v wire == 20
  | T.Handshake_failure -> U8.v wire == 40
  | T.Decode_error -> U8.v wire == 50
  | T.Decrypt_error -> U8.v wire == 51
  | T.Protocol_version -> U8.v wire == 70
  | T.Unsupported_extension -> U8.v wire == 110
  | T.Certificate_unknown -> U8.v wire == 46
  | T.Illegal_parameter -> U8.v wire == 47

noextract
let key_update_request_matches (wire:U8.t) (req:M.key_update_request) : prop =
  match req with
  | M.UpdateNotRequested -> U8.v wire == 0
  | M.UpdateRequested -> U8.v wire == 1

let alert_description_of_wire_or_unexpected
  (wire:U8.t)
  : T.alert_description =
  if wire = 0uy then T.Close_notify
  else if wire = 10uy then T.Unexpected_message
  else if wire = 20uy then T.Bad_record_mac
  else if wire = 40uy then T.Handshake_failure
  else if wire = 46uy then T.Certificate_unknown
  else if wire = 47uy then T.Illegal_parameter
  else if wire = 50uy then T.Decode_error
  else if wire = 51uy then T.Decrypt_error
  else if wire = 70uy then T.Protocol_version
  else if wire = 110uy then T.Unsupported_extension
  else T.Unexpected_message

let lemma_alert_description_of_wire_matches
  (wire:U8.t)
  (alert:T.alert_description)
  : Lemma
      (requires alert_description_matches wire alert)
      (ensures alert_description_of_wire_or_unexpected wire == alert /\
               alert_description_matches wire (alert_description_of_wire_or_unexpected wire))
=
  match alert with
  | T.Close_notify -> ()
  | T.Unexpected_message -> ()
  | T.Bad_record_mac -> ()
  | T.Handshake_failure -> ()
  | T.Decode_error -> ()
  | T.Decrypt_error -> ()
  | T.Protocol_version -> ()
  | T.Unsupported_extension -> ()
  | T.Certificate_unknown -> ()
  | T.Illegal_parameter -> ()

let lemma_alert_description_nonzero_not_close_notify
  (wire:U8.t)
  (alert:T.alert_description)
  : Lemma
      (requires alert_description_matches wire alert /\ U8.v wire <> 0)
      (ensures alert <> T.Close_notify)
=
  match alert with
  | T.Close_notify -> ()
  | T.Unexpected_message -> ()
  | T.Bad_record_mac -> ()
  | T.Handshake_failure -> ()
  | T.Decode_error -> ()
  | T.Decrypt_error -> ()
  | T.Protocol_version -> ()
  | T.Unsupported_extension -> ()
  | T.Certificate_unknown -> ()
  | T.Illegal_parameter -> ()

noextract
let cipher_suite_matches (wire:U16.t) (suite:T.cipher_suite) : prop =
  match suite with
  | T.TLS_CHACHA20_POLY1305_SHA256 -> U16.v wire == 0x1303
  | T.Unknown_cipherSuite n -> U16.v wire == U16.v n /\ U16.v n <> 0x1303

noextract
let signature_scheme_matches (wire:U16.t) (scheme:T.signature_scheme) : prop =
  match scheme with
  | T.Rsa_pss_rsae_sha256 -> U16.v wire == 0x0804
  | T.Ecdsa_secp256r1_sha256 -> U16.v wire == 0x0403
  | T.Ed25519 -> U16.v wire == 0x0807
  | T.Unknown_signatureScheme n ->
    U16.v wire == U16.v n /\
    U16.v n <> 0x0804 /\
    U16.v n <> 0x0403 /\
    U16.v n <> 0x0807

noextract
let byte_prefix_matches
  (storage:B.bytes)
  (len:SZ.t)
  (bytes:B.bytes)
  : prop =
  SZ.v len <= B.length storage /\
  Seq.equal bytes (Seq.slice storage 0 (SZ.v len))

noextract
let optional_byte_prefix_matches
  (present:bool)
  (storage:B.bytes)
  (len:SZ.t)
  (bytes:option B.bytes)
  : prop =
  if present then
    match bytes with
    | Some b -> byte_prefix_matches storage len b
    | None -> False
  else bytes == None

noextract
let rec cipher_suites_match
  (wire:Seq.seq U16.t)
  (len:nat)
  (suites:list T.cipher_suite)
  : Tot prop
    (decreases len)
  =
  if len == 0 then suites == []
  else if len <= Seq.length wire then
    match suites with
    | suite :: rest ->
      cipher_suite_matches (Seq.index wire 0) suite /\
      cipher_suites_match (Seq.slice wire 1 (Seq.length wire)) (len - 1) rest
    | [] -> False
  else False

noextract
let rec signature_schemes_match
  (wire:Seq.seq U16.t)
  (len:nat)
  (schemes:list T.signature_scheme)
  : Tot prop
    (decreases len)
  =
  if len == 0 then schemes == []
  else if len <= Seq.length wire then
    match schemes with
    | scheme :: rest ->
      signature_scheme_matches (Seq.index wire 0) scheme /\
      signature_schemes_match (Seq.slice wire 1 (Seq.length wire)) (len - 1) rest
    | [] -> False
  else False

noextract
let rec certificate_chain_matches
  (storage:B.bytes)
  (storage_len:nat)
  (offsets:Seq.seq SZ.t)
  (lens:Seq.seq SZ.t)
  (count:nat)
  (chain:list B.bytes)
  : Tot prop
    (decreases count)
  =
  if count == 0 then chain == []
  else if storage_len <= B.length storage /\
          count <= Seq.length offsets /\
          count <= Seq.length lens then
    match chain with
    | cert :: rest ->
      let offset = SZ.v (Seq.index offsets 0) in
      let cert_len = SZ.v (Seq.index lens 0) in
      offset + cert_len <= storage_len /\
      Seq.equal cert (Seq.slice storage offset (offset + cert_len)) /\
      certificate_chain_matches
        storage
        storage_len
        (Seq.slice offsets 1 (Seq.length offsets))
        (Seq.slice lens 1 (Seq.length lens))
        (count - 1)
        rest
    | [] -> False
  else False

let is_valid_client_hello ([@@@mkey] l:client_hello) (m:GCH.clientHello) : slprop =
  exists* random session_id server_name key_share cipher_suites signature_schemes.
    V.pts_to l.client_hello_random random **
    V.pts_to l.client_hello_session_id session_id **
    V.pts_to l.client_hello_server_name server_name **
    V.pts_to l.client_hello_key_share key_share **
    V.pts_to l.client_hello_cipher_suites cipher_suites **
    V.pts_to l.client_hello_signature_schemes signature_schemes **
    pure (
      V.is_full_vec l.client_hello_random /\
      V.is_full_vec l.client_hello_session_id /\
      V.length l.client_hello_session_id == 32 /\
      B.length session_id == 32 /\
      Seq.equal session_id (Sem.clientHello_session_id_32 m) /\
      V.is_full_vec l.client_hello_server_name /\
      V.is_full_vec l.client_hello_key_share /\
      V.is_full_vec l.client_hello_cipher_suites /\
      V.is_full_vec l.client_hello_signature_schemes /\
      V.length l.client_hello_random == 32 /\
      V.length l.client_hello_server_name == max_server_name_len /\
      V.length l.client_hello_key_share == 32 /\
      V.length l.client_hello_cipher_suites == max_cipher_suites /\
      V.length l.client_hello_signature_schemes == max_signature_schemes /\
      B.length random == 32 /\
      B.length server_name == max_server_name_len /\
      B.length key_share == 32 /\
      Seq.length cipher_suites == max_cipher_suites /\
      Seq.length signature_schemes == max_signature_schemes /\
      SZ.v l.client_hello_server_name_len <= B.length server_name /\
      SZ.v l.client_hello_cipher_suites_len <= Seq.length cipher_suites /\
      SZ.v l.client_hello_signature_schemes_len <= Seq.length signature_schemes /\
      Seq.equal random (Sem.clientHello_random m) /\
      optional_byte_prefix_matches
        l.client_hello_has_server_name
        server_name
        l.client_hello_server_name_len
        (Sem.clientHello_server_name m) /\
      (match Sem.clientHello_key_share_x25519 m with
       | Some k -> B.length k == 32 /\ Seq.equal key_share k
       | None -> False) /\
      cipher_suites_match
        cipher_suites
        (SZ.v l.client_hello_cipher_suites_len)
        (Sem.clientHello_cipher_suites m) /\
      (match Sem.clientHello_sig_algs m with
       | Some sas ->
         signature_schemes_match
           signature_schemes
           (SZ.v l.client_hello_signature_schemes_len)
           sas
       | None -> False))

let is_valid_server_hello ([@@@mkey] l:server_hello) (m:GSH.serverHello) : slprop =
  exists* random session_id key_share.
    V.pts_to l.server_hello_random random **
    V.pts_to l.server_hello_session_id session_id **
    V.pts_to l.server_hello_key_share key_share **
    pure (
      V.is_full_vec l.server_hello_random /\
      V.is_full_vec l.server_hello_session_id /\
      V.length l.server_hello_session_id == 32 /\
      B.length session_id == 32 /\
      Seq.equal session_id (Sem.serverHello_session_id_echo_32 m) /\
      V.is_full_vec l.server_hello_key_share /\
      V.length l.server_hello_random == 32 /\
      V.length l.server_hello_key_share == 32 /\
      (match Sem.serverHello_random m with
       | Some r -> Seq.equal random r
       | None -> False) /\
      (match Sem.serverHello_key_share_x25519 m with
       | Some k -> B.length k == 32 /\ Seq.equal key_share k
       | None -> False) /\
      (match Sem.serverHello_cipher_suite m with
       | Some cs ->
         cipher_suite_matches l.server_hello_cipher_suite cs /\
         cs == T.TLS_CHACHA20_POLY1305_SHA256
       | None -> False))

let is_valid_encrypted_extensions
  ([@@@mkey] l:encrypted_extensions)
  (m:GEE.encryptedExtensions)
  : slprop =
  exists* alpn.
    V.pts_to l.encrypted_extensions_alpn alpn **
    pure (
      V.is_full_vec l.encrypted_extensions_alpn /\
      V.length l.encrypted_extensions_alpn == max_alpn_len /\
      SZ.v l.encrypted_extensions_alpn_len <= B.length alpn /\
      optional_byte_prefix_matches
        l.encrypted_extensions_has_alpn
        alpn
        l.encrypted_extensions_alpn_len
        (Sem.encryptedExtensions_alpn m))

let is_valid_certificate_msg ([@@@mkey] l:certificate_msg) (m:GCert.certificate) : slprop =
  exists* chain_bytes offsets lens.
    V.pts_to l.certificate_msg_chain_bytes chain_bytes **
    V.pts_to l.certificate_msg_cert_offsets offsets **
    V.pts_to l.certificate_msg_cert_lens lens **
    pure (
      V.is_full_vec l.certificate_msg_chain_bytes /\
      V.is_full_vec l.certificate_msg_cert_offsets /\
      V.is_full_vec l.certificate_msg_cert_lens /\
      V.length l.certificate_msg_chain_bytes == max_certificate_chain_bytes /\
      V.length l.certificate_msg_cert_offsets == max_certificate_chain_entries /\
      V.length l.certificate_msg_cert_lens == max_certificate_chain_entries /\
      SZ.v l.certificate_msg_chain_bytes_len <= B.length chain_bytes /\
      SZ.v l.certificate_msg_cert_count <= Seq.length offsets /\
      SZ.v l.certificate_msg_cert_count <= Seq.length lens /\
      certificate_chain_matches
        chain_bytes
        (SZ.v l.certificate_msg_chain_bytes_len)
        offsets
        lens
        (SZ.v l.certificate_msg_cert_count)
        (Sem.certificate_entries m))

let is_valid_certificate_verify
  ([@@@mkey] l:certificate_verify)
  (m:GCV.certificateVerify)
  : slprop =
  exists* signature.
    V.pts_to l.certificate_verify_signature signature **
    pure (
      V.is_full_vec l.certificate_verify_signature /\
      V.length l.certificate_verify_signature == max_signature_len /\
      byte_prefix_matches
        signature
        l.certificate_verify_signature_len
        (Sem.certificateVerify_signature_bytes m) /\
      signature_scheme_matches l.certificate_verify_scheme (Sem.certificateVerify_scheme m))

let is_valid_finished ([@@@mkey] l:finished) (m:GFin.finished) : slprop =
  exists* verify_data.
    V.pts_to l.finished_verify_data verify_data **
    pure (
      V.is_full_vec l.finished_verify_data /\
      V.length l.finished_verify_data == 32 /\
      Seq.equal verify_data (Sem.finished_verify_data m))

let is_valid_handshake_msg ([@@@mkey] l:handshake_msg) (m:M.handshake_msg) : slprop =
  match l with
  | LClientHello lch ->
    exists* (mch:GCH.clientHello). is_valid_client_hello lch mch ** pure (m == M.ClientHello mch)
  | LServerHello lsh ->
    exists* (msh:GSH.serverHello). is_valid_server_hello lsh msh ** pure (m == M.ServerHello msh)
  | LEncryptedExtensions lee ->
    exists* (mee:GEE.encryptedExtensions). is_valid_encrypted_extensions lee mee ** pure (m == M.EncryptedExtensions mee)
  | LCertificate lcert ->
    exists* (mcert:GCert.certificate). is_valid_certificate_msg lcert mcert ** pure (m == M.Certificate mcert)
  | LCertificateVerify lcv ->
    exists* (mcv:GCV.certificateVerify). is_valid_certificate_verify lcv mcv ** pure (m == M.CertificateVerify mcv)
  | LFinished lfin ->
    exists* (mfin:GFin.finished). is_valid_finished lfin mfin ** pure (m == M.Finished mfin)
  | LHelloRetryRequest ->
    pure (m == M.HelloRetryRequest)

let is_valid_plaintext ([@@@mkey] l:plaintext) (m:M.plaintext) : slprop =
  exists* fragment.
    V.pts_to l.plaintext_fragment fragment **
    pure (
      V.is_full_vec l.plaintext_fragment /\
      V.length l.plaintext_fragment == max_record_fragment_len /\
      byte_prefix_matches fragment l.plaintext_fragment_len m.M.fragment /\
      content_type_matches l.plaintext_content_type m.M.content_type)

let is_valid_sealed_record ([@@@mkey] l:sealed_record) (m:M.sealed_record) : slprop =
  exists* fragment.
    V.pts_to l.sealed_record_fragment fragment **
    pure (
      V.is_full_vec l.sealed_record_fragment /\
      V.length l.sealed_record_fragment == max_record_fragment_len /\
      byte_prefix_matches fragment l.sealed_record_fragment_len m)

let is_valid_application_data ([@@@mkey] l:application_data) (m:B.bytes) : slprop =
  exists* bytes.
    V.pts_to l.application_data_bytes bytes **
    pure (
      V.is_full_vec l.application_data_bytes /\
      V.length l.application_data_bytes == max_record_fragment_len /\
      byte_prefix_matches bytes l.application_data_len m)

let is_valid_tls_message ([@@@mkey] l:tls_message) (m:M.tls_message) : slprop =
  match l with
  | LTlsHandshake lhs ->
    exists* mhs. is_valid_handshake_msg lhs mhs ** pure (m == M.TlsHandshake mhs)
  | LTlsApplicationData lapp ->
    exists* mapp. is_valid_application_data lapp mapp ** pure (m == M.TlsApplicationData mapp)
  | LTlsAlert lalert ->
    exists* malert. pure (alert_description_matches lalert malert /\ m == M.TlsAlert malert)
  | LTlsChangeCipherSpec ->
    pure (m == M.TlsChangeCipherSpec)
  | LTlsIgnoredPostHandshake lignored ->
    exists* body. is_valid_application_data lignored body ** pure (m == M.TlsIgnoredPostHandshake body)
  | LTlsKeyUpdate lreq ->
    exists* req. pure (key_update_request_matches lreq req /\ m == M.TlsKeyUpdate req)

let is_valid_tls_record ([@@@mkey] l:tls_record) (m:M.tls_record) : slprop =
  is_valid_sealed_record l.tls_record_fragment m.M.record_fragment **
  pure (content_type_matches l.tls_record_outer_type m.M.record_outer_type)

fn free_application_data
  (l:application_data)
  requires exists* m. is_valid_application_data l m
  ensures emp
{
  with m. unfold (is_valid_application_data l m);
  with bytes. _;
  V.free l.application_data_bytes;
}

fn free_client_hello
  (l:client_hello)
  requires exists* m. is_valid_client_hello l m
  ensures emp
{
  with m. unfold (is_valid_client_hello l m);
  with random session_id server_name key_share cipher_suites signature_schemes. _;
  V.free l.client_hello_random;
  V.free l.client_hello_session_id;
  V.free l.client_hello_server_name;
  V.free l.client_hello_key_share;
  V.free l.client_hello_cipher_suites;
  V.free l.client_hello_signature_schemes;
}

fn free_server_hello
  (l:server_hello)
  requires exists* m. is_valid_server_hello l m
  ensures emp
{
  with m. unfold (is_valid_server_hello l m);
  with random session_id key_share. _;
  V.free l.server_hello_random;
  V.free l.server_hello_session_id;
  V.free l.server_hello_key_share;
}

fn free_encrypted_extensions
  (l:encrypted_extensions)
  requires exists* m. is_valid_encrypted_extensions l m
  ensures emp
{
  with m. unfold (is_valid_encrypted_extensions l m);
  with alpn. _;
  V.free l.encrypted_extensions_alpn;
}

fn free_certificate_msg
  (l:certificate_msg)
  requires exists* m. is_valid_certificate_msg l m
  ensures emp
{
  with m. unfold (is_valid_certificate_msg l m);
  with chain_bytes offsets lens. _;
  V.free l.certificate_msg_chain_bytes;
  V.free l.certificate_msg_cert_offsets;
  V.free l.certificate_msg_cert_lens;
}

fn free_certificate_verify
  (l:certificate_verify)
  requires exists* m. is_valid_certificate_verify l m
  ensures emp
{
  with m. unfold (is_valid_certificate_verify l m);
  with signature. _;
  V.free l.certificate_verify_signature;
}

fn free_finished
  (l:finished)
  requires exists* m. is_valid_finished l m
  ensures emp
{
  with m. unfold (is_valid_finished l m);
  with verify_data. _;
  V.free l.finished_verify_data;
}

fn free_handshake_msg
  (l:handshake_msg)
  requires exists* m. is_valid_handshake_msg l m
  ensures emp
{
  with m. assert (pure True);
  match l {
    LClientHello lch -> {
      unfold (is_valid_handshake_msg (LClientHello lch) m);
      with mch. _;
      free_client_hello lch
    }
    LServerHello lsh -> {
      unfold (is_valid_handshake_msg (LServerHello lsh) m);
      with msh. _;
      free_server_hello lsh
    }
    LEncryptedExtensions lee -> {
      unfold (is_valid_handshake_msg (LEncryptedExtensions lee) m);
      with mee. _;
      free_encrypted_extensions lee
    }
    LCertificate lcert -> {
      unfold (is_valid_handshake_msg (LCertificate lcert) m);
      with mcert. _;
      free_certificate_msg lcert
    }
    LCertificateVerify lcv -> {
      unfold (is_valid_handshake_msg (LCertificateVerify lcv) m);
      with mcv. _;
      free_certificate_verify lcv
    }
    LFinished lfin -> {
      unfold (is_valid_handshake_msg (LFinished lfin) m);
      with mfin. _;
      free_finished lfin
    }
    LHelloRetryRequest -> {
      unfold (is_valid_handshake_msg LHelloRetryRequest m)
    }
  }
}

fn free_tls_message
  (l:tls_message)
  requires exists* m. is_valid_tls_message l m
  ensures emp
{
  with m. assert (pure True);
  match l {
    LTlsHandshake lhs -> {
      unfold (is_valid_tls_message (LTlsHandshake lhs) m);
      with mhs. _;
      free_handshake_msg lhs
    }
    LTlsApplicationData lapp -> {
      unfold (is_valid_tls_message (LTlsApplicationData lapp) m);
      with mapp. _;
      free_application_data lapp
    }
    LTlsIgnoredPostHandshake lignored -> {
      unfold (is_valid_tls_message (LTlsIgnoredPostHandshake lignored) m);
      with body. _;
      free_application_data lignored
    }
    LTlsKeyUpdate lreq -> {
      unfold (is_valid_tls_message (LTlsKeyUpdate lreq) m);
      with req. _
    }
    LTlsAlert lalert -> {
      unfold (is_valid_tls_message (LTlsAlert lalert) m);
      with malert. _
    }
    LTlsChangeCipherSpec -> {
      unfold (is_valid_tls_message LTlsChangeCipherSpec m)
    }
  }
}
