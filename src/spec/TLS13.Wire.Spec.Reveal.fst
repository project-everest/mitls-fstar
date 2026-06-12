module TLS13.Wire.Spec.Reveal
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module WS = TLS13.Wire.Spec
module GHS = TLS13.Wire.Generated.Handshake
module GSS = TLS13.Wire.Generated.SignatureScheme
module GCS = TLS13.Wire.Generated.CipherSuite
module GCV = TLS13.Wire.Generated.CertificateVerify
module GEEE = TLS13.Wire.Generated.ExtensionEncryptedExtensions
module GPN = TLS13.Wire.Generated.ProtocolName
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module GSHBody = TLS13.Wire.Generated.ServerHelloBody
module GESH = TLS13.Wire.Generated.ExtensionServerHello
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GNG = TLS13.Wire.Generated.NamedGroup
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GCert = TLS13.Wire.Generated.Certificate
module GCE = TLS13.Wire.Generated.CertificateEntry
module LP = LowParse.Spec

let lemma_ptm_change_cipher_spec fragment =
  if B.length fragment = 1 && U8.v (Seq.index fragment 0) = 1
  then assert (WS.nat_of_byte (Seq.index fragment 0) == 1)
  else ()

let lemma_ptm_application_data fragment = ()

let lemma_parse_plaintext_fragment_len input =
  match WS.parse_plaintext input with
  | Some pt -> Seq.lemma_len_slice input 0 (B.length input - 1)
  | None -> ()

let lemma_ptm_alert fragment =
  if B.length fragment <> 2
  then ()
  else assert (WS.nat_of_byte (Seq.index fragment 1) == U8.v (Seq.index fragment 1))

let handshake_synth h = WS.synth_handshake_msg_of h

let synth_cipher_suite c = WS.synth_cipher_suite c

let synth_signature_scheme s = WS.synth_signature_scheme s

let lemma_synth_signature_scheme s = ()

let lemma_ptm_handshake_some fragment v m =
  assert (WS.parse_handshake fragment == Some (m, B.length fragment))

let lemma_handshake_synth_finished b = ()

let lemma_handshake_synth_certificate_verify b = ()

let lemma_handshake_synth_key_update b = ()

let reveal_parse_ignored_post_handshake input = WS.parse_ignored_post_handshake input

(* a*65536 + b*256 + c == 1 with 0 <= a,b,c <= 255 forces a=b=0, c=1.
   (multiplication by literal constants is linear, so SMT handles this.) *)
let lemma_u24_one (input:B.bytes{B.length input >= 4})
  : Lemma (WS.read_u24 input 1 == 1 <==>
           (U8.v (Seq.index input 1) == 0 /\
            U8.v (Seq.index input 2) == 0 /\
            U8.v (Seq.index input 3) == 1))
= ()

let lemma_parse_key_update_def input =
  if B.length input = 5 then lemma_u24_one input else ()

let lemma_parse_ignored_post_handshake_def input = ()

let lemma_parse_handshake_none_of_lp_none fragment = ()

let lemma_parse_handshake_none_of_synth_none fragment v consumed = ()

let lemma_ptm_handshake_fallback fragment = ()


let reveal_synth_encrypted_extensions l = WS.synth_encrypted_extensions l

let reveal_alpn_first_name pnl = WS.alpn_first_name pnl

let lemma_handshake_synth_encrypted_extensions b = ()

let lemma_synth_ee_nil () = ()

let lemma_synth_ee_cons_non_alpn e tl = ()

let lemma_synth_ee_cons_alpn pnl tl = ()
let rec lemma_list_drop_index #a l i =
  if i = 0 then ()
  else (match l with | _ :: tl -> lemma_list_drop_index tl (i - 1))

let rec lemma_list_drop_length #a l =
  match l with
  | [] -> ()
  | _ :: tl -> lemma_list_drop_length tl

let lemma_alpn_first_name_index0 pnl = ()

(* --- ServerHello reveal interface --------------------------------------- *)

let reveal_key_exchange_to_key32 ke = WS.key_exchange_to_key32 ke

let lemma_reveal_key_exchange_to_key32 ke = ()

let reveal_sh_key_share l saw key_share = WS.sh_key_share l saw key_share

let lemma_sh_key_share_nil saw key_share = ()

let lemma_sh_key_share_cons e tl saw key_share = ()

let lemma_handshake_synth_server_hello_bad_version b = ()

let lemma_handshake_synth_server_hello_hrr b shb = ()

let lemma_handshake_synth_server_hello_sh b sf = ()

(* --- Certificate reveal interface --------------------------------------- *)

let reveal_synth_cert_chain l = WS.synth_cert_chain l

let reveal_cert_chain_total_bytes chain = WS.cert_chain_total_bytes chain

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

let lemma_handshake_synth_certificate b = ()
