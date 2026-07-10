module TLS13.Wire.Spec.Reveal.Handshake

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module GCert = TLS13.Wire.Generated.Certificate
module GCH = TLS13.Wire.Generated.ClientHello
module GCV = TLS13.Wire.Generated.CertificateVerify
module GEE = TLS13.Wire.Generated.EncryptedExtensions
module GFin = TLS13.Wire.Generated.Finished
module GHS = TLS13.Wire.Generated.Handshake
module GSH = TLS13.Wire.Generated.ServerHello
module LP = LowParse.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

(* All six lemmas are the definitional unfolding of [WS.serialize_handshake]'s
   per-constructor match arm.  With [friend TLS13.Wire.Spec] the definition is
   transparent, so each goal reduces to [Seq.equal x x]. *)

let lemma_ptm_handshake_some fragment v msg = ()

let lemma_serialize_handshake_client_hello ch = ()
let lemma_serialize_handshake_server_hello sh = ()
let lemma_serialize_handshake_encrypted_extensions ee = ()
let lemma_serialize_handshake_certificate cert = ()
let lemma_serialize_handshake_certificate_verify cv = ()
let lemma_serialize_handshake_finished fin = ()
