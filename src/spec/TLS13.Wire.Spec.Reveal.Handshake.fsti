module TLS13.Wire.Spec.Reveal.Handshake

(* Build-direction reveal lemmas exposing how the abstract high-level
   [TLS13.Wire.Spec.serialize_handshake] unfolds to the QuackyDucky-generated
   LowParse handshake serializer.  These are the per-constructor definitional
   unfoldings used by the impl serializers (TLS13.Impl.Serializer.Handshake) to
   connect the generated copyful-low writers to the spec.  Kept in a dedicated
   [Reveal.*] module (friending [TLS13.Wire.Spec]) so that [serialize_handshake]
   stays abstract everywhere else, matching the branch's spec-reveal design. *)

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
module WS = TLS13.Wire.Spec

val lemma_serialize_handshake_client_hello (ch:GCH.clientHello) :
  Lemma (Seq.equal (WS.serialize_handshake (M.ClientHello ch))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_client_hello ch)))

val lemma_serialize_handshake_server_hello (sh:GSH.serverHello) :
  Lemma (Seq.equal (WS.serialize_handshake (M.ServerHello sh))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_server_hello sh)))

val lemma_serialize_handshake_encrypted_extensions (ee:GEE.encryptedExtensions) :
  Lemma (Seq.equal (WS.serialize_handshake (M.EncryptedExtensions ee))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_encrypted_extensions ee)))

val lemma_serialize_handshake_certificate (cert:GCert.certificate) :
  Lemma (requires GCert.certificate_bytesize cert <= 16777215)
        (ensures Seq.equal (WS.serialize_handshake (M.Certificate cert))
                   (LP.serialize GHS.handshake_serializer
                      (GHS.Body_certificate (cert <: GHS.handshake_body_certificate))))

val lemma_serialize_handshake_certificate_verify (cv:GCV.certificateVerify) :
  Lemma (Seq.equal (WS.serialize_handshake (M.CertificateVerify cv))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_certificate_verify cv)))

val lemma_serialize_handshake_finished (fin:GFin.finished) :
  Lemma (Seq.equal (WS.serialize_handshake (M.Finished fin))
                   (LP.serialize GHS.handshake_serializer (GHS.Body_finished fin)))
