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
module T = TLS13.Types
module WS = TLS13.Wire.Spec

(* Parse-direction reveal: the "Some" arm of the handshake correspondence.  When
   the generated LowParse handshake parser consumes the whole fragment and the
   structural [synth_handshake_msg_of] dispatch yields [Some msg], the abstract
   [WS.parse_tls_message T.Handshake] returns exactly [M.TlsHandshake msg].  This
   is the definitional unfolding of [parse_tls_message] o [parse_handshake]; kept
   here (friending [TLS13.Wire.Spec]) so the impl parser can relate the copyful
   reader's generated [handshake] to the spec without unfolding [parse_tls_message]
   everywhere.  Replaces the pre-migration guarded [lemma_ptm_handshake_some]. *)
val lemma_ptm_handshake_some
  (fragment:B.bytes)
  (v:GHS.handshake)
  (msg:M.handshake_msg)
  : Lemma
    (requires LP.parse GHS.handshake_parser fragment == Some (v, B.length fragment) /\
              WS.synth_handshake_msg_of v == Some msg)
    (ensures WS.parse_tls_message T.Handshake fragment == Some (M.TlsHandshake msg))

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
