module TLS13.Wire.Spec.Reveal.Injective

(** Injectivity of the record framing and of the generated handshake serializer.

    Both facts are consequences of the QuackyDucky/LowParse codec being an
    honest serializer:

    * [serialize_record] appends the [fragment] verbatim after a fixed 5-byte
      header, so two records with equal wire images have equal fragments (no
      size bound is needed: the fragment always occupies the bytes from offset
      5 to the end).

    * [serialize_handshake] on a fixed constructor is [LP.serialize] of the
      generated [handshake_serializer], which is injective ([LP.serializer_injective]).

    These let [TLS13.Spec.WireFormatLemmas] recover message equality from raw
    wire-byte equality without friending the codec itself. *)

module B = TLS13.Bytes
module GCH = TLS13.Wire.Generated.ClientHello
module GSH = TLS13.Wire.Generated.ServerHello
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

val lemma_serialize_record_injective
  (ct:T.content_type)
  (f1 f2:B.bytes)
  : Lemma
      (requires
        Seq.equal (WS.serialize_record ct f1) (WS.serialize_record ct f2))
      (ensures Seq.equal f1 f2)

val lemma_serialize_handshake_client_hello_injective
  (ch1 ch2:GCH.clientHello)
  : Lemma
      (requires
        Seq.equal
          (WS.serialize_handshake (M.ClientHello ch1))
          (WS.serialize_handshake (M.ClientHello ch2)))
      (ensures ch1 == ch2)

val lemma_serialize_handshake_server_hello_injective
  (sh1 sh2:GSH.serverHello)
  : Lemma
      (requires
        Seq.equal
          (WS.serialize_handshake (M.ServerHello sh1))
          (WS.serialize_handshake (M.ServerHello sh2)))
      (ensures sh1 == sh2)
