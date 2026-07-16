module TLS13.Wire.Spec.Reveal.Injective

friend TLS13.Wire.Spec

module B = TLS13.Bytes
module GCH = TLS13.Wire.Generated.ClientHello
module GHS = TLS13.Wire.Generated.Handshake
module GSH = TLS13.Wire.Generated.ServerHello
module LP = LowParse.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

(* [serialize_record ct fragment] is, definitionally (via [friend WS]),
   [append a (append b (append lenb fragment))] where [a] (1 byte, the content
   type), [b] (2 bytes, the legacy version 0x0303) and [lenb] (2 bytes, the
   fragment length prefix) are fixed-width.  The fragment therefore appears
   verbatim after the 5-byte header, and three applications of
   [Seq.lemma_append_inj] recover it from the wire image. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let lemma_serialize_record_injective ct f1 f2 =
  let a = WS.u8 (WS.content_type_to_byte ct) in
  let b = WS.u16 0x0303 in
  let lenb1 = WS.u16 (B.length f1) in
  let lenb2 = WS.u16 (B.length f2) in
  assert (B.length a == 1);
  assert (B.length b == 2);
  assert (B.length lenb1 == 2);
  assert (B.length lenb2 == 2);
  assert (WS.serialize_record ct f1 == B.append a (B.append b (B.append lenb1 f1)));
  assert (WS.serialize_record ct f2 == B.append a (B.append b (B.append lenb2 f2)));
  Seq.lemma_append_inj
    a (B.append b (B.append lenb1 f1))
    a (B.append b (B.append lenb2 f2));
  Seq.lemma_append_inj
    b (B.append lenb1 f1)
    b (B.append lenb2 f2);
  Seq.lemma_append_inj lenb1 f1 lenb2 f2
#pop-options

(* [serialize_handshake (M.ClientHello ch)] unfolds (via [friend WS]) to
   [LP.serialize handshake_serializer (Body_client_hello ch)]; the generated
   serializer is injective ([LP.serializer_injective]), and the [Body_client_hello]
   constructor is injective, so equal wire images give equal records. *)
#push-options "--fuel 8 --ifuel 2 --z3rlimit 40"
let lemma_serialize_handshake_client_hello_injective ch1 ch2 =
  Seq.lemma_eq_elim
    (WS.serialize_handshake (M.ClientHello ch1))
    (WS.serialize_handshake (M.ClientHello ch2));
  assert (WS.serialize_handshake (M.ClientHello ch1) ==
          LP.serialize GHS.handshake_serializer (GHS.Body_client_hello ch1));
  assert (WS.serialize_handshake (M.ClientHello ch2) ==
          LP.serialize GHS.handshake_serializer (GHS.Body_client_hello ch2));
  LP.serializer_injective
    GHS.handshake_parser GHS.handshake_serializer
    (GHS.Body_client_hello ch1) (GHS.Body_client_hello ch2)
#pop-options

#push-options "--fuel 8 --ifuel 2 --z3rlimit 40"
let lemma_serialize_handshake_server_hello_injective sh1 sh2 =
  Seq.lemma_eq_elim
    (WS.serialize_handshake (M.ServerHello sh1))
    (WS.serialize_handshake (M.ServerHello sh2));
  assert (WS.serialize_handshake (M.ServerHello sh1) ==
          LP.serialize GHS.handshake_serializer (GHS.Body_server_hello sh1));
  assert (WS.serialize_handshake (M.ServerHello sh2) ==
          LP.serialize GHS.handshake_serializer (GHS.Body_server_hello sh2));
  LP.serializer_injective
    GHS.handshake_parser GHS.handshake_serializer
    (GHS.Body_server_hello sh1) (GHS.Body_server_hello sh2)
#pop-options
