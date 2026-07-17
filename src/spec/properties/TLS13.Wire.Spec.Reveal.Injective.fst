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
module WRU = TLS13.Wire.Spec.Reveal.Util

(* The generated TLSCiphertext image has a five-byte header in its valid domain,
   so append injectivity recovers the fragment directly. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 20"
let lemma_serialize_record_injective ct f1 f2 =
  let h1 = WRU.serialize_record_header ct (B.length f1) in
  let h2 = WRU.serialize_record_header ct (B.length f2) in
  WRU.lemma_serialize_record_reveal ct f1;
  WRU.lemma_serialize_record_reveal ct f2;
  Seq.lemma_eq_elim
    (WS.serialize_record ct f1)
    (WS.serialize_record ct f2);
  Seq.lemma_append_inj
    h1 f1
    h2 f2
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
