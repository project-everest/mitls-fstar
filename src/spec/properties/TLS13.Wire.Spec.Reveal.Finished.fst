module TLS13.Wire.Spec.Reveal.Finished

friend TLS13.Wire.Generated.Finished
friend TLS13.Wire.Generated.Handshake_body_finished
friend TLS13.Wire.Generated.HandshakeType
friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module E = FStar.Endianness
module GHS = TLS13.Wire.Generated.Handshake
module GFin = TLS13.Wire.Generated.Finished
module HT = TLS13.Wire.Generated.HandshakeType
module LP = LowParse.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module U32 = FStar.UInt32
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

(* The body of a Finished message is a fixed-length 32-byte record whose wire
   length prefix is the 3-byte big-endian [0; 0; 32]. *)
#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 100"
let lemma_vldata_bytes (vd: GHS.handshake_body_finished)
  : Lemma (LP.serialize GHS.handshake_body_finished_serializer vd ==
           Seq.append (B.of_list [0uy; 0uy; 32uy]) vd)
=
  LP.serialize_bounded_integer_spec 3 (U32.uint_to_t 32);
  E.n_to_be_be_to_n 3 (B.of_list [0uy; 0uy; 32uy]);
  E.reveal_be_to_n (B.of_list [0uy; 0uy; 32uy]);
  E.reveal_be_to_n (Seq.slice (B.of_list [0uy; 0uy; 32uy]) 0 2);
  E.reveal_be_to_n (Seq.slice (B.of_list [0uy; 0uy; 32uy]) 0 1);
  assert_norm (Seq.length (B.of_list [0uy; 0uy; 32uy]) = 3);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 2 = 32uy);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 1 = 0uy);
  assert_norm (Seq.index (B.of_list [0uy; 0uy; 32uy]) 0 = 0uy)
#pop-options

(* [serialize_handshake (M.Finished fin)] unfolds (via [friend TLS13.Wire.Spec])
   to [LP.serialize handshake_serializer (Body_finished fin)]; decompose the
   generated sum serializer into the 1-byte HandshakeType tag [20], the 3-byte
   length prefix [0; 0; 32] and the payload [fin]. *)
#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 100"
let lemma_serialize_finished_reveal fin =
  LP.serialize_sum_eq
    GHS.handshake_sum HT.handshakeType_repr_serializer GHS.serialize_handshake_cases
    (GHS.Body_finished fin);
  LP.serialize_enum_key_eq
    HT.handshakeType_repr_serializer HT.handshakeType_enum HT.Finished;
  assert_norm (LP.enum_repr_of_key HT.handshakeType_enum HT.Finished == 20z);
  LP.serialize_u8_spec 20z;
  lemma_vldata_bytes fin;
  Seq.lemma_seq_of_list_induction [20uy; 0uy; 0uy; 32uy];
  Seq.append_assoc (Seq.create 1 20uy) (B.of_list [0uy; 0uy; 32uy]) fin;
  Seq.lemma_eq_elim
    (WS.serialize_handshake (M.Finished fin))
    (B.append (B.of_list [20uy; 0uy; 0uy; 32uy]) fin)
#pop-options

(* Parse/serialize round-trip on the generated codec: parsing the wire image of a
   Finished message recovers exactly that message (with exact consumption). *)
#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 100"
let lemma_parse_finished_handshake fin =
  LP.parse_serialize GHS.handshake_serializer (GHS.Body_finished fin)
#pop-options
