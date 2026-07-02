module TLS13.Wire.Spec.Reveal.FinishedRoundTrip

friend TLS13.Wire.Generated.Finished
friend TLS13.Wire.Generated.Handshake_body_finished
friend TLS13.Wire.Generated.HandshakeType
friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module E = FStar.Endianness
module GHS = TLS13.Wire.Generated.Handshake
module HT = TLS13.Wire.Generated.HandshakeType
module LP = LowParse.Spec
module M = TLS13.Messages
module RF = TLS13.Wire.Spec.Reveal.Finished
module Seq = FStar.Seq
module T = TLS13.Types
module U32 = FStar.UInt32
module WS = TLS13.Wire.Spec

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

let lemma_ghs_serialize_eq_ws (vd: GHS.handshake_body_finished)
  : Lemma (Seq.equal
    (LP.serialize GHS.handshake_serializer (GHS.Body_finished vd))
    (WS.serialize_handshake (M.Finished ({ M.verify_data = vd }))))
=
  LP.serialize_sum_eq
    GHS.handshake_sum HT.handshakeType_repr_serializer GHS.serialize_handshake_cases
    (GHS.Body_finished vd);
  LP.serialize_enum_key_eq
    HT.handshakeType_repr_serializer HT.handshakeType_enum HT.Finished;
  assert_norm (LP.enum_repr_of_key HT.handshakeType_enum HT.Finished == 20z);
  LP.serialize_u8_spec 20z;
  lemma_vldata_bytes vd;
  RF.lemma_serialize_finished_reveal ({ M.verify_data = vd });
  Seq.lemma_seq_of_list_induction [20uy; 0uy; 0uy; 32uy];
  Seq.append_assoc (Seq.create 1 20uy) (B.of_list [0uy; 0uy; 32uy]) vd
#pop-options

#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 100"
let lemma_parse_finished_handshake_round_trip fragment fin =
  match LP.parse GHS.handshake_parser fragment with
  | Some (h, consumed) ->
    if consumed = B.length fragment then
      begin
        LP.parsed_data_is_serialize GHS.handshake_serializer fragment;
        Seq.lemma_eq_intro
          (Seq.slice fragment consumed (B.length fragment))
          B.empty;
        Seq.lemma_eq_intro
          (Seq.append (LP.serialize GHS.handshake_serializer h)
                      (Seq.slice fragment consumed (B.length fragment)))
          (LP.serialize GHS.handshake_serializer h);
        match h with
        | GHS.Body_finished vd ->
          assert (fin == { M.verify_data = vd });
          lemma_ghs_serialize_eq_ws vd;
          assert (Seq.equal
            (LP.serialize GHS.handshake_serializer h)
            (WS.serialize_handshake (M.Finished fin)));
          Seq.lemma_eq_elim
            fragment
            (LP.serialize GHS.handshake_serializer h)
        | _ ->
          assert False
      end
    else
      assert False
  | None ->
    assert False
#pop-options
