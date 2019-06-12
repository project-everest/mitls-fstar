module ParsersAux.Handshake
open Parsers.Handshake

module Seq = FStar.Seq
module LP = LowParse.Spec
module HT = Parsers.HandshakeType

friend Parsers.Handshake
friend Parsers.HandshakeType

#push-options "--z3rlimit 16"

let serialize_handshake_eq_client_hello h =
  assert_norm (LP.parse_sum_kind (LP.get_parser_kind HT.handshakeType_repr_parser) handshake_sum parse_handshake_cases == handshake_parser_kind);
  assert (LP.sum_tag_of_data handshake_sum h == handshakeType_as_enum_key HT.Client_hello);
  LP.serialize_sum_eq handshake_sum HT.handshakeType_repr_serializer serialize_handshake_cases h;
  HT.lemma_synth_handshakeType_inj ();
  HT.lemma_synth_handshakeType_inv ();
  LP.serialize_synth_eq _ HT.synth_handshakeType HT.serialize_handshakeType_key HT.synth_handshakeType_inv () (handshakeType_as_enum_key HT.Client_hello)

#pop-options
