module ParsersAux.Handshake
include Parsers.Handshake

module Seq = FStar.Seq
module LP = LowParse.Spec.Base
module HT = Parsers.HandshakeType

val serialize_handshake_eq_client_hello
  (h: handshake {M_client_hello? h})
: Lemma
  (LP.serialize handshake_serializer h ==
   LP.serialize HT.handshakeType_serializer HT.Client_hello `Seq.append`
   LP.serialize handshake_m_client_hello_serializer (M_client_hello?._0 h))
