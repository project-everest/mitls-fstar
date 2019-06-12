module ParsersAux.Eq

(* Since QuackyDucky is not hash-consing parser definitions, we need to explicitly prove that they are equal up to extensionality *)

open Parsers.MiTLSConfig_alpn_b_true
open Parsers.ClientHelloExtension_CHE_application_layer_protocol_negotiation

module LP = LowParse.Low.Base
module HS = FStar.HyperStack
module U32 = FStar.UInt32

val miTLSConfig_alpn_b_true_parser_ext (b: LP.bytes) : Lemma
  (
    LP.parse miTLSConfig_alpn_b_true_parser b == LP.parse clientHelloExtension_CHE_application_layer_protocol_negotiation_parser b
  )

val miTLSConfig_alpn_b_true_serializer_ext (x: miTLSConfig_alpn_b_true) : Lemma
  (
    LP.serialize miTLSConfig_alpn_b_true_serializer x ==
    LP.serialize clientHelloExtension_CHE_application_layer_protocol_negotiation_serializer x
  )

val valid_miTLSConfig_alpn_b_true_ext (h: HS.mem) (#rrel #rel: _) (s: LP.slice rrel rel) (pos: U32.t) : Lemma
  (
    (LP.valid miTLSConfig_alpn_b_true_parser h s pos \/ LP.valid clientHelloExtension_CHE_application_layer_protocol_negotiation_parser h s pos) ==>
    (LP.valid miTLSConfig_alpn_b_true_parser h s pos /\
     LP.valid_content_pos clientHelloExtension_CHE_application_layer_protocol_negotiation_parser h s pos (LP.contents miTLSConfig_alpn_b_true_parser h s pos) (LP.get_valid_pos miTLSConfig_alpn_b_true_parser h s pos))
 )
