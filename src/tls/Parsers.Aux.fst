module Parsers.Aux

friend Parsers.MiTLSConfig_alpn_b_true
friend Parsers.ClientHelloExtension_CHE_application_layer_protocol_negotiation

open Parsers.MiTLSConfig_alpn_b_true
open Parsers.ClientHelloExtension_CHE_application_layer_protocol_negotiation

module LP = LowParse.Low

let miTLSConfig_alpn_b_true_parser_ext (b: LP.bytes) : Lemma
  (
    LP.parse miTLSConfig_alpn_b_true_parser b == LP.parse clientHelloExtension_CHE_application_layer_protocol_negotiation_parser b
  )
= LP.parse_synth_eq miTLSConfig_alpn_b_true'_parser synth_miTLSConfig_alpn_b_true b;
  LP.parse_synth_eq clientHelloExtension_CHE_application_layer_protocol_negotiation'_parser synth_clientHelloExtension_CHE_application_layer_protocol_negotiation b

let miTLSConfig_alpn_b_true_serializer_ext (x: miTLSConfig_alpn_b_true) : Lemma
  (
    LP.serialize miTLSConfig_alpn_b_true_serializer x ==
    LP.serialize clientHelloExtension_CHE_application_layer_protocol_negotiation_serializer x
  )
= LP.serialize_synth_eq miTLSConfig_alpn_b_true'_parser synth_miTLSConfig_alpn_b_true miTLSConfig_alpn_b_true'_serializer synth_miTLSConfig_alpn_b_true_recip () x;
  LP.serialize_synth_eq clientHelloExtension_CHE_application_layer_protocol_negotiation'_parser synth_clientHelloExtension_CHE_application_layer_protocol_negotiation clientHelloExtension_CHE_application_layer_protocol_negotiation'_serializer synth_clientHelloExtension_CHE_application_layer_protocol_negotiation_recip () x

module HS = FStar.HyperStack
module U32 = FStar.UInt32

let valid_miTLSConfig_alpn_b_true_ext (h: HS.mem) (#rrel #rel: _) (s: LP.slice rrel rel) (pos: U32.t) : Lemma
  (
    (LP.valid miTLSConfig_alpn_b_true_parser h s pos \/ LP.valid clientHelloExtension_CHE_application_layer_protocol_negotiation_parser h s pos) ==>
    (LP.valid miTLSConfig_alpn_b_true_parser h s pos /\
     LP.valid_content_pos clientHelloExtension_CHE_application_layer_protocol_negotiation_parser h s pos (LP.contents miTLSConfig_alpn_b_true_parser h s pos) (LP.get_valid_pos miTLSConfig_alpn_b_true_parser h s pos))
 )
= LP.valid_facts miTLSConfig_alpn_b_true_parser h s pos;
  LP.valid_facts clientHelloExtension_CHE_application_layer_protocol_negotiation_parser h s pos;
  miTLSConfig_alpn_b_true_parser_ext (LP.bytes_of_slice_from h s pos)
