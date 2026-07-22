module TLS13.Wire.Spec.Reveal.ServerHello.Parseback

friend TLS13.Wire.Generated.Handshake
friend TLS13.Wire.Spec

module B = TLS13.Bytes
module GHS = TLS13.Wire.Generated.Handshake
module GSH = TLS13.Wire.Generated.ServerHello
module GSHB = TLS13.Wire.Generated.ServerHello_body
module LP = LowParse.Spec
module M = TLS13.Messages
module Seq = FStar.Seq
module T = TLS13.Types
module WS = TLS13.Wire.Spec

(* [serialize_handshake (M.ServerHello sh)] unfolds (via [friend TLS13.Wire.Spec])
   to [LP.serialize handshake_serializer (Body_server_hello sh)], and the generated
   parse/serialize round-trip ([LP.parse_serialize]) recovers [Body_server_hello sh]
   with exact consumption.  [synth_handshake_msg_of] then maps it to
   [M.ServerHello sh] unless the body is a HelloRetryRequest (which maps to
   [M.HelloRetryRequest], contradicting the hypothesis). *)
#push-options "--initial_fuel 20 --max_fuel 20 --z3rlimit 100"
let lemma_parse_tls_message_serialize_server_hello_key_share sh parsed_sh =
  LP.parse_serialize GHS.handshake_serializer (GHS.Body_server_hello sh);
  match sh.GSH.body with
  | GSHB.HelloRetryRequest _ -> ()
  | _ -> ()
#pop-options
