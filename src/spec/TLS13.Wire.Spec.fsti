module TLS13.Wire.Spec

module B = TLS13.Bytes
module H = TLS13.Handshake.Spec
module R = TLS13.Record.Spec
module T = TLS13.Types

type parse_error = T.tls_error

val parse_handshake:
  input:B.bytes ->
  Tot (option (H.handshake_msg & nat))

val parse_supported_server_hello:
  input:B.bytes ->
  Tot (option H.server_hello)

val serialize_supported_client_hello:
  hello:H.client_hello ->
  Tot B.bytes

val serialize_handshake:
  msg:H.handshake_msg ->
  Tot B.bytes

val parse_record:
  input:B.bytes ->
  Tot (option (T.content_type & R.sealed_record & nat))

val serialize_record:
  content_type:T.content_type ->
  fragment:B.bytes ->
  Tot B.bytes
