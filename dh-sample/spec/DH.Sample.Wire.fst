module DH.Sample.Wire

(**
  The three ISO-DH messages.  Serialization is deliberately separate from the
  protocol semantics and will be refined by the implementation layer.
*)

open DH.Sample.Types

noeq
type message =
  | Message1:
      initiator:principal ->
      initiator_share:share ->
      message
  | Message2:
      responder:principal ->
      responder_share:share ->
      responder_signature:signature ->
      message
  | Message3:
      initiator_signature:signature ->
      message
