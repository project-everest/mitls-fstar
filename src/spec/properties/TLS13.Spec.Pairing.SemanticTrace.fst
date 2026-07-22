module TLS13.Spec.Pairing.SemanticTrace

module Corr = TLS13.Spec.StateMachine.Correspondence
module Log = TLS13.Spec.StateMachine.Log
module SM = TLS13.Spec.StateMachine

(**
  Pure semantic trace pairing, independent of raw record bytes. Each endpoint's
  semantic TLS sends must correspond, in order, to the peer's receives.
**)
noextract
let paired_semantic_tls_io_traces
  (client_trace:list SM.conn_event)
  (server_trace:list SM.conn_event)
  : prop =
  Corr.tls_messages_correspond
    (Log.sent_tls_messages client_trace)
    (Log.received_tls_messages server_trace) /\
  Corr.tls_messages_correspond
    (Log.sent_tls_messages server_trace)
    (Log.received_tls_messages client_trace)
