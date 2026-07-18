module TLS13.Spec.Pairing.Transport

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties

noextract
let endpoint_transport_logs_exact
  (st:CS.connection_state)
  (received:B.bytes)
  (sent:B.bytes)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent /\
  Seq.equal received st.CS.cs_wire_log.CL.raw_received

noextract
let endpoint_transport_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length received == B.length st.CS.cs_wire_log.CL.raw_received

noextract
let paired_transport_histories
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  Seq.equal client_sent server_received /\
  Seq.equal server_sent client_received

noextract
let paired_driver_transport_logs_exact
  (client:CS.connection_state)
  (server:CS.connection_state)
  (client_received:B.bytes)
  (client_sent:B.bytes)
  (server_received:B.bytes)
  (server_sent:B.bytes)
  : prop =
  endpoint_transport_logs_exact client client_received client_sent /\
  endpoint_transport_logs_exact server server_received server_sent /\
  paired_transport_histories
    client_received
    client_sent
    server_received
    server_sent

noextract
let paired_protocol_received_logs_accounted
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  B.length client.CS.cs_wire_log.CL.raw_received <=
    B.length server.CS.cs_wire_log.CL.raw_sent /\
  (forall b.
    SeqP.count b client.CS.cs_wire_log.CL.raw_received <=
    SeqP.count b server.CS.cs_wire_log.CL.raw_sent) /\
  B.length server.CS.cs_wire_log.CL.raw_received <=
    B.length client.CS.cs_wire_log.CL.raw_sent /\
  (forall b.
    SeqP.count b server.CS.cs_wire_log.CL.raw_received <=
    SeqP.count b client.CS.cs_wire_log.CL.raw_sent)

noextract
let paired_protocol_received_logs_exact_prefix
  (client:CS.connection_state)
  (server:CS.connection_state)
  : prop =
  (exists client_retained.
     Seq.equal server.CS.cs_wire_log.CL.raw_sent
       (B.append client.CS.cs_wire_log.CL.raw_received client_retained)) /\
  (exists server_retained.
     Seq.equal client.CS.cs_wire_log.CL.raw_sent
       (B.append server.CS.cs_wire_log.CL.raw_received server_retained))
