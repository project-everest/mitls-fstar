module TLS13.ConnectionState.ClientNoCcsFromPairing

(**
  CLIENT-log mirror: discharge the
  [CCShape.log_has_no_received_ccs] hypothesis relied upon by
  [TLS13.ConnectionState.ClientCanonicalShape] directly from the flagship JOINT
  byte facts.  Re-based (Option C) off plain [CS.connection_state] endpoints so
  the module no longer imports [TLS13.System].
**)

module CS = TLS13.Spec.StateMachine
module CL = TLS13.ConnectionLog
module Seq = FStar.Seq
module WStep = TLS13.System.WireStep
module CCShape = TLS13.ConnectionState.ClientCanonicalShape

val lemma_no_received_ccs_from_pairing_client
  (client server : CS.connection_state)
  : Lemma
      (requires
        WStep.client_reachable (CS.initial client.CS.cs_model.CS.model_config) client /\
        WStep.server_reachable (CS.initial server.CS.cs_model.CS.model_config) server /\
        Seq.equal client.CS.cs_wire_log.CL.raw_sent server.CS.cs_wire_log.CL.raw_received /\
        Seq.equal server.CS.cs_wire_log.CL.raw_sent client.CS.cs_wire_log.CL.raw_received /\
        client.CS.cs_model.CS.model_config.CS.config_role == CS.ClientEndpoint /\
        server.CS.cs_model.CS.model_config.CS.config_role == CS.ServerEndpoint)
      (ensures
        CCShape.log_has_no_received_ccs client.CS.cs_event_log)
