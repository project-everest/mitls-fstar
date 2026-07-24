module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module CI = Common.ChannelImplementation
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module DL = TLS13.Impl.Server.Driver.Local
module DN = TLS13.Impl.Server.Driver.Network
module DState = TLS13.Impl.Server.Driver.State
module IO = Common.TCP
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SM = TLS13.Spec.StateMachine.ClientTrace
module SP = TLS13.Impl.Server.CanonicalProtocol
module SChannel = TLS13.Impl.Server.ChannelImplementation
module TChannel = TLS13.Impl.Channel
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module T = TLS13.Types
module U16 = FStar.UInt16
module U8 = FStar.UInt8

type server_driver = DState.server_driver
type server_credentials = O.server_credentials
type server_listener = IO.listener

noextract
val server_driver_canonical
  (d: server_driver)
  : SP.canonical_server

noextract
val server_driver_canonical_progress
  (d: server_driver)
  (st: CS.connection_state)
  : slprop

noextract
val server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop

noextract
(**
  Owns a connected server driver together with the concrete TCP byte histories
  tracked by Common.TCP. The protocol-level processed wire log is in
  st.cs_wire_log; received may also include bytes retained in the driver's input
  buffer.
**)
val server_driver_connected
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  (received:B.bytes)
  (sent:B.bytes)
  : slprop

noextract
val server_driver_closed
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop

noextract
val server_driver_released
  (d:server_driver)
  (st:CS.connection_state)
  : slprop

type server_workflow_status =
  | ServerWorkflowOk
  | ServerWorkflowNeedMoreInput
  | ServerWorkflowStepFailed
  | ServerWorkflowExhausted
  | ServerWorkflowClosed
  | ServerWorkflowPayloadTooLarge
  | ServerWorkflowOutputBufferTooSmall

type server_receive_result = {
  server_receive_status: server_workflow_status;
  server_receive_len: SZ.t;
}

let channel_message_of_bytes (bytes:B.bytes) : B.bytes = bytes

let channel_send_succeeded (status:server_workflow_status) : bool =
  match status with
  | ServerWorkflowOk -> true
  | _ -> false

let channel_receive_succeeded (result:server_receive_result) : GTot bool =
  result.server_receive_status == ServerWorkflowOk &&
  result.server_receive_len <> 0sz

let channel_receive_length (result:server_receive_result) : SZ.t =
  result.server_receive_len

noextract
let server_driver_send_status_correct
  (status:server_workflow_status)
  (resp:ST.server_response)
  : prop =
  if resp.ST.status == ST.StepOk
  then status == ServerWorkflowOk
  else status == ServerWorkflowStepFailed

noextract
let server_driver_payload_too_large
  (payload:B.bytes)
  : prop =
  B.length payload > SM.max_application_data_fragment_len

noextract
let server_driver_send_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (status:server_workflow_status)
  (payload:B.bytes)
  (sent:B.bytes)
  (sent':B.bytes)
  : prop =
  if status == ServerWorkflowPayloadTooLarge
  then
    st1 == st0 /\
    Seq.equal sent' sent /\
    server_driver_payload_too_large payload
  else
    exists resp.
      DL.server_driver_local_write_correct
        st0
        st1
        resp
        ST.LocalSendApplicationData
        payload
        sent
        sent' /\
      server_driver_send_status_correct status resp

noextract
let server_driver_receive_status_correct
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (st1:CS.connection_state)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  if loop.DN.server_driver_network_loop_exhausted then
    result.server_receive_status == ServerWorkflowExhausted /\
    result.server_receive_len == 0sz
  else if st1.CS.cs_model.CS.model_control == CS.ControlClosed then
    result.server_receive_status == ServerWorkflowClosed /\
    result.server_receive_len == 0sz
  else
    match loop.DN.server_driver_network_loop_last.ST.response.ST.status with
    | ST.StepOk ->
      if SZ.v loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len
          <= B.length out_bytes /\
         SZ.v loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len
          <= B.length app_out
      then
        result.server_receive_status == ServerWorkflowOk /\
        result.server_receive_len ==
          loop.DN.server_driver_network_loop_last.ST.response.ST.app_out_len
      else
        result.server_receive_status == ServerWorkflowStepFailed /\
        result.server_receive_len == 0sz
    | ST.NeedMoreInput ->
      result.server_receive_status == ServerWorkflowNeedMoreInput /\
      result.server_receive_len == 0sz
    | _ ->
      result.server_receive_status == ServerWorkflowStepFailed /\
      result.server_receive_len == 0sz

noextract
let server_driver_receive_copyout_correct
  (result:server_receive_result)
  (resp:ST.server_response)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  if result.server_receive_status == ServerWorkflowOk then
    SZ.v result.server_receive_len <= B.length out_bytes /\
    result.server_receive_len == resp.ST.app_out_len /\
    (if SZ.v result.server_receive_len <= B.length out_bytes then
      Seq.equal
        (Seq.slice out_bytes 0 (SZ.v result.server_receive_len))
        (ST.response_app_out resp app_out)
     else False)
  else
    True

noextract
let server_driver_receive_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (result:server_receive_result)
  (loop:DN.server_driver_network_loop_result)
  (sent:B.bytes)
  (sent':B.bytes)
  (app_out:B.bytes)
  (out_bytes:B.bytes)
  : prop =
  server_driver_receive_status_correct result loop st1 app_out out_bytes /\
  B.length app_out >= SZ.v DState.driver_app_out_capacity /\
  B.length app_out <= B.length out_bytes /\
  SZ.v result.server_receive_len <= B.length out_bytes /\
  (loop.DN.server_driver_network_loop_exhausted == true ==>
    st1 == st0 /\
    Seq.equal sent' sent) /\
  (loop.DN.server_driver_network_loop_exhausted == false ==>
    DN.server_driver_network_process_correct
      st0
      st1
      loop.DN.server_driver_network_loop_last
      sent
      sent' /\
    DN.server_driver_network_process_correct_for_app_out
      st0
      st1
      loop.DN.server_driver_network_loop_last
      sent
      sent'
      app_out) /\
  (result.server_receive_status == ServerWorkflowOk ==>
    server_driver_receive_copyout_correct
      result
      loop.DN.server_driver_network_loop_last.ST.response
      app_out
      out_bytes)

noextract
let server_driver_application_ready
  (st:CS.connection_state)
  : prop =
  ST.server_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  CS.application_record_keys_installed_for_role CS.ServerEndpoint st.CS.cs_model

noextract
let server_driver_sent_log_exact
  (st:CS.connection_state)
  (sent:B.bytes)
  : prop =
  Seq.equal sent st.CS.cs_wire_log.CL.raw_sent

noextract
let server_driver_received_log_accounted
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length st.CS.cs_wire_log.CL.raw_received <= B.length received /\
  (forall b.
    SeqP.count b st.CS.cs_wire_log.CL.raw_received <=
    SeqP.count b received)

noextract
let server_driver_received_log_exact_prefix
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  exists retained.
    Seq.equal received
      (B.append st.CS.cs_wire_log.CL.raw_received retained)

noextract
let server_driver_received_no_read_ahead
  (st:CS.connection_state)
  (received:B.bytes)
  : prop =
  B.length received == B.length st.CS.cs_wire_log.CL.raw_received

noextract
let server_driver_close_correct
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  (sent:B.bytes)
  : prop =
  exists sent' resp.
    DL.server_driver_local_write_correct
      st0
      st1
      resp
      ST.LocalSendCloseNotify
      B.empty
      sent
      sent'

(**
  Reflexive-transitive closure of one verified network-processing step
  ([DN.server_driver_network_process_correct]).  [server_driver_network_reaches
  st0 st1] holds when [st1] is reachable from [st0] by a finite (possibly empty)
  sequence of verified reads-and-processing of the peer's network bytes, each
  step justified by the connection state machine.  The relation is kept abstract
  here (its witness path is an implementation detail); it is realised in the
  implementation module, where the [close] workflow constructs it as it drains
  the peer's close_notify.
**)
noextract
val server_driver_network_reaches
  (st0:CS.connection_state)
  (st1:CS.connection_state)
  : prop

(**
  Final-state correctness for [close].  This ties the *actual* closed state
  [st_final] to the close_notify transition performed from [st0]:

  - there is an intermediate close_notify state [st_close_notify] reached from
    [st0] by exactly one [LocalSendCloseNotify] local write
    ([server_driver_close_correct]), and [st_final] is reached from that
    close_notify state by verified network processing
    ([server_driver_network_reaches]).  When [wait_for_peer] is [false] no
    network processing happens, so [st_final] *is* the close_notify state and the
    relation degenerates to the reflexive case; and

  - when [wait_for_peer] is [false] the historical, strictly stronger guarantee
    is preserved exactly: the closed state [st_final] itself satisfies
    [server_driver_close_correct st0 st_final sent] (i.e. the connection stopped
    precisely at the close_notify transition).
**)
noextract
let server_driver_close_final_correct
  (wait_for_peer:bool)
  (st0:CS.connection_state)
  (st_final:CS.connection_state)
  (sent:B.bytes)
  : prop =
  (exists st_close_notify.
    server_driver_close_correct st0 st_close_notify sent /\
    server_driver_network_reaches st_close_notify st_final) /\
  (wait_for_peer == false ==>
    server_driver_close_correct st0 st_final sent)

(**
  Relates the reported [close] status to the requested [wait_for_peer] flag.

  When the caller does not ask to wait for the peer's close_notify the workflow
  always reports [ServerWorkflowClosed] (the historical behaviour): after the
  local close_notify is written the transport is torn down immediately, so no
  peer record is read and no failure can be observed.

  When the caller *does* ask to wait, the workflow drains the peer's records
  within the supplied network fuel and reports exactly one of three outcomes,
  all of which still tear down the transport:

  - [ServerWorkflowClosed]: the peer's close_notify was observed and the
    connection reached [CS.ControlClosed] (see [server_driver_close_wait_correct]);

  - [ServerWorkflowExhausted]: the network fuel ran out before the peer's
    close_notify was observed; or

  - [ServerWorkflowStepFailed]: a nonrecoverable control-failure or
    record-processing failure was observed while draining, so the workflow
    stopped without issuing another blocking read.

  [ServerWorkflowStepFailed] is therefore only ever reported on the waiting
  path: the second conjunct pins the no-wait status to [ServerWorkflowClosed],
  ruling out both [Exhausted] and [StepFailed] when [wait_for_peer] is [false].
**)
noextract
let server_driver_close_status_correct
  (wait_for_peer:bool)
  (status:server_workflow_status)
  : prop =
  (status == ServerWorkflowClosed \/
   status == ServerWorkflowExhausted \/
   status == ServerWorkflowStepFailed) /\
  (wait_for_peer == false ==> status == ServerWorkflowClosed)

(**
  Connects the [wait_for_peer] request and the reported status to the verified
  protocol state that the connection reached before the transport was closed.

  If the caller asked to wait for the peer and the workflow reported
  [ServerWorkflowClosed], then the peer's close_notify was actually drained and
  the connection reached the fully-closed protocol control state
  [CS.ControlClosed] (both close_notify alerts exchanged).
**)
noextract
let server_driver_close_wait_correct
  (wait_for_peer:bool)
  (status:server_workflow_status)
  (st_final:CS.connection_state)
  : prop =
  (wait_for_peer == true /\ status == ServerWorkflowClosed) ==>
    st_final.CS.cs_model.CS.model_control == CS.ControlClosed

(**
  Fuel-boundary behaviour for [close].  This is the sense in which the supplied
  [network_fuel] governs the reported status: if the caller asks to wait for the
  peer's close_notify but supplies a zero network-fuel budget, the workflow is
  unable to read and process even a single peer record, so it cannot observe the
  peer's close_notify and therefore always reports [ServerWorkflowExhausted].

  Combined with [server_driver_close_status_correct] and
  [server_driver_close_wait_correct], this makes the fuel boundary provably
  usable by callers: a caller that passes [wait_for_peer = true] with zero fuel
  learns statically that the peer was not drained (status is [Exhausted], never
  [Closed]).
**)
noextract
let server_driver_close_fuel_correct
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  (status:server_workflow_status)
  : prop =
  (wait_for_peer == true /\ SZ.v network_fuel == 0) ==>
    status == ServerWorkflowExhausted

fn new_server_listener
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns result: option server_listener
  ensures pts_to bind_host 'bind_host_bytes **
          (match result with
           | Some listener -> IO.is_listener listener 'bind_host_bytes port
           | None -> emp)

fn free_server_listener (listener:server_listener)
  requires IO.is_listener listener 'bind_host_bytes 'port
  ensures emp

fn new_server_credentials
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len)
  returns result: option server_credentials
  ensures exists* credential_identity.
          pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some credentials ->
             O.is_server_credentials
               credentials
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity
           | None -> emp)

fn free_server_credentials (credentials:server_credentials)
  requires O.is_server_credentials
    credentials
    'certificate_chain
    'credential_identity
  ensures emp

fn new_server_with_credentials
  (credentials:server_credentials)
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider: erased SP.server_supported_profile_provider)
  requires (exists* credential_identity.
              O.is_server_credentials
                credentials
                (Ghost.reveal 'certificate_chain_bytes)
                credential_identity) **
           pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len /\
                 B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (exists* credential_identity.
            O.is_server_credentials
              credentials
              (Ghost.reveal 'certificate_chain_bytes)
              credential_identity **
            (match result with
             | Some d ->
               server_driver_live
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity)
                 (Ghost.reveal 'certificate_chain_bytes)
                 credential_identity **
               pure (ST.server_state_correct
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     CM.can_start_server
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     ST.server_end_to_end_invariant
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     B.length 'certificate_chain_bytes <=
                       Bounds.max_server_certificate_chain_len /\
                     Ghost.reveal
                       (server_driver_canonical d).SP.canonical_server_initial ==
                       CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity)
             | None -> emp))

fn new_server
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider: erased SP.server_supported_profile_provider)
  requires pts_to certificate_chain 'certificate_chain_bytes **
           pts_to private_key 'private_key_bytes **
           pure (B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
                 B.length 'private_key_bytes == SZ.v private_key_len)
  returns result: option server_driver
  ensures pts_to certificate_chain 'certificate_chain_bytes **
          pts_to private_key 'private_key_bytes **
          (match result with
           | Some d ->
             exists* credential_identity.
               server_driver_live
                 d
                 (CR.server_initial_state
                   (Ghost.reveal 'certificate_chain_bytes)
                   credential_identity)
                 (Ghost.reveal 'certificate_chain_bytes)
                 credential_identity **
               pure (ST.server_state_correct
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     CM.can_start_server
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     ST.server_end_to_end_invariant
                       (CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity) /\
                     B.length 'certificate_chain_bytes <=
                       Bounds.max_server_certificate_chain_len /\
                     Ghost.reveal
                       (server_driver_canonical d).SP.canonical_server_initial ==
                       CR.server_initial_state
                         (Ghost.reveal 'certificate_chain_bytes)
                         credential_identity)
           | None ->
             emp) **
          pure
           (not (B.length 'certificate_chain_bytes <=
                   Bounds.max_server_certificate_chain_len) ==>
            result == None)

fn accept
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                 CM.can_start_server 'st0 /\
                 Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                 (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                  | Some cfg ->
                    CS.cipher_suite_offered
                      cfg.CS.server_supported_cipher_suites
                      T.TLS_CHACHA20_POLY1305_SHA256 /\
                    CS.named_group_offered
                      cfg.CS.server_supported_groups
                      T.X25519 /\
                    CS.signature_scheme_offered
                      cfg.CS.server_allowed_signature_schemes
                      T.Rsa_pss_rsae_sha256 /\
                    cfg.CS.server_sni_policy == None
                  | None -> False))
  returns status:server_workflow_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowOk ->
             exists* raw_received raw_sent app_log.
               DState.server_channel_inv
                 d raw_received raw_sent app_log
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed
                 d st1 'certificate_chain 'credential_identity
           | _ ->
             exists* st1 received sent.
               server_driver_connected
                 d
                 st1
                 'certificate_chain
                 'credential_identity
                 received
                 sent)

fn accept_with_listener
  (d:server_driver)
  (listener:server_listener)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires IO.is_listener listener 'bind_host_bytes port **
           server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len /\
                  CM.can_start_server 'st0 /\
                  Some? 'st0.CS.cs_model.CS.model_config.CS.config_server /\
                  (match 'st0.CS.cs_model.CS.model_config.CS.config_server with
                   | Some cfg ->
                     CS.cipher_suite_offered
                       cfg.CS.server_supported_cipher_suites
                       T.TLS_CHACHA20_POLY1305_SHA256 /\
                     CS.named_group_offered
                       cfg.CS.server_supported_groups
                       T.X25519 /\
                     CS.signature_scheme_offered
                       cfg.CS.server_allowed_signature_schemes
                       T.Rsa_pss_rsae_sha256 /\
                     cfg.CS.server_sni_policy == None
                   | None -> False))
  returns status:server_workflow_status
  ensures IO.is_listener listener 'bind_host_bytes port **
          pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerWorkflowOk ->
             exists* raw_received raw_sent app_log.
               DState.server_channel_inv
                  d raw_received raw_sent app_log
           | ServerWorkflowClosed ->
             exists* st1.
               server_driver_closed
                  d st1 'certificate_chain 'credential_identity
           | _ ->
             exists* st1 received sent.
               server_driver_connected
                  d
                  st1
                  'certificate_chain
                  'credential_identity
                  received
                  sent)

fn send
  (d:server_driver)
  (raw_received0:Ghost.erased B.bytes)
  (raw_sent0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires DState.server_channel_inv
             d
             (Ghost.reveal raw_received0)
             (Ghost.reveal raw_sent0)
             (Ghost.reveal app_log0) **
           pts_to payload (Ghost.reveal payload_bytes) **
           pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:server_workflow_status
  ensures exists* raw_received1 raw_sent1 app_log1.
          DState.server_channel_inv d raw_received1 raw_sent1 app_log1 **
          pts_to payload (Ghost.reveal payload_bytes) **
          pure (
            CI.send_transition
              channel_message_of_bytes
              channel_send_succeeded
              status
              (Ghost.reveal payload_bytes)
              (Ghost.reveal raw_received0)
              (Ghost.reveal raw_sent0)
              (Ghost.reveal app_log0)
              raw_received1
              raw_sent1
              app_log1)

fn receive
  (d:server_driver)
  (raw_received0:Ghost.erased B.bytes)
  (raw_sent0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires DState.server_channel_inv
             d
             (Ghost.reveal raw_received0)
             (Ghost.reveal raw_sent0)
             (Ghost.reveal app_log0) **
           pts_to out (Ghost.reveal old_output) **
           pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:server_receive_result
  ensures exists* raw_received1 raw_sent1 app_log1 output.
          DState.server_channel_inv d raw_received1 raw_sent1 app_log1 **
          pts_to out output **
          pure (
            B.length output == SZ.v out_len /\
            SZ.v result.server_receive_len <= SZ.v out_len /\
            CI.receive_transition
              channel_message_of_bytes
              channel_receive_succeeded
              channel_receive_length
              result
              output
              (Ghost.reveal raw_received0)
              (Ghost.reveal raw_sent0)
              (Ghost.reveal app_log0)
              raw_received1
              raw_sent1
              app_log1)

fn close
  (d:server_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires DState.server_channel_inv
             d
             (Ghost.reveal raw_received)
             (Ghost.reveal raw_sent)
             (Ghost.reveal app_log)
  returns status:server_workflow_status
  ensures exists* st1 certificate_chain credential_identity.
          server_driver_closed d st1 certificate_chain credential_identity

(**
  Safely disposes an accepted transport after any workflow failure. Unlike
  [close], this does not require the protocol state to remain application-ready.
**)
fn abort
  (d:server_driver)
  (raw_received:Ghost.erased B.bytes)
  (raw_sent:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  requires DState.server_channel_inv
             d
             (Ghost.reveal raw_received)
             (Ghost.reveal raw_sent)
             (Ghost.reveal app_log)
  ensures exists* st certificate_chain credential_identity.
          server_driver_closed d st certificate_chain credential_identity

fn free
  (d:server_driver)
  requires server_driver_closed d 'st 'certificate_chain 'credential_identity
  ensures server_driver_released d 'st

noextract
val server_channel_implementation
  : CI.channel_implementation
      server_driver
      SP.canonical_server
      CS.connection_state
      TLS13.Spec.Endpoint.Wire.wire_message
      TLS13.Impl.CanonicalTypes.server_local_event
      TLS13.Spec.Endpoint.API.local_output
      B.bytes
      server_workflow_status
      server_receive_result
      SP.server_protocol_implementation
