module TLS13.Impl.Server.Driver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Bounds = TLS13.Impl.ConnectionState.Bounds
module BR = TLS13.Impl.Server.Driver.BufferedReceive
module BSend = TLS13.Impl.Server.Driver.BufferedSend
module CI = Common.ChannelImplementation
module CPI = Common.ProtocolImplementation
module CTypes = TLS13.Impl.CanonicalTypes
module CW = TLS13.Spec.Endpoint.Wire
module EAPI = TLS13.Spec.Endpoint.API
module CL = TLS13.ConnectionLog
module CM = TLS13.Impl.ConnectionState.Model
module CR = TLS13.Impl.ConnectionState.Repr
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module IO = Common.TCP
module O = TLS13.OpenSSL
module Seq = FStar.Seq
module SeqP = FStar.Seq.Properties
module SP = TLS13.Impl.Server.CanonicalProtocol
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module TChannel = TLS13.Impl.Channel
module U16 = FStar.UInt16
module U8 = FStar.UInt8

type server_driver = DS.top_server_driver
type server_credentials = O.server_credentials
type server_listener = IO.listener

noextract
val server_driver_canonical
  (d:server_driver)
  : SP.canonical_server

noextract
val server_driver_canonical_progress
  (d:server_driver)
  (st:CS.connection_state)
  : slprop

noextract
val server_driver_live
  (d:server_driver)
  (st:CS.connection_state)
  (certificate_chain:B.bytes)
  (credential_identity:CS.server_credential_identity)
  : slprop

noextract
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

(** {1 Generic channel vocabulary}

  These classify [server_workflow_status] for
  [Common.ChannelImplementation]: which outcomes appended to the application
  log, and which left the channel usable.  [send]/[receive] below are stated
  directly in these terms, and [server_channel_implementation] at the end of
  this interface instantiates the class on them.
**)

(* The channel's view of a message is the bytes themselves. *)
noextract
let channel_message_of_bytes (bytes:B.bytes) : B.bytes = bytes

noextract
let channel_send_succeeded (status:server_workflow_status) : bool =
  match status with
  | ServerWorkflowOk -> true
  | _ -> false

(* A send leaves the channel reusable exactly for success and for the
   payload-too-large rejection, which does not step the connection.  A hard
   step failure is terminal. *)
noextract
let channel_send_reusable (status:server_workflow_status) : bool =
  match status with
  | ServerWorkflowOk -> true
  | ServerWorkflowPayloadTooLarge -> true
  | _ -> false

noextract
let channel_receive_succeeded (result:server_receive_result) : bool =
  match result.server_receive_status with
  | ServerWorkflowOk -> true
  | _ -> false

noextract
let channel_receive_length (result:server_receive_result) : SZ.t =
  result.server_receive_len

(* A receive leaves the channel reusable for exactly the statuses where the
   connection stays open.  A peer close and a hard step failure are both
   terminal.  The cases are listed explicitly so the live set cannot silently
   admit an unintended status. *)
noextract
let channel_receive_reusable (result:server_receive_result) : bool =
  match result.server_receive_status with
  | ServerWorkflowOk -> true
  | ServerWorkflowNeedMoreInput -> true
  | ServerWorkflowExhausted -> true
  | ServerWorkflowOutputBufferTooSmall -> true
  | _ -> false

noextract
let server_driver_is_closed (d:server_driver) : slprop =
  exists* st certificate_chain credential_identity.
    DS.top_server_driver_closed d st certificate_chain credential_identity

(* The driver's terminal state, in the indexed form the channel class asks for.

   The class requires a [ci_terminal_inv i wire_received wire_sent app_log] but
   places no constraint whatsoever on it: it is mentioned only in the failure
   branch of [ci_send]/[ci_receive] and nowhere else.  It is simply "you still
   own the endpoint, but no protocol claim is made about it".

   We take that state to be the *closed* driver rather than the intermediate
   [DS.top_server_channel_terminal].  A failed send or receive means the
   connection control has already failed, so there is nothing graceful left to
   do with the endpoint, and disposing the transport immediately is the only
   policy this driver ever wants.  Choosing it here is what lets the public API
   and the class instance be the same functions: see the note on
   [server_channel_implementation] below.

   The wire and log indices are ignored, since a closed driver no longer
   indexes them.  The corresponding transition facts are not lost -- they are
   still asserted in the [pure] conjunct of [send]/[receive] on every branch. *)
noextract
let server_channel_closed
  (d:server_driver)
  (_wire_received _wire_sent:B.bytes)
  (_app_log:CI.application_log B.bytes)
  : slprop =
  server_driver_is_closed d

(* The channel state after a [send]/[receive].  A reusable outcome leaves the
   channel invariant; a terminal one disposes the transport, so the caller is
   left owning a closed driver and nothing else.

   This is definitionally the shape [CI.ci_send]/[CI.ci_receive] demand of
   their postconditions, with [ci_channel_inv := DS.top_server_channel_inv] and
   [ci_terminal_inv := server_channel_closed]. *)
noextract
let server_channel_after_operation
  (d:server_driver)
  (reusable:bool)
  (wire_received wire_sent pending:B.bytes)
  (app_log:CI.application_log B.bytes)
  : slprop =
  if reusable
  then DS.top_server_channel_inv d wire_received wire_sent pending app_log
  else server_channel_closed d wire_received wire_sent app_log

noextract
let server_driver_application_ready
  (st:CS.connection_state)
  : prop =
  ST.server_end_to_end_invariant st /\
  st.CS.cs_model.CS.model_control == CS.ControlApplicationData /\
  CS.application_record_keys_installed_for_role
    CS.ServerEndpoint st.CS.cs_model

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

fn new_server_listener
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires
    pts_to bind_host 'bind_host_bytes **
    pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns result:option server_listener
  ensures
    pts_to bind_host 'bind_host_bytes **
    (match result with
     | Some listener -> IO.is_listener listener 'bind_host_bytes port
     | None -> emp)

fn free_server_listener
  (listener:server_listener)
  requires IO.is_listener listener 'bind_host_bytes 'port
  ensures emp

fn new_server_credentials
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  requires
    pts_to certificate_chain 'certificate_chain_bytes **
    pts_to private_key 'private_key_bytes **
    pure (
      B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
      B.length 'private_key_bytes == SZ.v private_key_len)
  returns result:option server_credentials
  ensures
    exists* credential_identity.
      pts_to certificate_chain 'certificate_chain_bytes **
      pts_to private_key 'private_key_bytes **
      (match result with
       | Some credentials ->
         O.is_server_credentials
           credentials
           (Ghost.reveal 'certificate_chain_bytes)
           credential_identity
       | None -> emp)

fn free_server_credentials
  (credentials:server_credentials)
  requires
    O.is_server_credentials
      credentials 'certificate_chain 'credential_identity
  ensures emp

fn new_server_with_credentials
  (credentials:server_credentials)
  (certificate_chain:array U8.t)
  (certificate_chain_len:SZ.t)
  (private_key:array U8.t)
  (private_key_len:SZ.t)
  (#supported_profile_provider:erased SP.server_supported_profile_provider)
  requires
    (exists* credential_identity.
      O.is_server_credentials
        credentials
        (Ghost.reveal 'certificate_chain_bytes)
        credential_identity) **
    pts_to certificate_chain 'certificate_chain_bytes **
    pts_to private_key 'private_key_bytes **
    pure (
      B.length 'certificate_chain_bytes == SZ.v certificate_chain_len /\
      B.length 'private_key_bytes == SZ.v private_key_len /\
      B.length 'certificate_chain_bytes <=
        Bounds.max_server_certificate_chain_len)
  returns result:option server_driver
  ensures
    pts_to certificate_chain 'certificate_chain_bytes **
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
         pure (
           ST.server_state_correct
             (CR.server_initial_state
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity) /\
           ST.server_end_to_end_invariant
             (CR.server_initial_state
               (Ghost.reveal 'certificate_chain_bytes)
               credential_identity))
       | None -> emp))

fn accept_with_listener
  (d:server_driver)
  (listener:server_listener)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    IO.is_listener listener 'bind_host_bytes port **
    server_driver_live d 'st0 'certificate_chain 'credential_identity **
    pts_to bind_host 'bind_host_bytes **
    pure (
      B.length 'bind_host_bytes == SZ.v bind_host_len /\
      CM.can_start_server 'st0)
  returns status:server_workflow_status
  ensures
    IO.is_listener listener 'bind_host_bytes port **
    pts_to bind_host 'bind_host_bytes **
    (match status with
     | ServerWorkflowOk ->
       exists* wire_received wire_sent pending app_log.
         DS.top_server_channel_inv
           d wire_received wire_sent pending app_log
     | _ ->
       exists* st1.
         DS.top_server_driver_closed
           d st1 'certificate_chain 'credential_identity)

fn send
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (payload:array U8.t)
  (payload_bytes:Ghost.erased B.bytes)
  (payload_len:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to payload (Ghost.reveal payload_bytes) **
    pure (B.length (Ghost.reveal payload_bytes) == SZ.v payload_len)
  returns status:server_workflow_status
  ensures
    exists* wire_received1 wire_sent1 pending1 app_log1.
      server_channel_after_operation
        d
        (channel_send_reusable status)
        wire_received1
        wire_sent1
        pending1
        app_log1 **
      pts_to payload (Ghost.reveal payload_bytes) **
      pure (
        CI.send_transition
          channel_message_of_bytes
          channel_send_succeeded
          status
          (Ghost.reveal payload_bytes)
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          wire_received1
          wire_sent1
          app_log1)

(* Server-initiated KeyUpdate (RFC 8446 4.6.3).  [request] selects the request
   form: [true] sends [update_requested], asking the peer to rotate its own
   sending key in reply; [false] sends [update_not_requested], rotating only
   our write key.  The connection remains usable for application data. *)
fn send_key_update
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (request:bool)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0)
  returns status:server_workflow_status
  ensures
    exists* wire_received1 wire_sent1 pending1 app_log1.
      server_channel_after_operation
        d
        (channel_send_reusable status)
        wire_received1
        wire_sent1
        pending1
        app_log1 **
      pure (
        CPI.histories_ahead
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          wire_received1
          wire_sent1 /\
        app_log1 == Ghost.reveal app_log0)

fn receive
  (d:server_driver)
  (wire_received0:Ghost.erased B.bytes)
  (wire_sent0:Ghost.erased B.bytes)
  (pending0:Ghost.erased B.bytes)
  (app_log0:Ghost.erased (CI.application_log B.bytes))
  (out:array U8.t)
  (old_output:Ghost.erased B.bytes)
  (out_len:SZ.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received0)
      (Ghost.reveal wire_sent0)
      (Ghost.reveal pending0)
      (Ghost.reveal app_log0) **
    pts_to out (Ghost.reveal old_output) **
    pure (B.length (Ghost.reveal old_output) == SZ.v out_len)
  returns result:server_receive_result
  ensures
    exists* wire_received1 wire_sent1 pending1 app_log1 output.
      server_channel_after_operation
        d
        (channel_receive_reusable result)
        wire_received1
        wire_sent1
        pending1
        app_log1 **
      pts_to out output **
      pure (
        B.length output == SZ.v out_len /\
        SZ.v (channel_receive_length result) <= SZ.v out_len /\
        CI.receive_transition
          channel_message_of_bytes
          channel_receive_succeeded
          channel_receive_length
          result
          output
          (Ghost.reveal wire_received0)
          (Ghost.reveal wire_sent0)
          (Ghost.reveal app_log0)
          wire_received1
          wire_sent1
          app_log1)

fn close
  (d:server_driver)
  (wire_received:Ghost.erased B.bytes)
  (wire_sent:Ghost.erased B.bytes)
  (pending:Ghost.erased B.bytes)
  (app_log:Ghost.erased (CI.application_log B.bytes))
  (wait_for_peer:bool)
  (network_fuel:SZ.t)
  requires
    DS.top_server_channel_inv
      d
      (Ghost.reveal wire_received)
      (Ghost.reveal wire_sent)
      (Ghost.reveal pending)
      (Ghost.reveal app_log)
  returns status:server_workflow_status
  ensures
    exists* st certificate_chain credential_identity.
      DS.top_server_driver_closed d st certificate_chain credential_identity

fn free
  (d:server_driver)
  requires
    DS.top_server_driver_closed d 'st 'certificate_chain 'credential_identity
  ensures DS.top_server_driver_released d 'st

(** The production server driver as a [Common.ChannelImplementation]
    instance.

    There is deliberately no separate "channel" API: [ci_send] and [ci_receive]
    are literally [send] and [receive] above, and [ci_send_usable] /
    [ci_receive_usable] are literally [channel_send_reusable] /
    [channel_receive_reusable].  Everything this interface exposes is exactly
    what is verified against the class, and there is exactly one way to send
    and one way to receive on a server channel. **)
noextract
val server_channel_implementation
  : CI.channel_implementation
      DS.top_server_driver
      SP.canonical_server
      CS.connection_state
      CW.wire_message
      CTypes.server_local_event
      EAPI.local_output
      B.bytes
      server_workflow_status
      server_receive_result
      SP.server_protocol_implementation
