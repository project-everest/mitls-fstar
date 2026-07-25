module TLS13.Impl.Server.Driver.BufferedAccept

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BC = TLS13.Impl.Server.Driver.BufferedChannel
module BTH = TLS13.Impl.Server.Driver.BufferedTopHandshake
module BTrans = TLS13.Impl.Server.Driver.BufferedTransport
module BW = TLS13.Impl.Server.Driver.BufferedWorkflow
module CM = TLS13.Impl.ConnectionState.Model
module CS = TLS13.Spec.StateMachine
module DS = TLS13.Impl.Server.Driver.State
module ST = TLS13.Impl.Server.Types
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

let lemma_application_control_not_failed
  (st:CS.connection_state)
  : Lemma
      (requires
        st.CS.cs_model.CS.model_control == CS.ControlApplicationData)
      (ensures ST.server_connection_control_not_failed st)
=
  match st.CS.cs_model.CS.model_control with
  | CS.ControlApplicationData -> ()
  | _ -> assert False

fn run
  (d:DS.top_server_driver)
  (source:BTrans.server_transport_source)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  (local_fuel:SZ.t)
  (network_fuel:SZ.t)
  requires
    BTrans.owns_server_transport_source
      source 'bind_host_bytes port **
    DS.top_server_driver_live
      d 'st0 'certificate_chain 'credential_identity **
    pts_to bind_host 'bind_host_bytes **
    pure (
      B.length 'bind_host_bytes == SZ.v bind_host_len /\
      CM.can_start_server 'st0)
  returns status:accept_status
  ensures
    BTrans.owns_server_transport_source
      source 'bind_host_bytes port **
    pts_to bind_host 'bind_host_bytes **
    (match status with
     | BufferedAcceptOk ->
       exists* wire_received wire_sent pending app_log.
         DS.top_server_channel_inv
           d wire_received wire_sent pending app_log
     | _ ->
       exists* st1.
         DS.top_server_driver_closed
           d st1 'certificate_chain 'credential_identity)
{
  let transport =
    BTrans.accept_transport_once_from
      source d bind_host bind_host_len port;
  match transport {
    DS.ServerDriverListenFailed -> {
      BTrans.close_live_without_transport d;
      BufferedAcceptListenFailed
    }
    DS.ServerDriverAcceptFailed -> {
      BTrans.close_live_without_transport d;
      BufferedAcceptTransportFailed
    }
    DS.ServerDriverTransportOk -> {
      let handshake =
        BTH.run_connected d local_fuel network_fuel;
      match handshake {
        BW.HandshakeOk -> {
          with st1 received1 sent1.
            assert (DS.top_server_driver_connected
              d
              st1
              'certificate_chain
              'credential_identity
              received1
              sent1);
          assert (pure (
            st1.CS.cs_model.CS.model_control ==
              CS.ControlApplicationData));
          lemma_application_control_not_failed st1;
          BC.pack_connected_channel
            d
            (Ghost.hide st1)
            (Ghost.hide (Ghost.reveal 'certificate_chain))
            (Ghost.hide (Ghost.reveal 'credential_identity))
            (Ghost.hide received1)
            (Ghost.hide sent1);
          BufferedAcceptOk
        }
        BW.HandshakeExhausted -> {
          BTrans.close_transport_once d;
          BufferedAcceptExhausted
        }
        BW.HandshakeStepFailed -> {
          BTrans.close_transport_once d;
          BufferedAcceptHandshakeFailed
        }
        BW.HandshakeRandomFailed -> {
          BTrans.close_transport_once d;
          BufferedAcceptHandshakeFailed
        }
        BW.HandshakeSelectionNotReady -> {
          BTrans.close_transport_once d;
          BufferedAcceptHandshakeFailed
        }
        BW.HandshakeSentinelCollision -> {
          BTrans.close_transport_once d;
          BufferedAcceptHandshakeFailed
        }
      }
    }
  }
}
