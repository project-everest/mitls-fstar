module TLS13.Impl.Handle.Local

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open TLS13.Impl.Client.Types

module B = TLS13.Bytes
module C = TLS13.Impl.ConnectionState
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8

fn handle_local_event
  (c:C.connection_state)
  (kind:CT.local_event_kind)
  (payload:array U8.t)
  (payload_len:SZ.t)
  (network_out:array U8.t)
  (network_out_len:SZ.t)
  (app_out:array U8.t)
  (app_out_len:SZ.t)
  requires C.connection_exactly c 'st0 **
           pts_to payload 'payload_bytes **
           pts_to network_out 'old_network_out **
           pts_to app_out 'old_app_out **
           pure (B.length 'payload_bytes == SZ.v payload_len /\
                 B.length 'old_network_out == SZ.v network_out_len /\
                 B.length 'old_app_out == SZ.v app_out_len)
  returns resp: CT.client_response
  ensures exists* st1.
          C.connection_exactly c st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out 'old_network_out **
          pts_to app_out 'old_app_out **
          pure (B.length 'old_network_out == SZ.v network_out_len /\
                B.length 'old_app_out == SZ.v app_out_len /\
                CT.some_legal_response
                  'st0
                  st1
                  resp
                  'old_network_out
                  'old_app_out /\
                CT.legal_handled_local_response
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  'old_network_out
                  'old_app_out)
{
  match kind {
    LocalDeriveSharedSecret -> {
    let ok = C.try_derive_shared_secret c;
    if ok {
      with shared.
        assert (C.connection_exactly c (C.derived_shared_secret_state 'st0 shared));
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      assert (pure (CT.legal_response_for_event
        'st0
        (C.derived_shared_secret_state 'st0 shared)
        resp
        (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.derived_shared_secret_state 'st0 shared)
        resp
        CT.LocalDeriveSharedSecret
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent (CS.LocalDeriveSharedSecret shared))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.derived_shared_secret_state 'st0 shared)
        resp
        CT.LocalDeriveSharedSecret
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.derived_shared_secret_state 'st0 shared)
        resp
        'old_network_out
        'old_app_out));
      resp
    } else {
      C.mark_unexpected_message c;
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.IllegalTransition;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      assert (pure (CT.unexpected_message_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        CT.LocalDeriveSharedSecret
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        'old_network_out
        'old_app_out));
      resp
    }
  }
    LocalInstallClientHandshakeTrafficKeys -> {
    let ok = C.try_install_client_handshake_traffic_keys c;
    if ok {
      with material.
        assert (C.connection_exactly c
          (C.installed_traffic_keys_state 'st0 {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficWrite;
            CS.install_material = material;
          }));
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      assert (pure (CT.legal_response_for_event
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        })
        resp
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        }))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        })
        resp
        CT.LocalInstallClientHandshakeTrafficKeys
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        }))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        })
        resp
        CT.LocalInstallClientHandshakeTrafficKeys
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        })
        resp
        'old_network_out
        'old_app_out));
      resp
    } else {
      C.mark_unexpected_message c;
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.IllegalTransition;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      assert (pure (CT.unexpected_message_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        CT.LocalInstallClientHandshakeTrafficKeys
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        'old_network_out
        'old_app_out));
      resp
    }
  }
    LocalInstallServerHandshakeTrafficKeys -> {
    let ok = C.try_install_server_handshake_traffic_keys c;
    if ok {
      with material.
        assert (C.connection_exactly c
          (C.installed_traffic_keys_state 'st0 {
            CS.install_epoch = CS.TrafficHandshake;
            CS.install_direction = CS.TrafficRead;
            CS.install_material = material;
          }));
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      assert (pure (CT.legal_response_for_event
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        })
        resp
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        }))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        })
        resp
        CT.LocalInstallServerHandshakeTrafficKeys
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        }))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        })
        resp
        CT.LocalInstallServerHandshakeTrafficKeys
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficHandshake;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        })
        resp
        'old_network_out
        'old_app_out));
      resp
    } else {
      C.mark_unexpected_message c;
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.IllegalTransition;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      assert (pure (CT.unexpected_message_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        CT.LocalInstallServerHandshakeTrafficKeys
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.local_fail_state 'st0 C.tls_unexpected_message_error)
        resp
        'old_network_out
        'old_app_out));
      resp
    }
  }
    _ -> {
    C.mark_unexpected_message c;
    let resp = {
      CT.network_out_len = 0sz;
      CT.app_out_len = 0sz;
      CT.status = CT.IllegalTransition;
    };
    Seq.lemma_len_slice 'old_network_out 0 0;
    Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
    assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
    assert (pure (CT.unexpected_message_response
      'st0
      (C.local_fail_state 'st0 C.tls_unexpected_message_error)
      resp
      'old_network_out
      'old_app_out));
    assert (pure (CT.legal_handled_local_response
      'st0
      (C.local_fail_state 'st0 C.tls_unexpected_message_error)
      resp
      kind
      (Ghost.reveal 'payload_bytes)
      'old_network_out
      'old_app_out));
    assert (pure (CT.some_legal_response
      'st0
      (C.local_fail_state 'st0 C.tls_unexpected_message_error)
      resp
      'old_network_out
      'old_app_out));
    resp
  }
  }
}
