module TLS13.Impl.Handle.Local

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open TLS13.Impl.Client.Types

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module C = TLS13.Impl.ConnectionState
module CS = TLS13.Spec.ConnectionState
module CT = TLS13.Impl.Client.Types
module Arr = Pulse.Lib.Array
module M = TLS13.Messages
module Seq = FStar.Seq
module SZ = FStar.SizeT
module T = TLS13.Types
module U8 = FStar.UInt8
module X = TLS13.X509.Spec

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
                 B.length 'old_app_out == SZ.v app_out_len /\
                 CT.local_input_wf
                   'st0
                   kind
                   (Ghost.reveal 'payload_bytes))
  returns resp: CT.client_response
  ensures exists* st1 network_out_bytes app_out_bytes.
          C.connection_exactly c st1 **
          pts_to payload 'payload_bytes **
          pts_to network_out network_out_bytes **
          pts_to app_out app_out_bytes **
          pure (B.length network_out_bytes == SZ.v network_out_len /\
                B.length app_out_bytes == SZ.v app_out_len /\
                CT.some_legal_response
                  'st0
                  st1
                  resp
                  network_out_bytes
                  app_out_bytes /\
                CT.legal_handled_local_response
                  'st0
                  st1
                  resp
                  kind
                  (Ghost.reveal 'payload_bytes)
                  network_out_bytes
                  app_out_bytes)
{
  match kind {
    LocalStartHandshake -> {
    let ok = C.try_start_handshake c;
    if ok {
      with start.
        assert (C.connection_exactly c (C.started_handshake_state 'st0 start));
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      C.lemma_started_handshake_state_evolves 'st0 start;
      assert (pure (CT.legal_response_for_event
        'st0
        (C.started_handshake_state 'st0 start)
        resp
        (CS.ConnLocalEvent (CS.LocalStartHandshake start))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.started_handshake_state 'st0 start)
        resp
        CT.LocalStartHandshake
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent (CS.LocalStartHandshake start))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.started_handshake_state 'st0 start)
        resp
        CT.LocalStartHandshake
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.started_handshake_state 'st0 start)
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
        CT.LocalStartHandshake
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
    LocalInstallClientApplicationTrafficKeys -> {
    let ok = C.try_install_client_application_traffic_keys c;
    if ok {
      with material.
        assert (C.connection_exactly c
          (C.installed_traffic_keys_state 'st0 {
            CS.install_epoch = CS.TrafficApplication;
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
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        })
        resp
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
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
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        })
        resp
        CT.LocalInstallClientApplicationTrafficKeys
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
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
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficWrite;
          CS.install_material = material;
        })
        resp
        CT.LocalInstallClientApplicationTrafficKeys
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficApplication;
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
        CT.LocalInstallClientApplicationTrafficKeys
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
    LocalInstallServerApplicationTrafficKeys -> {
    let ok = C.try_install_server_application_traffic_keys c;
    if ok {
      with material.
        assert (C.connection_exactly c
          (C.installed_traffic_keys_state 'st0 {
            CS.install_epoch = CS.TrafficApplication;
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
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        })
        resp
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
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
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        })
        resp
        CT.LocalInstallServerApplicationTrafficKeys
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent (CS.LocalInstallTrafficKeys {
          CS.install_epoch = CS.TrafficApplication;
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
          CS.install_epoch = CS.TrafficApplication;
          CS.install_direction = CS.TrafficRead;
          CS.install_material = material;
        })
        resp
        CT.LocalInstallServerApplicationTrafficKeys
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.installed_traffic_keys_state 'st0 {
          CS.install_epoch = CS.TrafficApplication;
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
        CT.LocalInstallServerApplicationTrafficKeys
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
    LocalValidateCertificate -> {
    let ready = C.can_validate_certificate c payload_len;
    if ready {
      let peer = Ghost.hide (CT.local_validation_peer 'st0 (Ghost.reveal 'payload_bytes));
      assert (pure (CT.local_input_wf
        'st0
        CT.LocalValidateCertificate
        (Ghost.reveal 'payload_bytes)));
      assert (pure ('st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsCertificateReceived));
      assert (pure (CS.legal_event
        'st0.CS.cs_model
        (CS.ConnLocalEvent
          (CS.LocalValidateCertificate (Ghost.reveal peer)))));
      assert (pure ((Ghost.reveal peer).X.validated_hostname ==
        'st0.CS.cs_model.CS.model_config.CS.config_server_name));
      assert (pure ((Ghost.reveal peer).X.leaf_public_key ==
        (Ghost.reveal 'payload_bytes)));
      assert (pure ((Ghost.reveal peer).X.permitted_signature_schemes == []));
      C.mark_validated_certificate c payload payload_len #peer;
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      C.lemma_validated_certificate_state_evolves
        'st0
        (Ghost.reveal peer);
      assert (pure (CT.legal_response_for_event
        'st0
        (C.validated_certificate_state 'st0 (Ghost.reveal peer))
        resp
        (CS.ConnLocalEvent
          (CS.LocalValidateCertificate (Ghost.reveal peer)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.validated_certificate_state 'st0 (Ghost.reveal peer))
        resp
        CT.LocalValidateCertificate
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent
          (CS.LocalValidateCertificate (Ghost.reveal peer)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.validated_certificate_state 'st0 (Ghost.reveal peer))
        resp
        CT.LocalValidateCertificate
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.validated_certificate_state 'st0 (Ghost.reveal peer))
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
        CT.LocalValidateCertificate
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
    LocalVerifyCertificateSignature -> {
    let ready = C.can_verify_certificate_signature c;
    if ready {
      let cv = Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify);
      assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_certificate_verify ==
        Some (Ghost.reveal cv)));
      assert (pure (CT.local_input_wf
        'st0
        CT.LocalVerifyCertificateSignature
        (Ghost.reveal 'payload_bytes)));
      assert (pure ('st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsCertificateVerifyReceived));
      assert (pure (CS.legal_event
        'st0.CS.cs_model
        (CS.ConnLocalEvent
          (CS.LocalVerifyCertificateSignature (Ghost.reveal cv)))));
      C.mark_verified_certificate_signature c #cv;
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      C.lemma_verified_certificate_signature_state_evolves
        'st0
        (Ghost.reveal cv);
      assert (pure (CT.legal_response_for_event
        'st0
        (C.verified_certificate_signature_state 'st0 (Ghost.reveal cv))
        resp
        (CS.ConnLocalEvent
          (CS.LocalVerifyCertificateSignature (Ghost.reveal cv)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.verified_certificate_signature_state 'st0 (Ghost.reveal cv))
        resp
        CT.LocalVerifyCertificateSignature
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent
          (CS.LocalVerifyCertificateSignature (Ghost.reveal cv)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.verified_certificate_signature_state 'st0 (Ghost.reveal cv))
        resp
        CT.LocalVerifyCertificateSignature
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.verified_certificate_signature_state 'st0 (Ghost.reveal cv))
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
        CT.LocalVerifyCertificateSignature
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
    LocalVerifyFinished -> {
    let ready = C.can_verify_server_finished c payload_len;
    if ready {
      let fin = Ghost.hide (Some?.v 'st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished);
      assert (pure ('st0.CS.cs_model.CS.model_handshake.CS.hs_server_finished ==
        Some (Ghost.reveal fin)));
      assert (pure (CT.local_input_wf
        'st0
        CT.LocalVerifyFinished
        (Ghost.reveal 'payload_bytes)));
      assert (pure ('st0.CS.cs_model.CS.model_control ==
        CS.ControlHandshaking CS.HsServerFinishedReceived));
      assert (pure (CS.legal_event
        'st0.CS.cs_model
        (CS.ConnLocalEvent
          (CS.LocalVerifyFinished (Ghost.reveal fin)))));
      assert (pure (Seq.equal
        (Ghost.reveal 'payload_bytes)
        (TLS13.Wire.Spec.serialize_handshake (TLS13.Messages.Finished (Ghost.reveal fin)))));
      C.mark_verified_server_finished c payload payload_len #fin;
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      C.lemma_verified_server_finished_state_evolves
        'st0
        (Ghost.reveal fin);
      assert (pure (CT.legal_response_for_event
        'st0
        (C.verified_server_finished_state 'st0 (Ghost.reveal fin))
        resp
        (CS.ConnLocalEvent
          (CS.LocalVerifyFinished (Ghost.reveal fin)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.verified_server_finished_state 'st0 (Ghost.reveal fin))
        resp
        CT.LocalVerifyFinished
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent
          (CS.LocalVerifyFinished (Ghost.reveal fin)))
        B.empty
        B.empty
        'old_network_out
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.verified_server_finished_state 'st0 (Ghost.reveal fin))
        resp
        CT.LocalVerifyFinished
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.verified_server_finished_state 'st0 (Ghost.reveal fin))
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
        CT.LocalVerifyFinished
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
    LocalSendClientHello -> {
    let written_opt =
      C.try_send_client_hello
        c
        network_out
        network_out_len;
    match written_opt {
      Some written -> {
        with ch raw_sent network_out_bytes.
          assert (pts_to network_out network_out_bytes);
        assert (C.connection_exactly
          c
          (C.sent_client_hello_state 'st0 ch raw_sent));
        assert (pure (B.length network_out_bytes == SZ.v network_out_len));
        assert (pure (5 <= SZ.v written));
        assert (pure (SZ.v written <= B.length network_out_bytes));
        assert (pure (C.can_send_client_hello 'st0 ch raw_sent));
        assert (pure (Seq.equal
          raw_sent
          (Seq.slice network_out_bytes 0 (SZ.v written))));
        let resp = {
          CT.network_out_len = written;
          CT.app_out_len = 0sz;
          CT.status = CT.StepOk;
        };
        Seq.lemma_len_slice network_out_bytes 0 (SZ.v written);
        assert (pure (Seq.equal raw_sent (CT.response_network_out resp network_out_bytes)));
        Seq.lemma_len_slice 'old_app_out 0 0;
        Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
        C.lemma_sent_client_hello_state_evolves 'st0 ch raw_sent;
        assert (pure (CT.legal_response_for_event
          'st0
          (C.sent_client_hello_state 'st0 ch raw_sent)
          resp
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          })
          raw_sent
          B.empty
          network_out_bytes
          'old_app_out));
        assert (pure (CT.legal_local_response
          'st0
          (C.sent_client_hello_state 'st0 ch raw_sent)
          resp
          CT.LocalSendClientHello
          (Ghost.reveal 'payload_bytes)
          (CS.ConnNetworkEvent {
            CL.message_direction = CL.Sent;
            CL.message_value = M.TlsHandshake (M.ClientHello ch);
          })
          raw_sent
          B.empty
          network_out_bytes
          'old_app_out));
        assert (pure (CT.legal_handled_local_response
          'st0
          (C.sent_client_hello_state 'st0 ch raw_sent)
          resp
          CT.LocalSendClientHello
          (Ghost.reveal 'payload_bytes)
          network_out_bytes
          'old_app_out));
        assert (pure (CT.some_legal_response
          'st0
          (C.sent_client_hello_state 'st0 ch raw_sent)
          resp
          network_out_bytes
          'old_app_out));
        resp
      }
      None -> {
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
          CT.LocalSendClientHello
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
    LocalDeliverApplicationData -> {
    let ready = C.can_deliver_application_data c payload_len app_out_len;
    if ready {
      assert (pure (CT.local_input_wf
        'st0
        CT.LocalDeliverApplicationData
        (Ghost.reveal 'payload_bytes)));
      assert (pure (CS.legal_event
        'st0.CS.cs_model
        (CS.ConnLocalEvent
          (CS.LocalDeliverApplicationData (Ghost.reveal 'payload_bytes)))));
      pts_to_len payload;
      pts_to_len app_out;
      Arr.memcpy_l payload_len payload app_out;
      with app_out_bytes. assert (pts_to app_out app_out_bytes);
      assert (pure (B.length app_out_bytes == SZ.v app_out_len));
      assert (pure (Seq.equal
        (Seq.slice app_out_bytes 0 (SZ.v payload_len))
        (Seq.slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len))));
      assert (pure (Seq.equal
        (Ghost.reveal 'payload_bytes)
        (Seq.slice (Ghost.reveal 'payload_bytes) 0 (SZ.v payload_len))));
      C.mark_delivered_application_data c #(Ghost.reveal 'payload_bytes);
      let resp = {
        CT.network_out_len = 0sz;
        CT.app_out_len = payload_len;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice 'old_network_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_network_out 0 0);
      assert (pure (Seq.equal B.empty (CT.response_network_out resp 'old_network_out)));
      assert (pure (CT.response_app_out resp app_out_bytes ==
        Seq.slice app_out_bytes 0 (SZ.v payload_len)));
      assert (pure (Seq.equal
        (Ghost.reveal 'payload_bytes)
        (CT.response_app_out resp app_out_bytes)));
      C.lemma_delivered_application_data_state_evolves
        'st0
        (Ghost.reveal 'payload_bytes);
      assert (pure (CT.legal_response_for_event
        'st0
        (C.delivered_application_data_state 'st0 (Ghost.reveal 'payload_bytes))
        resp
        (CS.ConnLocalEvent
          (CS.LocalDeliverApplicationData (Ghost.reveal 'payload_bytes)))
        B.empty
        B.empty
        'old_network_out
        app_out_bytes));
      assert (pure (CT.legal_local_response
        'st0
        (C.delivered_application_data_state 'st0 (Ghost.reveal 'payload_bytes))
        resp
        CT.LocalDeliverApplicationData
        (Ghost.reveal 'payload_bytes)
        (CS.ConnLocalEvent
          (CS.LocalDeliverApplicationData (Ghost.reveal 'payload_bytes)))
        B.empty
        B.empty
        'old_network_out
        app_out_bytes));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.delivered_application_data_state 'st0 (Ghost.reveal 'payload_bytes))
        resp
        CT.LocalDeliverApplicationData
        (Ghost.reveal 'payload_bytes)
        'old_network_out
        app_out_bytes));
      assert (pure (CT.some_legal_response
        'st0
        (C.delivered_application_data_state 'st0 (Ghost.reveal 'payload_bytes))
        resp
        'old_network_out
        app_out_bytes));
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
        CT.LocalDeliverApplicationData
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
    LocalSendApplicationData -> {
    let ok =
      C.try_send_application_data
        c
        payload
        payload_len
        network_out
        network_out_len;
    if ok {
      with raw_sent network_out_bytes.
        assert (pts_to network_out network_out_bytes);
      assert (C.connection_exactly
        c
        (C.sent_application_data_state
          'st0
          (Ghost.reveal 'payload_bytes)
          raw_sent));
      assert (pure (B.length network_out_bytes == SZ.v network_out_len));
      assert (pure (SZ.v payload_len + 22 <= B.length network_out_bytes));
      assert (pure (C.can_send_application_data
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent));
      assert (pure (Seq.equal
        raw_sent
        (Seq.slice network_out_bytes 0 (SZ.v payload_len + 22))));
      assert (pure (SZ.fits (SZ.v payload_len + 22)));
      let written_len = SZ.add payload_len 22sz;
      assert (pure (SZ.v written_len == SZ.v payload_len + 22));
      let resp = {
        CT.network_out_len = written_len;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice network_out_bytes 0 (SZ.v written_len);
      assert (pure (Seq.equal raw_sent (CT.response_network_out resp network_out_bytes)));
      Seq.lemma_len_slice 'old_app_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
      C.lemma_sent_application_data_state_evolves
        'st0
        (Ghost.reveal 'payload_bytes)
        raw_sent;
      assert (pure (CT.legal_response_for_event
        'st0
        (C.sent_application_data_state
          'st0
          (Ghost.reveal 'payload_bytes)
          raw_sent)
        resp
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        })
        raw_sent
        B.empty
        network_out_bytes
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.sent_application_data_state
          'st0
          (Ghost.reveal 'payload_bytes)
          raw_sent)
        resp
        CT.LocalSendApplicationData
        (Ghost.reveal 'payload_bytes)
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsApplicationData (Ghost.reveal 'payload_bytes);
        })
        raw_sent
        B.empty
        network_out_bytes
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.sent_application_data_state
          'st0
          (Ghost.reveal 'payload_bytes)
          raw_sent)
        resp
        CT.LocalSendApplicationData
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.sent_application_data_state
          'st0
          (Ghost.reveal 'payload_bytes)
          raw_sent)
        resp
        network_out_bytes
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
        CT.LocalSendApplicationData
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
    LocalSendClientFinished -> {
    let ok = C.try_send_client_finished c network_out network_out_len;
    if ok {
      with fin raw_sent network_out_bytes.
        assert (pts_to network_out network_out_bytes);
      assert (C.connection_exactly c (C.sent_client_finished_state 'st0 fin raw_sent));
      assert (pure (B.length network_out_bytes == SZ.v network_out_len));
      assert (pure (58 <= B.length network_out_bytes));
      assert (pure (C.can_send_client_finished 'st0 fin raw_sent));
      assert (pure (Seq.equal raw_sent (Seq.slice network_out_bytes 0 58)));
      let resp = {
        CT.network_out_len = 58sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      assert (pure (58 <= B.length network_out_bytes));
      Seq.lemma_len_slice network_out_bytes 0 58;
      assert (pure (Seq.equal raw_sent (CT.response_network_out resp network_out_bytes)));
      Seq.lemma_len_slice 'old_app_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
      C.lemma_sent_client_finished_state_evolves 'st0 fin raw_sent;
      assert (pure (CT.legal_response_for_event
        'st0
        (C.sent_client_finished_state 'st0 fin raw_sent)
        resp
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished fin);
        })
        raw_sent
        B.empty
        network_out_bytes
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.sent_client_finished_state 'st0 fin raw_sent)
        resp
        CT.LocalSendClientFinished
        (Ghost.reveal 'payload_bytes)
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsHandshake (M.Finished fin);
        })
        raw_sent
        B.empty
        network_out_bytes
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.sent_client_finished_state 'st0 fin raw_sent)
        resp
        CT.LocalSendClientFinished
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.sent_client_finished_state 'st0 fin raw_sent)
        resp
        network_out_bytes
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
        CT.LocalSendClientFinished
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
    LocalSendCloseNotify -> {
    let ok =
      C.try_send_close_notify
        c
        network_out
        network_out_len;
    if ok {
      with raw_sent network_out_bytes.
        assert (pts_to network_out network_out_bytes);
      assert (C.connection_exactly
        c
        (C.sent_close_notify_state
          'st0
          raw_sent));
      assert (pure (B.length network_out_bytes == SZ.v network_out_len));
      assert (pure (24 <= B.length network_out_bytes));
      assert (pure (C.can_send_close_notify
        'st0
        raw_sent));
      assert (pure (Seq.equal
        raw_sent
        (Seq.slice network_out_bytes 0 24)));
      let resp = {
        CT.network_out_len = 24sz;
        CT.app_out_len = 0sz;
        CT.status = CT.StepOk;
      };
      Seq.lemma_len_slice network_out_bytes 0 24;
      assert (pure (Seq.equal raw_sent (CT.response_network_out resp network_out_bytes)));
      Seq.lemma_len_slice 'old_app_out 0 0;
      Seq.lemma_eq_intro B.empty (Seq.slice 'old_app_out 0 0);
      C.lemma_sent_close_notify_state_evolves 'st0 raw_sent;
      assert (pure (CT.legal_response_for_event
        'st0
        (C.sent_close_notify_state
          'st0
          raw_sent)
        resp
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        })
        raw_sent
        B.empty
        network_out_bytes
        'old_app_out));
      assert (pure (CT.legal_local_response
        'st0
        (C.sent_close_notify_state
          'st0
          raw_sent)
        resp
        CT.LocalSendCloseNotify
        (Ghost.reveal 'payload_bytes)
        (CS.ConnNetworkEvent {
          CL.message_direction = CL.Sent;
          CL.message_value = M.TlsAlert T.CloseNotify;
        })
        raw_sent
        B.empty
        network_out_bytes
        'old_app_out));
      assert (pure (CT.legal_handled_local_response
        'st0
        (C.sent_close_notify_state
          'st0
          raw_sent)
        resp
        CT.LocalSendCloseNotify
        (Ghost.reveal 'payload_bytes)
        network_out_bytes
        'old_app_out));
      assert (pure (CT.some_legal_response
        'st0
        (C.sent_close_notify_state
          'st0
          raw_sent)
        resp
        network_out_bytes
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
        CT.LocalSendCloseNotify
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
