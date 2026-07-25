module TLS13.Impl.Server.Driver.BufferedTransport

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module BT = Common.BufferedTCP
module DS = TLS13.Impl.Server.Driver.State
module IO = Common.TCP
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

fn accept_transport_once_from
  (source:server_transport_source)
  (d:DS.top_server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires
    owns_server_transport_source source 'bind_host_bytes port **
    DS.top_server_driver_live
      d 'st0 'certificate_chain 'credential_identity **
    pts_to bind_host 'bind_host_bytes **
    pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns status:DS.server_driver_transport_status
  ensures
    owns_server_transport_source source 'bind_host_bytes port **
    pts_to bind_host 'bind_host_bytes **
    (match status with
     | DS.ServerDriverTransportOk ->
       DS.top_server_driver_connected
         d
         'st0
         'certificate_chain
         'credential_identity
         B.empty
         B.empty
     | _ ->
       DS.top_server_driver_live
         d 'st0 'certificate_chain 'credential_identity)
{
  unfold (DS.top_server_driver_live
    d 'st0 'certificate_chain 'credential_identity);
  with storage_model.
    assert (BT.is_storage d.top_server_driver_storage storage_model);
  match source {
    None -> {
      let listener_opt = IO.listen_tcp bind_host bind_host_len port;
      match listener_opt {
        None -> {
          fold (DS.top_server_driver_live
            d 'st0 'certificate_chain 'credential_identity);
          rewrite
            (owns_server_transport_source None 'bind_host_bytes port)
            as
            (owns_server_transport_source source 'bind_host_bytes port);
          DS.ServerDriverListenFailed
        }
        Some listener -> {
          let channel_opt = IO.accept_tcp listener;
          match channel_opt {
            None -> {
              IO.close_listener listener;
              fold (DS.top_server_driver_live
                d 'st0 'certificate_chain 'credential_identity);
              rewrite
                (owns_server_transport_source None 'bind_host_bytes port)
                as
                (owns_server_transport_source source 'bind_host_bytes port);
              DS.ServerDriverAcceptFailed
            }
            Some raw_channel -> {
              IO.close_listener listener;
              let channel =
                BT.attach d.top_server_driver_storage raw_channel;
              Box.(d.top_server_driver_channel := Some channel);
              unfold (DS.top_server_driver_canonical_progress d 'st0);
              fold (DS.buffered_driver_canonical_progress
                (DS.top_server_as_buffered d channel)
                'st0);
              fold (DS.buffered_driver_indexed
                (DS.top_server_as_buffered d channel)
                'st0
                'certificate_chain
                'credential_identity
                (BT.pending storage_model)
                0sz
                storage_model
                B.empty
                B.empty
                B.empty);
              fold (DS.top_server_driver_connected_indexed
                d
                'st0
                'certificate_chain
                'credential_identity
                B.empty
                B.empty
                channel
                storage_model
                B.empty
                0sz);
              fold (DS.top_server_driver_connected
                d
                'st0
                'certificate_chain
                'credential_identity
                B.empty
                B.empty);
              rewrite
                (owns_server_transport_source None 'bind_host_bytes port)
                as
                (owns_server_transport_source source 'bind_host_bytes port);
              DS.ServerDriverTransportOk
            }
          }
        }
      }
    }
    Some listener -> {
      rewrite
        (owns_server_transport_source
          (Some listener) 'bind_host_bytes port)
        as
        (IO.is_listener listener 'bind_host_bytes port);
      let channel_opt = IO.accept_tcp listener;
      match channel_opt {
        None -> {
          fold (DS.top_server_driver_live
            d 'st0 'certificate_chain 'credential_identity);
          rewrite
            (IO.is_listener listener 'bind_host_bytes port)
            as
            (owns_server_transport_source
              source 'bind_host_bytes port);
          DS.ServerDriverAcceptFailed
        }
        Some raw_channel -> {
          let channel =
            BT.attach d.top_server_driver_storage raw_channel;
          Box.(d.top_server_driver_channel := Some channel);
          unfold (DS.top_server_driver_canonical_progress d 'st0);
          fold (DS.buffered_driver_canonical_progress
            (DS.top_server_as_buffered d channel)
            'st0);
          fold (DS.buffered_driver_indexed
            (DS.top_server_as_buffered d channel)
            'st0
            'certificate_chain
            'credential_identity
            (BT.pending storage_model)
            0sz
            storage_model
            B.empty
            B.empty
            B.empty);
          fold (DS.top_server_driver_connected_indexed
            d
            'st0
            'certificate_chain
            'credential_identity
            B.empty
            B.empty
            channel
            storage_model
            B.empty
            0sz);
          fold (DS.top_server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            B.empty
            B.empty);
          rewrite
            (IO.is_listener listener 'bind_host_bytes port)
            as
            (owns_server_transport_source
              source 'bind_host_bytes port);
          DS.ServerDriverTransportOk
        }
      }
    }
  }
}

fn close_transport_once
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_connected
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent
  ensures
    DS.top_server_driver_closed
      d 'st0 'certificate_chain 'credential_identity
{
  unfold (DS.top_server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with channel model committed buffered_len.
    assert (DS.top_server_driver_connected_indexed
      d
      'st0
      'certificate_chain
      'credential_identity
      'received
      'sent
      channel
      model
      committed
      buffered_len);
  unfold (DS.top_server_driver_connected_indexed
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent
    channel
    model
    committed
    buffered_len);
  let current_channel = Box.(!d.top_server_driver_channel);
  assert (pure (current_channel == Some channel));
  let concrete_channel = Some?.v current_channel;
  assert (pure (concrete_channel == channel));
  rewrite
    (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d channel)
      'st0
      'certificate_chain
      'credential_identity
      (BT.pending model)
      buffered_len
      model
      'received
      committed
      'sent)
    as
    (DS.buffered_driver_indexed
      (DS.top_server_as_buffered d concrete_channel)
      'st0
      'certificate_chain
      'credential_identity
      (BT.pending model)
      buffered_len
      model
      'received
      committed
      'sent);
  unfold (DS.buffered_driver_indexed
    (DS.top_server_as_buffered d concrete_channel)
    'st0
    'certificate_chain
    'credential_identity
    (BT.pending model)
    buffered_len
    model
    'received
    committed
    'sent);
  let detached = BT.close_detach concrete_channel;
  with detached_model.
    assert (BT.is_storage detached detached_model);
  BT.lemma_same_storage_unique
    concrete_channel
    d.top_server_driver_storage
    detached;
  rewrite
    (BT.is_storage detached detached_model)
    as
    (BT.is_storage d.top_server_driver_storage detached_model);
  Box.(d.top_server_driver_channel := DS.no_buffered_channel);
  unfold (DS.buffered_driver_canonical_progress
    (DS.top_server_as_buffered d concrete_channel)
    'st0);
  fold (DS.top_server_driver_canonical_progress d 'st0);
  fold (DS.top_server_driver_closed
    d 'st0 'certificate_chain 'credential_identity)
}

fn close_live_without_transport
  (d:DS.top_server_driver)
  requires
    DS.top_server_driver_live
      d 'st0 'certificate_chain 'credential_identity
  ensures
    DS.top_server_driver_closed
      d 'st0 'certificate_chain 'credential_identity
{
  unfold (DS.top_server_driver_live
    d 'st0 'certificate_chain 'credential_identity);
  fold (DS.top_server_driver_closed
    d 'st0 'certificate_chain 'credential_identity)
}
