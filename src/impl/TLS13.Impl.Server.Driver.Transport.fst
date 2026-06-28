module TLS13.Impl.Server.Driver.Transport

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open TLS13.Impl.Server.Driver.State

module B = TLS13.Bytes
module IO = Common.TCP
module Box = Pulse.Lib.Box
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

fn accept_transport_once
  (d:server_driver)
  (bind_host:array U8.t)
  (bind_host_len:SZ.t)
  (port:U16.t)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity **
           pts_to bind_host 'bind_host_bytes **
           pure (B.length 'bind_host_bytes == SZ.v bind_host_len)
  returns status:server_driver_transport_status
  ensures pts_to bind_host 'bind_host_bytes **
          (match status with
           | ServerDriverTransportOk ->
             server_driver_connected
               d
               'st0
               'certificate_chain
               'credential_identity
               B.empty
               B.empty
           | _ ->
             server_driver_live d 'st0 'certificate_chain 'credential_identity)
{
  unfold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
  let listener_opt = IO.listen_tcp bind_host bind_host_len port;
  match listener_opt {
    None -> {
      fold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
      ServerDriverListenFailed
    }
    Some listener -> {
      let ch_opt = IO.accept_tcp listener;
      match ch_opt {
        None -> {
          IO.close_listener listener;
          fold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
          ServerDriverAcceptFailed
        }
        Some ch -> {
          IO.close_listener listener;
          Box.(d.server_driver_channel := Some ch);
          fold (server_driver_connected
            d
            'st0
            'certificate_chain
            'credential_identity
            B.empty
            B.empty);
          ServerDriverTransportOk
        }
      }
    }
  }
}

fn close_transport_once
  (d:server_driver)
  requires server_driver_connected
             d
             'st0
             'certificate_chain
             'credential_identity
             'received
             'sent
  ensures server_driver_closed d 'st0 'certificate_chain 'credential_identity
{
  unfold (server_driver_connected
    d
    'st0
    'certificate_chain
    'credential_identity
    'received
    'sent);
  with ch buffered buffered_len.
    assert (Box.pts_to d.server_driver_channel (Some ch) **
            IO.is_channel ch 'received 'sent **
            server_driver_buffers d buffered buffered_len);
  let current_channel = Box.(!d.server_driver_channel);
  assert (pure (current_channel == Some ch));
  assert (pure (Some? current_channel));
  let concrete_ch = Some?.v current_channel;
  assert (pure (current_channel == Some concrete_ch));
  assert (pure (Some concrete_ch == Some ch));
  rewrite (IO.is_channel ch 'received 'sent) as
    (IO.is_channel concrete_ch 'received 'sent);
  IO.close concrete_ch;
  Box.(d.server_driver_channel := no_channel);
  fold (server_driver_closed d 'st0 'certificate_chain 'credential_identity);
}

fn close_live_without_transport
  (d:server_driver)
  requires server_driver_live d 'st0 'certificate_chain 'credential_identity
  ensures server_driver_closed d 'st0 'certificate_chain 'credential_identity
{
  unfold (server_driver_live d 'st0 'certificate_chain 'credential_identity);
  fold (server_driver_closed d 'st0 'certificate_chain 'credential_identity);
}
