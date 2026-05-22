module TLS13.Handshake.Driver

#lang-pulse

open Pulse.Lib.Pervasives

module HS = TLS13.Handshake
module IO = TLS13.IO
module S = TLS13.StateMachine
module ST = TLS13.State

fn run_client_handshake (ctx: HS.handshake_context) (ch: IO.channel)
  requires HS.is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.Start)
  returns ok: bool
  ensures exists* s'.
          HS.is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure ((ok ==> s'.S.phase == S.ApplicationData) /\
                (not ok ==> s'.S.phase == S.Failed))
{
  HS.send_client_hello ctx ch;
  let ok_server_hello = HS.recv_server_hello ctx ch;
  if ok_server_hello {
    let ok_encrypted_extensions = HS.recv_encrypted_extensions ctx ch;
    if ok_encrypted_extensions {
      let ok_certificate = HS.recv_certificate ctx ch;
      if ok_certificate {
        let ok_valid_certificate = HS.validate_certificate ctx;
        if ok_valid_certificate {
          let ok_certificate_verify = HS.recv_certificate_verify ctx ch;
          if ok_certificate_verify {
            let ok_server_finished = HS.recv_server_finished ctx ch;
            if ok_server_finished {
              HS.send_client_finished ctx ch
            } else {
              false
            }
          } else {
            false
          }
        } else {
          false
        }
      } else {
        false
      }
    } else {
      false
    }
  } else {
    false
  }
}
