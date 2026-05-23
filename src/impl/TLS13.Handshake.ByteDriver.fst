module TLS13.Handshake.ByteDriver

#lang-pulse

open Pulse.Lib.Pervasives

module E = TLS13.Handshake.ByteDriver.External
module IO = TLS13.IO
module U8 = FStar.UInt8

let max_encrypted_records_per_message : U8.t = 8uy

fn rec ensure_pending_handshake_message_with_fuel
  (ctx: E.context)
  (ch: IO.channel)
  (fuel: U8.t)
  requires E.is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx ** IO.is_channel ch
  decreases (U8.v fuel)
{
  let pending = E.pending_handshake_message_complete ctx;
  if pending {
    true
  } else if (fuel = 0uy) {
    false
  } else {
    let ok = E.read_next_encrypted_handshake_record ctx ch;
    if ok {
      let fuel' = U8.(fuel -^ 1uy);
      ensure_pending_handshake_message_with_fuel ctx ch fuel'
    } else {
      false
    }
  }
}

fn ensure_pending_handshake_message (ctx: E.context) (ch: IO.channel)
  requires E.is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx ** IO.is_channel ch
{
  ensure_pending_handshake_message_with_fuel ctx ch max_encrypted_records_per_message
}

fn recv_encrypted_handshake (ctx: E.context) (ch: IO.channel)
  requires E.is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx ** IO.is_channel ch
{
  E.reset_encrypted_handshake ctx;

  let has_ee = ensure_pending_handshake_message ctx ch;
  if has_ee {
    let ee_type = E.pending_handshake_message_type ctx;
    if (ee_type = 0x08uy) {
      let ee_ok = E.accept_encrypted_extensions ctx;
      if ee_ok {
        let has_cert = ensure_pending_handshake_message ctx ch;
        if has_cert {
          let cert_type = E.pending_handshake_message_type ctx;
          if (cert_type = 0x0buy) {
            let cert_ok = E.accept_certificate ctx;
            if cert_ok {
              let has_cv = ensure_pending_handshake_message ctx ch;
              if has_cv {
                let cv_type = E.pending_handshake_message_type ctx;
                if (cv_type = 0x0fuy) {
                  let cv_ok = E.accept_certificate_verify ctx;
                  if cv_ok {
                    let has_finished = ensure_pending_handshake_message ctx ch;
                    if has_finished {
                      let finished_type = E.pending_handshake_message_type ctx;
                      if (finished_type = 0x14uy) {
                        let finished_ok = E.accept_finished ctx;
                        if finished_ok {
                          E.encrypted_handshake_complete ctx
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
