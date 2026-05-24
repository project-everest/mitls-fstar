module TLS13.Handshake.ByteDriver

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module B = TLS13.Bytes
module Cast = FStar.Int.Cast
module E = TLS13.Handshake.ByteDriver.External
module IO = TLS13.IO
module RF = TLS13.Record.Framing
module SZ = FStar.SizeT
module U16 = FStar.UInt16
module U8 = FStar.UInt8

let max_encrypted_records_per_message : U8.t = 8uy
let encrypted_handshake_fragment_capacity : SZ.t = 20000sz

fn rec read_raw_exact
  (ctx: E.context)
  (ch: IO.channel)
  (buf: array U8.t)
  (total_len: SZ.t)
  (offset: SZ.t)
  (remaining: SZ.t)
  requires E.is_context ctx 'p **
           IO.is_channel ch **
           pts_to buf 'old **
           pure (B.length 'old == SZ.v total_len /\
                 SZ.v offset + SZ.v remaining == SZ.v total_len)
  returns ok: bool
  ensures exists* bytes.
          E.is_context ctx 'p **
          IO.is_channel ch **
          pts_to buf bytes **
          pure (B.length bytes == SZ.v total_len)
  decreases (SZ.v remaining)
{
  if (remaining = 0sz) {
    true
  } else {
    assert (pure (SZ.v remaining > 0));
    let n = E.read_raw ctx ch buf total_len offset remaining;
    if (n = 0sz) {
      false
    } else {
      with bytes. assert (pts_to buf bytes);
      let offset' = SZ.(offset +^ n);
      let remaining' = SZ.(remaining -^ n);
      assert (pure (SZ.v remaining' < SZ.v remaining));
      assert (pure (SZ.v offset' + SZ.v remaining' == SZ.v total_len));
      read_raw_exact ctx ch buf total_len offset' remaining'
    }
  }
}

fn read_next_encrypted_handshake_record (ctx: E.context) (ch: IO.channel)
  requires E.is_context ctx 'p ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx 'p ** IO.is_channel ch
{
  let mut header = [| 0uy; 5sz |];
  let header_ok = read_raw_exact ctx ch header 5sz 0sz 5sz;
  if header_ok {
    let mut content_type_out = [| 0uy; 1sz |];
    let mut fragment_len_out = [| 0uy; 2sz |];
    let header_parse_ok =
      RF.parse_record_header header 5sz content_type_out 1sz fragment_len_out 2sz;
    if header_parse_ok {
      let content_type = content_type_out.(0sz);
      let frag_hi = fragment_len_out.(0sz);
      let frag_lo = fragment_len_out.(1sz);
      let frag_hi16 = Cast.uint8_to_uint16 frag_hi;
      let frag_lo16 = Cast.uint8_to_uint16 frag_lo;
      let frag16 = U16.logor (U16.shift_left frag_hi16 8ul) frag_lo16;
      let fragment_len = SZ.uint16_to_sizet frag16;
      if (content_type = 20uy) {
        if SZ.(fragment_len =^ 1sz) {
          let mut ccs = [| 0uy; 1sz |];
          let ccs_ok = read_raw_exact ctx ch ccs 1sz 0sz 1sz;
          if ccs_ok {
            let b = ccs.(0sz);
            b = 1uy
          } else {
            false
          }
        } else {
          false
        }
      } else if ((content_type = 23uy) &&
                 SZ.(16sz <^ fragment_len) &&
                 SZ.(fragment_len <=^ encrypted_handshake_fragment_capacity)) {
        let mut cipher = [| 0uy; fragment_len |];
        let fragment_ok = read_raw_exact ctx ch cipher fragment_len 0sz fragment_len;
        if fragment_ok {
          E.process_encrypted_handshake_record ctx header 5sz cipher fragment_len
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

fn rec ensure_pending_handshake_message_with_fuel
  (ctx: E.context)
  (ch: IO.channel)
  (fuel: U8.t)
  requires E.is_context ctx 'p ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx 'p ** IO.is_channel ch
  decreases (U8.v fuel)
{
  let pending = E.pending_handshake_message_complete ctx;
  if pending {
    true
  } else if (fuel = 0uy) {
    false
  } else {
    let ok = read_next_encrypted_handshake_record ctx ch;
    if ok {
      let fuel' = U8.(fuel -^ 1uy);
      ensure_pending_handshake_message_with_fuel ctx ch fuel'
    } else {
      false
    }
  }
}

fn ensure_pending_handshake_message (ctx: E.context) (ch: IO.channel)
  requires E.is_context ctx 'p ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx 'p ** IO.is_channel ch
{
  ensure_pending_handshake_message_with_fuel ctx ch max_encrypted_records_per_message
}

fn recv_encrypted_handshake (ctx: E.context) (ch: IO.channel)
  requires E.is_context ctx 'p ** IO.is_channel ch
  returns ok: bool
  ensures exists* p'. E.is_context ctx p' ** IO.is_channel ch **
          pure (ok ==> p' == E.Complete)
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
