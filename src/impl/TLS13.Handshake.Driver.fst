module TLS13.Handshake.Driver

#lang-pulse

open Pulse.Lib.Pervasives

module HS = TLS13.Handshake
module IO = TLS13.IO
module RTC = FStar.ReflexiveTransitiveClosure
module S = TLS13.StateMachine
module ST = TLS13.State

let lemma_evolves_trans (s0:S.conn_state) (s1:S.conn_state) (s2:S.conn_state)
  : Lemma
      (requires S.conn_evolves s0 s1 /\ S.conn_evolves s1 s2)
      (ensures S.conn_evolves s0 s2)
  =
  assert (RTC.transitive S.conn_evolves)

fn run_client_handshake (ctx: HS.handshake_context) (ch: IO.channel)
  requires HS.is_handshake_context ctx 'st 's **
           IO.is_channel ch **
           pure ('s.S.phase == S.Start)
  returns ok: bool
  ensures exists* s'.
          HS.is_handshake_context ctx 'st s' **
          IO.is_channel ch **
          pure (S.conn_evolves 's s' /\
               (ok ==> s'.S.phase == S.ApplicationData /\ Some? s'.S.peer) /\
               (not ok ==> s'.S.phase == S.Failed))
{
  let ok_client_hello = HS.send_client_hello ctx ch;
  with s1. assert (HS.is_handshake_context ctx 'st s1);
  if ok_client_hello {
    let ok_server_hello = HS.recv_server_hello ctx ch;
    with s2. assert (HS.is_handshake_context ctx 'st s2);
    lemma_evolves_trans 's s1 s2;
    if ok_server_hello {
      let ok_encrypted_extensions = HS.recv_encrypted_extensions ctx ch;
      with s3. assert (HS.is_handshake_context ctx 'st s3);
      lemma_evolves_trans 's s2 s3;
      if ok_encrypted_extensions {
        let ok_certificate = HS.recv_certificate ctx ch;
        with s4. assert (HS.is_handshake_context ctx 'st s4);
        lemma_evolves_trans 's s3 s4;
        if ok_certificate {
          let ok_valid_certificate = HS.validate_certificate ctx;
          with s5. assert (HS.is_handshake_context ctx 'st s5);
          lemma_evolves_trans 's s4 s5;
          if ok_valid_certificate {
           let ok_certificate_verify = HS.recv_certificate_verify ctx ch;
           with s6. assert (HS.is_handshake_context ctx 'st s6);
           lemma_evolves_trans 's s5 s6;
           if ok_certificate_verify {
             let ok_server_finished = HS.recv_server_finished ctx ch;
             with s7. assert (HS.is_handshake_context ctx 'st s7);
             lemma_evolves_trans 's s6 s7;
             if ok_server_finished {
               let ok_client_finished = HS.send_client_finished ctx ch;
               with s8. assert (HS.is_handshake_context ctx 'st s8);
               lemma_evolves_trans 's s7 s8;
               ok_client_finished
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
