module TLS13.Handshake.ByteDriver

#lang-pulse

open Pulse.Lib.Pervasives

module E = TLS13.Handshake.ByteDriver.External
module IO = TLS13.IO

fn ensure_pending_handshake_message (ctx: E.context) (ch: IO.channel)
  requires E.is_context ctx ** IO.is_channel ch
  returns ok: bool
  ensures E.is_context ctx ** IO.is_channel ch
{
  let pending0 = E.pending_handshake_message_complete ctx;
  if pending0 {
    true
  } else {
    let ok1 = E.read_next_encrypted_handshake_record ctx ch;
    if ok1 {
      let pending1 = E.pending_handshake_message_complete ctx;
      if pending1 { true } else {
        let ok2 = E.read_next_encrypted_handshake_record ctx ch;
        if ok2 {
          let pending2 = E.pending_handshake_message_complete ctx;
          if pending2 { true } else {
            let ok3 = E.read_next_encrypted_handshake_record ctx ch;
            if ok3 {
              let pending3 = E.pending_handshake_message_complete ctx;
              if pending3 { true } else {
                let ok4 = E.read_next_encrypted_handshake_record ctx ch;
                if ok4 {
                  let pending4 = E.pending_handshake_message_complete ctx;
                  if pending4 { true } else {
                    let ok5 = E.read_next_encrypted_handshake_record ctx ch;
                    if ok5 {
                      let pending5 = E.pending_handshake_message_complete ctx;
                      if pending5 { true } else {
                        let ok6 = E.read_next_encrypted_handshake_record ctx ch;
                        if ok6 {
                          let pending6 = E.pending_handshake_message_complete ctx;
                          if pending6 { true } else {
                            let ok7 = E.read_next_encrypted_handshake_record ctx ch;
                            if ok7 {
                              let pending7 = E.pending_handshake_message_complete ctx;
                              if pending7 { true } else {
                                let ok8 = E.read_next_encrypted_handshake_record ctx ch;
                                if ok8 {
                                  E.pending_handshake_message_complete ctx
                                } else {
                                  false
                                }
                              }
                            } else {
                              false
                            }
                          }
                        } else {
                          false
                        }
                      }
                    } else {
                      false
                    }
                  }
                } else {
                  false
                }
              }
            } else {
              false
            }
          }
        } else {
          false
        }
      }
    } else {
      false
    }
  }
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
