module FStar.Test

open FStar.HyperStack.ST
open FStar.HyperStack.IO

(* Force enough monomorphizations to appear in FStar.h so that hand-written headers have the right
 * definitions in scope. *)
let dummy (): St (
  // This one needed by krembytes.h
  option string *
  // These two needed by transport.h
  FStar.Error.optResult string unit *
  FStar.Tcp.recv_result 0
) =
  Some "",
  FStar.Error.Correct (),
  FStar.Tcp.RecvWouldBlock
