module Negotiation.Writers

// This module is for testing purposes only,
// currently it is not integrated with the rest of miTLS
// (it should be eventually)

open Mem
open TLSInfo
open TLSConstants
open HandshakeMessages

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module LP = LowParse.Low.Base
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

(* extraction test, do not run *)

val test_write_final_extensions
  (#rrelcfg #relcfg: _)
  (scfg: B.mbuffer LP.byte rrelcfg relcfg)
  (pcfg: U32.t)
  (edi: bool)
  (#rrel #rel: _)
  (sin: B.mbuffer LP.byte rrel rel)
  (pin_from pin_to: U32.t)
  (now: U32.t)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from: U32.t)
: HST.Stack U32.t
  (requires (fun _ -> False))
  (ensures (fun _ _ _ -> True))
