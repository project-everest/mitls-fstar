(* This file is transitional. It gathers all manual calls to the
   LowParse combinators (beyond LowParse.*.Base) so that they can be
   extracted with cross-module inlining enabled for this file but not
   its clients, until cross-module inlining issues UNrelated to
   parsing are fixed.

   As stated in Makefile.common, for now, only Parsers.* and Format.*
   should explicitly call non-base LowParse combinators. Thus, this
   file should *only* depend on Parsers.* and Format.*
   
*)

module Parsers.Misc

module B = FStar.Bytes
module L = FStar.List.Tot
module LP = LowParse.SLow
module PCS = Parsers.CipherSuite

val cipherSuitesVLBytes
  (l: list PCS.cipherSuite { L.length l < 256 } )
: Tot (b: B.bytes { B.length b <= 65536 } )

val parseVLCipherSuites (b: B.bytes) : Tot (option ((l: list PCS.cipherSuite { 1 <= L.length l /\ L.length l <= 255 } ) * B.bytes))
