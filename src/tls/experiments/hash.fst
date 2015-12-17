(*--build-config
    options:--admit_fsi Set --admit_fsi Seq --admit_fsi CoreSig --admit_fsi CoreKeys --verify_module Hash;
    variables:LIB=../../../../FStar/lib
              PLATFORM=../../../libs/fst/Platform
              CORECRYPTO=../../../libs/fs/CoreCrypto;
    other-files:$LIB/string.fst $LIB/classical.fst $LIB/list.fst $LIB/ext.fst
                $LIB/FStar.Set.fsi $LIB/FStar.Heap.fst $LIB/FStar.ST.fst $LIB/mref.fst
                $LIB/seq.fsi $LIB/seqproperties.fst $PLATFORM/Bytes.fst
                $CORECRYPTO/CoreKeys.fsi $CORECRYPTO/CoreSig.fsi
--*)
(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

(* an agile library for asymmetric keys covering their usage in PKI
   for signing (with various hashes), encrypting, and DH key
   exchanging, with dynamic key compromise.  *)

module Hash

open Bytes

(* as defined in TLSConstants.hashAlg, but needs to be relocated *)

type alg =
  | NULL
  | MD5SHA1
  | MD5
  | SHA
  | SHA256
  | SHA384

assume val compute: alg -> bytes -> Tot bytes
