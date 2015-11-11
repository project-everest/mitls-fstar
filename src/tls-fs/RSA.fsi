(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module RSA

open TLSInfo
open Bytes
open TLSConstants

val encrypt: RSAKey.pk -> ProtocolVersion -> PMS.rsapms -> bytes 
val decrypt: RSAKey.sk -> SessionInfo -> ProtocolVersion -> bool -> bytes -> PMS.rsapms
