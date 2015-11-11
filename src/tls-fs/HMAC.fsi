(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module HMAC

open Bytes
open TLSConstants

type key = bytes
type data = bytes
type mac = bytes

val tls_mac:       macAlg -> key -> data -> mac
val tls_macVerify: macAlg -> key -> data -> mac -> bool

(* SSL/TLS Constants *)

val ssl_pad1_md5: bytes
val ssl_pad2_md5: bytes
val ssl_pad1_sha1: bytes
val ssl_pad2_sha1: bytes
