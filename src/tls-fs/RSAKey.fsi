(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module RSAKey

type sk
type pk = { pk : CoreACiphers.pk }

type modulus  = Bytes.bytes
type exponent = Bytes.bytes

#if ideal
val honest: pk -> bool
val strong: TLSConstants.ProtocolVersion -> bool
#endif

val gen: unit -> pk * sk
val coerce: pk -> CoreACiphers.sk -> sk

val repr_of_rsapkey : pk -> CoreACiphers.pk
val repr_of_rsaskey : sk -> CoreACiphers.sk

val create_rsapkey : modulus * exponent -> pk
//val create_rsaskey : modulus * exponent -> sk
