(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module CoreHash
open Bytes

open CryptoProvider

(* ---------------------------------------------------------------------- *)
type engine = HashEngine of MessageDigest

let name (HashEngine engine) =
    engine.Name

let digest (HashEngine engine) (b : bytes) =
    abytes (engine.Digest (cbytes b))

(* ---------------------------------------------------------------------- *)
let md5engine    () = HashEngine (CoreCrypto.Digest "MD5"   )
let sha1engine   () = HashEngine (CoreCrypto.Digest "SHA1"  )
let sha256engine () = HashEngine (CoreCrypto.Digest "SHA256")
let sha384engine () = HashEngine (CoreCrypto.Digest "SHA384")
let sha512engine () = HashEngine (CoreCrypto.Digest "SHA512")

(* ---------------------------------------------------------------------- *)
let dohash (factory : unit -> engine) (x : bytes) =
    let engine = factory () in
        (digest engine x)

let md5    x = dohash md5engine    x
let sha1   x = dohash sha1engine   x
let sha256 x = dohash sha256engine x
let sha384 x = dohash sha384engine x
let sha512 x = dohash sha512engine x
