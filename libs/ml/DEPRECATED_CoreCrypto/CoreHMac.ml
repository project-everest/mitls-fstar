(*-------------------------------------------------------------------- *)
open Bytes

type engine = HMac of CoreCrypto.hmac
type key    = bytes

let name (HMac engine) =
    engine.hm_name

let mac (HMac engine) (b : bytes) =
    abytes (engine.hm_process(cbytes b))

let md5engine    (k : key) = HMac (CoreCrypto.hmac "MD5"    (cbytes k))
let sha1engine   (k : key) = HMac (CoreCrypto.hmac "SHA1"   (cbytes k))
let sha256engine (k : key) = HMac (CoreCrypto.hmac "SHA256" (cbytes k))
let sha384engine (k : key) = HMac (CoreCrypto.hmac "SHA384" (cbytes k))
let sha512engine (k : key) = HMac (CoreCrypto.hmac "SHA512" (cbytes k))

let dohmac (factory : key -> engine) (k : key) (data : bytes) =
    mac (factory k) data

let md5    (k : key) (data : bytes) = dohmac md5engine    k data
let sha1   (k : key) (data : bytes) = dohmac sha1engine   k data
let sha256 (k : key) (data : bytes) = dohmac sha256engine k data
let sha384 (k : key) (data : bytes) = dohmac sha384engine k data
let sha512 (k : key) (data : bytes) = dohmac sha512engine k data
