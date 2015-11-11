module CoreCrypto.HMac
(* -------------------------------------------------------------------- *)
open Platform.Bytes

type engine
type key = bytes

assume val name   : engine -> string
assume val mac    : engine -> bytes -> bytes

assume val md5engine    : key -> engine
assume val sha1engine   : key -> engine
assume val sha256engine : key -> engine
assume val sha384engine : key -> engine
assume val sha512engine : key -> engine

assume val md5    : key -> bytes -> bytes
assume val sha1   : key -> bytes -> bytes
assume val sha256 : key -> bytes -> bytes
assume val sha384 : key -> bytes -> bytes
assume val sha512 : key -> bytes -> bytes
