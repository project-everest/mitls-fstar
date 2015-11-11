module CoreCrypto.Hash
open Platform.Bytes

type engine

assume val name   : engine -> string
assume val digest : engine -> bytes -> bytes

assume val md5engine    : unit -> engine
assume val sha1engine   : unit -> engine
assume val sha256engine : unit -> engine
assume val sha384engine : unit -> engine
assume val sha512engine : unit -> engine

assume val md5    : bytes -> bytes
assume val sha1   : bytes -> bytes
assume val sha256 : bytes -> bytes
assume val sha384 : bytes -> bytes
assume val sha512 : bytes -> bytes
