module CoreCrypto.ACiphers
(* -------------------------------------------------------------------- *)
open Platform.Bytes

type sk = | RSASKey: CoreCrypto.Keys.rsaskey -> sk
type pk = | RSAPKey: CoreCrypto.Keys.rsapkey -> pk

type plain = bytes
type ctxt  = bytes

assume val gen_key: unit -> sk * pk
assume val encrypt_pkcs1 : pk -> plain -> ctxt
assume val decrypt_pkcs1 : sk -> ctxt  -> option plain
