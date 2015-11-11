open Bytes

type sk = RSASKey of CoreKeys.rsaskey
type pk = RSAPKey of CoreKeys.rsapkey

type plain = bytes
type ctxt  = bytes

val encrypt_pkcs1 : pk -> plain -> ctxt
val decrypt_pkcs1 : sk -> ctxt  -> plain option
