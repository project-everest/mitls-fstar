module CoreCrypto.ECDH

open Platform.Bytes
open CoreCrypto.Keys

val gen_key : ecdhparams -> ecdhskey * ecdhpkey
val agreement : ecdhparams -> ecdhskey -> ecdhpkey -> bytes
val serialize : ecdhpkey -> bytes
val is_on_curve : ecdhparams -> ecpoint -> bool
