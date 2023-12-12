module DHDBManager

open CoreCrypto
open Platform.Byte
open DHDB

assume val defaultDHPrimeConfidence : nat
assume val load_default_params : (string -> dhdb -> (nat * nat) -> (dhdb * dh_params))
