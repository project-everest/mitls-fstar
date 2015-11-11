module CoreECDH

open Bytes
open CoreKeys
open Org.BouncyCastle.Math
open Org.BouncyCastle.Crypto
open Org.BouncyCastle.Crypto.Digests
open Org.BouncyCastle.Crypto.Generators
open Org.BouncyCastle.Crypto.Signers
open Org.BouncyCastle.Crypto.Parameters
open Org.BouncyCastle.Math.EC
open Org.BouncyCastle.Security

val gen_key : ecdhparams -> ecdhskey * ecdhpkey
val agreement : ecdhparams -> ecdhskey -> ecdhpkey -> bytes
val serialize : ecdhpkey -> bytes
val is_on_curve : ecdhparams -> ecpoint -> bool