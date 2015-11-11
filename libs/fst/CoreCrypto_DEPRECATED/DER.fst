module CoreCrypto.DER
(* -------------------------------------------------------------------- *)
open Platform.Bytes

type dervalue =
    | Bool       of bool
    | Bytes      of bytes
    | Utf8String of string
    | Sequence   of list dervalue 

assume val encode : dervalue -> bytes
assume val decode : bytes -> option dervalue
