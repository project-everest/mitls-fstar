module DHGroup

open FStar.HyperHeap
open Platform.Bytes
open Platform.Error
open CoreCrypto
open TLSError
open TLSConstants

type params = dhp:CoreCrypto.dh_params{length dhp.dh_p < 65536 && length dhp.dh_g < 65536}

type share = b:bytes{length b < 65536}

type key = k:CoreCrypto.dh_key{
  let dhp = k.dh_params in 
  length dhp.dh_p < 65536 && length dhp.dh_g < 65536 /\
  length k.dh_public < 65536}

type group =
  | Named    of ffdhe
  | Explicit of params

type secret = bytes

val ffdhe2048: params
let ffdhe2048 =
  let p = "ffffffffffffffffadf85458a2bb4a9aafdc5620273d3cf1d8b9c583ce2d3695a9e13641146433fbcc939dce249b3ef97d2fe363630c75d8f681b202aec4617ad3df1ed5d5fd65612433f51f5f066ed0856365553ded1af3b557135e7f57c935984f0c70e0e68b77e2a689daf3efe8721df158a136ade73530acca4f483a797abc0ab182b324fb61d108a94bb2c8e3fbb96adab760d7f4681d4f42a3de394df4ae56ede76372bb190b07a7c8ee0a6d709e02fce1cdf7e2ecc03404cd28342f619172fe9ce98583ff8e4f1232eef28183c3fe3b1b4c6fad733bb5fcbc2ec22005c58ef1837d1683b2c6f34a26c1b2effa886b423861285c97ffffffffffffffff" in
  let g = "02" in
  assume (length (bytes_of_hex p) < 65536);
  assume (length (bytes_of_hex g) < 65536);
  { 
    dh_p = bytes_of_hex p;      
    dh_g = bytes_of_hex g; 
    dh_q = None;
    safe_prime = true
  }

assume val ffdhe3072: params
assume val ffdhe4096: params
assume val ffdhe6144: params
assume val ffdhe8192: params

private val params_of_group: group -> Tot params
let params_of_group = function
  | Named FFDHE2048 -> ffdhe2048
  | Named FFDHE3072 -> ffdhe3072
  | Named FFDHE4096 -> ffdhe4096
  | Named FFDHE6144 -> ffdhe6144
  | Named FFDHE8192 -> ffdhe8192
  | Explicit params -> params

val keygen: group -> Tot key
let keygen g =
  let params = params_of_group g in
  dh_gen_key params

val dh_responder: key -> Tot (key * secret)
let dh_responder gx =
  let params = gx.dh_params in
  let y = dh_gen_key params in
  let shared = dh_agreement y gx.dh_public in
  y, shared

val dh_initiator: key -> key -> Tot secret
let dh_initiator x gy =
  dh_agreement x gy.dh_public

val serialize: params -> share -> Tot bytes
let serialize dhp dh_Y =
  lemma_repr_bytes_values (length (dhp.dh_p));
  lemma_repr_bytes_values (length (dhp.dh_g));
  lemma_repr_bytes_values (length dh_Y);
  let pb  = vlbytes 2 dhp.dh_p in 
  let gb  = vlbytes 2 dhp.dh_g in
  let pkb = vlbytes 2 dh_Y in
  pb @| gb @| pkb
