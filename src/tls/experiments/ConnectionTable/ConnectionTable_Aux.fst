module ConnectionTable_Aux

module AE = Crypto.AEAD
module B = LowStar.Buffer

let connection_id = UInt8.t

let configuration = UInt32.t

let alg = Spec.AEAD.AES128_GCM

let cookie = c:AE.cipher_p alg
  {B.length c == 64 + AE.iv_length + Spec.AEAD.tag_length alg}

let cookie_rgn = Mem.tls_define_region
let table_rgn  = Mem.tls_tables_region
let other_rgn  = Mem.tls_psk_region

let random = Seq.lseq UInt8.t 32

let id_of_random (r:random) : connection_id =
  Seq.index r 0

noeq
type client_hello =
  | CH1: random -> client_hello
  | CH2: random -> ck:cookie{B.frameOf ck == other_rgn} -> client_hello

let ch_random = function
  | CH1 r -> r
  | CH2 r _ -> r
  
let has_cookie = CH2?

let get_cookie (ch:client_hello{has_cookie ch}) =
  let CH2 _ cookie = ch in
  cookie

let ch_of_cookie (ch:client_hello{has_cookie ch}) =
  let CH2 random _ = ch in
  CH1 random

val ch_compatible: ch:client_hello -> cfg:configuration -> bool
let ch_compatible ch cfg = false

let rgn = table_rgn
