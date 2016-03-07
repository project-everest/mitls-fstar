module KeySchedule
(*the top level key schedule module, it should not expose secrets to Handshake *)

type ff_all_groups =
  | FF_2048
  | FF_4096
  | FF_8192
  | FF_arbitrary of CoreCrypto.dh_params
  
type dh_group = 
  | FFDH of ff_all_groups
  | ECDH of ECGroup.ec_all_curve

type dh_key = 
  | FFKey of CoreCrypto.dh_key
  | ECKey of CoreCrypto.ec_key

type dh_secret = bytes // -> abstract
type ms = bytes // -> abstract

assume val dh_keygen: g:dh_group -> Tot (x:dh_key)
(*x contains public key share gx, 
  in TLS 1.2 in fact used to generate y
 *)

assume val dh_shared_secret1: y:dh_key -> gx:dh_key -> Tot (gxy:dh_secret)

assume val dh_shared_secret2: gy:dh_key -> Tot (x:dh_key * gxy:dh_secret)
(*x contains public key share gx*)



(* TLS <= 1.2 *)
assume val derive_keys: gxy:dh_secret -> cr:random -> sr:random -> log:bytes -> 
	                rd:rid -> wr:rid -> i:id -> ST ((both i) * ms)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))


val dh_init_12S: #region:rid g:dh_group -> ST (gx:dh_key)

let dh_init_12S r g =
  let x = dh_keygen g
  let xref = ralloc r 0 in
  let xref := x
  x.public //likely have to output an additional state containing the x reference

  
assume val derive_12C: #region:rid -> gx:dh_key -> ... -> ST(gy:dh_key * (both i) * ms)

let derive1 r gx cr sr log rd wr i = 
  let (y, gxy) = dh_shared_secret2 gx 
  y.public, derive_keys gxy cr sr log rd wr i


assume val derive_12S: #region:rid -> gy:dh_key -> ... -> ST ((both i) * ms)

let derive_12S r gy cr sr log rd wr i =
  let xref = lookup r //likely pass a separate state
  derive_keys (dh_shared_secret1 !xref) cr sr log rd wr i

(* TLS 1.3 *)
assume val derive_handshake_keys: gxy:dh_secret -> log: bytes ->
				  rd:rid -> wr:rid -> i:id -> ST ((both i) * ms)
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

assume val derive_finished_keys: gxs:dh_secret -> gxy:dh_secret -> log: bytes -> Tot (ts:ms * cf:ms * sf:ms)

assume val derive_traffic_keys: ts:ms -> log: bytes -> 
				rd:rid -> wr:rid -> i:id -> ST (both i)     
  (requires (fun h -> True))
  (ensures (fun h0 i h1 -> True))

//
val dh_init_13S: #region:rid g:dh_group -> ST (gs:dh_key) //s
val dh_init_13C: #region:rid g:dh_group -> ST (gx:dh_key) //x

assume val derive_12S_1: #region:rid -> gx:dh_key -> ... -> ST(gy:dh_key * (both i)) //handshake
assume val derive_12S_2: #region:rid -> ... -> ST(ts:ms * cf:ms * sf:ms) //finished
assume val derive_12S_3: #region:rid -> ... -> ST(both i) //traffic

assume val derive_12C_1: #region:rid -> gy:dh_key -> ... -> ST(both i) //handshake
assume val derive_12C_2: #region:rid -> gs:dh_key -> ... -> ST(ts:ms * cf:ms * sf:ms) //finished
assume val derive_12C_3: #region:rid -> ... -> ST(both i) //traffic
