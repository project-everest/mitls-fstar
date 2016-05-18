module StatefulPlain
open Platform.Bytes

open TLSConstants
open TLSInfo
open Range

(* This interface hides TLS-specific details of the record layer; 
   it does *not* includes the corresponding function *)

val ad_Length : id -> Tot (l: nat { l <= 3 })
//val makeAD: i:id -> ct:ContentType -> Tot (lbytes (ad_Length i))

type adata  (i:id) = lbytes (ad_Length i) 

val parseAD: i:id -> ad:adata i -> Tot ContentType // a bit too concrete

type plain (i:id) (ad:adata i) (r:range) 

val ghost_repr: #i:id -> #ad:adata i -> #rg:range -> plain i ad rg -> GTot (rbytes rg)

val repr:  i:id{ ~(safeId i)} -> ad:adata i -> rg:range -> p: plain i ad rg -> Tot (b:rbytes rg { b = ghost_repr p })

type wf_ad_rg (i:id) (ad:adata i) (rg:range) = 
  Wider Range.fragment_range rg  /\ 
  (parseAD i ad = Change_cipher_spec ==> rg = zero)


val mk_plain: i:id{ ~(authId i)} -> ad:adata i -> rg:range { wf_ad_rg i ad rg } -> b:rbytes rg -> Tot (p:plain i ad rg {ghost_repr p = b})

type cipher (i:id) = b:bytes { valid_clen i (length b) }
