module StAE
open TLSConstants
open TLSInfo

let is_stream_ae i = pv_of_id i = TLS_1p3
let is_stateful_lhae i = pv_of_id i <> TLS_1p3 /\ is_AEAD i.aeAlg 

type state (i:id) (rw:rw) = 
  | Stream: u:unit{is_stream_ae i} -> StreamAE.state i rw -> state i rw
  | StLHAE: u:unit{is_stateful_lhae i} -> StatefulLHAE.state i rw -> state i rw

type reader i = state i Reader
type writer i = state i Writer

let stream_ae (#i:id{is_stream_ae i}) (#rw:rw) (s:state i rw) 
  : Tot (StreamAE.state i rw)
  = let Stream _ s = s in s

let st_lhae (#i:id{is_stateful_lhae i}) (#rw:rw) (s:state i rw) 
  : Tot (StatefulLHAE.state i rw)
  = let StLHAE _ s = s in s

open FStar.HyperHeap
type n_rid = r:rid{r <> root}

let region (#i:id) (#rw:rw) (s:state i rw) 
  : Tot n_rid
  = match s with 
    | Stream _ s -> StreamAE.State.region s
    | StLHAE _ s -> StatefulLHAE.region s

let peer_region (#i:id) (#rw:rw) (s:state i rw{is_stateful_lhae i \/ rw=Reader})
  : Tot n_rid
  = match s with 
    | Stream _ s -> StreamAE.State.log_region s
    | StLHAE _ s -> StatefulLHAE.peer_region s
