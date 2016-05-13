module StAE

(* Multiplexing between StatefulLHAE and StreaAE for the record layer *) 

open FStar.Monotonic.RRef

open Platform.Bytes

open TLSConstants
open TLSInfo

let is_stream_ae i = pv_of_id i = TLS_1p3
let is_stateful_lhae i = pv_of_id i <> TLS_1p3 /\ is_AEAD i.aeAlg /\ ~ (authId i)

// as a temporary hack, we currently disable AuthId for TLS 1.2.
// so that we can experiment with TLS and StreamAE


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

let region (#i:id) (#rw:rw) (s:state i rw): Tot n_rid
  = match s with 
    | Stream _ s -> StreamAE.State.region s
    | StLHAE _ s -> StatefulLHAE.region s

let log_region (#i:id) (#rw:rw) (s:state i rw): Tot n_rid
  = match s with 
    | Stream _ s -> StreamAE.State.log_region s
    | StLHAE _ s -> StatefulLHAE.peer_region s //FIXME

let writable_seqn (#i:id) (#rw:rw) (s:state i rw) h = 
    match s with 
    | Stream _ s -> is_seqn (m_sel h (StreamAE.ctr (StreamAE.State.counter s)) + 1)
    | StLHAE _ s -> is_seqn (sel h (StatefulLHAE.State.seqn s) + 1) 

let log (#i:id { is_stream_ae i }) (#rw:rw) (s:state i rw) : Tot (StreamAE.log_ref (log_region s) i)
  = match s with 
    | Stream _ s -> StreamAE.State.log s

let seqn (#i:id { is_stream_ae i }) (#rw:rw) (s:state i rw): Tot (StreamAE.seqn_ref (region s) i (log s))
  = match s with 
    | Stream _ s -> StreamAE.State.counter s

(*

*)
type cipher (i:id) = b:bytes {Range.valid_clen i (length b)}

let cipher_noId b : cipher noId = b 

type entry i = 
  | EStream: u:unit{is_stream_ae i}     -> StreamAE.entry i  -> entry i 
  | EStLHAE: u:unit{is_stateful_lhae i} -> StatefulLHAE.entry i  -> entry i 

val fragment_entry: #i:id -> e: entry i -> Tot (Content.fragment i)

let fragment_entry #i = function 
  | EStream _ (StreamAE.Entry _ _ f) -> f 
  | EStLHAE _ (StatefulLHAE.Entry _ _ f) -> f 

let writer_modifies #i h0 wr h1 = 
  match wr with 
  | Stream _ wr -> True 
  | StLHAE _ wr -> (
      HyperHeap.modifies (Set.singleton (StatefulLHAE.region wr)) h0 h1 /\
      Heap.modifies (!{ as_ref (StatefulLHAE.log wr), as_ref (StatefulLHAE.seqn wr)}) (Map.sel h0 (StatefulLHAE.region wr)) (Map.sel h1 (StatefulLHAE.region wr)) )

