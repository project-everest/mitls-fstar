module StAE // See StAE.fsti

open FStar.HyperHeap
open FStar.Monotonic.RRef

open Platform.Bytes

open TLSConstants
open TLSInfo
open Content

let is_stream_ae i = pv_of_id i = TLS_1p3
let is_stateful_lhae i = pv_of_id i <> TLS_1p3 /\ is_AEAD i.aeAlg /\ ~ (authId i)

// NB as a temporary hack, we currently disable AuthId for TLS 1.2.
// so that we can experiment with TLS and StreamAE

type state' (i:id) (rw:rw) = 
  | Stream: u:unit{is_stream_ae i}         -> StreamAE.state i rw -> state' i rw
  | StLHAE: u:unit{is_stateful_lhae i} -> StatefulLHAE.state i rw -> state' i rw

let state = state'

(*
let stream_ae (#i:id{is_stream_ae i}) (#rw:rw) (s:state i rw) 
  : Tot (StreamAE.state i rw)
  = let Stream _ s = s in s

let st_lhae (#i:id{is_stateful_lhae i}) (#rw:rw) (s:state i rw) 
  : Tot (StatefulLHAE.state i rw)
  = let StLHAE _ s = s in s
*)

let region (#i:id) (#rw:rw) (s:state i rw): Tot rgn
  = match s with 
    | Stream _ s -> StreamAE.State.region s
    | StLHAE _ s -> StatefulLHAE.region s

let log_region (#i:id) (#rw:rw) (s:state i rw): Tot rgn
  = match s with 
    | Stream _ s -> StreamAE.State.log_region s
    | StLHAE _ s -> if rw = Writer then StatefulLHAE.region s else StatefulLHAE.peer_region s //FIXME

let writable_seqn (#i:id) (#rw:rw) (s:state i rw) h = 
    match s with 
    | Stream _ s -> is_seqn (m_sel h (StreamAE.ctr (StreamAE.State.counter s)) + 1)
    | StLHAE _ s -> is_seqn (sel h (StatefulLHAE.State.seqn s) + 1) 

// TODO extend library? We need a full spec
assume val seq_mapT: ('a -> Tot 'b) -> seq 'a -> Tot (seq 'b)

let logT #i #rw (s:state i rw) h = 
  match s with 
  | Stream _ s -> let written = m_sel h (StreamAE.State.log s) in 
                 let projet (StreamAE.Entry #i l c p) : fragment i = p in
                 seq_mapT #(StreamAE.entry i) #(fragment i) project written 

let seqnT #i #rw (s:state i rw) h = 
  match s with 
  | Stream _ s       -> m_sel (StreamAE.State.counter s) h
  | StLHAE _ s -> sel (StatefulLHAE.State.seqn) h

let gen parent i = 
  assert(is_stream_ae i); 
  Stream(StreamAE.gen parent i)

let coerce parent i kiv = 
  assert(is_stream_ae i); 
  let kv, iv = split kiv (CoreCrypto.aeadKeySize (StreamAE.alg i)) in
  Stream(StreamAE.coerce parent i kv iv)

let leak #i #role s = 
  assert(is_stream_ae i); 
  StreamAE.leak s 

let genReader parent w i = 
  assert(is_stream_ae i); 
  Stream(StreamAE.genReader parent i w)

let encrypt #i e f = 
  match e with
  | Stream _ s -> StreamAE.encrypt s f

let decrypt #i d c = 
  match d with
  | Stream _ s -> StreamAE.decrypt s c

(*

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

*)
