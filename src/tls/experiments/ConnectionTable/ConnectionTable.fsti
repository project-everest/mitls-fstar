module ConnectionTable
include ConnectionTable_Aux

open FStar.Monotonic.DependentMap

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Ghost

module T = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap
module B = LowStar.Buffer
module AEAD = Crypto.AEAD
module AE = Crypto.AE
module EE = EverCrypt.Error

(*
  The connection table and ids are model artifacts that do not exist
  in concrete code. So functions that modify the connection state 
  do it through a connection reference rather than looking up in the table.

- API functions take (id:maybe_id) (c:connection_ref id) as arguments.
  There is no real dependency on id in connection_ref and maybe_id is
  just unit and discarded in concrete code.
  Note that we cannot store the id in the connection reference to avoid
  having to pass it as argument, because we need to use it in specifications.
  We could still store it and keep a witness that the id is the same
  as the index, but this is of little use.

- In miTLS, we'll use

  type connection_id = random // Unique across clients and server connections

  Always sampled fresh upon connection creation

  type connection = TLS.Handshake.Machine.tt

  and the table will map r:random -> connection

  TLS.Handshake.Machine defines

  type state =
  | Client:
    client_rgn: rgn ->
    client_cfg: client_config ->
    client_state: client_mref client_rgn client_cfg -> state

  | Server:
    server_rgn: rgn ->
    server_cfg: server_config ->
    server_state: server_mref server_rgn server_cfg -> state
 
  let tt =
    | Connection: 
      nonce: if model then TLSInfo.random else unit -> 
      state: t {token_p st (fun h -> nonce_of st h == nonce)}
*)

val cookie_key : k:option (AE.state alg cookie_phi){
  Some? k ==>
    (let k = Some?.v k in 
     (model ==> AE.safe k) /\
     B.loc_includes (B.loc_region_only true cookie_rgn) (AE.footprint k))} 

inline_for_extraction
val create:
    id:maybe_id
  -> cfg:configuration
  -> ST (connection_ref id)
  (requires fun h0 ->
    if model then
      let t:_connection_table = table in
      inv t h0 /\ 
      ~(T.defined t id h0)
    else True)
  (ensures  fun h0 c h1 ->
    (if model then 
      let t:_connection_table = table in
      inv t h1 /\
      B.modifies (B.loc_mreference t) h0 h1 /\
      T.defined t id h1 /\
      sel h1 t == T.upd (sel h0 t) id c
     else 
       B.modifies B.loc_none h0 h1) /\
    frameOf c `extends` rgn /\
    fresh_region (frameOf c) h0 h1 /\
    ~(h0 `contains` c) /\
    h1 `contains` c /\
    sel h1 c == Init cfg)

inline_for_extraction
val free_connection:
    id:maybe_id
  -> c:connection_ref id
  -> ST unit
  (requires fun h0 ->
    c `is_live_for_rw_in` h0 /\
    (if model then
      let t:_connection_table = table in
      inv t h0 /\ 
      T.defined t id h0 /\
      T.value_of t id h0 == c
    else True))
  (ensures  fun h0 _ h1 -> 
    (if model then 
      let t:_connection_table = table in
      inv t h1 /\
      T.defined t id h1 /\
      T.value_of t id h0 == c
     else True) /\
    h0 `contains` c /\
    h1 == HyperStack.free c h0)

val receive_client_hello1:
    id:maybe_id
  -> c:connection_ref id
  -> ch:client_hello{~(has_cookie ch)}
  -> ST unit
  (requires fun h0 ->
    (if model then
       let t:_connection_table = table in
       inv t h0 /\
       T.defined t id h0 /\
       T.value_of t id h0 == c
    else True) /\
    h0 `contains` c /\
    Init? (sel h0 c))
  (ensures  fun h0 _ h1 ->
    B.modifies (B.loc_mreference c) h0 h1 /\
    (if model then
       let t:_connection_table = table in
       inv t h1 /\
       T.defined t id h1 /\
       T.value_of t id h1 == c
     else True) /\
     (if ch_compatible ch (Init?.cfg (sel h0 c)) then
       sel h1 c == Sent_ServerHello ch (if model then 0uy else ())
     else
       sel h1 c == Sent_HRR ch))

val random_of_buffer: b:B.buffer UInt8.t -> ST random
  (requires fun h -> B.live h b /\ B.length b >= 32)
  (ensures  fun h0 r h1 -> h0 == h1 /\ r == Seq.slice (B.as_seq h0 b) 0 32)

(*
   Validates a cookie in a second ClientHello.
   In the model, if the cookie is valid we get the connection ID 
   where the cookie was originally sent.
   When using appropriate integrity protection, valid cookies must have
   been created and sent in an early HelloRetryRequest.
*)
val validate_cookie:
    ck:cookie
  -> Stack (option (maybe_id & random))
  (requires fun h0 ->
    B.frameOf ck == other_rgn /\
    Some? cookie_key /\
    AE.invariant h0 (Some?.v cookie_key) /\ 
    B.live h0 ck /\
    (model ==> inv table h0))
  (ensures  fun h0 o h1 ->
    B.modifies (AE.footprint (Some?.v cookie_key)) h0 h1 /\
    AE.invariant h1 (Some?.v cookie_key) /\ 
    equal_domains h0 h1 /\
    (match o with
    | None -> True
    | Some (id, random) ->
      if model then
        let t:_connection_table = table in
        id == id_of_random random /\
        T.defined t id h0 /\
        (let c = T.value_of t id h0 in
           token_p c (fun h ->
             Sent_HRR? (sel h c) /\
             CH1 random == Sent_HRR?.ch (sel h c)))
      else True))

val receive_client_hello2:
    id:maybe_id 
  -> c:connection_ref id
  -> ch2:client_hello{has_cookie ch2}
  -> ST bool
  (requires fun h0 ->
    Some? cookie_key /\
    AE.invariant h0 (Some?.v cookie_key) /\ 
    B.live h0 (CH2?.ck ch2) /\
    (if model then
      let t:_connection_table = table in
      inv t h0 /\
      T.defined t id h0 /\ 
      T.value_of t id h0 == c
    else True) /\
    h0 `contains` c /\
    Init? (sel h0 c) /\ 
    has_cookie ch2)
  (ensures  fun h0 b h1 ->
    AE.invariant h1 (Some?.v cookie_key) /\ 
    (if model then
      let t:_connection_table = table in
      inv t h1 /\
      T.defined t id h1
    else True) /\
    (let c' = sel h1 c in
     if b then      
       B.modifies (B.loc_union 
         (AE.footprint (Some?.v cookie_key)) 
         (B.loc_mreference c)) h0 h1 /\
       Sent_ServerHello? c' /\
       Sent_ServerHello?.ch c' == ch2
     else 
       B.modifies (AE.footprint (Some?.v cookie_key)) h0 h1))

val receive_client_finished:
    id:maybe_id
  -> c:connection_ref id
  -> ST unit
  (requires fun h0 ->
    (if model then
      let t:_connection_table = table in
      inv t h0 /\
      T.defined t id h0 /\ 
      T.value_of t id h0 == c
    else True) /\
    h0 `contains` c /\
    Sent_ServerHello? (sel h0 c))
  (ensures  fun h0 b h1 ->
    B.modifies (B.loc_mreference c) h0 h1 /\
    (if model then
      let t:_connection_table = table in
      inv t h1 /\
      T.defined t id h1
    else True) /\
    (let c0 = sel h0 c in
     let c1 = sel h1 c in
     Complete? c1 /\
     Complete?.ch c1 == Sent_ServerHello?.ch c0))
