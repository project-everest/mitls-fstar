module TLSOld


(* THIS IS ONLY CALLED BY send, WHICH IS NOT USED ANYMORE, EXCEPT IN TEST (possibly)
   SHOULD REMOVE IT *)
val send_payload: c:connection -> i:id -> f:Content.fragment i -> ST (Content.encrypted f)
  (requires (fun h ->
    let es = epochs c h in // implying epochs_inv es
    let j = iT c.hs Writer h in
    st_inv c h /\
    (if j < 0 then is_PlaintextID i
     else indexable es j /\
	 (let e = Seq.index es j in
	  i === epoch_id e /\
	  incrementable (writer_epoch e) h))))
  (ensures (fun h0 payload h1 ->
    let es = epochs c h0 in
    let j = iT c.hs Writer h0 in
    st_inv c h0 /\
    st_inv c h1 /\
    (if j < 0
     then h0 == h1
     else (indexable es j /\
	  j = iT c.hs Writer h1 /\  //16-05-16 would be nice to write just j = iT c.hs Writer h1
	  (let e = Seq.index es j in
	   i === epoch_id e /\ (
	   let j : StAE.stae_id = i in //this is provable from the equality on i; using j below for better implicit args
	   let wr: writer j = writer_epoch e in
	   modifies (Set.singleton (region wr)) h0 h1 /\
	   seqnT wr h1 = seqnT wr h0 + 1 /\
	   (authId j ==> StAE.fragments #j wr h1 == snoc (StAE.fragments #j wr h0) f)
//		     /\ StAE.frame_f (StAE.fragments #i wr) h1 (Set.singleton (StAE.log_region wr)))
       )) /\
    True ))))

(* #reset-options "--log_queries --initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0" *)
let send_payload c i f =
    let j = Handshake.i c.hs Writer in
    if j<0
    then Content.repr i f
    else let es = MS.i_read (MkEpochs.es c.hs.log) in
	 let e = Seq.index es j in
	 StAE.encrypt (writer_epoch e) f
 

assume val frame_ae:
  h0:HH.t -> h1: HH.t -> c:connection -> Lemma(
    // restrictions of h0 and h1 to the footprint of st_inv and iT in c are the same /\
    st_inv c h0 ==> st_inv c h1 /\ op_Equality #int (iT c.hs Writer h0) (iT c.hs Writer h1))


let maybe_indexable (es:seq 'a) (i:int) = i=(-1) \/ indexable es i

let send_requires (c:connection) (i:id) (h:HH.t) = 
    let st = sel h c.state in
    let es = epochs c h in 
    let j = iT c.hs Writer h in
    maybe_indexable es j /\
    st_inv c h /\
    st <> Close /\
    st <> Half Reader /\
    (j < 0 ==> is_PlaintextID i) /\
    (j >= 0 ==> (
       let e = Seq.index es j in
       let wr = writer_epoch e in 
       Map.contains h (StAE.region wr) /\ NS: Needed to add this explicitly here. TODO: Soon, we will get this by just requiring mc_inv h, which includes this property
       Map.contains h (StAE.log_region wr) /\ NS: Needed to add this explicitly here. TODO: Soon, we will get this by just requiring mc_inv h, which includes this property
       i == epoch_id e /\
       incrementable (writer_epoch e) h))

val send: c:connection -> #i:id -> f: Content.fragment i -> ST (result unit)
  (requires (send_requires c i))
  (ensures (fun h0 _ h1 ->
    let es = epochs c h0 in
    let j = iT c.hs Writer h0  in
    let st = sel h0 c.state in
    maybe_indexable es j /\
    st_inv c h0 /\
    st_inv c h1 /\
    j == iT c.hs Writer h1 /\ // should follow from the modifies clause
    (if j < 0 then is_PlaintextID i /\ h0 == h1 else
       let e = Seq.index es j in
       i == epoch_id e /\ (
       let j : StAE.stae_id = i in
       let wr: writer j = writer_epoch e in
       modifies (Set.singleton (region wr)) h0 h1 /\
       seqnT wr h1 == seqnT wr h0 + 1 /\
       (authId i ==> StAE.fragments wr h1 == snoc (StAE.fragments wr h0) f )))))

let send c #i f =
  let pv = Handshake.version c.hs in // let Record replace TLS 1.3
  let ct, rg = Content.ct_rg i f in
  let payload = send_payload c i f in
  lemma_repr_bytes_values (length payload);
  assume (repr_bytes (length payload) <= 2); //NS: How are we supposed to prove this?
  let record = Record.makePacket ct (is_PlaintextID i) pv payload in
  let r = Transport.send (C.tcp c) record in
  match r with
    | Error(x)  -> Error(AD_internal_error,x)
    | Correct _ -> Correct()







(*16-05-20 not used yet?

(* Several test functions to drive the Handshake manually until the big
 [writeOne] function is complete. *)

let test_send_alert (c: connection) (i: id) (ad: alertDescription) =
  match send c #i (Content.ct_alert i ad) with
  | Correct () ->
      disconnect c; WriteError (Some ad) ""
  | Error (x,y) ->
      unrecoverable c y

let test_send (c:connection) (i:id) =
  let hs_response = Handshake.next_fragment c.hs in
  match hs_response with
  | Handshake.OutSome rg f ->
     send c #i (Content.CT_Handshake rg f)
  | _ -> failwith "ERROR"

let test_send_hs_fragment (c: connection) (i: id) (rg: frange i) (f: rbytes rg) =
  match send c #i (Content.CT_Handshake rg f) with
  | Correct ()   -> WriteAgain
  | Error (x,y) -> unrecoverable c y

let test_send_data (c: connection) (i: id) (rg: frange i) (f: rbytes rg) =
  match send c (Content.CT_Data rg f) with
  | Correct ()   -> Written (* Fairly, tell we're done, and we won't write more data *)
  | Error (x,y) -> unrecoverable c y
*) 


