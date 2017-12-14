module TLSOld


(* THIS IS ONLY CALLED BY send, WHICH IS NOT USED ANYMORE, EXCEPT IN TEST (possibly)
   SHOULD REMOVE IT *)
val send_payload: c:connection -> i:id -> f:Content.fragment i -> ST (Content.encrypted f)
  (requires (fun h ->
    let es = epochs c h in // implying epochs_inv es
    let j = iT c.hs Writer h in
    st_inv c h /\
    (if j < 0 then PlaintextID? i
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
    else let es = MS.i_read (MkEpochs?.es c.hs.log) in
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
    (j < 0 ==> PlaintextID? i) /\
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
    (if j < 0 then PlaintextID? i /\ h0 == h1 else
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
  let record = Record.makePacket ct (PlaintextID? i) pv payload in
  let r = Transport.send (C?.tcp c) record in
  match r with
    | Error(x)  -> Error(AD_internal_error,x)
    | Correct _ -> Correct()


(*16-05-29 BEGIN OLDER VARIANT

val writeOne: c:connection -> i:id -> appdata: option (rg:frange i & DataStream.fragment i rg) -> ST ioresult_w
  (requires (fun h ->
    send_requires c i h
    /\ (let st = sel h c.state in
       let j = iT c.hs Writer h in
       j >= 0 ==> st=AD))) // CF 16-05-27 too strong
(*  (ensures (fun h0 r h1 -> True)) *)
(*     let st = sel h0 c.state in *)
(*     let es = sel h0 c.hs.log in *)
(*     let j = iT c.hs Writer h0  in *)
(*     st_inv c h0 /\ *)
(*     st_inv c h1 /\ *)
(*     j == iT c.hs Writer h1 /\ *) //16-05-16 used to be =; see other instance above
(*     (if j < 0 then PlaintextID? i /\ h0 = h1 else *)
(*        let e = Seq.index es j in *)
(*        i == epoch_id e /\ ( *)
(*        let wr:writer i = writer_epoch e in *)
(*        modifies (Set.singleton (C?.region c)) h0 h1 *)
(* )))) *)


let writeOne c i appdata =
  allow_inversion (Handshake.outgoing i);
  let h0 = get() in
  let wopt = current_writer c i in
  // alerts are now sent immediately, so we now start with Handshake
   match next_fragment i c.hs with
    | Handshake.OutError (x,y) -> unrecoverable c y // a bit blunt
    | Handshake.Outgoing om send_ccs next_keys complete ->

      // we send handshake & CCS messages, and process key changes (TODO:restore precise checks and error handling)
      match sendHandshake wopt om send_ccs with
      | Error (_,y) -> unrecoverable c y
      | _   ->
        if next_keys           then c.state := BC; // much happening ghostly
        let st = !c.state in
        if complete && st = BC then c.state := AD; // much happening ghostly too
        if complete
	then WriteHSComplete
        else if Some? om && send_ccs
	then WriteAgain
        else
             // we finally attempt to send some application data; we may statically know that st = AD
             match st, appdata with
	     | AD, Some (rg,f) -> begin
	       match sendFragment c wopt (Content.CT_Data rg f) with
	       | Error (_,y) -> unrecoverable c y
	       | _   -> Written (* Fairly, tell we're done, and we won't write more data *)
	       end
             | _ -> WriteDone // We are finishing a handshake. Tell we're done; the next read will complete it.



let is_current_writer (#c:connection) (#i:id) (wopt:option (cwriter i c)) (h:HH.t) =
  match wopt with
  | None -> True
  | Some w ->
    iT c.hs Writer h >= 0
    /\ (let epoch_i = eT c.hs Writer h in
       w == Epoch?.w epoch_i)


////////////////////////////////////////////////////////////////////////////////
//NS reached up to here
////////////////////////////////////////////////////////////////////////////////


// in TLS 1.2 we send the Finished messages immediately after CCS
// in TLS 1.3 we send e.g. ServerHello in plaintext then encrypted HS

val writeAllFinishing: c:connection -> i:id -> ST ioresult_w
  (requires (fun h ->
    send_requires c i h)) //16-05-28 too strong: already includes incrementable.
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\ modifies (Set.singleton c.region) h0 h1 /\
    (WriteError? r \/ WriteClose? r \/ Written? r)
  ))

let rec writeAllFinishing c i =
    assume false; //16-05-28
    if no_seqn_overflow c Writer then
    match writeOne c i None with
    // we disable writing temporarily
    | WriteAgain          -> writeAllFinishing c i
//   | WriteDone           -> MustRead

    // all other cases disable writing permanently
//  | WriteAgainClosing   -> writeClosing c i
    | WriteError x y      -> WriteError x y
    | WriteClose           -> WriteClose // why would we do that?

//  | MustRead            // excluded since responded only here
//  | Written             // excluded since we are not sending AD
//  | WriteAgainFinishing // excluded by the handshake logic (not easily proved)
    | WriteHSComplete     // excluded since we need an incoming CCS (not easily proved)
                          -> unexpected "[writeAllFinishing] writeOne returned wrong result"
    else                    unexpected "[writeAllFinishing] seqn overflow"


// called both by read (with no appData) and write (with some appData fragment)
// returns to read  { WriteError, WriteClose, WriteDone, WriteHSComplete }
// returns to write { WriteError, Written }
// (TODO: write returns { WriteHSComplete, MustRead } in renegotiation)
val writeAll: c:connection -> i:id -> appdata: option (rg:frange i & DataStream.fragment i rg) -> ST ioresult_w
  (requires (fun h ->
    send_requires c i h /\  //16-05-28 too strong: already includes incrementable.
    (Some? appdata ==> sel h c.state = AD)))
  (ensures (fun h0 r h1 ->
    st_inv c h1 /\ modifies (Set.singleton c.region) h0 h1 /\
    (None? appdata ==> WriteError? r \/ WriteDone? r \/ WriteHSComplete? r )))

let rec writeAll c i appdata =
    if no_seqn_overflow c Writer then
    (assume false; // TODO
    match writeOne c i appdata with
    | WriteAgain          -> writeAll c i appdata
//  | WriteAgainClosing   -> writeClosing c i // TODO, using updated epoch_id (epoch_w c)
    | WriteAgainFinishing -> // next writer epoch!
                            writeAllFinishing c i // TODO, using updated epoch_id (epoch_w c)
    | WriteError x y      -> WriteError x y
    | WriteClose           -> WriteClose
    | WriteDone           -> WriteDone
//  | MustRead            -> MustRead
    | Written             -> Written
    | _                   -> unexpected "[writeAll] writeOne returned wrong result")
    else                    unexpected "[writeAll] seqn overflow"


//Question: NS, BP, JL: Is it possible for write to return WriteAgain or a partially written data?
// no: we always write the whole fragment or we get a fatal error.

let write c i rg data = writeAll c i (Some (| rg, data |))

END OLDER VARIANT *)




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
