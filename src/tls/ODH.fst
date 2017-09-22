module KEF

type kefalg
val keflen: a:kefalg -> Tot nat

type kef_type =
  | PSK: pski:PSK.pskid -> ikm
  // DH extraction, constant salt
  | DH: g:DH.group -> ishare:DH.share g -> ikm
  // DH extraction, early secret salt
  | DH_PSK: esId:TLSInfo.esId -> g:DH.group -> ishare:DH.keyshare g -> ikm
  // Zero extraction, handshake secret salt
  | ZERO: hsId: TLSInfo.hsId -> ikm

// Instance indexing. TODO: check that there is no possible collision
// between DH and DH_PSK instances
type pre_id = {
  alg: kefalg;
  kef_type: kef_type;
}

let safety_table =
  (if Flags.ideal_kef then
    MM.alloc #kef_region #id #(fun i -> bool) #(fun _ -> True)
  else unit)

type registered (i:id) =
  (if Flags.ideal_kef then
    MR.witnessed (MM.defined safety_table i)
  else True)

type id = i:pre_id{registered i}

type safeId (i:id) =
  (if Flags.ideal_kef then
    MR.witnessed (MM.contains KEF.safe_table i true)
  else False)

let is_safe (i:id) : ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 -> modifies_none h0 h1 /\ b <==> safeId i))
  =
  Flags.ideal_KEF_PRF &&
  (match i.kef_type with
  | PSK pski -> PSK.safePSK pski
  | DH_PSK esId _ _ _ -> honest_esId esId)

type dhrole =
  | Initiator
  | Responder

type role (i:id) =
  (match i.kef_type with
  | DH _ _ | DH_PSK _ _ _ -> dhrole
  | _ -> unit)

type salt (i:id) =
  (match i.kef_type with
  | PSK _  | DH _ _ -> unit
  | DH_PSK esId _ _ ->
    expanded_secret (EarlySecretID esId)
  | ZERO hsId ->
    expanded_secret (HandshakeSecretID hsId))

// The type of the input key material to extract
type ikm (i:id) (ir:role i) =
  (match i.kef_type with
  | PSK pski -> PSK.psk pski
  | DH g si | DH_PSK _ g si ->
    if ir = Initiator then CommonDH.secret g
    else unit
  | ZERO _ -> unit)

type extracted_secret (i:id) =
  lbytes (keflen i.alg)

type extractor_instance (i:id) =
  (match i.kef_type with
  | PSK _ | ZERO _ -> KEF_PRF.state i
  | DH _ _ _ -> KEF_PRF_ODH.state i
  | DH_PSK esId _ _ _ ->
    if honest_esId esId then
      KEF_PRF.state i
    else
      KEF_PRF_ODH.state i)

///////////////////////////////////////////

// Middle extraction modeled as a PRF keyed by the extraction salt
module KEF_PRF
open KEF

type id = i:id{PSK? i.kef_type \/ DH_PSK? i.kef_type}

type prf_key (i:id) = salt i

type prf_domain (i:id) =
  (match i.kef_type with
  | PSK _ -> unit // Can only extract 0 in pure PSK
  | DH_PSK _ g _ _ -> DH.secret g

type prf_range (i:id) (d:domain i) = extracted_secret i

(* Compact style: only allocate log for idealized instances *)
type log (i:id) (r:rgn) =
  (if safeId i then
    MM.t r (prf_domain i) (prf_range i)
  else
    unit)

type state (i:id) =
  | State:
     r:rgn ->
     key: prf_key i ->
     log: log i r ->
     state i

let create (i:id) (parent:rgn) (key:prf_key i) : ST (state i)
  (requires (fun h0 -> True))
  (ensures (fun h0 st h1 ->
    modifies_none h0 h1 /\
    extends st.r parent /\
    stronger_fresh_region st.r h0 h1 /\
    if safeId i then
      h1 `contains` st.log /\
      MM.m_sel h1 st.log == MM.empty_map
    else
      True))
  =
  let r = new_region parent in
  let key =
    if is_safe i then Random.bytes (prf_keylen i)
    else key in
  let log =
    if is_safe i then
      MM.alloc #r #(prf_domain i) #(prf_range i) #grows
    else () in
  State r key log

let extract (i:id) (st:state i) (v:prf_domain i) : ST (prf_range i v)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    if safeId i then
      (match MM.sel (MR.m_sel h0 st.log) v with
      | None ->
        modifies_one st.r h0 h1 /\
        MR.m_sel h1 st.log == MM.upd (MR.m_sel h0 st.log) v r) /\
        witnessed (MM.contains st.log v r)
      | Some r' ->
        modifies_none h0 h1 /\
        r' = r)
    else
      h0 = h1
  ))
  =
  if is_safe i then
    (match MM.lookup st.log v with
    | Some r -> r
    | None ->
      let r = Bytes.random (keflen i.alg) in
      m_recall st.log;
      MM.extend st.log v r; r)
  else
    let concrete_v =
      (match i.kef_type with
      | PSK pskid -> zH (PSK.pskid_hash pskid)
      | DH_PSK _ _ _ _ -> v) in
    Hacl.KEF.extract (i.alg) concrete_v st.key // st.key is the salt

module KEF_PRF_ODH

type id = i:KEF.id{DH? i.kef_type \/ DH_PSK? i.kef_type}

let ishare_of_id (i:id) =
  match i.kef_type with
  | DH g si -> (| g, si |)
  | DH_PSK _ g si -> (| g, si |)

type odh_index (i:id) =
  (let g, _ = ishare_of_id i in
  sr:share g * n:salt i)

type odh_extracted (i:id) (j:odh_index i) =
  extracted_secret i

type odh_log (i:id) (r:rgn) =
  (if safeId i then
    MM.t r (odh_index i) (odh_extracted i)
  else
    unit)

type state (i:id) (ir:dhrole) =
  | State:
    r: rgn ->
    key: ikm i ir -> // initiator keyshare or responder salt
    log: odh_log i r -> // Map of responder share and salt to extracted secrets
    // The responder share used by the initiator.
    initiator_responder: rref r (o:option (odh_index i){is_Some o ==> MR.witnessed (MM.defined log (Some.v o))}) ->
    state i

type odh_initiator (i:id) = state i Initiator
type odh_responder (i:id) = state i Responder

let create (i:id) (ir:role i) (parent:rgn) (ikm:ikm i ir) : ST (state i ir)
  (requires (fun h0 -> True))
  (ensures (fun h0 st h1 ->
    modifies_none h0 h1 /\
    stronger_fresh_region r parent /\
    empty_log (MM.sel h1 st.log) /\
    is_None (sel h1 st.initiator_responder)))
  =
  let r = new_region parent in
  let (g, si) = ishare_of_id i in
  let log =
    if is_safe i then
      MM.alloc #r #(odh_index i) #(odh_extracted i) #(fun _ -> True)
    else () in
  let initiator_responder = ralloc r None in
  State r key log initiator_responder

type rshare (i:id) = (let (| g, si |) = ishare_of_id i in DH.share g)
type rsecret (i:id) = (let (| g, si |) = ishare_of_id i in DH.secret g)

// Non-terminating function to generate a fresh responder share that doesn't appear in the ODH table
let fresh_sharegen: i:id -> log:log -> n:salt i -> ST (rshare i * rsecret i)
  (requires (fun h0 -> True))
  (ensures (fun h0 (sr, gxy) h1 ->
    modifies_none h0 h1 /\
    honest i ==> MM.fresh log (sr, n) h1))
  =
  let sr, gxy = DH.dh_responder si in
  if is_honest i then
    match MM.lookup log (sr, n) with
    | None -> (sr, gxy)
    | Some _ -> fresh_sharegen i log n
  else sr, gxy

(* Global table of extractor instances indexed by id *)
let odh_region:rgn = new_region tls_tables_region
type kef_prf_table =
  (if Flags.ideal_kef then
    MM.t odh_region id  grows
  else
    ())

let kef_prf_instances : kef_table =
  (if Flags.ideal_kef then
    MM.alloc #odh_region #id #KEF_PRF.state #(fun _ -> True)
  else
    ())

// Memoizing wrapper to KEF_PRF instances
// Note that the behavior is always concrete if the extraction is pure ODH
let prf (i:id) (gxy:extracted_secret i) (n:salt i) =
  if DH_PSK? i.kef_type && Flags.ideal_kef then
    let st : KEF_PRF.state i =
      match MM.lookup kef_prf_instances i with
      | Some st -> st
      | None ->
        let st = KEF_PRF.create i n in
        MR.m_recall kef_prf_instances;
        MM.extend kef_prf_instances i st; st
      in
    KEF_PRF.extract i st gxy
  else
    let concrete_n = match i.kef_type with
      | DH _ _ _ -> zH (hashalg i)
      | DH_PSK _ _ _ _ -> n in
    Hacl.KEF.extract (i.alg) gxy n

let extract_responder (i:id) (st:odh_responder i) : ST (rshare i * extracted_secret i)
  (requires (fun h0 -> True))
  (ensures (fun h0 (sr,r) h1 ->
    let (| g, si |) = ishare_of_id i in
    let n:salt i = st.key in
    (if safeId i then
      modifies_one st.r h0 h1 /\
      MR.m_sel h1 st.log == MM.upd (MR.m_sel h0 st.log) (sr, n) r /\
      MR.witnessed (MM.defined st.log (sr, n)) /\
      MR.witnessed (MM.contains st.log (sr, n) r)
    else h0 = h1)))
  =
  let (| g, si |) = ishare_of_id i in
  let n : salt i = st.key in
  let sr, gxy = fresh_sharegen i st.log n in
  if is_honest i then
    let r = Bytes.random (keflen i.alg) in
    m_recall st.log;
    MM.extend st.log (sr, n) r; // we know (sr,n) is fresh from fresh_sharegen
    (sr, r)
  else
    let r = prf i gxy concrete_n in
    (sr, r)

let extract_initiator (i:id) (st:odh_initiator i) (sr:rshare i) (n:salt i)
  : ST (extracted_secret i)
  (requires (fun h0 ->
    is_None (MR.m_sel st.initiator_responder h0)))
  (ensures (fun h0 r h1 ->
    let g, si = ishare_of_id i in
    modifies_one st.r h0 h1 /\
    safeId i /\ MR.witnessed (MM.contains st.log (sr,n)) ==>
      (MM.defined st.log (sr,n) r h1 /\
      HH.sel h1 st.initiator_responder == Some (sr,n))
  ))
  =
  let g, si = ishare_of_id i in
  let ksi : DH.keyshare g{DH.pubshare ksi = si} = st.key in
  let gxy = DH.dh_initiator ksi sr in
  if is_safe i then
    match MM.lookup st.log (sr, n) with
    | None -> prf i gxy n // behave concretely
    | Some r -> st.initiator_responder := (sr, n); r
  else
    prf i gxy n
