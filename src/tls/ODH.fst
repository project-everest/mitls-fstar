(**************************************************************************)
(** A simple idealization of CommonDH that records honestly generated shares *)
module DH
module MS = MonotoneSet

type group
val strongGroup: g:group -> GTot bool
type share (g:group)
type keyshare (g:group)
val pubshare: g:group -> s:keyshare g -> share g

(* Global log of honestly generated DH shares *)
private let dh_region:rgn = new_region tls_tables_region
private type share_table =
  (if Flags.ideal_kef then
    MS.t dh_region (g:group & s:share g) grows
  else
    ())

abstract let share_log: share_table =
  (if Flags.ideal_kef then
    MS.alloc #dh_region #(g:group & s:share g) #grows
  else
    ())

abstract type honest_share (#g:group) (s:share g) =
  Flags.ideal_kef ==> witnessed (MS.contains share_log (g,s))

let is_honest (#g:group) (s:share g) : ST bool
  (requires (fun h0 -> True))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1 /\
    b <==> honest_share s)) =
  if Flags.ideal_kef then
    Some? (MS.lookup share_log (g,s))
  else None

let keygen (g:group) : ST (s:keyshare g)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 ->
    if Flags.ideal_kef then
      modifies_one dh_region h0 h1 /\
      MR.m_sel h1 share_log == Set.union (MR.m_sel h0 share_log) (Set.singleton (g, pubshare s)) /\
      witnessed (MS.contains share_log (g, pubshare s))
    else h0 = h1))
  =
  let ks = CommonDH.keygen g in
  if Flags.ideal_kef then
   begin
    MR.m_recall share_log;
    MS.append share_log (g, pubshare ks);
    witness share_log (MS.contains share_log (g, pubshare ks))
   end;
  ks

let initiator (#g:group) (si:keyshare g) (sr:share g)
  : St (keyshare g * secret g) =
  CommonDH.initiator si sr

let responder (#g:group) (si:share g)
  : St (secret g) =
  CommonDH.responder si

let coerce (g:group) (b:mlbytes (CommonDH.explen g)) : Tot (s:share g{hasExp s}) =
  CommonDH.exponentiate g (CommonDH.generator g) exp
let parse (g:group) (b:mlbytes (CommonDH.sharelen g)) : Tot (result (share g)) =
  CommonDH.parse g b
let serialize (#g:group) (s:share g) : Tot (b:mlbytes (CommonDH.sharelen g))
  (ensures (parse g b = s))
  = CommonDH.serialize g s

////////////////////////////////////////////////////////////////////////////////

module KEF

type kefalg
val keflen: a:kefalg -> Tot nat

type kef_type =
  // PSK extraction, zero salt
  | PSK: pski:PSK.pskid -> ikm
  // DH extraction, constant salt
  | DH: g:DH.group -> ishare:DH.share g -> ikm
  // DH extraction, early secret salt
  | DH_PSK: esId:TLSInfo.esId -> g:DH.group -> ishare:DH.keyshare g -> ikm
  // Zero extraction, handshake secret salt
  | ZERO: hsId: TLSInfo.hsId -> ikm

// Instance indexing. TODO: check that there is no possible collision
// between DH and DH_PSK instances
type id = {
  alg: kefalg;
  kef_type: kef_type;
}

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
// For ODH, the responder share is ephemeral and generated as part of extraction
// (see multi-initiator ODH-extract assumption)
type ikm (i:id) (ir:role i) =
  (match i.kef_type with
  | PSK pski -> PSK.psk pski
  | DH g si | DH_PSK _ g si ->
    if ir = Initiator then
      // The initiator instance is created after the responder share is known
      (ks:DH.keyshare g{pubshare ks = si})
    else
      // The label must be picked at instance creation time for the responder
      (n:salt i)
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

(* Global table of extractor instances indexed by id *)
let kef_region:rgn = new_region tls_tables_region
type kef_table =
  (if Flags.ideal_kef then
    MM.t kef_region id extractor_instance grows
  else
    ())

let kef_instances : kef_table =
  (if Flags.ideal_kef then
    MM.alloc #kef_region #id #extractor_instance #grows
  else
    ())

let lookup_instance (i:id) : ST (option (extractor_instance i))
  (requires (fun h0 -> True))
  (ensures (fun h0 sto h1 ->
    modifies_none h0 h1 /\
    if Flags.ideal_kef then
      Some? sto ==> witnessed (MM.contains kef_instances i (Some?.v sto))
    else
      sto == None))
  =
  if Flags.ideal_kef then
    MM.lookup kef_instances i
  else
    None

let extract_instance (#i:id) (st:extractor_instance i)
  (ir:role) (ikm:ikm i ir) (salt:salt i) : ST (extracted_secret i)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    modifies_none h0 h1))
  =
  (match i.kef_type with
  | PSK _ | ZERO _ -> KEF_PRF.extract i st ir ikm salt
  | DH _ _ _ -> KEF_PRF_ODH.extract i st ir ikm salt
  | DH_PSK esId _ _ _ ->
    if honest_esId esId then
      KEF_PRF.extract i st ir ikm salt
    else
      KEF_PRF_ODH.extract i st ir ikm salt)

let extract (i:id) (ir:role i) (ikm:ikm i ir) (salt:salt i)
  : ST (extracted_secret i)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 -> h0=h1))
  =
  let st =
    match lookup_instance i with
    | Some st -> st
    | None ->
      (match i.kef_type with
      | PSK pskid -> KEF_PRF.create
        )
  | Some (st:extractor_instance i) =


///////////////////////////////////////////

module KEF_PRF
open KEF

type id = i:id{PSK? i.kef_type \/ ZERO? i.kef_type \/ DH_PSK? i.kef_type}

let safeId (i:id) =
  (match i.kef_type with
  | PSK pski -> PSK.safePSK pski
  | ZERO hsId -> honest_hsId hsId
  | DH_PSK esId _ _ _ -> honest_esId esId)

(** Type of values used to key the PRF *)
type prf_key (i:id) =
  (match i.kef_type with
  | PSK pski -> PSK.psk pski
  | ZERO hsId -> expanded_secret (HandshakeSecretID hsId)
  | DH_PSK esId _ _ _ -> expanded_secret (EarlySecretID esId))

let prf_keylen (i:id) =
  (match i.kef_type with
  | PSK pski -> PSK.psklen pski
  | ZERO hsId -> hashlen (hsId_hash hsId)
  | DH_PSK esId _ _ _ -> hashlen (esId_hash esId)

(** Type of the domain of the keyed PRF *)
type prf_domain (i:id) =
  (match i.kef_type with
  | PSK _ -> unit
  | ZERO _ -> unit
  | DH_PSK _ _ _ _ -> bytes

type prf_range (i:id) (d:domain i) = extracted_secret i

(* Compact style: only allocate log for idealized instances *)
type log (i:id) (r:rgn) =
  (if Flags.ideal_kef /\ safeId i then
    MM.t r (prf_domain i) (prf_range i)
  else
    unit)

type state (i:id) =
  | State:
     r:rgn ->
     key: prf_key i
     log: log i r ->
     state i

let create (i:id) (parent:rgn) : ST (state i)
  (requires (fun h0 -> safeId i))
  (ensures (fun h0 st h1 ->
    modifies_none h0 h1 /\
    extends st.r parent /\
    stronger_fresh_region st.r h0 h1 /\
    if Flags.ideal_kef then
      h1 `contains` st.log /\
      MM.m_sel h1 st.log == MM.empty_map
    else
      True))
  =
  let r = new_region parent in
  let key : prf_key i = Bytes.random (prf_keylen i) in
  let log =
    if Flags.ideal_kef then
      MM.alloc #r #(prf_domain i) #(prf_range i) #grows
    else () in
  State r key log

let coerce (i:id) (r:rgn) (k:prf_key i) : ST (state i)
  (requires (fun h0 -> ~(safeId i)))
  (ensures (fun h0 st h1 -> h0 = h1))
  =
  State r k ()

let extract (i:id) (st:state i) (v:prf_domain i) : ST (prf_range i v)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    if Flags.ideal_kef /\ safeId i then
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
  if Flags.ideal_kef && safeId i then
    (match MM.lookup st.log v with
    | Some r -> r
    | None ->
      let r = Bytes.random (keflen i.alg) in
      m_recall st.log;
      MM.extend st.log v r; r)
  else
    let concrete_v =
      (match i.kef_type with
      | PSK pskid -> zH (PSK.pskid_hash pskid // TODO move from KeySchedule
      | ZERO hsId -> zH (hsId_hash hsId)
      | DH_PSK _ _ _ _ -> v) in
    Hacl.KEF.extract (i.alg) st.key concrete_v // e.g. HKDF

module KEF_PRF_ODH

type id = i:KEF.id{DH? i.kef_type \/ DH_PSK? i.kef_type}

let ishare_of_id (i:id) =
  match i.kef_type with
  | DH g si -> (g, si)
  | DH_PSK _ g si -> (g, si)

inline_for_extraction let safeId (i:id) : Tot bool =
  let (g, si, sr) = shares_of_id i in
  Flags.ideal_kef && DH.strongGroup g && DH.honest_share si && DH.honest_share sr

type salt (i:id) =
  (match i.kef_type with
  | DH _ _ _ -> unit
  | DH_PSK esId _ _ _ -> expanded_secret (EarlySecretID esId))

type odh_index (i:id) =
  (let g, _ = ishare_of_id i in
  sr:share g * n:salt i)

type odh_extracted (i:id) (j:odh_index i) =
  extracted_secret i

type log (i:id) (r:rgn) =
  (if safeId i then
    MM.t r (odh_index i) (odh_extracted i)
  else
    unit)

type odh_key (i:id) (ir:dhrole) =
  (let g, si = ishare_of_id i in
  if ir = Initiator then
    ks:DH.keyshare g{DH.pubshare ks = si}
   else
    sr:DH.keyshare g{honest_share (pubshare ks)} * DH.secret (g,si,pubshare sr) * n:salt i)

type state (i:id) (ir:dhrole) =
  | State:
    r: rgn ->
    key: odh_key i ir ->
    log: log i r ->
    state i

type odh_initiator (i:id) = state i Initiator
type odh_responder (i:id) = state i Responder

let create (i:id) (ir:role i) (ikm:ikm i ir) : ST (state i ir)
  (requires (fun h0 -> True))
  (ensures (fun h0 st h1 -> True))
  =
  let r = new_region parent in
  let (g, si) = ishare_of_id i in
  let log =
    if Flags.ideal_kef && DH.is_honest si then
      MM.alloc #r #(odh_index i) #(odh_extracted i) #grows
    else () in
  let key = match ir with
    | Initiator -> ikm
    | Responder ->
      let n = ikm in
      let sr, secret = DH.responder g si in
      (sr, secret, n)
    in
  State r key log

let extract_responder (i:id) (st:odh_responder i) : ST (extracted_secret i)
  (requires (fun h0 ->
    let sr, _, n = st.key in
    MM.fresh st.log (pubshare sr, n) h0)) // Can only call once
  (ensures (fun h0 (sr,r) h1 ->
    let (g, si) = ishare_of_id i in
    let (sr, _, n) = st.key in
    if Flags.ideal_kef then
      DH.honestGroup g /\ DH.honest_share si ==>
        (modifies_one st.r h0 h1 /\
        MR.m_sel h1 st.log == MM.upd (MR.m_sel h0 st.log) (pubshare sr, n) r /\
        witnessed (MM.contains st.log (pubshare sr, n) r))
    else h0 = h1))
  =
  let g, si = ishare_of_id i in
  let sr, secret, n = st.key in
  if Flags.ideal_kef && DH.strongGroup g && DH.is_honest si then
    let r = Bytes.random (keflen i.alg) in
    m_recall st.log;
    MM.extend st.log (pubshare sr, n) r;
    (sr, r)
  else
    let concrete_n = match i.kef_type with
      | DH _ _ _ -> zH (hashalg i)
      | DH_PSK _ _ _ _ -> n in
    let r = Hacl.KEF.extract (i.alg) secret concrete_n in
    (sr, r)

let extract_initiator (i:id) (st:odh_initiator i)
  (sr:share (fst (ishare_of_id i)) (n:salt i)
  : ST (extracted_secret i)
  (requires (fun h0 -> safeId i ==> MM.defined st.log (sr, n)))
  (ensures (fun h0 r h1 ->
    let g, si = ishare_of_id i in
    modifies_none h0 h1 /\
    (Flags.ideal_kef /\ DH.strongGroup g /\ DH.honest_share si) ==>
      (r == MM.value st.log (si, n))))
  =
  let g, si = ishare_of_id i in
  let ksi = st.key in
  let secret = DH.initiator ksi sr in
  let concrete_n = match i.kef_type with
    | DH _ _ _ -> zH (hashalg i)
    | DH_PSK _ _ _ _ -> n in
  let r = Hacl.KEF.extract (i.alg) secret concrete_n in
  if Flags.ideal_kef && DH.strongGroup g && DH.is_honest si then
    (match MM.lookup st.log (sr, n) with
    | Some r -> r)
  else r

(*
let extract (i:id) (st:state i) (ir:role i) (s:salt i)
  : ST (odh_extracted i s)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    if Flags.ideal_kef /\ safeId i then
      (match MM.sel (MR.m_sel h0 st.log) s with
      | None ->
        (ir == Initiator ==> modifies_none h0 h1) /\
        (ir == Responder ==>
          modifies_one st.r h0 h1 /\
          MR.m_sel h1 st.log == MM.upd (MR.m_sel h0 st.log) s r /\
          witnessed (MM.contains st.log s r))
      | Some r' ->
        modifies_none h0 h1 /\
        r' = r)
    else
      h0 = h1))
  =
  let concrete_s =
    match i.kef_type with
    | DH _ _ _ -> zH (hashalg i)
    | DH_PSK _ _ _ _ -> s in

    module PRF_ODH

    val strongKef: a:keflag -> GTot bool
    val strongGroup: g:group -> GTot bool

    type share (g:group)
    val hasSecret: #g:group -> share g -> GTot bool
    type keyshare (g:group) = s:share g{hasSecret s}
    val honestShare: share -> GTot bool

    val keysharegen: g:group -> ST (s:keyshare g)
    val sharecoerce: g:group -> pub:bytes{length pub = elemlen g} -> ST (s:share g{~(honestShare s)})
    val keysharecoerce: g:group -> priv:bytes{length priv = keylen g} -> ST (s:keyshare g{~(honestShare s)})
    val pubshare: keyshare -> Tot share

    type salt (k:kefalg) = b:bytes{length b = saltlen k}
    val honestSalt: #k:kefalg -> salt k -> GTot bool
    val psk_zero_salt: k:kefalg -> Tot (n:salt k{~(honestSalt n)})
    val saltgen: k:kefalg -> ST (n:salt k{n <> psk_zero_salt k})
    val saltcoerce: k:kefalg -> b:bytes{length b = saltlen k} -> ST (n:salt k{~(honestSalt n)})

    type extracted_secret (k:kefalg) (g:group)
    type safeExtract (k:kefalg) (g:group) (ks:keyshare g) (s:share g) (n:salt k) =
      strongKef k /\ ((honestShare ks /\ honestShare s /\ strongGroup g) \/ (honestSalt n))

    type dhrole =
    | Initiator
    | Responder

    val odh_table : monotone_map (k:kefalg & g:group & s1:share g & s2:share g & n:salt k) (extracted_secret k g)

    type registered_secret (k:kefalg) (g:group) (ks:keyshare g) (s:share g) (n:salt k) (h:mem) =
      is_Some (lookup odh_table (k,g,ks,s,n) h)

    type stored_secret (k:kefalg) (g:group) (ks:keyshare g) (s:share g) (n:salt k) (e:extracted_secret k g) (h:mem) =
      registered_secret k g ks s n /\ lookup odh_table (k,g,ks,s,n) h = Some e

    val extract: k:kefalg -> g:group -> role:dhrole -> ks:keyshare g -> s:share g -> n:salt k -> ST (extracted_secret k g)
      (requires (fun h0 -> True)) // Maybe restrict to calling once per role?
      (ensures (fun h0 r h1 ->
        safeExtract k g ks s n ==>
          let (s1, s2) =
            match role with
            | Initiator -> (pubshare ks, s)
            | Responder -> (s, pubshare ks) in
          match lookup odh_table (k,g,s1,s2,n) with
          | None ->
            m_sel h1 odh_table = update_map (m_sel h0 odh_table) (k,g,s1,s2,n) r
          | Some r' -> r' = r
      ))

    let extract k g role ks s n =
      if safeExtract k g ks s n then
        let (s1, s2) =
          match role with
          | Initiator -> (pubshare ks, s)
          | Responder -> (s, pubshare ks) in
        (match m_lookup odh_table (k,g,s1,s2,n) with
        | None ->
           let r = KDF.gen k in
           update_map odh_table (k,g,s1,s2,n) r; r
        | Some r -> r)
      else
        let ikm = CommonDH.exponentiate g ks s in
        HKDF.hkdf_extract k n ikm

*)
