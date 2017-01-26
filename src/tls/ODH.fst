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

(**************************************************************************)
module DH

type group
val strongGroup: g:group -> GTot bool
type share (g:group)
type hasExp (#g:group) (s:share g)
abstract type exponent (g:group)
val share_exponent: #g:group -> s:share g{hasExp s} -> Tot (exponent g)

(* Global log of honestly generated DH shares *)
private let dh_region:rgn = new_region tls_tables_region
private type share_table =
  (if Flags.ideal_kef then
    monotone_set dh_region (g:group & s:share g) grows
  else
    ())

abstract let share_log: share_table =
  (if Flags.ideal_kef then
    MS.alloc #dh_region #(g:group & s:share g) #grows
  else
    ())

abstract type honest_share (#g:group) (s:share g) =
  (if Flags.ideal_kef then
    witnessed (fun h -> MS.contains (MS.m_sel h share_log) (g,s))
  else False)

let keygen (g:group) : ST (s:share g{hasExp s})
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 ->
    honest_share s /\
    if Flags.ideal_kef then
      modifies_one dh_region h0 h1 /\
      MS.m_sel h1 share_log == Set.union (MS.m_sel h0 share_log) (Set.singleton (g, s))
    else
      h0 = h1
  ))
  =
  let share = CommonDH.keygen g in
  if Flags.ideal_kef then begin
    MR.m_recall share_log;
    MS.append share_log (g,share);
    witness (MS.contains (MS.m_read share_log) (g,share))
  end;
  share

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
  | DH: g:DH.group -> ishare:DH.share g -> sshare: DH.share g -> ikm
  // DH extraction, early secret salt
  | DH_PSK: esId:TLSInfo.esId -> g:DH.group -> ishare:DH.keyshare g -> sshare: DH.share g -> ikm
  // Zero extraction, handshake secret salt
  | ZERO: hsId: TLSInfo.hsId -> ikm

// Instance indexing. TODO: check that there is no possible collision
// between DH and DH_PSK instances
type id = {
  alg: kefalg;
  kef_type: kef_type;
}

type role =
  | Initiator
  | Responder

// The type of the input key material to extract
type ikm (i:id) (ir:role) =
  (match i.kef_type with
  | PSK pski -> PSK.psk pski
  | DH g si sr | DH_PSK _ g si sr ->
    if ir = Initiator then
      (si:DH.share g{DH.hasExp si} * sr:DH.share g)
    else
      (si:DH.share g * sr:DH.share g{DH.hasExp sr})
  | ZERO _ -> unit)

type salt (i:id) =
  (match i.kef_type with
  | PSK _  | DH _ _ _ -> unit
  | DH_PSK esId _ _ _ ->
    expanded_secret (EarlySecretID esId)
  | ZERO hsId ->
    expanded_secret (HandshakeSecretID hsId))

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
private let kef_region:rgn = new_region tls_tables_region
private type kef_table =
  (if Flags.ideal_kef then
    MM.t kef_region id extractor_instance grows
  else
    ())

abstract let kef_instances : kef_table =
  (if Flags.ideal_kef then
    MM.alloc #kef_region #id #extractor_instance #grows
  else
    ())

let lookup_instance (i:id) =
  if Flags.ideal_kef then
    MM.lookup kef_instances i
  else None

let extract_instance (#i:id) (st:extractor_instance i) (ir:role) (ikm:ikm i ir) (salt:salt i)
  : ST (extracted_secret i)
  =
  (match i.kef_type with
  | PSK _ | ZERO _ -> KEF_PRF.extract i st ir ikm salt
  | DH _ _ _ -> KEF_PRF_ODH.extract i st ir ikm salt
  | DH_PSK esId _ _ _ ->
    if honest_esId esId then
      KEF_PRF.extract i st ir ikm salt
    else
      KEF_PRF_ODH.extract i st ir ikm salt)

let extract (i:id) (ir:role) (ikm:ikm i ir) (salt:salt i)
  : ST (extracted_secret i)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 -> h0=h1))
  =
  match lookup_instance i with
  | None ->
  | Some (st:extractor_instance i) =



///////////////////////////////////////////

module KEF_PRF
open KEF

type psk_id (i:id) =
  is_PSK i.source \/ is_PSK_DHE i.source
type id = i:id{psk_id i}

let pskid (i:id) =
  match i.source with
  | PSK i -> i
  | PSK_DHE i g -> i

type log (i:id) (r:rgn) =
  (if Flags.ideal_kef /\ safeId i then
    monotone_map #r bytes (extracted_secret i)
  else
    unit)

type key (i:id) = PSK.kexlen (pskid i)

type state (i:id) =
  | State:
     r:rgn ->
     key: key i
     log: log i r ->
     state i

let create (i:id) (parent:rgn) : ST (state i)
  (requires (fun h0 -> safeId i))
  (ensures (fun h0 st h1 ->
    modifies_none h0 h1 /\
    extends st.r parent /\
    stronger_fresh_region st.r h0 h1 /\
    MM.m_sel h1 st.log == MM.empty_map))
  =
  let r = new_region parent in
  let key = Random.bytes (PSK.kexlen (pskid i)) in
  let log =
    if Flags.ideal_kef then
      MM.alloc #r () // ...
    else () in
  State r key log

let coerce (i:id) (r:rgn) (k:key i) : ST (state i)
  (requires (fun h0 -> ~(safeId i)))
  (ensures (fun h0 st h1 -> h0 = h1))
  =
  State r k ()

type fresh_input (i:id{safeId i}) (st:state i) (ikm:bytes) (h:mem) =
  is_None (MM.sel (MR.m_sel h st.log) ikm)

let compute (i:id) (st:state i) (ikm:bytes) : ST (extracted_secret i)
  (requires (fun h0 -> safeId i ==> fresh_input i st ikm h0))
  (ensures (fun h0 s h1 ->
    if safeId i /\ Flags.ideal_kef then
      modifies_one st.r h0 h1 /\
      MM.m_sel h1 st.log == MM.upd (m_sel h0 st.log) ikm s) /\
      witnessed (MM.contains (m_sel h1 st.log) ikm)
    else h0 = h1
  ))
  =
  if Flags.ideal_kef && safeId i then
    let secret = Random.bytes (KEF.keflen i.alg) in
    m_recall st.log;
    MM.extend st.log ikm secret;
    witness (is_Some (MM.lookup st.log ikm));
    secret
  else
    Hacl.KEF.compute (i.alg) ikm (st.key) // e.g. HKDF

module KEF_PRF_ODH

type odh_id (i:id) =
  DH? i.kef_type \/ DH_PSK? i.kef_type
type id = i:KEF.id{odh_id i}

let shares_of_id (i:id) =
  match i.kef_type with
  | DH g si sr -> (g, si, sr)
  | DH_PSK _ g si sr -> (g, si, sr)

type ikm (i:id) (ir:role) =
  (match i.kef_type with
  | DH g si sr | DH_PSK _ g si sr ->
    if ir = Initiator then
      e:DH.exponent si{DH.hasExp si /\ DH.share_exponent si = e}
    else
      e:DH.exponent sr{DH.hasExp sr /\ DH.share_exponent sr = e})

type salt (i:id) =
  (match i.kef_type with
  | DH _ _ _ ->
    unit
  | DH_PSK esId _ _ _ ->
    expanded_secret (EarlySecretID esId))

type state (i:id) =
  | State: log: monotone_map (i:id & l:label i) (extracted_secret) -> state i

let extract (i:id) (st:state i) (ir:role) (ikm:ikm i ir) (s:salt i)
  : ST (extracted_secret i)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 -> h0 = h1))
  =
  let (g, si, sr) = shares_of_id i in
  if Flags.ideal_kef && DH.is_honest si && DH.is_honest sr then

  else
    let ikm =
      if ir = Initiator then
        DH.exponentiate sr ikm
      else
        DH.exponentiate si ikm in
    let s = Hacl.KEF.extract i.kefalg in
    s

let extract_responder k g s n =
  let ks = keysharegen g in
  if safeExtract k g ks s n then
    (match m_lookup odh_table (k,g,s,pubshare ks,n) with
    | None ->
       let r = KDF.gen k in
       update_map odh_table (k,g,s,pubshare ks,n) r; r
    | Some r -> r)
  else
    let ikm = CommonDH.exponentiate g ks s in
    ks, HKDF.hkdf_extract k n ikm

let extract_initiator k g ks s n =
    (match m_lookup odh_table (k,g, pubshare ks, s,n) with
    | Some r -> r
    | None ->
      let ikm = CommonDH.exponentiate g ks s in
      HKDF.hkdf_extract k n ikm
