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
private type exponent (g:group)

(* Global log of honestly generated DH shares *)
private let dh_region:rgn = new_region tls_tables_region
private type share_table =
  if Flags.ideal_kef then
    monotone_map dh_region (g:group & s:share g) (e:exponent g) grows
  else
    ()

abstract let share_log: share_table =
  if Flags.ideal_kef then
    MM.alloc #dh_region #(g:group & s:share g) #(e:exponent g) #grows
  else
    ()

abstract type honest_share (#g:group) (s:share g) =
  if Flags.ideal_kef then
    witnessed (fun h -> Some? (MM.sel (MR.m_sel h share_log) (g,s)))
  else False

private let share_exp (#g:group) (s:share g) : ST (exponent g)
  (requires (fun h0 -> honest_share s))
  (ensures (fun h0 e h1 -> h0 = h1))
  =
  MR.m_recall share_log;
  Some.v (MM.sel (m_read share_log) (g,s))

let gen (g:group) : ST (s:share g)
  (requires (fun h0 -> True))
  (ensures (fun h0 ks h1 ->
    honest_share ks /\
    if Flags.ideal_kef then
      modifies_one dh_region h0 h1 /\
      MM.m_sel h1 share_log == MM.upd (m_sel h0 share_log) (g, ks) (share_exp ks))
    else
      h0 = h1
  ))
  =
  if Flags.ideal_kef then
    let exp = Random.bytes (CommonDH.explen g) in
    let share = CommonDH.exponentiate g exp in
    m_recall share_log;
    MM.extend share_log (g,share) exp;
    witness (is_Some (MM.lookup share_log (g,share)));
    share
  else
    CommonDH.keygen g

let parse (g:group) (b:lbytes (CommonDH.explen g)) : Tot (result (share g)) = ...

module KEF

type kefalg
val keflen: a:kefalg -> Tot nat

type ikmId =
  | PSK: id:PSK.pskid -> ikm
  | DHE: g:DH.group -> local_share:DH.keyshare g -> peer_share: DH.share g -> ikm
  | ZERO: ikm

type saltId =
  | Null
  | ExpandedEarlySecret of TLSInfo.esId
  | ExpandedHandshakeSecret of TLSInfo.hsId

type role =
  | Initiator
  | Responder

type id = {
  alg: kefalg;
  ikm: ikmId;
  salt: saltId;
}

type extracted_secret (i:id) =
  lbytes (keflen i.alg)

let safeId (i:id) : Tot bool =
  match i.source with
  | PSK pski -> PSK.safePSK i
  | PSK_DHE pski g ->
    if PSK.safePSK pski then true
    else CommonDH.safeGroup g
  | DHE g -> CommonDH.safeGroup g

///////////////////////////////////////////

module KEF_PRF_PSK
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
  is_DHE i.source \/ is_PSK_DHE i.source
type id = i:KEF.id{odh_id i}

let group_of_id (i:id) =
  match i.source with
  | DHE g -> g
  | PSK_DHE _ g -> g

let safeId (i:id) =
  CommonDH.safeGroup (group_of_id i)

val share_table: monotone_map (share i) ()

type

type state (i:id) =
  | State: unit -> state i

let create (i:id) =

type id = {
  alg: keflag;
  group: group;
  role: role;
  nonce: Nonce.t;
}

type state (i:id) =
  | ODH:
    r:rgn ->



type share (g:group)
val hasSecret: #g:group -> share g -> GTot bool
type keyshare (g:group) = s:share g{hasSecret s}

val keysharegen: g:group -> ST (s:keyshare g)
val sharecoerce: g:group -> pub:bytes{length pub = elemlen g} -> ST (s:share g{~(honestShare s)})
val keysharecoerce: g:group -> priv:bytes{length priv = keylen g} -> ST (s:keyshare g{~(honestShare s)})
val pubshare: keyshare -> Tot share

type salt (k:kefalg) = b:bytes{length b = saltlen k}
val honestSalt: #k:kefalg -> salt k -> GTot bool
val psk_zero_salt: k:kefalg -> Tot (n:salt k{~(honestSalt n)})
val saltgen: k:kefalg -> ST (n:salt k{n <> psk_zero_salt k})
val saltcoerce: k:kefalg -> b:bytes{length b = saltlen k} -> ST (n:salt k{~(honestSalt n)})

type sid = (k:kefalg & g:group & s1:share g & s2:share g & n:salt k)
type extracted_secret (i:sid)

type safeExtract (k:kefalg) (g:group) (ks:keyshare g) (s:share g) (n:salt k) =
  strongKef k /\ ((honestShare ks /\ honestShare s /\ strongGroup g) \/ (honestSalt n))


val odh_table : monotone_map (k:kefalg & g:group & s1:share g & s2:share g & n:salt k) (extracted_secret k g)

type registered_secret (k:kefalg) (g:group) (ks:keyshare g) (s:share g) (n:salt k) (h:mem) =
  is_Some (lookup odh_table (k,g,ks,s,n) h)

type stored_secret (k:kefalg) (g:group) (ks:keyshare g) (s:share g) (n:salt k) (e:extracted_secret k g) (h:mem) =
  registered_secret k g ks s n /\ lookup odh_table (k,g,ks,s,n) h = Some e

val extract_initiator: k:kefalg -> g:group -> s1:keyshare g -> s2:share g -> n:salt k -> ST (i:sid & extracted_secret i)
  (requires (fun h0 -> True)) // Maybe restrict to calling once per role?
  (ensures (fun h0 r h1 ->
    safeExtract k g ks s n ==>
  ))

  create_initiator: share, list (salt k)

(inititiator_sharer, responder_share, salt) -> (secret)

val extract_responder: k:kefalg -> g:group -> s1:share g -> n:salt k -> ST (share g & i:sid & extracted_secret i)
  (requires (fun h0 -> True)) // Maybe restrict to calling once per role?
  (ensures (fun h0 (s2, i, r) h1 ->
    safeExtract k g ks s n ==>
      match lookup odh_table (k,g,s1,s2,n) with
      | None ->
        m_sel h1 odh_table = update_map (m_sel h0 odh_table) (k,g,s1,s2,n) r
      | Some r' -> r' = r
  ))
