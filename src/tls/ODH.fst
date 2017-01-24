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

module KEF

type kefalg
val keflen: a:kefalg -> Tot nat

type secret_source =
  | PSK of PSK.pskid
  | PSK_DHE of PSK.pskid * CommonDH.group
  | DHE of CommonDH.group

type role =
  | Initiator
  | Responder

type id = {
  alg: kefalg;
  source: secret_source;
  role: role;
  nonce: Nonce.random;
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

type psk_id (i:id) =
  is_PSK i.source \/ is_PSK_DHE i.source
type id = i:KEF.id{psk_id i}

let pskid (i:id) =
  match i.source with
  | PSK i -> i
  | PSK_DHE i g -> i

let safeId (i:id) = PSK.safePSK (pskid i)

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

let create (i:id) (r:rgn) : ST (state i)
  (requires (fun h0 -> safeId i))
  (ensures (fun h0 st h1 -> s0 = s1))
  =
  let key = Random.bytes (PSK.kexlen (pskid i)) in
  let log =
    if Flags.ideal_kef then
      MM.alloc () // ...
    else () in
  State r key log

let coerce (i:id) (r:rgn) (k:key i) : ST (state i)
  (requires (fun h0 -> ~(safeId i)))
  (ensures (fun h0 st h1 -> h0 = h1))
  =
  State r k ()

let compute (i:id) (st:state i) (ikm:bytes) : ST (extracted_secret i)
  (requires (fun h0 -> ))

module KEF_PRF_ODH

module PRF_ODH



val share_table: monotone_map

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

val extract_responder: k:kefalg -> g:group -> s1:share g -> n:salt k -> ST (share g & i:sid & extracted_secret i)
  (requires (fun h0 -> True)) // Maybe restrict to calling once per role?
  (ensures (fun h0 (s2, i, r) h1 ->
    safeExtract k g ks s n ==>
      match lookup odh_table (k,g,s1,s2,n) with
      | None ->
        m_sel h1 odh_table = update_map (m_sel h0 odh_table) (k,g,s1,s2,n) r
      | Some r' -> r' = r
  ))
