(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module DH

open Platform.Bytes
open DHGroup
open ECGroup
open CoreCrypto
open CommonDH

#if ideal
// Local predicate definitions
type predHE = HonestExponential of bytes * bytes * elt
#endif

#if ideal
// log of honestly generated elements
type honest_entry = (dhparams * elt)
let honest_log = ref([]: list<honest_entry>)
#if verify
let honest dhp gx = failwith "only used in ideal implementation, unverified"
#else
let honest dhp gx = List.exists (fun el-> el = (dhp,gx)) !honest_log 
#endif

let safeDH (dhp:dhparams) (gx:elt) (gy:elt): bool = 
    honest dhp gx && honest dhp gy && goodPP dhp
#endif

#if ideal
// log for looking up good pms values using their id
type entry = dhparams * elt * elt * PMS.dhpms
let log: list<entry> ref = ref []
let rec assoc (dhp:dhparams) (gx:elt) (gy:elt) entries: option<PMS.dhpms> = 
    match entries with 
    | []                      -> None 
    | (dhp',gx',gy', pms)::entries when dhp=dhp' && gx=gx' && gy=gy' -> Some(pms) 
    | _::entries              -> assoc dhp gx gy entries
#endif

let leak   (dhp:parameters) (gx:element) (Key(b)) = b
let coerce (dhp:parameters) (gx:element) b = Key(b)

let genKey (dhp : parameters) : element * secret =
    match dhp with
    | DHP_P(dhp) -> 
        let k = CoreCrypto.dh_gen_key dhp in
        let e = k.dh_public in
        #if ideal
        #if verify
        Pi.assume(Elt(dhp.dhp,dhp.dhg,e));
        Pi.assume(HonestExponential(dhp.dhp,dhp.dhg,e));
        #else
        honest_log := (dhp,e)::!honest_log;
        #endif
        #endif
        ({dhe_nil with dhe_p = Some e}, Key (Some.v k.dh_private))
    | DHP_EC(ecdhp) ->
        let k = CoreCrypto.ec_gen_key ecdhp in
        let e = k.ec_point in
        ({dhe_nil with dhe_ec = Some e}, Key(Some.v k.ec_priv))

let serverGenDH filename dhdb minSize =
    let (dhdb,dhp) = defaultDHparams filename dhdb minSize in
    let (e,s) = genKey (DHP_P(dhp)) in 
    (Some dhdb, DHP_P dhp, e, s)

let serverGenECDH curve =
    let dhp = DHP_EC(getParams curve) in
    let (e,s) = genKey dhp in
    (None, dhp, e, s)

let clientGenExp (dhp : parameters) (gs : element) =
    let (gc,c) = genKey dhp in
    let (Key ck) = c in
    match dhp with
    | DHP_P(dhp) -> 
        let p = dhp.dh_p in
        let csk = {dh_params = dhp; dh_public = get_p gc; dh_private = Some ck} in
        let spk = get_p gs in
        let pms = CoreCrypto.dh_agreement csk spk in
        //#begin-ideal
        #if ideal
        if safeDH dhp gs gc then 
          match assoc dhp gs gc !log with
          | Some(pms) -> (gc,pms)
          | None -> 
                     let pms=PMS.sampleDH dhp gs gc in
                     log := (dhp,gs,gc,pms)::!log;
                     (gc,pms)
        else 
          (Pi.assume(DHGroup.Elt(dhp.dh_p,dhp.dh_g,pms));
          let dpms = PMS.coerceDH dhp gs gc pms in
          (gc,dpms))
        //#end-ideal 
        #else
        let dpms = PMS.coerceDH dhp (get_p gs) (get_p gc) pms in
        (gc,dpms)
        #endif
    | DHP_EC(ecp) ->
        let csk = {ec_params = ecp; ec_point = get_ec gc; ec_priv = Some ck} in
        let spk = get_ec gs in
        let pms = CoreCrypto.ecdh_agreement csk spk in
        let dpms = PMS.coerceECDH ecp (get_ec gs) (get_ec gc) pms in
        (gc, dpms)

let serverExp (dhp : parameters) (gs : element) (gc : element) (sk : secret) =
    let (Key s) = sk in
    match dhp with
    | DHP_P(dhp) -> 
        let p = dhp.dh_p in
        let ssk = {dh_params = dhp; dh_public = get_p gs; dh_private = Some s} in
        let pms = CoreCrypto.dh_agreement ssk (get_p gc) in
        //#begin-ideal
        #if ideal
        if safeDH dhp gs gc then
          match assoc dhp gs gc !log with
          | Some(pms) -> pms
          | None ->
                     let pms=PMS.sampleDH dhp gs gc in
                     log := (dhp,gs,gc,pms)::!log;
                     pms
        else
          (Pi.assume(DHGroup.Elt(dhp.dh_p,dhp.dh_g,pms));
          let dpms = PMS.coerceDH dhp gs gc pms in
          dpms)
        //#end-ideal
        #else
        let dpms = PMS.coerceDH dhp (get_p gs) (get_p gc) pms in
        dpms
        #endif
    | DHP_EC(ecp) ->
        let ssk = {ec_params = ecp; ec_point = get_ec gs; ec_priv = Some s} in
        let pms = CoreCrypto.ecdh_agreement ssk (get_ec gc) in
        let dpms = PMS.coerceECDH ecp (get_ec gs) (get_ec gc) pms in
        dpms

val serialize: element -> bytes
let serialize (e:element) : bytes =
    match e with
    | {dhe_p = Some x; dhe_ec = None } -> 
      let bl = TLSConstants.vlbytes 2 x in
      bl
    | {dhe_p = None; dhe_ec = Some p } -> 
      let ecb = CoreCrypto.ec_point_serialize p in
      let bl = TLSConstants.vlbytes 1 ecb in
      bl
    | _ -> failwith "(serialize impossible)"
