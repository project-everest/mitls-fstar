module DHGroup

open Platform.Bytes
open Platform.Error
open TLSError
open CoreCrypto
open FStar.HyperHeap


type elt = bytes

(* Use to idealize *)
type preds = | Elt of bytes * bytes * elt
type predPP = | PP of bytes * bytes

#if 1
val goodPP_log: FStar.ST.ref (list CoreCrypto.dh_params)
(* Code should be let goodPP_log = ST.alloc Nil but it misses some type annotations to 
   compile the OCaml code 
   TODO : FIXME
   *)
let goodPP_log = 
  let dummy = {
     dh_p = empty_bytes;
     dh_g = empty_bytes;
     dh_q = None;
     safe_prime = false;
  } in
  let nil = Nil in
  let dummy = dummy::nil in ST.alloc (List.Tot.tl dummy) 

let goodPP (dhp:dh_params) = List.Tot.mem dhp !goodPP_log

let pp (dhp:CoreCrypto.dh_params) : CoreCrypto.dh_params =
    goodPP_log := (dhp ::!goodPP_log);
    dhp
#endif



let genElement dhp: elt =
    let e = CoreCrypto.dh_gen_key dhp in
(*
    assume (Elt(dhp.dhp,dhp.dhg,e));
*)
    e.dh_public

let checkParams dhdb minSize p g =
    match DHDB.dh_check_params dhdb 
          DHDB.defaultDHPrimeConfidence 
          minSize p g with
    | None -> Error(AD_insufficient_security,"dh_check_params")
    | Some(res) ->
        let (dhdb,dhpar) = res in
#if ideal
        let dhpar = pp dhpar in
        let rp = dhpar.dh_p in
        let rg = dhpar.dh_g in
        if rp <> p || rg <> g then
            failwith "Trusted code returned inconsitent value"
        else
#endif
        correct (dhdb,dhpar)


let checkElement dhp (b:bytes): option elt =
    if DHDB.dh_check_element dhp b then
        (
(*
        assume(Elt(dhp.dh_p,dhp.dh_g,b));
*)
        Some(b))
    else
        None

let defaultDHparams file dhdb minSize =
    let (dhdb,dhp) = DHDB.load_default_params file dhdb minSize in
#if ideal
    let dhp = pp dhp  in
#endif
    (dhdb,dhp)
