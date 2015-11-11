(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module DHGroup

open Bytes
open Error
open TLSError
open CoreKeys

type elt = bytes

(* Use to idealize *)
type preds = | Elt of bytes * bytes * elt
type predPP = | PP of bytes * bytes

#if ideal // JK : used to be 1, not accepted by VS
let goodPP_log : ref<list<dhparams>> = 
      ref []

let goodPP dhp =  List.mem dhp !goodPP_log

let pp (dhp:CoreKeys.dhparams) : CoreKeys.dhparams =
    goodPP_log := (dhp ::!goodPP_log); 
    dhp
#endif



let genElement dhp: elt =
    let (_, e) = CoreDH.gen_key dhp in
(*
    assume (Elt(dhp.dhp,dhp.dhg,e));
*)
    e

let checkParams dhdb minSize p g =
    match CoreDH.check_params dhdb DHDB.defaultDHPrimeConfidence minSize p g with
    | Error(x) -> Error(AD_insufficient_security,x)
    | Correct(res) ->
        let (dhdb,dhpar) = res in
#if ideal
        let dhpar = pp dhpar in
        let rp = dhpar.dhp in
        let rg = dhpar.dhg in
        if rp <> p || rg <> g then
            failwith "Trusted code returned inconsitent value"
        else
#endif
        correct (dhdb,dhpar)


let checkElement dhp (b:bytes): option<elt> =
    if CoreDH.check_element dhp b then
        (
(*
        assume(Elt(dhp.dhp,dhp.dhg,b));
*)
        Some(b))
    else
        None

let defaultDHparams file dhdb minSize =
    let (dhdb,dhp) = DHDBManager.load_default_params file dhdb minSize in
#if ideal
    let dhp = pp dhp  in
#endif
    (dhdb,dhp)
