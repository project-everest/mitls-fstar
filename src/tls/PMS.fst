module PMS

(* Split from KEF *)

open FStar.HyperStack.All

open FStar.Bytes
open TLSConstants
open CoreCrypto

let ideal = Flags.ideal_PMS // controls idealization of PMS.


type rsarepr = bytes
(*private*)
type rsaseed = {seed: rsarepr}

// To ideally avoid collisions concerns between Honest and Coerced pms we use a sum type.
type rsapms =
//#if ideal
  | IdealRSAPMS of rsaseed
//#endif
  | ConcreteRSAPMS of rsarepr

//#if ideal
//this function is used to determine whether idealization should be performed
let honestRSAPMS (pk:RSAKey.pk) (cv:TLSConstants.protocolVersion) pms =
  match pms with
  | IdealRSAPMS(s)    -> true
  | ConcreteRSAPMS(s) -> false
//#endif

let genRSA (pk:RSAKey.pk) (vc:protocolVersion): EXT rsapms =
    let verBytes = versionBytes vc in
    let rnd = CoreCrypto.random 46 in
    let pms = verBytes @| rnd in
    if ideal && RSAKey.honest pk && RSAKey.strong vc then
        IdealRSAPMS({seed=pms})
    else
        ConcreteRSAPMS(pms)

let coerceRSA (pk:RSAKey.pk) (cv:protocolVersion) b = ConcreteRSAPMS(b)
let leakRSA (pk:RSAKey.pk) (cv:protocolVersion) pms =
  match pms with
//  #if ideal
  | IdealRSAPMS(_) -> FStar.Error.unexpected "pms is dishonest" //MK changed to unexpected from unreachable
//  #endif
  | ConcreteRSAPMS(b) -> b



// The trusted setup for Diffie-Hellman computations
//open CoreCrypto.Keys

type dhrepr = bytes
(*private*) type dhseed = {seed: dhrepr}

// To ideally avoid collisions concerns between Honest and Coerced pms we use a sum type.
type dhpms =
//#if ideal
  | IdealDHPMS of dhseed
//#endif
  | ConcreteDHPMS of dhrepr

//#if ideal
let honestDHPMS (g:CommonDH.group) (gx:CommonDH.share g) (gy:CommonDH.share g) pms =
  match pms with
  | IdealDHPMS(s)    -> true
  | ConcreteDHPMS(s) -> false
//#endif

let coerceDH (g:CommonDH.group) (gx:CommonDH.share g) (gy:CommonDH.share g) b =
  ConcreteDHPMS(b)

type pms =
  | RSAPMS of RSAKey.pk * protocolVersion * rsapms
  | DHPMS: g:CommonDH.group -> CommonDH.share g -> CommonDH.share g -> dhpms -> pms
  | DummyPMS

let honestPMS = function
  | RSAPMS (pk, pv, pms) -> honestRSAPMS pk pv pms
  | DHPMS g gx gy pms -> honestDHPMS g gx gy pms
  | DummyPMS -> false
