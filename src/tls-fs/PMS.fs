(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module PMS 

(* Split from KEF *) 

open Bytes
open TLSConstants
//open Seq

type rsarepr = bytes
(*private*) 
type rsaseed = {seed: rsarepr}

// To ideally avoid collisions concerns between Honest and Coerced pms we use a sum type. 
type rsapms = 
#if ideal 
  | IdealRSAPMS of rsaseed 
#endif
  | ConcreteRSAPMS of rsarepr

//#if ideal
//this function is used to determine whether idealization should be performed
let honestRSAPMS (pk:RSAKey.pk) (cv:TLSConstants.ProtocolVersion) pms = 
  match pms with 
  //| IdealRSAPMS(s)    -> true
  | ConcreteRSAPMS(s) -> false
//#endif 

let genRSA (pk:RSAKey.pk) (vc:ProtocolVersion): rsapms = 
    let verBytes = versionBytes vc in
    let rnd = Nonce.random 46 in
    let pms = verBytes @| rnd in
    #if ideal
      if RSAKey.honest pk && RSAKey.strong vc then 
        IdealRSAPMS({seed=pms}) 
      else 
    #endif
        ConcreteRSAPMS(pms)  

let coerceRSA (pk:RSAKey.pk) (cv:ProtocolVersion) b = ConcreteRSAPMS(b)
let leakRSA (pk:RSAKey.pk) (cv:ProtocolVersion) pms = 
  match pms with 
  #if ideal
  | IdealRSAPMS(_) -> Error.unexpected "pms is dishonest" //MK changed to unexpected from unreachable
  #endif
  | ConcreteRSAPMS(b) -> b 



// The trusted setup for Diffie-Hellman computations
open CoreKeys

type dhrepr = bytes
(*private*) type dhseed = {seed: dhrepr}

// To ideally avoid collisions concerns between Honest and Coerced pms we use a sum type.
type dhpms = 
#if ideal 
  | IdealDHPMS of dhseed 
#endif
  | ConcreteDHPMS of dhrepr

//#if ideal
let honestDHPMS (p:CommonDH.parameters) (g:CommonDH.element) (gx:CommonDH.element) pms = 
  match pms with 
  //| IdealDHPMS(s)    -> true
  | ConcreteDHPMS(s) -> false 
//#endif

let sampleDH dhp (gx:DHGroup.elt) (gy:DHGroup.elt) = 
    let gz = DHGroup.genElement dhp in
    #if ideal
    IdealDHPMS({seed=gz}) 
    #else
    ConcreteDHPMS(gz)  
    #endif

let coerceDH (dhp:dhparams) (gx:DHGroup.elt) (gy:DHGroup.elt) b = ConcreteDHPMS(b) 
let coerceECDH (dhe:ecdhparams) (gx:ECGroup.point) (gy:ECGroup.point) b = ConcreteDHPMS(b) 

type pms = 
  | RSAPMS of RSAKey.pk * ProtocolVersion * rsapms
  | DHPMS of CommonDH.parameters * CommonDH.element * CommonDH.element * dhpms
