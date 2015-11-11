(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module PMS

open Platform.Bytes
open TLSConstants
open Platform.Error
open TLSError
open DHGroup
open CoreCrypto

//CF some of those types are private to PMS & KEF

type rsarepr = bytes
type rsaseed = {seed: rsarepr}
type rsapms = 
#if ideal 
  | IdealRSAPMS of rsaseed 
#endif
  | ConcreteRSAPMS of rsarepr

type dhrepr = bytes
type dhseed = {seed: dhrepr}

type dhpms = 
#if ideal 
  | IdealDHPMS of dhseed 
#endif
  | ConcreteDHPMS of dhrepr

#if ideal
val honestRSAPMS: RSAKey.pk -> TLSConstants.ProtocolVersion -> rsapms -> bool
#endif

val genRSA: RSAKey.pk -> TLSConstants.ProtocolVersion -> rsapms

val coerceRSA: RSAKey.pk -> ProtocolVersion -> rsarepr -> rsapms
val leakRSA: RSAKey.pk -> ProtocolVersion -> rsapms -> rsarepr

#if ideal
val honestDHPMS: bytes -> bytes -> elt -> elt -> dhpms -> bool 
#endif

val sampleDH: dh_params -> DHGroup.elt -> DHGroup.elt -> dhpms

val coerceDH: dh_params -> DHGroup.elt -> DHGroup.elt -> DHGroup.elt -> dhpms
//val coerceECDH: ecdh_params  -> ECGroup.point -> ECGroup.point -> bytes -> dhpms

(* Used when generating key material from the MS. 
   The result must still be split into the various keys.
   Of course this method can do the splitting internally and return a record/pair *)

                               
//TODO SSL 3 specific encoding function for certificate verify

type pms = 
  | RSAPMS of RSAKey.pk * ProtocolVersion * rsapms
  | DHPMS of CommonDH.parameters * CommonDH.element * CommonDH.element * dhpms

//CF 15-04-06 to be moved to .fst, and possibly grouped
val honestRSAPMS: RSAKey.pk -> ProtocolVersion -> rsapms -> Tot bool
val honestDHPMS: CommonDH.parameters -> CommonDH.element -> CommonDH.element -> dhpms -> Tot bool
                                                                           
