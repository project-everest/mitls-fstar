(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module TLSExtensions

open Bytes
open Error
open TLSError
open TLSConstants
open TLSInfo

// Following types only used in handshake
type clientExtension
type serverExtension

// Client side
val prepareClientExtensions: config -> ConnectionInfo -> cVerifyData -> list<clientExtension>
val clientExtensionsBytes: list<clientExtension> -> bytes
val parseServerExtensions: bytes -> Result<(list<serverExtension>)>
val negotiateClientExtensions: list<clientExtension> -> list<serverExtension> -> bool -> cipherSuite -> Result<negotiatedExtensions>

// Server side
val parseClientExtensions: bytes -> cipherSuites -> Result<(list<clientExtension>)>
val negotiateServerExtensions: list<clientExtension> -> config -> cipherSuite -> (cVerifyData * sVerifyData) -> bool -> (list<serverExtension> * negotiatedExtensions)
val serverExtensionsBytes: list<serverExtension> -> bytes

// Extension-specific
val checkClientRenegotiationInfoExtension: config -> list<clientExtension> -> cVerifyData -> bool
val checkServerRenegotiationInfoExtension: config -> list<serverExtension> -> cVerifyData -> sVerifyData -> bool

#if TLSExt_sessionHash
val hasExtendedMS: negotiatedExtensions -> bool
#endif

#if TLSExt_extendedPadding
val hasExtendedPadding: id -> bool
#endif

//CF what are those doing here? relocate? 
//AP Partially relocate to TLSConstants, partially implement the mandatory signature extension, and embed them there. Maybe TODO before v1.0?
val sigHashAlgBytes: Sig.alg -> bytes
val parseSigHashAlg: bytes -> Result<Sig.alg>
val sigHashAlgListBytes: list<Sig.alg> -> bytes
val parseSigHashAlgList: bytes -> Result<list<Sig.alg>>
val default_sigHashAlg: ProtocolVersion -> cipherSuite -> list<Sig.alg>
val sigHashAlg_contains: list<Sig.alg> -> Sig.alg -> bool
val cert_type_list_to_SigHashAlg: list<certType> -> ProtocolVersion -> list<Sig.alg>
val cert_type_list_to_SigAlg: list<certType> -> list<sigAlg>
val sigHashAlg_bySigList: list<Sig.alg> -> list<sigAlg> -> list<Sig.alg>
