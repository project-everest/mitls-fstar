(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module SessionDB

open TLSInfo
open FStar.Date

//CF type SessionIndex = sessionID * role * Cert.hint
//CF flattened for simpler refinements 

type StorableSession = SessionInfo * PRF.masterSecret * epoch
type SessionIndex = sessionID * role * Cert.hint

#if ideal
type entry = sessionID * role * Cert.hint * StorableSession 
type t = list entry
#else
type t
#endif

val create: config -> t
val select: t -> sessionID -> role -> Cert.hint -> option StorableSession
val insert: t -> sessionID -> role -> Cert.hint -> StorableSession -> t
val remove: t -> sessionID -> role -> Cert.hint -> t

val getAllStoredIDs: t -> list SessionIndex
