(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module Alert

open Error
open TLSError
open TLSInfo
open Range

[<NoEquality;NoComparison>]
type pre_al_state
type state = pre_al_state

type ALFragReply =
    | EmptyALFrag
    | ALFrag of range * HSFragment.fragment
    | LastALFrag of range * HSFragment.fragment * alertDescription
    | LastALCloseFrag of range * HSFragment.fragment

[<NoEquality;NoComparison>]
type alert_reply =
    | ALAck of state
    | ALFatal of alertDescription * state
    | ALWarning of alertDescription * state
    | ALClose_notify of state

val alertBytes: alertDescription -> Bytes.bytes
val parseAlert: Bytes.bytes -> Result<alertDescription>

val init: ConnectionInfo -> state

val send_alert: ConnectionInfo -> state -> alertDescription -> state

val next_fragment: ConnectionInfo -> state -> (ALFragReply * state) 

val recv_fragment: ConnectionInfo -> state -> range -> HSFragment.fragment -> Result<alert_reply>

val is_incoming_empty: ConnectionInfo -> state -> bool
val reset_incoming: ConnectionInfo -> state -> ConnectionInfo -> state
val reset_outgoing: ConnectionInfo -> state -> ConnectionInfo -> state

