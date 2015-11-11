(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

module MiHTTPChannel

open Bytes
open MiHTTPData

type channelid = bytes
type hostname  = string

type channel_infos = {
    channelid : bytes;
    hostname  : hostname;
}

type channel

(* Channels statically bound to a hostname *)
type rchannel = channel

type auth =
| ACert of string

type cstate = {
    c_channelid   : cbytes;
    c_hostname    : hostname;
    c_credentials : string option;
}

type request = { uri: string; }

val save_channel    : channel -> cstate
val restore_channel : cstate -> channel

val cinfos : channel -> channel_infos

val connect : hostname -> channel
val request : channel -> auth option -> string -> unit
val poll    : channel -> (request * cdocument) option
