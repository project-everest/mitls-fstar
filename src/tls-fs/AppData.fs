(* Copyright (C) 2012--2015 Microsoft Research and INRIA *)

#light "off"

module AppData

open Error
open TLSError
open Bytes
open TLSInfo
open DataStream
open Range

type output_buffer =
    | NoneOBuf of stream
    | SomeOBuf of stream (* current stream *) * range * AppFragment.plain * stream (* future stream *)

type app_state = {
  app_incoming: stream;
  app_outgoing: output_buffer;
}

let inStream  (c:ConnectionInfo) state = state.app_incoming

let outStream (c:ConnectionInfo) state =
    match state.app_outgoing with
    | NoneOBuf(s) -> s
    | SomeOBuf(s,_,_,_) -> s

let init ci =
  let ki_in = mk_id ci.id_in in
  let ki_out = mk_id ci.id_out in
  let in_s = DataStream.init ci.id_in in
  let out_s = DataStream.init ci.id_out in
    {app_outgoing = (NoneOBuf(out_s));
     app_incoming = in_s
    }

// Stores appdata in the output buffer, so that it will possibly sent on the network
let writeAppData (c:ConnectionInfo) (a:app_state) (r:range) (f:AppFragment.plain) (s':stream) =
    let s = outStream c a in
    {a with app_outgoing = SomeOBuf(s,r,f,s')}

let noneOutBuf ki s = NoneOBuf(s)
let some x = Some x
// When polled, gives Dispatch the next fragment to be delivered,
// and commits to it (adds it to the output stream)
let next_fragment (c:ConnectionInfo) (a:app_state) =
    let out = a.app_outgoing in
    match out with
    | NoneOBuf(_) -> None
    | SomeOBuf (s,r,f,s') ->
        let b' = noneOutBuf c.id_out s' in
        some (r,f,{a with app_outgoing = b'})

// Clear contents from the output buffer
let clearOutBuf (c:ConnectionInfo) (a:app_state) =
    let s = outStream c a in
    {a with app_outgoing = NoneOBuf(s)}

// Gets a fragment from Dispatch, adds it to the stream and return it as a delta
let recv_fragment (ci:ConnectionInfo)  (a:app_state)  (r:range) (f:AppFragment.fragment) =
    // pre: snd a.app_incoming = None
    let s = a.app_incoming in
    let (d,ns) = AppFragment.delta ci.id_in s r f in
    let a = {a with app_incoming = ns} in
    (d,a)

let reset_outgoing (ci:ConnectionInfo) (a:app_state) (nci:ConnectionInfo) = 
  let ki = nci.id_out in
  let out_s = DataStream.init ki in
    {a with 
       app_outgoing = NoneOBuf(out_s)
    }

let reset_incoming (ci:ConnectionInfo) (a:app_state) (nci:ConnectionInfo) = 
  let ki = nci.id_in in
  let in_s = DataStream.init ki in
    {a with 
       app_incoming =  in_s
    }
