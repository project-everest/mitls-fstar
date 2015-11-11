module Record

(* (optional) encryption and processing of the outer (untrusted) record format *)

open FStar.Seq
open Platform.Bytes
open Platform.Error

open TLSError
open TLSInfo
open TLSConstants
open Range

// Consider merging this module with Content?

// ------------------------outer packet format -------------------------------

type header = b:lbytes 5

let makePacket ct ver (data: b:bytes { repr_bytes (length b) <= 2}) =
    let bct  = ctBytes ct in
    let bver = versionBytes ver in
    let bl   = bytes_of_int 2 (length data) in
    let hdr: header = bct @| bver @| bl in
    hdr @| data

let parseHeader (hdr:header) =
    let (ct1,b4) = split hdr 1 in
    let (pv2,len2) = split b4 2 in
    match parseCT ct1 with
    | Error(z) -> Error(z)
    | Correct(ct) ->
    match TLSConstants.parseVersion pv2 with
    | Error(z) -> Error(z)
    | Correct(pv) ->
    let len = int_of_bytes len2 in
    if len <= 0 || len > max_TLSCipher_fragment_length then
        Error(AD_illegal_parameter, perror __SOURCE_FILE__ __LINE__ "Wrong frgament length")
    else
        correct(ct,pv,len)

(* TODO, possibly a parameter from dispatch *)
assume val is_Null: id -> Tot bool

// hopefully we only care about the writer, not the cn state
// the postcondition is of the form
//   authId i ==> f is added to the writer log
let recordPacketOut i (wr:StatefulLHAE.writer i) pv f =
    let ct, rg = Content.ct_rg i f in
    let payload =
      if is_Null i
      then Content.repr i f
      else
        let ad = StatefulPlain.makeAD i ct in
        StatefulLHAE.encrypt #i #ad #rg wr f in
    makePacket ct pv payload

(* TODO
let recordPacketIn i (rd:StatefulLHAE.reader i) ct payload =
    if is_Null i
    then
      let rg = Range.point (length payload) in
      let msg = Content.mk_fragment i ct rg payload in
      Correct (rg,msg)
    else
      let ad = StatefulPlain.makeAD i ct in
      let r = StatefulLHAE.decrypt #i #ad rd payload in
      match r with
      | Some f -> Correct f
      | None   -> Error("bad decryption")
*)




(*
// replaced by StatefulLHAE's state?
type ConnectionState =
    | NullState
    | SomeState of TLSFragment.history * StatefulLHAE.state

let someState (e:epoch) (rw:rw) h s = SomeState(h,s)

type sendState = ConnectionState
type recvState = ConnectionState

let initConnState (e:epoch) (rw:rw) s =
  let i = mk_id e in
  let h = TLSFragment.emptyHistory e in
  someState e rw h s

let nullConnState (e:epoch) (rw:rw) = NullState
*)

(*
let history (e:epoch) (rw:rw) s =
    match s with
    | NullState ->
        let i = mk_id e in
        TLSFragment.emptyHistory e
    | SomeState(h,_) -> h
*)
