module Alert

open FStar.Heap
open FStar.Seq
open FStar.Error
open FStar.Bytes

open TLSError
open TLSConstants
open TLSInfo
open Parse
open Mem

module Range = Range
open Range

//16-05-29 not much protocol left; consider merging with TLSError

(* Conversions *)

val alertBytes: alert -> Tot (lbytes 2)
let alertBytes = 
  LowParseWrappers.wrap_serializer32_constant_length alert_serializer32 2 ()

val parse: pinverse_t alertBytes 
// eta-expansion required for kremlin extraction
let parse x = 
  LowParseWrappers.wrap_parser32_constant_length 
    alert_serializer32 2 () alert_parser32
    "" //(perror __SOURCE_FILE__ __LINE__ "")
    x

let alertBytes_then_parse (a:alert) : Lemma (parse (alertBytes a) == Correct a) = 
  LowParseWrappers.lemma_inverse_serializer32_parser32_constant_length alert_serializer32 2 () alert_parser32 "" a
  
let parse_then_alertBytes (x:lbytes 2) : 
  Lemma (
    match parse x with
    | Correct a -> alertBytes a `equal` x
    | _ -> True) = 
  LowParseWrappers.lemma_pinverse_serializer32_parser32_constant_length alert_serializer32 2 () alert_parser32 "" x


(* 16-05-29 now integrated with the record layer, for simplicity

(*** alert protocol ***)

// TLS 1.2 and earlier miTLS supported alert fragmentation;
// TLS 1.3 and miTLS* forbid it (a slight deviation from TLS 1.2):
// each alert fragment carries exactly a 2-byte alert.

// outgoing buffer: either empty or a complete alert

type fragment = f:lbytes 2 { exists ad. f = alertBytes ad }

type buffer = option fragment

//* moving to stateful private state; NS: should it be abstract?
private type state = | State:
  #region: rid ->
  outgoing: rref region buffer -> (* empty if nothing to be sent *)
  state

let region s = s.region

val init: r0:rid -> ST state
  (requires (fun h -> True))
  (ensures (fun h0 s h1 ->
    modifies Set.empty h0 h1 /\
    extends (State?.region s) r0 /\
    fresh_region (State?.region s) h0 h1))

let init r0 =
  let r = new_region r0 in
  State (ralloc r None)

// ---------------- outgoing alerts -------------------
val send : s:state -> ad:alertDescription{isFatal ad} -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> modifies_one (region s) h0 h1))
let send (State b) (ad:alertDescription{isFatal ad}) =
    if !b = None
    then b := Some (alertBytes ad)

    (* alert generation is underspecified, so we just ignore subsequent requests *)
    (* FIXED? We should only send fatal alerts. Right now we'll interpret any sent alert
       as fatal, and so will close the connection afterwards. *)
    (* Note: we only support sending one (fatal) alert in the whole protocol execution
       (because we'll tell dispatch an alert has been sent when the buffer gets empty)
       So we only add an alert on an empty buffer (we don't enqueue more alerts) *)

val next_fragment: s:state -> ST (option alertDescription)
  (requires (fun _ -> True))
  (ensures (fun h0 r h1 -> modifies_one (State?.region s) h0 h1))

let next_fragment (State b) =
  match !b with
  | None -> None
  | Some f -> b:= None;
             (match parse f with | Correct ad -> Some ad | Error _ -> None)

// ---------------- incoming alerts -------------------

// no more recv_fragment as alerts are now parsed by Content.

let reset s = s.outgoing := None   // we silently discard any unsent alert.

*)
