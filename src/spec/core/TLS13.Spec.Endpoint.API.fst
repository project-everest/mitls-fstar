module TLS13.Spec.Endpoint.API

module B = TLS13.Bytes
module CL = TLS13.ConnectionLog
module CS = TLS13.Spec.StateMachine
module M = TLS13.Messages
module Seq = FStar.Seq

(**
  Core semantic endpoint output vocabulary.

  [local_output] is the role-neutral, representation-independent local (i.e.
  non-network) output surface of an endpoint state machine: the application
  bytes an endpoint delivers to its caller.  Concrete status/response enums and
  machine-width lengths remain implementation details.
 **)

type local_output =
  | AppOut: bytes:B.bytes -> local_output

let local_output_bytes (out:local_output) : B.bytes =
  match out with
  | AppOut bytes -> bytes

let rec local_outputs_bytes (outs:list local_output) : Tot (list B.bytes)
  (decreases outs)
=
  match outs with
  | [] -> []
  | out :: rest -> local_output_bytes out :: local_outputs_bytes rest

let local_outputs_app_bytes (outs:list local_output) : B.bytes =
  CL.concat_bytes (local_outputs_bytes outs)

let conn_event_app_received_delta (ev:CS.conn_event) : list B.bytes =
  match ev with
  | CS.ConnNetworkEvent msg ->
    (match msg.CL.message_direction, msg.CL.message_value with
     | CL.Received, M.TlsApplicationData bytes -> [bytes]
     | _, _ -> [])
  | CS.ConnProtectedHandshake _ -> []
  | CS.ConnCleartextHandshake _ -> []
  | CS.ConnLocalEvent local ->
    (match local with
     | CS.LocalDeliverApplicationData bytes -> [bytes]
     | _ -> [])

let local_outputs_match
  (ev:CS.conn_event)
  (outs:list local_output)
  : prop =
  Seq.equal
    (local_outputs_app_bytes outs)
    (CL.concat_bytes (conn_event_app_received_delta ev))

noextract
let local_outputs_of_app_bytes (bytes:B.bytes) : GTot (list local_output) =
  if B.length bytes == 0 then [] else [AppOut bytes]

let lemma_local_outputs_of_app_bytes_exact (bytes:B.bytes)
  : Lemma
      (ensures Seq.equal
        (local_outputs_app_bytes (local_outputs_of_app_bytes bytes))
        bytes)
=
  if B.length bytes == 0 then (
    Seq.lemma_eq_intro bytes B.empty
  ) else (
    Seq.append_empty_r bytes
  )
