module TLS13.Impl.Endpoint.Types

module SZ = FStar.SizeT

(**
  Role-neutral extraction-facing step shapes shared by client and server
  endpoint APIs. Endpoint-specific modules alias these types so their public
  names remain stable.
**)

type endpoint_status =
  | StepOk
  | NeedMoreInput
  | DecodeError
  | IllegalTransition
  | OutputBufferTooSmall
  | ConnectionFailed

type endpoint_response = {
  network_out_len: SZ.t;
  app_out_len: SZ.t;
  status: endpoint_status;
}

type endpoint_buffer_response = {
  response: endpoint_response;
  consumed_len: SZ.t;
}
