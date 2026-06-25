module Calc.Log

(**
  Ghost log with monotonic references for calc sample.
  Demonstrates wire-to-semantic correspondence pattern with full byte parsing.

  The per-message leaf codec (parse_request / serialize_response) is the
  QuackyDucky-generated parser/serializer (Calc.Wire.Generated.{Request,Response});
  this module supplies only the calc-specific stream/log framing on top of it
  (parse_requests / serialize_responses / all_parse) plus the monotonic ghost log.
**)

module L = FStar.List.Tot
open FStar.List.Tot
open Calc.Spec
module Seq = FStar.Seq
module R = FStar.ReflexiveTransitiveClosure
open FStar.Preorder

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module LP = LowParse.Spec
open Calc.Wire.Generated.OpType
open Calc.Wire.Generated.Request
open Calc.Wire.Generated.RespType
open Calc.Wire.Generated.Response

type bytes = Seq.seq U8.t

(** Per-message leaf codec, via the generated QuackyDucky parser/serializer.
    Both messages are constant 5-byte (request_parser_kind/response_parser_kind
    are strong_parser_kind 5 5), so parse on a 5-byte buffer consumes exactly 5
    and serialize produces exactly 5. **)

let parse_request (b: bytes{Seq.length b == 5}) : GTot (option request) =
  match LP.parse request_parser b with
  | Some (r, _) -> Some r
  | None -> None

let serialize_response (r: response) : GTot (b: bytes{Seq.length b == 5}) =
  LP.serialize_length response_serializer r;
  LP.serialize response_serializer r

(** Parse sequence of request bytes (each request is 5 bytes) **)
let rec parse_requests (b: bytes)
  : GTot (list request) (decreases (Seq.length b))
  =
  if Seq.length b < 5 then []
  else
    let msg_bytes = Seq.slice b 0 5 in
    let rest = Seq.slice b 5 (Seq.length b) in
    match parse_request msg_bytes with
    | None -> []  // Stop at first unparseable message
    | Some req -> req :: parse_requests rest

(** Serialize sequence of responses (each response is 5 bytes) **)
let rec serialize_responses (resps: list response)
  : GTot bytes (decreases resps)
  =
  match resps with
  | [] -> Seq.empty
  | r :: rs -> Seq.append (serialize_response r) (serialize_responses rs)

(** All messages in bytes parse successfully **)
let rec all_parse (b: bytes{Seq.length b % 5 == 0})
  : GTot prop (decreases (Seq.length b))
  =
  if Seq.length b < 5 then True
  else
    let msg_bytes = Seq.slice b 0 5 in
    let rest = Seq.slice b 5 (Seq.length b) in
    Some? (parse_request msg_bytes) /\ all_parse rest

(** Ghost log tracks wire-to-semantic state **)
noeq
type calc_log = {
  input_bytes: bytes;           // All request bytes received
  output_bytes: bytes;          // All response bytes sent
  requests: list request;       // Parsed requests
  responses: list response;     // Responses sent
  current_state: calc_stack;    // Current stack state
}

(** Initial log **)
let initial_log : calc_log = {
  input_bytes = Seq.empty;
  output_bytes = Seq.empty;
  requests = [];
  responses = [];
  current_state = [];
}

(**
  Log consistency: Full wire-to-semantic correspondence

  1. input_bytes parses to requests
  2. output_bytes serializes responses
  3. current_state matches running requests through state machine
  4. responses match state machine outputs
**)
let log_consistent (log:calc_log) : prop =
  let (state, resps) = run [] log.requests in
  // Byte length invariants (checked first so they refine the types)
  Seq.length log.input_bytes % 5 == 0 /\
  Seq.length log.output_bytes % 5 == 0 /\
  // All input bytes parse successfully
  all_parse log.input_bytes /\
  // Semantic consistency
  log.current_state == state /\
  log.responses == resps /\
  // Wire-to-semantic correspondence
  parse_requests log.input_bytes == log.requests /\
  serialize_responses log.responses `Seq.equal` log.output_bytes

(** Update the log for one processed request.

    Because the generated request type is a uniform record { op; operand }, a
    single step_log handles every operation (the dispatch happens inside step),
    replacing the six per-op step_log_* of the hand-written codec. **)
let step_log (req: request)
             (req_bytes: bytes{Seq.length req_bytes == 5})
             (resp_bytes: bytes{Seq.length resp_bytes == 5})
             (log: calc_log)
  : calc_log =
  let (new_state, response) = step log.current_state req in
  {
    input_bytes = Seq.append log.input_bytes req_bytes;
    output_bytes = Seq.append log.output_bytes resp_bytes;
    requests = log.requests @ [req];
    responses = log.responses @ [response];
    current_state = new_state;
  }

(** Single-step evolution relation **)
let log_single_step : R.binrel calc_log =
  fun log0 log1 ->
    (exists (req:request)
            (req_bytes:bytes{Seq.length req_bytes == 5})
            (resp_bytes:bytes{Seq.length resp_bytes == 5}).
       log1 == step_log req req_bytes resp_bytes log0)

(** Preorder for monotonic ghost reference **)
let log_evolves : preorder calc_log = R.closure log_single_step

(** log_evolves is reflexive **)
val lemma_log_evolves_refl (log: calc_log) : Lemma (log_evolves log log)
let lemma_log_evolves_refl log = ()

(** Helper lemma: extending run preserves consistency **)
val lemma_run_extend
  (s:calc_stack)
  (reqs:list request)
  (req:request)
  (s':calc_stack)
  (resps:list response)
  (s'':calc_stack)
  (resp:response)
  : Lemma
      (requires
        run s reqs == (s', resps) /\
        step s' req == (s'', resp))
      (ensures
        run s (reqs @ [req]) == (s'', resps @ [resp]))
      (decreases reqs)

let rec lemma_run_extend s reqs req s' resps s'' resp =
  match reqs with
  | [] -> ()
  | r :: rest ->
      let (s1, resp1) = step s r in
      let (s2, resps2) = run s1 rest in
      lemma_run_extend s1 rest req s2 resps2 s'' resp

(** Helper lemma: serialize_responses produces bytes of length 5*n **)
val lemma_serialize_responses_length
  (resps: list response)
  : Lemma (Seq.length (serialize_responses resps) == 5 * L.length resps)

let rec lemma_serialize_responses_length resps =
  match resps with
  | [] -> ()
  | r :: rest ->
      lemma_serialize_responses_length rest

(** Helper lemma: parse_requests on a single 5-byte message **)
val lemma_parse_requests_single
  (b: bytes{Seq.length b == 5})
  (req: request)
  : Lemma
      (requires parse_request b == Some req)
      (ensures parse_requests b == [req])

let lemma_parse_requests_single b req =
  Seq.lemma_eq_intro (Seq.slice b 0 5) b

(** Helper lemma: serializing a list appends the serializations **)
val lemma_serialize_responses_append
  (resps1: list response)
  (resps2: list response)
  : Lemma (serialize_responses (resps1 @ resps2) `Seq.equal`
           Seq.append (serialize_responses resps1) (serialize_responses resps2))

let rec lemma_serialize_responses_append resps1 resps2 =
  match resps1 with
  | [] -> ()
  | r :: rest ->
      lemma_serialize_responses_append rest resps2

(** Helper lemma: serialize_responses of a singleton list **)
val lemma_serialize_responses_single
  (resp: response)
  : Lemma (serialize_responses [resp] `Seq.equal` serialize_response resp)

let lemma_serialize_responses_single resp = ()

(** Helper: slicing the beginning of an append **)
val lemma_slice_append_prefix
  (s1: bytes{Seq.length s1 >= 5})
  (s2: bytes)
  : Lemma (Seq.slice (Seq.append s1 s2) 0 5 `Seq.equal` Seq.slice s1 0 5)

let lemma_slice_append_prefix s1 s2 =
  Seq.lemma_index_app1 s1 s2 0;
  Seq.lemma_index_app1 s1 s2 1;
  Seq.lemma_index_app1 s1 s2 2;
  Seq.lemma_index_app1 s1 s2 3;
  Seq.lemma_index_app1 s1 s2 4

(** Helper: appending a parseable 5-byte message extends the parse list **)
val lemma_parse_requests_append_one
  (bytes1: bytes{Seq.length bytes1 % 5 == 0})
  (msg_bytes: bytes{Seq.length msg_bytes == 5})
  (req: request)
  : Lemma
      (requires parse_request msg_bytes == Some req /\ all_parse bytes1)
      (ensures parse_requests (Seq.append bytes1 msg_bytes) == parse_requests bytes1 @ [req])
      (decreases (Seq.length bytes1))

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let rec lemma_parse_requests_append_one bytes1 msg_bytes req =
  if Seq.length bytes1 < 5 then begin
    Seq.lemma_eq_intro (Seq.append bytes1 msg_bytes) msg_bytes;
    lemma_parse_requests_single msg_bytes req
  end
  else begin
    lemma_slice_append_prefix bytes1 msg_bytes;
    FStar.Seq.Properties.lemma_slice_first_in_append bytes1 msg_bytes 5;
    let first_msg = Seq.slice bytes1 0 5 in
    let rest = Seq.slice bytes1 5 (Seq.length bytes1) in
    // all_parse bytes1 means: Some? (parse_request first_msg) /\ all_parse rest
    match parse_request first_msg with
    | Some r -> lemma_parse_requests_append_one rest msg_bytes req
  end
#pop-options

(** Helper: appending a parseable message preserves all_parse **)
val lemma_all_parse_append
  (b1: bytes{Seq.length b1 % 5 == 0})
  (b2: bytes{Seq.length b2 == 5})
  : Lemma (requires all_parse b1 /\ Some? (parse_request b2))
          (ensures all_parse (Seq.append b1 b2))
          (decreases (Seq.length b1))

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec lemma_all_parse_append b1 b2 =
  if Seq.length b1 < 5 then
    Seq.lemma_eq_intro (Seq.append b1 b2) b2
  else begin
    let msg1 = Seq.slice b1 0 5 in
    let rest1 = Seq.slice b1 5 (Seq.length b1) in
    lemma_slice_append_prefix b1 b2;
    FStar.Seq.Properties.lemma_slice_first_in_append b1 b2 5;
    lemma_all_parse_append rest1 b2
  end
#pop-options

(** Lemma: step_log preserves consistency (uniform over the request) **)
val lemma_step_log_consistent
  (req: request)
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log{log_consistent log})
  : Lemma
      (requires
        parse_request req_bytes == Some req /\
        serialize_response (snd (step log.current_state req)) `Seq.equal` resp_bytes)
      (ensures log_consistent (step_log req req_bytes resp_bytes log))

let lemma_step_log_consistent req req_bytes resp_bytes log =
  let new_log = step_log req req_bytes resp_bytes log in
  let (new_state, spec_resp) = step log.current_state req in

  // Existing state and responses
  let (old_state, old_resps) = run [] log.requests in
  assert (old_state == log.current_state);
  assert (old_resps == log.responses);

  // Semantic consistency: extend the run by one request
  lemma_run_extend [] log.requests req old_state old_resps new_state spec_resp;
  assert (run [] (log.requests @ [req]) == (new_state, old_resps @ [spec_resp]));

  // Wire-to-semantic correspondence for requests
  lemma_parse_requests_single req_bytes req;
  lemma_parse_requests_append_one log.input_bytes req_bytes req;
  assert (parse_requests new_log.input_bytes == new_log.requests);

  // Length invariants (needed for all_parse refinement)
  assert (Seq.length new_log.input_bytes % 5 == 0);
  assert (Seq.length new_log.output_bytes % 5 == 0);

  // all_parse for the new log
  lemma_all_parse_append log.input_bytes req_bytes;
  assert (all_parse new_log.input_bytes);

  // Wire-to-semantic correspondence for responses
  lemma_serialize_responses_single spec_resp;
  lemma_serialize_responses_append log.responses [spec_resp];
  assert (serialize_responses new_log.responses `Seq.equal` new_log.output_bytes)

(** Initial log is consistent **)
val lemma_initial_log_consistent : unit -> Lemma (log_consistent initial_log)
let lemma_initial_log_consistent () = ()

(** Lemma: step_log produces a single-step evolution **)
val lemma_step_log_evolves
  (req: request)
  (req_bytes: bytes{Seq.length req_bytes == 5})
  (resp_bytes: bytes{Seq.length resp_bytes == 5})
  (log: calc_log)
  : Lemma (log_single_step log (step_log req req_bytes resp_bytes log))

let lemma_step_log_evolves req req_bytes resp_bytes log = ()
