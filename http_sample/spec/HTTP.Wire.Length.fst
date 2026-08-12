module HTTP.Wire.Length

(**
  Hand-written IETF HTTP/1.1 wire format — the *Content-Length delimited*
  profile — as a `Common.WireFormat.wire_format` instance.

  Companion of `HTTP.Wire.Chunked`.  A GET exchange with a Content-Length body
  reduces to three wire messages:

    * `Msg_request target`   — "GET " target " HTTP/1.1" CRLF CRLF
    * `Msg_response code len` — response head declaring the body length:
         "HTTP/1.1 " ddd " " CRLF "Content-Length: " dddddddd CRLF CRLF
    * `Msg_body payload`     — a raw body segment.

  ── The body boundary (cf. TFTP DATA) ───────────────────────────────────────
  Unlike a chunk, a Content-Length body segment carries NO length marker on the
  wire — its length is supplied out of band (the head's Content-Length, consumed
  one transport read at a time).  So `Msg_body` is *datagram-delimited*: exactly
  like TFTP's DATA packet, `http_parse` reads "all remaining bytes" as the body
  and leaves an EMPTY residual, and we deliberately do NOT instantiate the
  OPTIONAL `Common.WireFormat.wire_format_stream_laws` (a body segment is not a
  strong/prefix parser).  The driver feeds exactly one segment per read, so
  buffer-end == message-end, which is what `wf_parse_serialize_exact` needs.

  Because a stateless parser cannot otherwise tell a bare body segment from a
  request/response line, a `Msg_body` payload is refined by `body_ok`: its first
  byte (if any) is neither 'G' (0x47) nor 'H' (0x48), so it can never collide
  with the "GET "/"HTTP/1.1 " markers.  This is the direct analog of TFTP's
  `zero_free` refinement on its NUL-terminated fields — a documented modeling
  restriction that makes the union unambiguously parseable.
**)

module Seq = FStar.Seq
module SP  = FStar.Seq.Properties
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module TCP = Common.TCP
module WF  = Common.WireFormat
module W   = HTTP.Wire.Common

(* ─── Fixed literals ───────────────────────────────────────────────────────── *)
let lit_get      : TCP.bytes = W.lit [0x47uy;0x45uy;0x54uy;0x20uy]
let req_tail     : TCP.bytes = W.lit [0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy;0x0Duy;0x0Auy]
let resp_prefix  : TCP.bytes = W.lit [0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x20uy]
let cl_tail_pre  : TCP.bytes = W.lit [0x20uy;0x0Duy;0x0Auy;0x43uy;0x6Fuy;0x6Euy;0x74uy;0x65uy;0x6Euy;0x74uy;0x2Duy;0x4Cuy;0x65uy;0x6Euy;0x67uy;0x74uy;0x68uy;0x3Auy;0x20uy]  (* " \r\nContent-Length: " *)
let cl_tail_post : TCP.bytes = W.lit [0x0Duy;0x0Auy;0x0Duy;0x0Auy]  (* "\r\n\r\n" *)

(* Literals for a *real* origin-server request line carrying a Host header (and
   Connection: close so the peer closes after the response, delimiting the body
   for a read-to-EOF client).  Layout:
     "GET " target " HTTP/1.1\r\nHost: " host "\r\nConnection: close\r\n\r\n"  *)
let req_host_mid  : TCP.bytes = W.lit [0x20uy;0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy;0x48uy;0x6Fuy;0x73uy;0x74uy;0x3Auy;0x20uy]  (* " HTTP/1.1\r\nHost: " *)
let req_host_tail : TCP.bytes = W.lit [0x0Duy;0x0Auy;0x43uy;0x6Fuy;0x6Euy;0x6Euy;0x65uy;0x63uy;0x74uy;0x69uy;0x6Fuy;0x6Euy;0x3Auy;0x20uy;0x63uy;0x6Cuy;0x6Fuy;0x73uy;0x65uy;0x0Duy;0x0Auy;0x0Duy;0x0Auy]  (* "\r\nConnection: close\r\n\r\n" *)

(* ─── Message union ────────────────────────────────────────────────────────── *)
type status_code = c:U16.t{100 <= U16.v c /\ U16.v c < 1000}
type content_len = n:nat{n < W.max_len8}

let body_ok (p:TCP.bytes) : bool =
  Seq.length p = 0 || (Seq.index p 0 <> 0x47uy && Seq.index p 0 <> 0x48uy)

type body_payload = p:TCP.bytes{ body_ok p }

noeq
type http_message =
  | Msg_request  : target:W.token -> http_message
  | Msg_response : code:status_code -> len:content_len -> http_message
  | Msg_body     : payload:body_payload -> http_message

(* ─── Serialization ────────────────────────────────────────────────────────── *)
let ser_request (target:W.token) : TCP.bytes =
  Seq.append lit_get (Seq.append target (Seq.cons W.bSP req_tail))

(* A real origin-server GET request line with a Host header. *)
let ser_request_host (target host:W.token) : TCP.bytes =
  Seq.append lit_get
    (Seq.append target
      (Seq.append req_host_mid
        (Seq.append host req_host_tail)))

(* Client POST request HEAD carrying a variable-width Content-Length.  Layout:
       "POST " target " HTTP/1.1\r\nContent-Length: " <digits(len)> "\r\n\r\n"
   The request body (len bytes) is sent immediately after this head.  Mirrors
   `ser_response`'s variable-width digit run (`W.enc_dec_var`) but on the request
   side; the closing `cl_tail_post` ("\r\n\r\n") is shared with the response. *)
let lit_post : TCP.bytes = W.lit [0x50uy;0x4Fuy;0x53uy;0x54uy;0x20uy]  (* "POST " *)
let req_post_mid : TCP.bytes =
  W.lit [0x20uy;0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy;
         0x43uy;0x6Fuy;0x6Euy;0x74uy;0x65uy;0x6Euy;0x74uy;0x2Duy;0x4Cuy;0x65uy;0x6Euy;
         0x67uy;0x74uy;0x68uy;0x3Auy;0x20uy]   (* " HTTP/1.1\r\nContent-Length: " *)

let ser_request_post (target:W.token) (len:content_len) : TCP.bytes =
  Seq.append lit_post
    (Seq.append target
      (Seq.append req_post_mid
        (Seq.append (W.enc_dec_var len) cl_tail_post)))

let ser_response (code:status_code) (len:content_len) : TCP.bytes =
  Seq.append resp_prefix
    (Seq.append (W.enc_dec3 (U16.v code))
      (Seq.append cl_tail_pre
        (Seq.append (W.enc_dec8 len) cl_tail_post)))

let ser_body (p:body_payload) : TCP.bytes = p

let http_serialize (m:http_message) : GTot TCP.bytes =
  match m with
  | Msg_request target   -> ser_request target
  | Msg_response code len -> ser_response code len
  | Msg_body p           -> ser_body p

(* ─── Parsing ──────────────────────────────────────────────────────────────── *)
let parse_request (input:TCP.bytes) : GTot (WF.parse_result http_message) =
  if Seq.length input < 4 then None else
  let rest0 = Seq.slice input 4 (Seq.length input) in
  match W.split_sp rest0 with
  | None -> None
  | Some (target, tl) ->
    if W.space_free target && W.bseq_eq tl req_tail
    then Some (Msg_request target, Seq.empty)
    else None

(* ─── Headers-tolerant request-line parse (receive side) ───────────────────── *)
(* "HTTP/1.1\r\n" — the request-line version token immediately following the
   target's trailing space.  A REAL client (curl, browsers) sends the mandatory
   request line then one-or-more header lines and a terminating CRLFCRLF:
       "GET " target " HTTP/1.1\r\n"  header-lines*  "\r\n"
   `parse_request` (above) accepts ONLY the header-less internal form; this
   `parse_request_line` is the tolerant companion used on a server to parse a
   real client's request head.  It recovers the space-free `target` between the
   "GET " prefix and the " HTTP/1.1\r\n" version token and deliberately IGNORES
   every byte after that token (all headers), returning just the target.  *)
let req_ver : TCP.bytes =
  W.lit [0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy]  (* "HTTP/1.1\r\n" *)

let parse_request_line (input:TCP.bytes) : GTot (option W.token) =
  if Seq.length input < 4 then None
  else if not (W.bseq_eq (Seq.slice input 0 4) lit_get) then None
  else
    let rest0 = Seq.slice input 4 (Seq.length input) in
    match W.split_sp rest0 with
    | None -> None
    | Some (target, tl) ->
      if W.space_free target
         && Seq.length tl >= 10
         && W.bseq_eq (Seq.slice tl 0 10) req_ver
      then Some target
      else None

(* Method-aware request-line parse.  A real client's request line is
       METHOD SP target SP "HTTP/1.1" CRLF   header-lines*   CRLF
   (`parse_request_line` above hard-codes METHOD = "GET").  This recovers BOTH
   the method token (the bytes before the first space) and the target token (the
   space-free bytes before the second space), then requires the version token,
   ignoring every byte after it (all headers).  Both returned components are
   space-free by construction of `split_sp`.  Used on a server to accept `POST`
   (and any other method) from a real peer. *)
let parse_request_line_m (input:TCP.bytes) : GTot (option (TCP.bytes & TCP.bytes)) =
  match W.split_sp input with
  | None -> None
  | Some (meth, rest0) ->
    (match W.split_sp rest0 with
     | None -> None
     | Some (target, tl) ->
       if Seq.length tl >= 10 && W.bseq_eq (Seq.slice tl 0 10) req_ver
       then Some (meth, target)
       else None)

(* This definition had been left at F*'s default rlimit of 5, which it only just
   fit under Z3 4.13.3; under 4.15.3 the query is cancelled and the first
   unproved obligation surfaces as a subtyping failure on `U16.uint_to_t code`.
   Nothing is wrong with the proof — it just needs a realistic budget. *)
#push-options "--z3rlimit 20"
let parse_response (input:TCP.bytes) : GTot (WF.parse_result http_message) =
  if Seq.length input < 9 then None else
  let rest0 = Seq.slice input 9 (Seq.length input) in
  if Seq.length rest0 < 3 then None else
  let codeb = Seq.slice rest0 0 3 in
  if not (W.dec3_ok codeb) then None else
  let code = W.dec_dec3 codeb in
  let rest1 = Seq.slice rest0 3 (Seq.length rest0) in
  if Seq.length rest1 < 19 then None else
  if not (W.bseq_eq (Seq.slice rest1 0 19) cl_tail_pre) then None else
  let rest2 = Seq.slice rest1 19 (Seq.length rest1) in
  if Seq.length rest2 < 8 then None else
  let lenb = Seq.slice rest2 0 8 in
  if not (W.dec8_ok lenb) then None else
  let len = W.dec_dec8 lenb in
  let tl = Seq.slice rest2 8 (Seq.length rest2) in
  if 100 <= code && code < 1000 && len < W.max_len8 && W.bseq_eq tl cl_tail_post
  then Some (Msg_response (U16.uint_to_t code) len, Seq.empty)
  else None
#pop-options

let parse_body (input:TCP.bytes) : GTot (WF.parse_result http_message) =
  if body_ok input then Some (Msg_body input, Seq.empty) else None

let http_parse (input:TCP.bytes) : GTot (WF.parse_result http_message) =
  if Seq.length input >= 4 && W.bseq_eq (Seq.slice input 0 4) lit_get
  then parse_request input
  else if Seq.length input >= 9 && W.bseq_eq (Seq.slice input 0 9) resp_prefix
  then parse_response input
  else parse_body input

(* ─── Disambiguation helper ────────────────────────────────────────────────── *)
let lemma_bseq_neq_first (a b:TCP.bytes)
  : Lemma (requires Seq.length a > 0 /\ Seq.length b > 0 /\ Seq.index a 0 =!= Seq.index b 0)
          (ensures not (W.bseq_eq a b))
= W.lemma_bseq_eq a b

(* ─── The round-trip law ───────────────────────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let lemma_http_parse_serialize_exact (m:http_message)
  : Lemma
      (ensures
        exists parsed.
          http_parse (http_serialize m) == Some (parsed, Seq.empty) /\
          parsed == m)
= match m with
  | Msg_request target ->
    let input = ser_request target in
    SP.append_slices lit_get (Seq.append target (Seq.cons W.bSP req_tail));
    W.lemma_bseq_eq_refl lit_get;
    W.split_sp_append target req_tail;
    W.lemma_bseq_eq_refl req_tail;
    assert (http_parse input == Some (Msg_request target, Seq.empty))
  | Msg_response code len ->
    let input = ser_response code len in
    let x0 = Seq.append (W.enc_dec3 (U16.v code))
               (Seq.append cl_tail_pre (Seq.append (W.enc_dec8 len) cl_tail_post)) in
    let x1 = Seq.append cl_tail_pre (Seq.append (W.enc_dec8 len) cl_tail_post) in
    let x2 = Seq.append (W.enc_dec8 len) cl_tail_post in
    (* request prefix fails ('H' <> 'G'); response prefix matches *)
    SP.append_slices resp_prefix x0;
    Seq.lemma_index_app1 resp_prefix x0 0;
    lemma_bseq_neq_first (Seq.slice input 0 4) lit_get;
    W.lemma_bseq_eq_refl resp_prefix;
    let rest0 = Seq.slice input 9 (Seq.length input) in
    assert (rest0 == x0);
    SP.append_slices (W.enc_dec3 (U16.v code))
      (Seq.append cl_tail_pre (Seq.append (W.enc_dec8 len) cl_tail_post));
    W.lemma_dec3_roundtrip (U16.v code);
    let rest1 = Seq.slice rest0 3 (Seq.length rest0) in
    assert (rest1 == x1);
    SP.append_slices cl_tail_pre (Seq.append (W.enc_dec8 len) cl_tail_post);
    W.lemma_bseq_eq_refl cl_tail_pre;
    let rest2 = Seq.slice rest1 19 (Seq.length rest1) in
    assert_norm (Seq.length cl_tail_pre == 19);
    assert (rest2 == x2);
    SP.append_slices (W.enc_dec8 len) cl_tail_post;
    W.lemma_dec8_roundtrip len;
    W.lemma_bseq_eq_refl cl_tail_post;
    assert (http_parse input == Some (Msg_response code len, Seq.empty))
  | Msg_body p ->
    let input = ser_body p in
    (* body branch: neither prefix matches (first byte, if any, is not 'G'/'H') *)
    (if Seq.length input >= 4 then begin
       assert (Seq.index p 0 <> 0x47uy /\ Seq.index p 0 <> 0x48uy);
       lemma_bseq_neq_first (Seq.slice input 0 4) lit_get
     end);
    (if Seq.length input >= 9 then
       lemma_bseq_neq_first (Seq.slice input 0 9) resp_prefix);
    assert (http_parse input == Some (Msg_body p, Seq.empty))
#pop-options

(* ─── Body parse-correspondence (receive side) ─────────────────────────────── *)
(* A body_ok segment parses to exactly the Msg_body carrying it, with no residual.
   This is the receive-side analog of `lemma_parse_chunk_parts` (Chunked): the
   driver reads `len` body bytes into a buffer and this certifies the decode. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let lemma_parse_body_exact (p:TCP.bytes)
  : Lemma (requires body_ok p)
          (ensures http_parse p == Some (Msg_body p, Seq.empty #U8.t))
= (if Seq.length p >= 4 then begin
     assert (Seq.index p 0 <> 0x47uy /\ Seq.index p 0 <> 0x48uy);
     lemma_bseq_neq_first (Seq.slice p 0 4) lit_get
   end);
  (if Seq.length p >= 9 then
     lemma_bseq_neq_first (Seq.slice p 0 9) resp_prefix)
#pop-options

(* ─── Variable-width Content-Length response head (RFC 9112 §6.2) ───────────────
   The fixed `ser_response`/`parse_response` above pad Content-Length to 8 digits
   ("00000025") and cap it at 10^8.  A real origin server emits the minimal-width
   canonical decimal ("Content-Length: 25") and bodies may exceed 10^8.  These
   companions mirror the fixed pair but use the variable-width decimal codec
   (`W.enc_dec_var` / `W.dec_dec_var`), lifting the cap to an arbitrary `nat`
   while preserving an EXACT round-trip.  The trailing CRLFCRLF's first byte
   (0x0D) is not a digit, so the maximal decimal run cuts exactly at the length. *)
let ser_response_var (code:status_code) (len:nat) : TCP.bytes =
  Seq.append resp_prefix
    (Seq.append (W.enc_dec3 (U16.v code))
      (Seq.append cl_tail_pre
        (Seq.append (W.enc_dec_var len) cl_tail_post)))

(* Same story as `parse_response` above: left at the default rlimit of 5, which
   it only just fit under Z3 4.13.3. *)
#push-options "--z3rlimit 20"
let parse_response_var (input:TCP.bytes) : GTot (option (status_code & nat)) =
  if Seq.length input < 9 then None else
  if not (W.bseq_eq (Seq.slice input 0 9) resp_prefix) then None else
  let rest0 = Seq.slice input 9 (Seq.length input) in
  if Seq.length rest0 < 3 then None else
  let codeb = Seq.slice rest0 0 3 in
  if not (W.dec3_ok codeb) then None else
  let code = W.dec_dec3 codeb in
  let rest1 = Seq.slice rest0 3 (Seq.length rest0) in
  if Seq.length rest1 < 19 then None else
  if not (W.bseq_eq (Seq.slice rest1 0 19) cl_tail_pre) then None else
  let rest2 = Seq.slice rest1 19 (Seq.length rest1) in
  let dl = W.dec_prefix_len rest2 in
  if dl = 0 then None else                          (* 1*DIGIT: at least one digit *)
  let lenb = Seq.slice rest2 0 dl in
  let tl = Seq.slice rest2 dl (Seq.length rest2) in
  W.lemma_dec_prefix_all_dec rest2;                 (* all_dec lenb (= slice rest2 0 dl) *)
  let len = W.dec_dec_var lenb in
  if 100 <= code && code < 1000 && W.bseq_eq tl cl_tail_post
  then Some (U16.uint_to_t code, len)
  else None
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"
let lemma_parse_ser_response_var (code:status_code) (len:nat)
  : Lemma (ensures parse_response_var (ser_response_var code len) == Some (code, len))
= let input = ser_response_var code len in
  let x0 = Seq.append (W.enc_dec3 (U16.v code))
             (Seq.append cl_tail_pre (Seq.append (W.enc_dec_var len) cl_tail_post)) in
  let x1 = Seq.append cl_tail_pre (Seq.append (W.enc_dec_var len) cl_tail_post) in
  let x2 = Seq.append (W.enc_dec_var len) cl_tail_post in
  SP.append_slices resp_prefix x0;
  W.lemma_bseq_eq_refl resp_prefix;
  let rest0 = Seq.slice input 9 (Seq.length input) in
  assert (rest0 == x0);
  SP.append_slices (W.enc_dec3 (U16.v code)) x1;
  W.lemma_dec3_roundtrip (U16.v code);
  let rest1 = Seq.slice rest0 3 (Seq.length rest0) in
  assert (rest1 == x1);
  SP.append_slices cl_tail_pre x2;
  W.lemma_bseq_eq_refl cl_tail_pre;
  assert_norm (Seq.length cl_tail_pre == 19);
  let rest2 = Seq.slice rest1 19 (Seq.length rest1) in
  assert (rest2 == x2);
  W.lemma_enc_dec_var_roundtrip len;                (* all_dec (enc_dec_var len); decodes to len *)
  assert_norm (Seq.length cl_tail_post > 0 /\ not (W.is_dec (Seq.index cl_tail_post 0)));
  W.lemma_dec_prefix_len_run (W.enc_dec_var len) cl_tail_post;
  W.lemma_bseq_eq_refl cl_tail_post;
  assert (parse_response_var input == Some (code, len))
#pop-options

(* ─── The wire_format instance ─────────────────────────────────────────────── *)
noextract
let http_wire_format : WF.wire_format http_message =
{
  WF.wf_serialize = http_serialize;
  WF.wf_parse = http_parse;
  WF.wf_parse_serialize_exact = lemma_http_parse_serialize_exact;
}
