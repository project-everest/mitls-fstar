module HTTP.Wire.Chunked

(**
  Hand-written IETF HTTP/1.1 wire format (RFC 7230/7231) — the *chunked
  transfer-encoding* profile — as a `Common.WireFormat.wire_format` instance.

  ── Why this is written and proved BY HAND (not QuackyDucky) ─────────────────
  Like TFTP, HTTP is a *text* protocol (request/status lines, CRLF-delimited
  headers, hex chunk sizes) whose grammar exceeds the EverParse/QuackyDucky DSL,
  so `http_serialize` / `http_parse` are defined directly over `FStar.Seq` and the
  round-trip law `wf_parse_serialize_exact` is discharged by hand, reusing the
  ASCII/numeric helpers of `HTTP.Wire.Common`.

  ── The message union ───────────────────────────────────────────────────────
  A GET exchange with a chunked response body reduces to three self-delimiting
  wire messages:

    * `Msg_request target`  — the client's request line:
         "GET " target " HTTP/1.1" CRLF CRLF
    * `Msg_response code`    — the response head (chunked framing):
         "HTTP/1.1 " ddd " " CRLF "Transfer-Encoding: chunked" CRLF CRLF
    * `Msg_chunk payload`    — one chunk of the body:
         hhhh CRLF payload CRLF        (hhhh = 4-hex-digit size = |payload|)

  A chunk with an EMPTY payload is the RFC last-chunk ("0000" CRLF CRLF): its
  bytes coincide with a size-0 chunk, so the *empty chunk terminates the body*
  (the TFTP short-final-block / YMODEM EOT analog).  Because every message begins
  with an unambiguous marker — "GET "/‘G’, "HTTP/1.1 "/‘H’, or a hex digit for a
  chunk size — the union is fully self-delimiting and `http_parse` disambiguates
  by leading bytes.
**)

module Seq = FStar.Seq
module SP  = FStar.Seq.Properties
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module TCP = Common.TCP
module WF  = Common.WireFormat
module W   = HTTP.Wire.Common

(* ─── Fixed literals ───────────────────────────────────────────────────────── *)
let lit_get     : TCP.bytes = W.lit [0x47uy;0x45uy;0x54uy;0x20uy]                     (* "GET " *)
let req_tail    : TCP.bytes = W.lit [0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x0Duy;0x0Auy;0x0Duy;0x0Auy]  (* "HTTP/1.1\r\n\r\n" *)
let resp_prefix : TCP.bytes = W.lit [0x48uy;0x54uy;0x54uy;0x50uy;0x2Fuy;0x31uy;0x2Euy;0x31uy;0x20uy]                        (* "HTTP/1.1 " *)
let resp_tail   : TCP.bytes = W.lit [0x20uy;0x0Duy;0x0Auy;0x54uy;0x72uy;0x61uy;0x6Euy;0x73uy;0x66uy;0x65uy;0x72uy;0x2Duy;0x45uy;0x6Euy;0x63uy;0x6Fuy;0x64uy;0x69uy;0x6Euy;0x67uy;0x3Auy;0x20uy;0x63uy;0x68uy;0x75uy;0x6Euy;0x6Buy;0x65uy;0x64uy;0x0Duy;0x0Auy;0x0Duy;0x0Auy]  (* " \r\nTransfer-Encoding: chunked\r\n\r\n" *)

(* ─── Message union ────────────────────────────────────────────────────────── *)
type status_code = c:U16.t{100 <= U16.v c /\ U16.v c < 1000}
type chunk_payload = b:TCP.bytes{Seq.length b <= 65535}

noeq
type http_message =
  | Msg_request  : target:W.token -> http_message
  | Msg_response : code:status_code -> http_message
  | Msg_chunk    : payload:chunk_payload -> http_message

(* ─── Serialization ────────────────────────────────────────────────────────── *)
let ser_request (target:W.token) : TCP.bytes =
  Seq.append lit_get (Seq.append target (Seq.cons W.bSP req_tail))

let ser_response (code:status_code) : TCP.bytes =
  Seq.append resp_prefix (Seq.append (W.enc_dec3 (U16.v code)) resp_tail)

let ser_chunk (p:chunk_payload) : TCP.bytes =
  Seq.append (W.enc_hex4 (Seq.length p))
    (Seq.append W.crlf (Seq.append p W.crlf))

let http_serialize (m:http_message) : GTot TCP.bytes =
  match m with
  | Msg_request target -> ser_request target
  | Msg_response code  -> ser_response code
  | Msg_chunk p        -> ser_chunk p

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

let parse_response (input:TCP.bytes) : GTot (WF.parse_result http_message) =
  if Seq.length input < 9 then None else
  let rest0 = Seq.slice input 9 (Seq.length input) in
  if Seq.length rest0 < 3 then None
  else
    let codeb = Seq.slice rest0 0 3 in
    if not (W.dec3_ok codeb) then None
    else
      let code = W.dec_dec3 codeb in
      let tl = Seq.slice rest0 3 (Seq.length rest0) in
      if 100 <= code && code < 1000 && W.bseq_eq tl resp_tail
      then Some (Msg_response (U16.uint_to_t code), Seq.empty)
      else None

let lemma_dec_hex4_bound (b:TCP.bytes{W.hex4_ok b})
  : Lemma (W.dec_hex4 b <= 65535) = ()

let parse_chunk (input:TCP.bytes) : GTot (WF.parse_result http_message) =
  if Seq.length input < 8 then None
  else
    let szb = Seq.slice input 0 4 in
    if not (W.hex4_ok szb) then None
    else
      let n = W.dec_hex4 szb in
      lemma_dec_hex4_bound szb;
      if Seq.length input < 8 + n then None
      else if not (W.bseq_eq (Seq.slice input 4 6) W.crlf) then None
      else
        let payload : chunk_payload = Seq.slice input 6 (6 + n) in
        if not (W.bseq_eq (Seq.slice input (6 + n) (8 + n)) W.crlf) then None
        else Some (Msg_chunk payload, Seq.slice input (8 + n) (Seq.length input))

let http_parse (input:TCP.bytes) : GTot (WF.parse_result http_message) =
  if Seq.length input >= 4 && W.bseq_eq (Seq.slice input 0 4) lit_get
  then parse_request input
  else if Seq.length input >= 9 && W.bseq_eq (Seq.slice input 0 9) resp_prefix
  then parse_response input
  else parse_chunk input

(* ─── Disambiguation helpers ───────────────────────────────────────────────── *)
let lemma_bseq_neq_first (a b:TCP.bytes)
  : Lemma (requires Seq.length a > 0 /\ Seq.length b > 0 /\ Seq.index a 0 =!= Seq.index b 0)
          (ensures not (W.bseq_eq a b))
= W.lemma_bseq_eq a b

#push-options "--z3rlimit 40"
let lemma_enc_hex4_first (n:nat{n < 65536})
  : Lemma (W.is_hex (Seq.index (W.enc_hex4 n) 0) /\
           Seq.index (W.enc_hex4 n) 0 =!= 0x47uy /\
           Seq.index (W.enc_hex4 n) 0 =!= 0x48uy)
= W.lemma_hexdig_unhex ((n / 4096) % 16)
#pop-options

(* ─── The round-trip law ───────────────────────────────────────────────────── *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let lemma_http_parse_serialize_exact (m:http_message)
  : Lemma
      (ensures
        exists parsed.
          http_parse (http_serialize m) == Some (parsed, Seq.empty) /\
          parsed == m)
= match m with
  | Msg_request target ->
    let input = ser_request target in
    (* request branch is taken: prefix == lit_get *)
    SP.append_slices lit_get (Seq.append target (Seq.cons W.bSP req_tail));
    W.lemma_bseq_eq_refl lit_get;
    W.split_sp_append target req_tail;
    W.lemma_bseq_eq_refl req_tail;
    assert (http_parse input == Some (Msg_request target, Seq.empty))
  | Msg_response code ->
    let input = ser_response code in
    (* request prefix fails ('H' <> 'G'); response prefix matches *)
    SP.append_slices resp_prefix (Seq.append (W.enc_dec3 (U16.v code)) resp_tail);
    Seq.lemma_index_app1 resp_prefix (Seq.append (W.enc_dec3 (U16.v code)) resp_tail) 0;
    lemma_bseq_neq_first (Seq.slice input 0 4) lit_get;
    W.lemma_bseq_eq_refl resp_prefix;
    let rest0 = Seq.slice input 9 (Seq.length input) in
    SP.append_slices (W.enc_dec3 (U16.v code)) resp_tail;
    W.lemma_dec3_roundtrip (U16.v code);
    W.lemma_bseq_eq_refl resp_tail;
    assert (http_parse input == Some (Msg_response code, Seq.empty))
  | Msg_chunk p ->
    let n = Seq.length p in
    let input = ser_chunk p in
    lemma_enc_hex4_first n;
    SP.append_slices (W.enc_hex4 n) (Seq.append W.crlf (Seq.append p W.crlf));
    (* first byte is a hex digit: neither request nor response prefix matches *)
    Seq.lemma_index_app1 (W.enc_hex4 n) (Seq.append W.crlf (Seq.append p W.crlf)) 0;
    lemma_bseq_neq_first (Seq.slice input 0 4) lit_get;
    (if Seq.length input >= 9 then lemma_bseq_neq_first (Seq.slice input 0 9) resp_prefix);
    (* chunk branch decodes *)
    W.lemma_hex4_roundtrip n;
    SP.append_slices W.crlf (Seq.append p W.crlf);
    SP.append_slices p W.crlf;
    W.lemma_bseq_eq_refl W.crlf;
    assert (http_parse input == Some (Msg_chunk p, Seq.empty))
#pop-options

(* ─── Receive-side correspondence: parsing a chunk read as (header, body) ───── *)
(* A hex digit is never 'G' (0x47) or 'H' (0x48), so a buffer whose first byte is
   a hex digit is dispatched by `http_parse` to `parse_chunk` (not request /
   response). *)
let lemma_is_hex_not_GH (c:U8.t)
  : Lemma (requires W.is_hex c) (ensures c =!= 0x47uy /\ c =!= 0x48uy) = ()

(* If a 6-byte header `h` is a well-formed  hex4 | CRLF  decoding to `n`, and a
   body `b` is  <n bytes> | CRLF, then `http_parse (h ++ b)` yields exactly the
   chunk carrying those n payload bytes and consumes the whole frame.  This is
   the spec the verified receive codec is checked against. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let lemma_parse_chunk_parts (h b:TCP.bytes) (n:nat)
  : Lemma
    (requires
      Seq.length h == 6 /\ W.hex4_ok (Seq.slice h 0 4) /\
      Seq.equal (Seq.slice h 4 6) W.crlf /\
      W.dec_hex4 (Seq.slice h 0 4) == n /\ n <= 65535 /\
      Seq.length b == n + 2 /\ Seq.equal (Seq.slice b n (n + 2)) W.crlf)
    (ensures
      http_parse (Seq.append h b) ==
        Some (Msg_chunk (Seq.slice b 0 n), Seq.empty #U8.t))
= let f = Seq.append h b in
  SP.append_slices h b;
  (* slice f 0 4 == slice h 0 4, slice f 4 6 == slice h 4 6,
     slice f 6 (6+n) == slice b 0 n, slice f (6+n) (8+n) == slice b n (n+2) *)
  Seq.lemma_index_slice h 0 4 0;               (* index (slice h 0 4) 0 == index h 0 *)
  lemma_is_hex_not_GH (Seq.index (Seq.slice h 0 4) 0);
  lemma_bseq_neq_first (Seq.slice f 0 4) lit_get;
  (if Seq.length f >= 9 then lemma_bseq_neq_first (Seq.slice f 0 9) resp_prefix);
  (* the two CRLF checks in parse_chunk *)
  W.lemma_bseq_eq (Seq.slice f 4 6) W.crlf;
  W.lemma_bseq_eq (Seq.slice f (6 + n) (8 + n)) W.crlf;
  ()
#pop-options


(* ─── Variable-width (RFC 9112) single-chunk parser ────────────────────────── *)
(* Real origin servers write a minimal-width hex chunk size (`chunk-size =
   1*HEXDIG`, RFC 9112 §7.1), e.g. "1cf\r\n", instead of our encoder's fixed
   4-hex-digit size.  `parse_chunk_var` consumes ONE such frame off the front of
   `input`:  <1+ hex digits> CRLF <size payload bytes> CRLF , returning the
   payload together with the residual bytes.  The size token is the MAXIMAL hex
   run at the front (`hex_prefix_len`), so parsing is deterministic; chunk
   extensions (`;name=val` after the size) are NOT accepted — the byte after the
   size run must be CR.  Returns `(payload, rest)` directly (no 65535 cap, so it
   is not tied to the `chunk_payload` refinement used by the fixed-width union). *)
let parse_chunk_var (input:TCP.bytes) : GTot (option (TCP.bytes & TCP.bytes)) =
  let len = Seq.length input in
  let k = W.hex_prefix_len input in
  if k = 0 then None
  else begin
    W.lemma_hex_prefix_len_bound input;      (* k <= len, so the slice below is well-formed *)
    let hs = Seq.slice input 0 k in
    if not (W.all_hex hs) then None           (* always true for the maximal run; refines hs *)
    else
      let n = W.dec_hex_var hs in
      if len < k + 2 then None
      else if not (W.bseq_eq (Seq.slice input k (k + 2)) W.crlf) then None
      else if n = 0 then
        (* last chunk `1*"0" CRLF`: consume only the size line (trailers, if any,
           and the final CRLF are left in the residual — not interpreted here). *)
        Some (Seq.empty #U8.t, Seq.slice input (k + 2) len)
      else if len < k + 2 + n + 2 then None
      else if not (W.bseq_eq (Seq.slice input (k + 2 + n) (k + 2 + n + 2)) W.crlf) then None
      else
        let payload = Seq.slice input (k + 2) (k + 2 + n) in
        let rest    = Seq.slice input (k + 2 + n + 2) len in
        Some (payload, rest)
  end

(* The maximal hex prefix of `hs ++ rest` is exactly `hs` when `hs` is all-hex
   and the first byte of `rest` (if any) is not a hex digit. *)
let rec lemma_hex_prefix_len_app (hs rest:TCP.bytes)
  : Lemma
    (requires
      W.all_hex hs /\
      (Seq.length rest == 0 \/ (Seq.length rest > 0 /\ not (W.is_hex (Seq.index rest 0)))))
    (ensures W.hex_prefix_len (Seq.append hs rest) == Seq.length hs)
    (decreases Seq.length hs)
= let f = Seq.append hs rest in
  if Seq.length hs = 0 then
    Seq.lemma_eq_intro f rest
  else begin
    let hs' = Seq.slice hs 1 (Seq.length hs) in
    Seq.lemma_index_app1 hs rest 0;                                   (* index f 0 == index hs 0 *)
    Seq.lemma_eq_intro (Seq.slice f 1 (Seq.length f)) (Seq.append hs' rest);
    lemma_hex_prefix_len_app hs' rest
  end

(* CR (the first byte of CRLF) is not a hex digit — so a size run is never
   extended across the size-line terminator. *)
let lemma_cr_not_hex (_:unit)
  : Lemma (not (W.is_hex W.bCR) /\ Seq.index W.crlf 0 == W.bCR)
= assert_norm (not (W.is_hex W.bCR));
  assert_norm (Seq.index W.crlf 0 == W.bCR)

(* One well-formed variable-width frame `hs ++ CRLF ++ payload ++ CRLF ++ suffix`
   (hs a non-empty hex run decoding to n, payload of n bytes) is consumed off the
   front, yielding `(payload, suffix)`.  The spec relation the verified
   variable-width decoder is checked against. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let lemma_parse_chunk_var_prefix (hs payload suffix:TCP.bytes) (n:nat)
  : Lemma
    (requires
      W.all_hex hs /\ Seq.length hs > 0 /\
      W.dec_hex_var hs == n /\ 0 < n /\ Seq.length payload == n)
    (ensures
      parse_chunk_var
        (Seq.append hs (Seq.append W.crlf (Seq.append payload (Seq.append W.crlf suffix)))) ==
        Some (payload, suffix))
= let c    = Seq.append W.crlf suffix in
  let b    = Seq.append payload c in
  let a    = Seq.append W.crlf b in
  let f    = Seq.append hs a in
  let k    = Seq.length hs in
  lemma_cr_not_hex ();
  (* A starts with CR, so the maximal hex run of f is exactly hs. *)
  Seq.lemma_index_app1 W.crlf b 0;                (* index a 0 == index crlf 0 == CR *)
  lemma_hex_prefix_len_app hs a;                  (* hex_prefix_len f == k *)
  (* relate f-slices to the components via right-nested append_slices *)
  SP.append_slices hs a;                          (* slice f 0 k == hs;  slice f (k+i)(k+j) == slice a i j *)
  SP.append_slices W.crlf b;                      (* slice a 0 2 == crlf; slice a (2+i)(2+j) == slice b i j *)
  SP.append_slices payload c;                     (* slice b 0 n == payload; slice b (n+i)(n+j) == slice c i j *)
  SP.append_slices W.crlf suffix;                 (* slice c 0 2 == crlf; slice c 2 (2+|suffix|) == suffix *)
  (* the size token slice equals hs, so all_hex holds and its value is n *)
  Seq.lemma_eq_elim hs (Seq.slice f 0 k);
  (* the two CRLF checks: bridge Seq.equal to boolean bseq_eq *)
  Seq.lemma_eq_intro (Seq.slice f k (k + 2)) W.crlf;
  Seq.lemma_eq_intro (Seq.slice f (k + 2 + n) (k + 2 + n + 2)) W.crlf;
  W.lemma_bseq_eq (Seq.slice f k (k + 2)) W.crlf;
  W.lemma_bseq_eq (Seq.slice f (k + 2 + n) (k + 2 + n + 2)) W.crlf;
  (* the payload and residual slices *)
  Seq.lemma_eq_intro (Seq.slice f (k + 2) (k + 2 + n)) payload;
  Seq.lemma_eq_intro (Seq.slice f (k + 2 + n + 2) (Seq.length f)) suffix;
  ()
#pop-options

(* The size-0 last chunk `hs ++ CRLF ++ suffix` (hs decoding to 0) is consumed as
   the terminator: empty reassembly with the whole `suffix` (trailers + final
   CRLF) as residual. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let lemma_parse_chunk_var_end (hs suffix:TCP.bytes)
  : Lemma
    (requires W.all_hex hs /\ Seq.length hs > 0 /\ W.dec_hex_var hs == 0)
    (ensures
      parse_chunk_var (Seq.append hs (Seq.append W.crlf suffix)) ==
        Some (Seq.empty #U8.t, suffix))
= let a = Seq.append W.crlf suffix in
  let f = Seq.append hs a in
  let k = Seq.length hs in
  lemma_cr_not_hex ();
  Seq.lemma_index_app1 W.crlf suffix 0;           (* index a 0 == CR *)
  lemma_hex_prefix_len_app hs a;                  (* hex_prefix_len f == k *)
  SP.append_slices hs a;                          (* slice f 0 k == hs; slice f (k+i)(k+j) == slice a i j *)
  SP.append_slices W.crlf suffix;                 (* slice a 0 2 == crlf; slice a 2 (2+|suffix|) == suffix *)
  Seq.lemma_eq_elim hs (Seq.slice f 0 k);
  Seq.lemma_eq_intro (Seq.slice f k (k + 2)) W.crlf;
  W.lemma_bseq_eq (Seq.slice f k (k + 2)) W.crlf;
  Seq.lemma_eq_intro (Seq.slice f (k + 2) (Seq.length f)) suffix;
  ()
#pop-options


noextract
let http_wire_format : WF.wire_format http_message =
{
  WF.wf_serialize = http_serialize;
  WF.wf_parse = http_parse;
  WF.wf_parse_serialize_exact = lemma_http_parse_serialize_exact;
}
