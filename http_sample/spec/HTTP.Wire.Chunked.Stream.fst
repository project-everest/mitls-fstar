module HTTP.Wire.Chunked.Stream

(**
  Multi-chunk *streaming reassembly* spec for the HTTP/1.1 chunked
  transfer-encoding, layered on `HTTP.Wire.Chunked`.

  `parse_chunks` decodes a sequence of chunk frames — each `hhhh CRLF payload
  CRLF` — concatenating their payloads, and STOPS at the first empty (size-0)
  chunk (the RFC last-chunk terminator `0000 CRLF CRLF`), returning the
  reassembled body together with whatever bytes follow the terminator.  It is
  defined directly in terms of `HTTP.Wire.Chunked.parse_chunk` (the single-chunk
  prefix parser), so no request/response disambiguation is involved.

  The three lemmas below are the spec the verified in-buffer decoder
  `HTTP.Impl.Codec.Chunked.Stream.http_decode_chunks` is checked against:

    * lemma_parse_chunk_prefix — one well-formed frame `h ++ b` consumed off the
      front of `h ++ b ++ suffix` leaves residual `suffix`;
    * lemma_parse_chunks_step  — a non-empty frame prepends its payload to the
      reassembly of the remaining stream;
    * lemma_parse_chunks_end   — an empty frame terminates the body.
*)

module Seq = FStar.Seq
module SP  = FStar.Seq.Properties
module U8  = FStar.UInt8
module TCP = Common.TCP
module WF  = Common.WireFormat
module W   = HTTP.Wire.Common

open HTTP.Wire.Chunked

(* Prepend an already-decoded prefix `pre` to the body of a parse_chunks result.
   The loop invariant of the verified decoder is
     parse_chunks (whole) == recon (decoded-so-far) (parse_chunks (remaining)). *)
let recon (pre:TCP.bytes) (r:option (TCP.bytes & TCP.bytes))
  : option (TCP.bytes & TCP.bytes) =
  match r with
  | Some (body, rest) -> Some (Seq.append pre body, rest)
  | None -> None

(* Reassemble a chunked body: concatenate chunk payloads until the first empty
   chunk, returning (body, bytes-after-terminator).  Structurally decreasing on
   the input length: `parse_chunk` consumes 8+n >= 8 bytes, so the residual is
   strictly shorter (the explicit guard makes this manifest to F-star). *)
let rec parse_chunks (input:TCP.bytes)
  : GTot (option (TCP.bytes & TCP.bytes)) (decreases (Seq.length input)) =
  match parse_chunk input with
  | Some (Msg_chunk p, rest) ->
    if Seq.length p = 0 then Some (Seq.empty #U8.t, rest)
    else if Seq.length rest < Seq.length input then
      (match parse_chunks rest with
       | Some (body, rest') -> Some (Seq.append p body, rest')
       | None -> None)
    else None
  | _ -> None

(* One well-formed chunk frame `h ++ b` (6-byte hex4|CRLF header decoding to `n`,
   body of `n` payload bytes + trailing CRLF) is consumed off the front of
   `h ++ b ++ suffix`, yielding the chunk carrying `slice b 0 n` with residual
   exactly `suffix`.  Generalizes HTTP.Wire.Chunked.lemma_parse_chunk_parts with
   a trailing `suffix`. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 150"
let lemma_parse_chunk_prefix (h b suffix:TCP.bytes) (n:nat)
  : Lemma
    (requires
      Seq.length h == 6 /\ W.hex4_ok (Seq.slice h 0 4) /\
      Seq.equal (Seq.slice h 4 6) W.crlf /\
      W.dec_hex4 (Seq.slice h 0 4) == n /\ n <= 65535 /\
      Seq.length b == n + 2 /\ Seq.equal (Seq.slice b n (n + 2)) W.crlf)
    (ensures
      parse_chunk (Seq.append (Seq.append h b) suffix) ==
        Some (Msg_chunk (Seq.slice b 0 n), suffix))
= let hb = Seq.append h b in
  let f  = Seq.append hb suffix in
  SP.append_slices h b;                 (* slices of hb in terms of h,b *)
  SP.append_slices hb suffix;           (* slices of f  in terms of hb,suffix *)
  (* slice f 0 4 == slice h 0 4 *)
  Seq.lemma_eq_intro (Seq.slice f 0 4) (Seq.slice h 0 4);
  (* slice f 4 6 == slice h 4 6 (== crlf) *)
  Seq.lemma_eq_intro (Seq.slice f 4 6) (Seq.slice h 4 6);
  (* payload slice f 6 (6+n) == slice b 0 n *)
  Seq.lemma_eq_intro (Seq.slice f 6 (6 + n)) (Seq.slice b 0 n);
  (* trailing crlf slice f (6+n) (8+n) == slice b n (n+2) (== crlf) *)
  Seq.lemma_eq_intro (Seq.slice f (6 + n) (8 + n)) (Seq.slice b n (n + 2));
  (* residual slice f (8+n) (length f) == suffix *)
  Seq.lemma_eq_intro (Seq.slice f (8 + n) (Seq.length f)) suffix;
  (* bridge the two CRLF checks from Seq.equal to the boolean bseq_eq *)
  W.lemma_bseq_eq (Seq.slice f 4 6) W.crlf;
  W.lemma_bseq_eq (Seq.slice f (6 + n) (8 + n)) W.crlf;
  ()
#pop-options

(* A non-empty well-formed frame at the head distributes over parse_chunks:
   its payload is prepended to the reassembly of the remaining stream. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 150"
let lemma_parse_chunks_step (h b suffix:TCP.bytes) (n:nat)
  : Lemma
    (requires
      Seq.length h == 6 /\ W.hex4_ok (Seq.slice h 0 4) /\
      Seq.equal (Seq.slice h 4 6) W.crlf /\
      W.dec_hex4 (Seq.slice h 0 4) == n /\ 0 < n /\ n <= 65535 /\
      Seq.length b == n + 2 /\ Seq.equal (Seq.slice b n (n + 2)) W.crlf)
    (ensures
      parse_chunks (Seq.append (Seq.append h b) suffix) ==
        recon (Seq.slice b 0 n) (parse_chunks suffix))
= let f = Seq.append (Seq.append h b) suffix in
  lemma_parse_chunk_prefix h b suffix n;
  (* parse_chunk f == Some (Msg_chunk (slice b 0 n), suffix); payload length is n>0 *)
  assert (Seq.length (Seq.slice b 0 n) == n);
  assert (Seq.length suffix < Seq.length f);
  ()
#pop-options

(* recon composes by concatenating the decoded prefixes (append associativity):
   the invariant-maintenance law for the decoder loop. *)
let lemma_recon_compose (a c:TCP.bytes) (r:option (TCP.bytes & TCP.bytes))
  : Lemma (recon a (recon c r) == recon (Seq.append a c) r)
= match r with
  | Some (body, rest) -> Seq.append_assoc a c body
  | None -> ()

(* An empty well-formed frame (size 0, body = just CRLF) terminates the body:
   the reassembly is empty with the whole `suffix` as residual. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 150"
let lemma_parse_chunks_end (h b suffix:TCP.bytes)
  : Lemma
    (requires
      Seq.length h == 6 /\ W.hex4_ok (Seq.slice h 0 4) /\
      Seq.equal (Seq.slice h 4 6) W.crlf /\
      W.dec_hex4 (Seq.slice h 0 4) == 0 /\
      Seq.length b == 2 /\ Seq.equal (Seq.slice b 0 2) W.crlf)
    (ensures
      parse_chunks (Seq.append (Seq.append h b) suffix) ==
        Some (Seq.empty #U8.t, suffix))
= lemma_parse_chunk_prefix h b suffix 0;
  (* parse_chunk (h++b++suffix) == Some (Msg_chunk (slice b 0 0), suffix);
     slice b 0 0 is empty, so parse_chunks returns the terminator case. *)
  Seq.lemma_eq_intro (Seq.slice b 0 0) (Seq.empty #U8.t);
  ()
#pop-options

(* ─── Variable-width (RFC 9112) streaming reassembly ───────────────────────── *)
(* The variable-width analog of `parse_chunks`: decode a stream of minimal-width
   chunk frames (see `HTTP.Wire.Chunked.parse_chunk_var`), concatenating the
   payloads until the first size-0 chunk (`1*"0" CRLF`), returning the reassembled
   body together with whatever follows the terminator (trailers + final CRLF).
   Structurally decreasing: a non-empty frame consumes k+2+n+2 >= 5 bytes, so the
   residual is strictly shorter (the explicit guard makes this manifest). *)
let rec parse_chunks_var (input:TCP.bytes)
  : GTot (option (TCP.bytes & TCP.bytes)) (decreases (Seq.length input)) =
  match parse_chunk_var input with
  | Some (p, rest) ->
    if Seq.length p = 0 then Some (Seq.empty #U8.t, rest)
    else if Seq.length rest < Seq.length input then
      (match parse_chunks_var rest with
       | Some (body, rest') -> Some (Seq.append p body, rest')
       | None -> None)
    else None
  | None -> None

(* A non-empty variable-width frame at the head distributes over parse_chunks_var:
   its payload is prepended to the reassembly of the remaining stream. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let lemma_parse_chunks_var_step (hs payload suffix:TCP.bytes) (n:nat)
  : Lemma
    (requires
      W.all_hex hs /\ Seq.length hs > 0 /\
      W.dec_hex_var hs == n /\ 0 < n /\ Seq.length payload == n)
    (ensures
      parse_chunks_var
        (Seq.append hs (Seq.append W.crlf (Seq.append payload (Seq.append W.crlf suffix)))) ==
        recon payload (parse_chunks_var suffix))
= let f = Seq.append hs (Seq.append W.crlf (Seq.append payload (Seq.append W.crlf suffix))) in
  lemma_parse_chunk_var_prefix hs payload suffix n;
  (* parse_chunk_var f == Some (payload, suffix), payload length n>0, and
     |suffix| < |f| (the frame consumes hs++CRLF++payload++CRLF >= 4 bytes). *)
  assert (Seq.length payload == n);
  assert (Seq.length suffix < Seq.length f);
  ()
#pop-options

(* The size-0 last chunk terminates the body: empty reassembly with the whole
   `suffix` as residual. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
let lemma_parse_chunks_var_end (hs suffix:TCP.bytes)
  : Lemma
    (requires W.all_hex hs /\ Seq.length hs > 0 /\ W.dec_hex_var hs == 0)
    (ensures
      parse_chunks_var (Seq.append hs (Seq.append W.crlf suffix)) ==
        Some (Seq.empty #U8.t, suffix))
= lemma_parse_chunk_var_end hs suffix
#pop-options
