module DH.Sample.Wire

(**
  DH.Sample.Wire — explicit wire format for the three DH sample messages.

  The three protocol messages are

      msg1  (A -> B) :  A, g^x
      msg2  (B -> A) :  B, g^y, Sign_B(A, g^x, g^y)
      msg3  (A -> B) :  Sign_A(B, g^x, g^y)

  encoded with a one-byte DISJOINT TAG followed by FIXED-SIZE fields:

      Msg1 :  [tag=1 : 1][A : 4][g^x : 4]                        (total  9 bytes)
      Msg2 :  [tag=2 : 1][B : 4][g^y : 4][Sign_B : 8]            (total 17 bytes)
      Msg3 :  [tag=3 : 1][Sign_A : 8]                            (total  9 bytes)

  Because every field is fixed size, each message is a *strong prefix* parser:
  a prefix of a byte stream determines the message and leaves a well-defined
  residual.  We prove both the exact round-trip law required by
  `Common.WireFormat.wire_format` (`wf_parse_serialize_exact`) and the stronger
  stream-prefix law of `Common.WireFormat.wire_format_stream_laws`.
*)

module Seq = FStar.Seq
module SP  = FStar.Seq.Properties
module U8  = FStar.UInt8
module WF  = Common.WireFormat
open DH.Sample.Types

(** ── The structured message type ───────────────────────────────────────── *)

noeq
type dh_message =
  | Msg1 : initiator:principal -> gx:dh_share -> dh_message
  | Msg2 : responder:principal -> gy:dh_share -> sig_b:signature -> dh_message
  | Msg3 : sig_a:signature -> dh_message

(** The disjoint tag byte of each message. *)
let tag_of (m:dh_message) : byte =
  match m with
  | Msg1 _ _   -> 1uy
  | Msg2 _ _ _ -> 2uy
  | Msg3 _     -> 3uy

(** The (fixed) serialized length of each message. *)
let msg_len (m:dh_message) : nat =
  match m with
  | Msg1 _ _   -> 9
  | Msg2 _ _ _ -> 17
  | Msg3 _     -> 9

(** ── Serialization ─────────────────────────────────────────────────────── *)

(** A one-byte sequence carrying a tag. *)
let tag_bytes (t:byte) : lbytes 1 = Seq.create 1 t

(**
  Serialize a message to bytes: tag byte followed by its fixed-size fields, all
  concatenated left to right.  Built entirely from `append` so that the parse
  proofs can use `FStar.Seq.Properties.append_slices` to recover each field.
*)
let serialize (m:dh_message) : bytes =
  match m with
  | Msg1 a gx      -> Seq.append (tag_bytes 1uy) (Seq.append a gx)
  | Msg2 b gy sig  -> Seq.append (tag_bytes 2uy) (Seq.append b (Seq.append gy sig))
  | Msg3 sig       -> Seq.append (tag_bytes 3uy) sig

(** Serialization produces exactly `msg_len m` bytes. *)
let lemma_serialize_len (m:dh_message)
  : Lemma (ensures Seq.length (serialize m) == msg_len m)
= ()

(** ── Parsing ───────────────────────────────────────────────────────────── *)

(**
  Parse the first message out of a byte string.  Returns the parsed message
  together with the unconsumed residual bytes, or `None` on a malformed /
  too-short input.  Fields are recovered by slicing at fixed offsets.
*)
let parse (input:bytes) : WF.parse_result dh_message =
  if Seq.length input < 1 then None
  else begin
    let n = Seq.length input in
    let tag = U8.v (Seq.index input 0) in
    if tag = 1 then begin
      if n >= 9 then
        let a  = Seq.slice input 1 5 in
        let gx = Seq.slice input 5 9 in
        Some (Msg1 a gx, Seq.slice input 9 n)
      else None
    end else if tag = 2 then begin
      if n >= 17 then
        let b   = Seq.slice input 1 5 in
        let gy  = Seq.slice input 5 9 in
        let sig = Seq.slice input 9 17 in
        Some (Msg2 b gy sig, Seq.slice input 17 n)
      else None
    end else if tag = 3 then begin
      if n >= 9 then
        let sig = Seq.slice input 1 9 in
        Some (Msg3 sig, Seq.slice input 9 n)
      else None
    end else None
  end

(** ── Round-trip proofs ─────────────────────────────────────────────────── *)

(*
  Field extraction from a serialized (possibly extended) buffer is handled
  automatically by the SMT patterns on `Seq.lemma_index_app1/app2/index_slice`:
  each `Seq.slice (serialize m ++ rest) i j` reduces, index by index, to the
  corresponding field.  We only need to feed the length facts and, for the
  residual, `append_slices`.
*)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(**
  The stream-prefix law: parsing the serialization of [m] followed by arbitrary
  trailing bytes [rest] recovers [m] exactly and returns [rest] as residual.
  This is the strong-prefix property that makes the wire format usable for
  stream transports, and it implies the exact round-trip below.
*)
let lemma_parse_serialize_prefix (m:dh_message) (rest:bytes)
  : Lemma
      (ensures
        parse (Seq.append (serialize m) rest) == Some (m, rest))
=
  let s = serialize m in
  let full = Seq.append s rest in
  (* tag byte survives concatenation: index 0 of `full` is the tag of `s`. *)
  assert (Seq.index full 0 == Seq.index s 0);
  (* the residual after the message is exactly `rest`. *)
  SP.append_slices s rest;
  match m with
  | Msg1 a gx ->
    assert (Seq.equal (Seq.slice full 1 5) a);
    assert (Seq.equal (Seq.slice full 5 9) gx);
    assert (Seq.equal (Seq.slice full 9 (Seq.length full)) rest)
  | Msg2 b gy sig ->
    assert (Seq.equal (Seq.slice full 1 5) b);
    assert (Seq.equal (Seq.slice full 5 9) gy);
    assert (Seq.equal (Seq.slice full 9 17) sig);
    assert (Seq.equal (Seq.slice full 17 (Seq.length full)) rest)
  | Msg3 sig ->
    assert (Seq.equal (Seq.slice full 1 9) sig);
    assert (Seq.equal (Seq.slice full 9 (Seq.length full)) rest)

(**
  The exact round-trip law required by `Common.WireFormat.wire_format`:
  parsing the serialization of [m] (with no trailing bytes) recovers [m] and
  leaves an empty residual.  Derived from the prefix law with `rest = empty`.
*)
let lemma_parse_serialize_exact (m:dh_message)
  : Lemma
      (ensures
        exists parsed.
          parse (serialize m) == Some (parsed, Seq.empty) /\
          parsed == m)
=
  lemma_parse_serialize_prefix m Seq.empty;
  Seq.append_empty_r (serialize m);
  assert (Seq.equal (Seq.append (serialize m) Seq.empty) (serialize m));
  assert (parse (serialize m) == Some (m, Seq.empty))

#pop-options

(** ── Wire-format class instances ───────────────────────────────────────── *)

(**
  The `Common.WireFormat.wire_format` instance for DH messages.  `wf_serialize`
  and `wf_parse` are `GTot`; our pure `serialize`/`parse` lift directly.
*)
noextract
let dh_wire_format : WF.wire_format dh_message = {
  WF.wf_serialize = (fun m -> serialize m);
  WF.wf_parse     = (fun b -> parse b);
  WF.wf_parse_serialize_exact = lemma_parse_serialize_exact;
}

(**
  The stronger stream laws instance: the strong-prefix property proved above.
  Having this means the composed system (DH.Sample.StateMachine) satisfies the
  stream-refinement disjunct of `Common.WireFormatStateMachine.valid_byte_trace`.
*)
noextract
let dh_wire_format_stream_laws
  : WF.wire_format_stream_laws dh_message dh_wire_format = {
  WF.wfsl_parse_serialize_prefix = lemma_parse_serialize_prefix;
}
