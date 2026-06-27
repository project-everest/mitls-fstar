module TLS13.Wire.Spec.RevealDecode

(**
  Spec-reveal helper for the M/L record decoders (TLS13.Impl.Parser).

  TLS13.Wire.Spec exposes [parse_record]/[parse_plaintext] as abstract vals.
  The record decoders in TLS13.Impl.Parser need to *construct* the result of
  these spec parsers from the header / inner-plaintext bytes they validate at
  run time.  This module friends TLS13.Wire.Spec and re-exports the needed
  construction facts as lemmas referring only to spec types (B/M/T), which
  TLS13.Impl.Parser then consumes as an ordinary non-friend dependence.
*)

module B = TLS13.Bytes
module M = TLS13.Messages
module T = TLS13.Types
module Seq = FStar.Seq
module U8 = FStar.UInt8
module WS = TLS13.Wire.Spec

(* Construct [parse_record]'s full result from validated outer-record header
   bytes: content-type byte in {0x14,0x15,0x16,0x17}, version 0x0303, and a
   2-byte big-endian fragment length bounded by 16640 with enough input. *)
val lemma_parse_record_from_header (raw:B.bytes)
  : Lemma
    (requires
      B.length raw >= 5 /\
      (let b0 = U8.v (Seq.index raw 0) in
       b0 = 0x14 \/ b0 = 0x15 \/ b0 = 0x16 \/ b0 = 0x17) /\
      U8.v (Seq.index raw 1) = 0x03 /\
      U8.v (Seq.index raw 2) = 0x03 /\
      (let flen = U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) in
       flen <= 16640 /\ 5 + flen <= B.length raw))
    (ensures
      (let flen = U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) in
       match WS.parse_record raw with
       | None -> False
       | Some (ct, frag, consumed) ->
         consumed == 5 + flen /\
         Seq.equal frag (Seq.slice raw 5 (5 + flen)) /\
         (U8.v (Seq.index raw 0) = 0x14 ==> ct == T.ChangeCipherSpec) /\
         (U8.v (Seq.index raw 0) = 0x15 ==> ct == T.Alert) /\
         (U8.v (Seq.index raw 0) = 0x16 ==> ct == T.Handshake) /\
         (U8.v (Seq.index raw 0) = 0x17 ==> ct == T.ApplicationData)))

val lemma_parse_record_wire_from_header (raw:B.bytes)
  : Lemma
    (requires
      B.length raw >= 5 /\
      (let b0 = U8.v (Seq.index raw 0) in
       b0 = 0x14 \/ b0 = 0x15 \/ b0 = 0x16 \/ b0 = 0x17) /\
      U8.v (Seq.index raw 1) = 0x03 /\
      (let b0 = U8.v (Seq.index raw 0) in
       U8.v (Seq.index raw 2) = 0x03 \/
       (b0 = 0x16 /\ U8.v (Seq.index raw 2) = 0x01)) /\
      (let flen = U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) in
       flen <= 16640 /\ 5 + flen <= B.length raw))
    (ensures
      (let flen = U8.v (Seq.index raw 3) * 256 + U8.v (Seq.index raw 4) in
       match WS.parse_record_wire raw with
       | None -> False
       | Some (ct, frag, consumed) ->
         consumed == 5 + flen /\
         Seq.equal frag (Seq.slice raw 5 (5 + flen)) /\
         (U8.v (Seq.index raw 0) = 0x14 ==> ct == T.ChangeCipherSpec) /\
         (U8.v (Seq.index raw 0) = 0x15 ==> ct == T.Alert) /\
         (U8.v (Seq.index raw 0) = 0x16 ==> ct == T.Handshake) /\
         (U8.v (Seq.index raw 0) = 0x17 ==> ct == T.ApplicationData)))

val lemma_parse_record_wire_prefix
  (input:B.bytes)
  (content_type:T.content_type)
  (fragment:M.sealed_record)
  (consumed:nat)
  : Lemma
    (requires
      WS.parse_record_wire input == Some (content_type, fragment, consumed) /\
      consumed <= B.length input)
    (ensures
      WS.parse_record_wire (Seq.slice input 0 consumed) ==
        Some (content_type, fragment, consumed))

val lemma_parse_record_wire_from_prefix
  (input:B.bytes)
  (content_type:T.content_type)
  (fragment:M.sealed_record)
  (consumed:nat)
  : Lemma
    (requires
      consumed <= B.length input /\
      WS.parse_record_wire (Seq.slice input 0 consumed) ==
        Some (content_type, fragment, consumed))
    (ensures
      WS.parse_record_wire input == Some (content_type, fragment, consumed))

(* Construct [parse_plaintext]'s result for a TLSInnerPlaintext whose last byte
   is a recognised content type (no trailing zero padding): the recovered
   fragment is the prefix, and the content type matches the last byte. *)
val lemma_parse_plaintext_some (input:B.bytes)
  : Lemma
    (requires
      B.length input >= 1 /\
      (let b = U8.v (Seq.index input (B.length input - 1)) in
       b = 0x14 \/ b = 0x15 \/ b = 0x16 \/ b = 0x17))
    (ensures
      (match WS.parse_plaintext input with
       | None -> False
       | Some pt ->
         Seq.equal pt.M.fragment (Seq.slice input 0 (B.length input - 1)) /\
         (let b = U8.v (Seq.index input (B.length input - 1)) in
          (b = 0x14 ==> pt.M.content_type == T.ChangeCipherSpec) /\
          (b = 0x15 ==> pt.M.content_type == T.Alert) /\
          (b = 0x16 ==> pt.M.content_type == T.Handshake) /\
          (b = 0x17 ==> pt.M.content_type == T.ApplicationData))))

(* Reveal serialize_tls_message on a handshake message. *)
val lemma_serialize_tls_message_handshake (hs:M.handshake_msg)
  : Lemma (WS.serialize_tls_message (M.TlsHandshake hs) ==
           (T.Handshake, WS.serialize_handshake hs))

(* Reveal serialize_tls_message on ChangeCipherSpec (content type only;
   the fragment is recovered via lemma_parse_tls_message_change_cipher_spec). *)
val lemma_serialize_tls_message_change_cipher_spec (_:unit)
  : Lemma (fst (WS.serialize_tls_message M.TlsChangeCipherSpec) == T.ChangeCipherSpec)

(* A successful ChangeCipherSpec parse pins the fragment to the serialized
   ChangeCipherSpec payload (the single byte 0x01). *)
val lemma_parse_tls_message_change_cipher_spec (fragment:B.bytes)
  : Lemma
    (requires WS.parse_tls_message T.ChangeCipherSpec fragment == Some M.TlsChangeCipherSpec)
    (ensures Seq.equal fragment (snd (WS.serialize_tls_message M.TlsChangeCipherSpec)))
