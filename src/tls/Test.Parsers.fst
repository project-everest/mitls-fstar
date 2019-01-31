module Test.Parsers

open C.String
open FStar.Error
open FStar.HyperStack.ST
open LowStar.BufferOps
open Parsers

module B = FStar.Bytes
module LB = LowStar.Buffer
module LPL = LowParse.Low.Base

open FStar.Printf
open TLSError
open TLSConstants

// No need to verify test for now
#set-options "--admit_smt_queries true"

let discard _ : ST unit (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1)) = ()
let bprint s = discard (FStar.IO.debug_print_string (s^"\n"))

let from_bytes (b:B.bytes{B.length b <> 0}) : StackInline LPL.buffer8
  (requires (fun h0 -> True))
  (ensures  (fun h0 buf h1 ->
    LB.(modifies loc_none h0 h1) /\
    LB.live h1 buf /\ LB.unused_in buf h0 /\
    LB.length buf = B.length b /\
    B.reveal b `Seq.equal` LB.as_seq h1 buf))
  =
  let h0 = get () in
  let len = FStar.UInt32.uint_to_t (B.length b) in
  let lb = LB.alloca 0uy len in
  FStar.Bytes.store_bytes b lb;
  let h1 = get () in
  LB.(modifies_only_not_unused_in loc_none h0 h1);
  lb

let test_clientHello () : St bool =
  (* From Chrome 70 *)
  let chb = B.bytes_of_hex "0303c4168caa4297df69306988b842fe1f62f7cf07dcb2ad03aeb0012eae4b84e3cc203b03c8b3c20860716b6d8c405a9f64306ae660c77a51fe01f7c7c8f301458c9a00228a8a130113021303c02bc02fc02cc030cca9cca8c013c014009c009d002f0035000a010001914a4a0000ff010001000000000e000c0000096c6f63616c686f73740017000000230000000d00140012040308040401050308050501080606010201000500050100000000001200000010000e000c02683208687474702f312e3175500000000b000201000033002b00294a4a000100001d00209aad9849cf973510294b18ad9dfbcce2ee087b21276ba16f89570254796dcb75002d00020101002b000b0a9a9a0304030303020301000a000a00084a4a001d00170018001b00030200025a5a000100001500cb0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" in
  print !$" - ClientHello (intermediate)\n";
  let b =
    match ClientHello.clientHello_parser32 chb with
    | None -> bprint " failed to parse CH!\n"; false
    | Some (ch, len) ->
      if B.len chb <> len then
	(print !$"leftover bytes after parsing!\n"; false)
      else
	if ClientHello.clientHello_serializer32 ch <> chb then
	(print !$"roundtrip serialization failed!\n"; false)
	else
          (print !$"  + Roundtrip serialization matches!\n"; true)
    in
  let b' =
    let open HandshakeMessages in
    let open Parsers.CertificateEntry13 in
    let open Parsers.CertificateExtension in
    let open Parsers.CertificateStatus in
    let open Parsers.CertificateStatusType in
    let ext = CE_status_request ({status_type = Ocsp; response = B.bytes_of_hex "00"}) in
    let cert1 = { cert_data = B.bytes_of_hex "3003000000"; extensions = [ext] } in
    let cert2 = { cert_data = B.bytes_of_string "hello world"; extensions = [] } in
    let m = { crt_request_context = B.empty_bytes; crt_chain13 = [cert1; cert2] } in
    let b = handshakeMessageBytes (Some TLS_1p3) (Certificate13 m) in
    bprint (sprintf " - Certificate13 test: %s\n" (B.hex_of_bytes b));
    match parseMessage b with
    | Error z -> bprint (" Parsing error: "^string_of_error z); false
    | Correct None -> bprint " Message not fully parsed!\n"; false
    | Correct (Some (| rem, hst, payload, _ |)) -> bprint " Roundtrip OK!\n"; true
    in
  b && b'
  (*
  print !$" - ClientHello (low-level)\n";
  let b' =
    let open FStar.UInt32 in
    let lb = from_bytes chb in
    let slice = { LPL.base = lb; LPL.len = B.len chb } in
    if ClientHello.clientHello_validator slice 0ul >^ LPL.validator_max_length then
      (print !$"Validator failed on ClientHello!\n"; false)
    else
      let pos_random = ClientHello.accessor_clientHello_random slice 0ul in
      let p_random = LB.sub lb pos_random 32ul in
      bprint (sprintf " Read client_random: %s" (B.hex_of_bytes (B.of_buffer 32ul p_random)));
      true
    in
  b && b' *)



// called from Test.Main
let main () : St C.exit_code =
  match test_clientHello () with
  | false ->
    print !$"ClientHello test failed.\n";
    C.EXIT_FAILURE
  | true ->
    print !$"ClientHello test succeeded.\n";
    C.EXIT_SUCCESS
