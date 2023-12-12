module MiTLS.Test.Parsers
open MiTLS

open MiTLS.C.String
open FStar.Error
open FStar.HyperStack.ST
open LowStar.BufferOps
open MiTLS.Parsers

module B = FStar.Bytes
module LB = LowStar.Buffer
module LPL = LowParse.Low.Base

open FStar.Printf
open MiTLS.TLSError
open MiTLS.TLSConstants

// No need to verify test for now
#set-options "--admit_smt_queries true"

noextract let discard _ : ST unit
  (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1))
  = ()
inline_for_extraction noextract
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
  let chb = B.bytes_of_hex "010001fc0303b30cf9db2c59d0480d35bbb18033ec4f1028e6e55152b1b12dd7c9a1d481c59d208e0ba25081bc93271b829c0ca05d1981455fe006e36342a9ad5694c78ed81fae00221a1a130113021303c02bc02fc02cc030cca9cca8c013c014009c009d002f0035000a010001918a8a0000ff0100010000000010000e00000b74657374332e68742e76630017000000230000000d00140012040308040401050308050501080606010201000500050100000000001200000010000e000c02683208687474702f312e3175500000000b000201000033002b0029aaaa000100001d0020ab558f928509b78605488a081ca63f24c99777251885e31bfe1d976fe5e8f22b002d00020101002b000b0a8a8a0304030303020301000a000a0008aaaa001d00170018001b0003020002fafa000100001500c9000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" in
  print !$" - ClientHello (intermediate)\n";
  let b =
    match ClientHello.clientHello_parser32 chb with
    | None -> false
    | Some (ch, len) ->
      if B.len chb <> len then
	(print !$"leftover bytes after parsing!\n"; false)
      else
	if ClientHello.clientHello_serializer32 ch <> chb then
	(print !$"roundtrip serialization failed!\n"; false)
	else
          true
    in
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
  b && b'

// called from Test.Main
let main () : St C.exit_code =
  match test_clientHello () with
  | false ->
    print !$"ClientHello test failed.\n";
    C.EXIT_FAILURE
  | true ->
    print !$"ClientHello test succeeded.\n";
    C.EXIT_SUCCESS
