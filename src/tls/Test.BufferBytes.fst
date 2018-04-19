module Test.BufferBytes

open FStar.Bytes
open FStar.Error
open FStar.Printf
open FStar.HyperStack
open FStar.HyperStack.IO
open FStar.HyperStack.ST

module BB = BufferBytes

let lbuffer (l:nat) = b:Buffer.buffer UInt8.t {Buffer.length b == l}

#reset-options "--admit_smt_queries true"
let test _ =
   let b1 = Bytes.bytes_of_hex "1234567890abcdef1234567890abcdef" in
   let b2 = Bytes.bytes_of_hex "cafedecafbabedeadbeeffeec0ffee33" in
   assume(UInt.fits (UInt32.v (len b1)) 32);
   assume(UInt.fits (UInt32.v (len b2)) 32);
   let buf1 = BB.from_bytes b1 in
   let buf1 : lbuffer 16 = buf1 in
   let buf2 = BB.from_bytes b2 in
   let buf2 : lbuffer 16 = buf2 in
   let b1' = BB.to_bytes 16 buf1 in
   let b2' = BB.to_bytes 16 buf2 in
   let b12 = Bytes.append b1' b2' in
   let buf3 = Buffer.create 0xAAuy (UInt32.uint_to_t 32) in
   BB.store_bytes 32 buf3 16 b12;
   BB.store_bytes 16 buf3 0 b12;
   let b3 = BB.to_bytes 32 buf3 in
   print_string ("b1 = " ^ (Bytes.hex_of_bytes b1) ^ "\n");
   print_string ("b2 = " ^ (Bytes.hex_of_bytes b2) ^ "\n");
   print_string ("b12= " ^ (Bytes.hex_of_bytes b12) ^ "\n");
   print_string ("b3 = " ^ (Bytes.hex_of_bytes b3) ^ "\n");
   b1 = b1' && b2 = b2' && b12 = b3

// Called from Test.Main
let main () =
  if test () then C.EXIT_SUCCESS else C.EXIT_FAILURE
