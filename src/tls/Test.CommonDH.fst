module Test.CommonDH

open FStar.Bytes
open FStar.Error
open FStar.Printf
open FStar.HyperStack
open FStar.HyperStack.ST


open Parse
open TLSError
open TLSConstants

module DH = CommonDH

let prefix = "Test.CommonDH"

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string (prefix^": "^s^".\n"))
// let print = C.String,print
// let print = FStar.HyperStack.IO.print_string

val test: DH.group -> St bool
let test group =
  let initiator_key_and_share = DH.keygen group in
  let gx = DH.pubshare initiator_key_and_share in
  let gy, gxy = DH.dh_responder gx in
  let gxy' = DH.dh_initiator initiator_key_and_share gy in
  let gxy  = hex_of_bytes gxy in
  let gxy' = hex_of_bytes gxy' in
  if gxy = gxy' then true
  else
    begin
      print ("Unexpected output: output = " ^ gxy' ^ "\nexpected = " ^ gxy);
      false
    end

let groups : list Parse.namedGroup =
  let open CoreCrypto in
  let open Parse in
  [
    FFDHE FFDHE2048;
    FFDHE FFDHE3072;
    FFDHE FFDHE4096;
    FFDHE FFDHE6144;
    FFDHE FFDHE8192;
    SEC ECC_P256;
    SEC ECC_P384;
    SEC ECC_P521;
    SEC ECC_X25519;
    // TODO: Not implemented; see ECGroup.fst
    //SEC ECC_X448
  ]

let rec test_groups (groups:list Parse.namedGroup) : St bool =
  match groups with
  | g :: gs ->
    let Some group = DH.group_of_namedGroup g in
    print ("Testing " ^ DH.string_of_group group);
    test group && test_groups gs
  | _ -> true

// Called from Test.Main
let main () =
  if test_groups groups then C.EXIT_SUCCESS else C.EXIT_FAILURE
