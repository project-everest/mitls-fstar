module Test.CommonDH

open FStar.Bytes
open FStar.Error
open FStar.Printf
open FStar.HyperStack
open FStar.HyperStack.ST

open TLSError
open TLSConstants
open Format.NamedGroup
open Format.NamedGroupList

module DH = CommonDH

#set-options "--lax"

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
  let gx = DH.ipubshare initiator_key_and_share in
  let gy, gxy = DH.dh_responder group gx in
  let gxy' = DH.dh_initiator group initiator_key_and_share gy in
  let gxy  = hex_of_bytes gxy in
  let gxy' = hex_of_bytes gxy' in
  if gxy = gxy' then true
  else
    begin
      print ("Unexpected output: output = " ^ gxy' ^ "\nexpected = " ^ gxy);
      false
    end

let groups : namedGroupList =
  [
    SECP256R1;
    SECP384R1;
    SECP521R1;
    X25519;
    FFDHE2048;
    FFDHE3072;
    FFDHE4096;
    FFDHE6144;
    FFDHE8192;
    // TODO: Not implemented; see ECGroup.fst
    //X448
  ]

let rec test_groups (groups:namedGroupList) : St bool =
  match groups with
  | g :: gs ->
    let Some group = DH.group_of_namedGroup g in
    print ("Testing " ^ DH.string_of_group group);
    if not (test group) then false else test_groups gs
  | _ -> true

// Called from Test.Main
let main () =
  if test_groups groups then C.EXIT_SUCCESS else C.EXIT_FAILURE
