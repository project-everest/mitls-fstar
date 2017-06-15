module TestDH

open Platform.Bytes
open CoreCrypto
open CommonDH
open TLSConstants

val discard: bool -> ST unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1))
let discard _ = ()
let print s = discard (IO.debug_print_string ("TestKS| "^s^"\n"))


let main () : ML unit =
  let g = default_group in
  let gx = keygen g in
  let gy, gxy = dh_responder #g (pubshare gx) in
  let gxy' = dh_initiator #g gx gy in
  let gxy  = hex_of_bytes gxy in
  let gxy' = hex_of_bytes gxy' in
  if gxy = gxy' then
    print ("DH exchange test: OK\n")
  else
    begin
      print ("DH exchange test: KO\n");
      print ("Unexpected output: output = " ^ gxy' ^ "\nexpected = " ^ gxy ^ "\n");
      failwith "Error!"
    end
