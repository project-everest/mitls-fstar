module TestDH

open Platform.Bytes
open CoreCrypto
open CommonDH
open TLSConstants

let main () =
  let group = default_group in
  let gx = keygen group in
  let gy, gxy = dh_responder gx in
  let gxy' = dh_initiator gx gy in
  let gxy  = hex_of_bytes gxy in
  let gxy' = hex_of_bytes gxy' in
  if gxy = gxy' then
    IO.print_string ("DH exchange test: OK\n")
  else
    begin
      IO.print_string ("DH exchange test: KO\n");
      IO.print_string ("Unexpected output: output = " ^ gxy' ^ "\nexpected = " ^ gxy ^ "\n");
      failwith "Error!"
    end
