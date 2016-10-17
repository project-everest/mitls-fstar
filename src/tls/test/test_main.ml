(* Main driver for tests. *)

let _ =
  Parsing_test.main ();
  TestRecord.main ();
(*  TestDH.main (); -- NS: 10/17 disabling this temporarily until further investigation *)
  Test_hkdf.main ();
  TestGCM.main ();
  ()
