(* Main driver for tests. *)

let _ =
  Parsing_test.main ();
  TestRecord.main ();
  TestDH.main ();
  TestClient.main ();
  ()
