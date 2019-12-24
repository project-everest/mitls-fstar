module CipherSuite

let name_of_cipherSuite_of_name =
   _ by (
     let open FStar.Tactics in
     let n = intro () in
     destruct (binder_to_term n); 
     let _ = repeat (fun () -> iseq [fun () ->
       let breq = intro () in rewrite breq ; norm [delta; iota; zeta; primops]; trivial ()
     ])
     in
     let _ = intro () in
     let breq = intro () in
     rewrite breq;
     norm [delta; iota; zeta; primops];
     trivial ()
   )

#reset-options "--max_ifuel 8 --initial_ifuel 8 --max_fuel 2 --initial_fuel 2 --z3cliopt smt.arith.nl=false --z3rlimit 256 --using_facts_from '* -LowParse.Spec.Base'"

let cipherSuite_of_name_of_cipherSuite c = ()

//#reset-options
//#set-options "--admit_smt_queries true"
let cipherSuiteName_of_cipherSuite13_of_cipherSuiteName _ = ()

let cipherSuite13_of_cipherSuiteName_of_cipherSuite13 _ = ()

let cipherSuite13_of_cipherSuite_of_cipherSuite13 _ = ()

let cipherSuite_of_cipherSuite13_of_cipherSuite _ = ()

let cipherSuite13_writer =
  fun c #rrel #rel out pos ->
  begin match c with
  | Constraint_TLS_AES_128_GCM_SHA256 _ -> finalize_cipherSuite13_TLS_AES_128_GCM_SHA256 out pos
  | Constraint_TLS_AES_256_GCM_SHA384 _ -> finalize_cipherSuite13_TLS_AES_256_GCM_SHA384 out pos
  | Constraint_TLS_CHACHA20_POLY1305_SHA256 _ -> finalize_cipherSuite13_TLS_CHACHA20_POLY1305_SHA256 out pos
  | Constraint_TLS_AES_128_CCM_SHA256 _ -> finalize_cipherSuite13_TLS_AES_128_CCM_SHA256 out pos
  | Constraint_TLS_AES_128_CCM_8_SHA256 _ -> finalize_cipherSuite13_TLS_AES_128_CCM_8_SHA256 out pos
  end;
  pos `UInt32.add` 2ul

let cipherSuite13_reader =
  fun #rrel #rel inp pos ->
  let c = cipherSuite_reader inp pos in
  cipherSuite13_of_cipherSuiteName c
