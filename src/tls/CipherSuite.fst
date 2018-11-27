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

#reset-options
