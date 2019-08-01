module Test

open ConnectionTable_Aux
open ConnectionTable

open FStar.HyperStack.ST

#set-options "--z3rlimit 100"

(*
   This tests the server side of a full handshake with mismatched parameters:

   1. Allocate an empty connection table
   2. Create a first connection c1 with id = 1 (in Init state)
   3. Receive a ClientHello ch1 with random 0 on c1. Transition c1 to Sent_HRR 0 ch1
   4. Deallocate c1
   5. Create a second connection c2 (in Init state)
   6. Receive a ClientHello ch2 on c2 with a random and cookie extension matching ch1.
   7. If the configuration of c2 is compatible with ch2,
      a. Transition c2 to Sent_ServerHello 0 ch2 1, with c1 as the matching initial connection
      b. Receive a ClientFinished on c2. Transition c2 to Complete 0 ch2 1
   8. Deallocate c2
*)
let test
  (cfg:configuration)
  (ch1:client_hello{~(has_cookie ch1) /\ ch_random ch1 == 0ul})
  (ch2:client_hello{has_cookie ch2 /\ ch_random ch2 == 0ul})
: ST connection_table
  (requires fun _ ->
    witnessed (region_contains_pred rgn) /\ ch_of_cookie ch2 == ch1 /\
    ~(ch_compatible ch1 cfg))
  (ensures  fun h0 t h1 -> inv t h1)
=
  let t = alloc () in
  let c1 = create t 1ul cfg in
  receive_client_hello1 t 1ul ch1;
  free_connection t 1ul;
  let c2 = create t 2ul cfg in
  if receive_client_hello2 t 2ul ch2 then receive_client_finished t 2ul;
  free_connection t 2ul;
  t
