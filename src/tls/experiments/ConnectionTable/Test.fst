module Test

open ConnectionTable_Aux
open ConnectionTable

open FStar.HyperStack.ST

#set-options "--z3rlimit 100"// --max_fuel 0 --max_ifuel 0"

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
module T = FStar.Monotonic.DependentMap

let test
  (cfg:configuration)
  (ch1:client_hello{~(has_cookie ch1) /\ ch_random ch1 == 0ul})
  (ch2:client_hello{has_cookie ch2 /\ ch_random ch2 == 0ul})
: ST connection_table
  (requires fun _ ->
      witnessed (region_contains_pred rgn) /\ ch_of_cookie ch2 == ch1 /\
    ~(ch_compatible ch1 cfg))
  (ensures  fun h0 t h1 -> 
    if model then 
      let t:_connection_table = t in
      inv t h1
    else True)
=
  let id1:maybe_id = if model then 1ul else () in
  let id2:maybe_id = if model then 2ul else () in
  let t = alloc () in
  let c1 = create t id1 cfg in
  receive_client_hello1 t id1 c1 ch1;
  free_connection t id1 c1;
  let h1 = get () in
  assert (
    if model then
      let t:_connection_table = t in
      ~(T.defined t id2 h1)
    else True);
  let c2 = create t id2 cfg in
  if receive_client_hello2 t id2 c2 ch2 then 
    receive_client_finished t id2 c2;
  free_connection t id2 c2;
  t
