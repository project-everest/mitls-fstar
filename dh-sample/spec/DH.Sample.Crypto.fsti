module DH.Sample.Crypto

(**
  Abstract concrete cryptography.  These laws provide functional correctness,
  not computational DH hardness or signature unforgeability.
*)

open DH.Sample.Types

val public_share:
  scalar ->
  Tot share

val derive:
  scalar ->
  share ->
  Tot session_key

val lemma_agreement
  (left right:scalar)
  : Lemma
      (ensures
        derive left (public_share right) ==
        derive right (public_share left))

val transcript:
  principal ->
  share ->
  share ->
  Tot bytes

val sign:
  principal ->
  bytes ->
  Tot signature

val verify:
  principal ->
  bytes ->
  signature ->
  Tot prop

val lemma_signatures_verify
  (signer:principal)
  (content:bytes)
  : Lemma
      (ensures
        verify signer content (sign signer content))
