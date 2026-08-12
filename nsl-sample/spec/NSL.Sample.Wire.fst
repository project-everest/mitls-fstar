module NSL.Sample.Wire

(** NSL transports one opaque public-key ciphertext per flight. *)

open NSL.Sample.Types

noeq
type message =
  | Encrypted:
      ciphertext ->
      message
