module NSL.Sample.Crypto

(**
  Abstract concrete PKE boundary.  This interface states functional correctness
  only; the computational-to-DY correspondence is an explicit premise of the
  security theorem.
 *)

open NSL.Sample.Types

val encrypt:
  recipient:principal ->
  randomness:pke_randomness ->
  message:plaintext ->
  Tot ciphertext

val decrypt:
  recipient:principal ->
  ciphertext ->
  Tot (option plaintext)

val lemma_decrypt_encrypt
  (recipient:principal)
  (randomness:pke_randomness)
  (message:plaintext)
  : Lemma
      (ensures
        decrypt recipient (encrypt recipient randomness message) ==
        Some message)
