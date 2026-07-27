module DH.Sample.Crypto

(**
  DH.Sample.Crypto — the trusted cryptographic interface of the DH sample.

  This module deliberately provides NO executable toy implementation.  Its
  operations are abstract, and clients may use only the functional-correctness
  laws stated here:

    * `dh_exp x` computes the public share corresponding to private scalar `x`;
    * `dh_agree x (dh_exp y)` and `dh_agree y (dh_exp x)` agree;
    * a signature produced by `sign` is accepted by `verify`;
    * `transcript` constructs the signed protocol transcript.

  In particular, the interface exposes no inverse from a public share to its
  scalar and no concrete arithmetic from which such an inverse can be derived.

  This `.fsti` has intentionally no implementation in `dh-sample`.  It is an
  explicit trusted boundary to be instantiated by a real cryptographic library.
  The interface laws below state correctness only.  Computational assumptions
  such as CDH hardness and EUF-CMA security are not expressible as these simple
  F* equations and are not machine-checked by this development; they belong to
  the chosen implementation and to a future computational refinement proof.
  The current symbolic theorem instead proves security in the DY* model and
  names the ideal source-machine boundaries used to connect signature
  acceptance to symbolic provenance.
*)

open DH.Sample.Types

(** Derive a public DH share from a private scalar. *)
val dh_exp : dh_scalar -> Tot dh_share

(** Derive a session secret from a private scalar and a peer public share. *)
val dh_agree : dh_scalar -> dh_share -> Tot shared_secret

(** Functional correctness of two-party DH key agreement. *)
val lemma_dh_agree (x y:dh_scalar)
  : Lemma (ensures dh_agree x (dh_exp y) == dh_agree y (dh_exp x))

(** Construct the protocol transcript signed by each role. *)
val transcript : principal -> dh_share -> dh_share -> Tot bytes

(** Produce and verify signatures under a principal's abstract signing key. *)
val sign : principal -> bytes -> Tot signature
val verify : principal -> bytes -> signature -> Tot prop

(** Functional correctness of signature generation and verification. *)
val lemma_sign_verify (signer:principal) (content:bytes)
  : Lemma (ensures verify signer content (sign signer content))
