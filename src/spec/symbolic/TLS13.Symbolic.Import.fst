module TLS13.Symbolic.Import

(*
 * Convenience import and dependency smoke test for the complete TLS symbolic
 * development.  Importing this module forces all foundation, product,
 * invariant, authentication, secrecy, and record-security modules to resolve.
 * The small aliases below are not security claims.
 *)

module DY = DY.Core
module Authentication = TLS13.Symbolic.Authentication
module Bridge = TLS13.Symbolic.Bridge
module Events = TLS13.Symbolic.Events
module Invariant = TLS13.Symbolic.Invariant
module Labels = TLS13.Symbolic.Labels
module Lemmas = TLS13.Symbolic.Lemmas
module Profile = TLS13.Symbolic.Profile
module Product = TLS13.Symbolic.Product
module RecordSecurity = TLS13.Symbolic.RecordSecurity
module Secrecy = TLS13.Symbolic.Secrecy
module Terms = TLS13.Symbolic.Terms
module Usages = TLS13.Symbolic.Usages

(* Identity smoke test confirming that the DY byte type is in scope. *)
let core_import_smoke (x:DY.bytes) : DY.bytes = x

(* Re-export the symbolic proof profile's fixed cipher suite. *)
let profile_cipher_suite = Profile.profile_cipher_suite

(* Re-export the canonical symbolic empty transcript. *)
let empty_transcript = Terms.empty_transcript

(* Re-export the TLS-specific DY cryptographic usage classification. *)
let crypto_usages = Usages.tls_crypto_usages
