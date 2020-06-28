module Negotiation.Writers.LayeredEffects

friend Negotiation

module LWP = LowParseWriters.Parsers
module Aux = Negotiation.Writers.Aux
module Aux2 = Negotiation.Writers.Aux2

#reset-options "--z3cliopt smt.arith.nl=false"

open TLSConstants
open Extensions
open Negotiation

module U32 = FStar.UInt32
module B = LowStar.Buffer

#push-options "--z3rlimit 16 --query_stats"

let write_binder_ph'
  (#inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
  ()
: LWP.Write unit LWP.emp lwp_pskBinderEntry (fun _ -> True) (fun _ _ out -> out == compute_binder_ph_new (LWP.deref_spec tc)) inv
=
  let c = LWP.deref CipherSuite.cipherSuite13_reader (Parsers.TicketContents13.lwp_accessor_ticketContents13_cs tc) in
  let (CipherSuite13 _ h) = cipherSuite_of_cipherSuite13 c in
  let len : U32.t = Hacl.Hash.Definitions.hash_len h in
  LWP.put_vlbytes 32ul 255ul len (Seq.create (U32.v len) 0uy) (fun b ->
    B.fill b 0uy len
  );
  LWP.valid_synth _ _ _ _ _ Aux.valid_pskBinderEntry_intro

let write_obfuscate_age'
  (#inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  ()
: LWP.Write unit LWP.emp Parsers.PskIdentity.lwp_pskIdentity (fun _ -> True) (fun _ _ out -> out == obfuscate_age_new now (LWP.deref_spec ri)) inv
=
  LWP.cat (Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_identity ri);
  let tk = Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_ticket ri in
  let creation_time = LWP.deref LowParse.Low.Int.read_u32 (Parsers.TicketContents13.lwp_accessor_ticketContents13_creation_time tk) in
  let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
  let age_add = LWP.deref LowParse.Low.Int.read_u32 (Parsers.TicketContents13.lwp_accessor_ticketContents13_age_add tk) in
  let obfuscated_age = PSK.encode_age age age_add in
  LWP.append LWP.parse_u32 LowParse.Low.Int.write_u32 obfuscated_age;
  LWP.valid_synth _ _ _ _ _ Aux.valid_pskIdentity_intro

#pop-options
