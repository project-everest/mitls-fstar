module Test.BindersAge

module LWP = LowParse.Writers.NoHoare.Combinators
module U32 = FStar.UInt32
module B = LowStar.Buffer

let hash_len (c: Parsers.CipherSuite13.cipherSuite13) : Tot (u: U32.t { 32 <= U32.v u /\ U32.v u <= 255 }) =
  let open Parsers.CipherSuite13 in
  match c with
  | Constraint_TLS_AES_128_GCM_SHA256 _ -> 32ul
  | Constraint_TLS_AES_256_GCM_SHA384 _ -> 48ul
  | Constraint_TLS_CHACHA20_POLY1305_SHA256 _ -> 32ul
  | Constraint_TLS_AES_128_CCM_SHA256 _ -> 32ul
  | Constraint_TLS_AES_128_CCM_8_SHA256 _ -> 32ul

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let compute_binder_ph1
  (inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
  ()
: LWP.TWrite unit LWP.parse_empty Parsers.PskBinderEntry.lwp_pskBinderEntry inv
=
  let cs = Parsers.TicketContents13.lwp_accessor_ticketContents13_cs tc in
  let c = LWP.deref Parsers.CipherSuite13.cipherSuite13_reader cs in
  let len : U32.t = hash_len c in
  LWP.put_vlbytes 32ul 255ul len (Seq.create (U32.v len) 0uy) (fun b ->
    B.fill b 0uy len
  )

 //  ; LWP.valid_rewrite Parsers.PskBinderEntry.pskBinderEntry_lwp_rewrite // automatic thanks to subcomp

[@@ noextract_to "Kremlin"] noextract
let compute_binder_ph2 = compute_binder_ph1 // to avoid inline_for_extraction in effect indices, implicit args, etc.

// this will be extracted as a C function
let extract_compute_binder
  (inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: Tot (LWP.extract_t inv (compute_binder_ph2 inv tc))
= LWP.extract _ (compute_binder_ph1 inv tc)

// this will be inlined as an explicit function call
inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let compute_binder_ph
  (#inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: LWP.TWrite unit LWP.parse_empty Parsers.PskBinderEntry.lwp_pskBinderEntry inv
= LWP.wrap_extracted_impl _ _ (extract_compute_binder inv tc)

inline_for_extraction
let encode_age age mask = U32.(age +%^ mask)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let obfuscate_age1
  (inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
  ()
: LWP.TWrite unit LWP.parse_empty Parsers.PskIdentity.lwp_pskIdentity inv
=
  let id = Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_identity ri in
  let tk = Parsers.ResumeInfo13.lwp_accessor_resumeInfo13_ticket ri in
  let ct = Parsers.TicketContents13.lwp_accessor_ticketContents13_creation_time tk in
  let creation_time = LWP.deref LowParse.Low.Int.read_u32 ct in
  let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
  let aa = Parsers.TicketContents13.lwp_accessor_ticketContents13_age_add tk in
  let age_add = LWP.deref LowParse.Low.Int.read_u32 aa in
  let obfuscated_age = encode_age age age_add in
  Parsers.PskIdentity.pskIdentity_lwriter
    (fun _ -> LWP.cat id)
    (fun _ -> LWP.start LWP.parse_u32 LowParse.Low.Int.write_u32 obfuscated_age)

[@@ noextract_to "Kremlin"] noextract
let obfuscate_age2 = obfuscate_age1

let extract_obfuscate_age
  (inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: Tot (LWP.extract_t inv (obfuscate_age2 inv now ri))
= LWP.extract inv (obfuscate_age1 inv now ri)

inline_for_extraction
[@@ noextract_to "Kremlin"] noextract
let obfuscate_age
  (#inv: LWP.memory_invariant)
  (now: U32.t)
  (ri: LWP.ptr Parsers.ResumeInfo13.lwp_resumeInfo13 inv)
: LWP.TWrite unit LWP.parse_empty Parsers.PskIdentity.lwp_pskIdentity inv
= LWP.wrap_extracted_impl _ _ (extract_obfuscate_age inv now ri)

