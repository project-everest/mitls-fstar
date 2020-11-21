module Test

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LP = LowParse.Low.Base
module B = LowStar.Buffer
module LPW = LowParse.Low.Writers

#reset-options "--z3cliopt smt.arith.nl=false"

#push-options "--z3rlimit 64 --query_stats"

#restart-solver

let hash_len (c: Parsers.CipherSuite13.cipherSuite13) : Tot (u: U32.t { 32 <= U32.v u /\ U32.v u <= 255 }) =
  let open Parsers.CipherSuite13 in
  match c with
  | Constraint_TLS_AES_128_GCM_SHA256 _ -> 32ul
  | Constraint_TLS_AES_256_GCM_SHA384 _ -> 48ul
  | Constraint_TLS_CHACHA20_POLY1305_SHA256 _ -> 32ul
  | Constraint_TLS_AES_128_CCM_SHA256 _ -> 32ul
  | Constraint_TLS_AES_128_CCM_8_SHA256 _ -> 32ul

inline_for_extraction
noextract
let write_binder_ph
  (#rrel #rel: _)
  (sin: LP.slice rrel rel)
  (pin: U32.t)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    LP.live_slice h sin /\
    LP.live_slice h sout /\
    U32.v pout_from <= U32.v sout.LP.len /\
    U32.v sout.LP.len < U32.v LP.max_uint32 /\ // to error code
    LP.valid Parsers.TicketContents13.ticketContents13_parser h sin pin /\
    B.loc_disjoint (LP.loc_slice_from_to sin pin (LP.get_valid_pos Parsers.TicketContents13.ticketContents13_parser h sin pin)) (LP.loc_slice_from sout pout_from)
  ))
  (ensures (fun h pout_to h' ->
    B.modifies (LP.loc_slice_from sout pout_from) h h' /\ (
    if pout_to = LP.max_uint32
    then
      True
    else
      LP.valid_pos Parsers.PskBinderEntry.pskBinderEntry_parser h' sout pout_from pout_to
  )))
=
  let h0 = HST.get () in
  let c = Parsers.CipherSuite13.cipherSuite13_reader sin (Parsers.TicketContents13.accessor_ticketContents13_cs sin pin) in
  let len : U32.t = hash_len c in
  if (1ul `U32.add` len) `U32.gt` (sout.LP.len `U32.sub` pout_from)
  then begin
    LP.max_uint32
  end else begin
    let pout_payload = pout_from `U32.add` 1ul in
    // TODO: replace with a custom fill once target slice is replaced with the stash
    B.fill (B.sub sout.LP.base pout_payload len) 0uy len;
    Parsers.PskBinderEntry.pskBinderEntry_finalize sout pout_from len
  end

#restart-solver

inline_for_extraction
let encode_age age mask = U32.(age +%^ mask)

inline_for_extraction
noextract
let write_obfuscate_age
  (now: U32.t)
  (#rrel #rel: _)
  (sin: LP.slice rrel rel)
  (pin: U32.t)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from: U32.t)
: HST.Stack U32.t
  (requires (fun h ->
    LP.valid Parsers.ResumeInfo13.resumeInfo13_parser h sin pin /\
    B.loc_disjoint (LP.loc_slice_from_to sin pin (LP.get_valid_pos Parsers.ResumeInfo13.resumeInfo13_parser h sin pin)) (LP.loc_slice_from sout pout_from) /\
    LP.live_slice h sout /\
    U32.v pout_from <= U32.v sout.LP.len /\
    U32.v sout.LP.len < U32.v LP.max_uint32
  ))
  (ensures (fun h res h' ->
    B.modifies (LP.loc_slice_from sout pout_from) h h' /\ (
    if res = LP.max_uint32
    then True
    else LP.valid_pos Parsers.PskIdentity.pskIdentity_parser h' sout pout_from res
  )))
= let h = HST.get () in
  let sin_id = Parsers.ResumeInfo13.accessor_resumeInfo13_identity sin pin in
  let pout_oage = LP.copy_weak _ Parsers.PskIdentity.pskIdentity_identity_jumper sin sin_id sout pout_from in
  if pout_oage = LP.max_uint32
  then LP.max_uint32
  else if 4ul `U32.gt` (sout.LP.len `U32.sub` pout_oage)
  then LP.max_uint32
  else begin
    let pin_tkt = Parsers.ResumeInfo13.accessor_resumeInfo13_ticket sin pin in
    let creation_time = LowParse.Low.Int.read_u32 sin (Parsers.TicketContents13.accessor_ticketContents13_creation_time sin pin_tkt) in
    let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
    let age_add = LowParse.Low.Int.read_u32 sin (Parsers.TicketContents13.accessor_ticketContents13_age_add sin pin_tkt) in
    let obfuscated_age = encode_age age age_add in
    let pout_to = LowParse.Low.Int.write_u32 obfuscated_age sout pout_oage in
    let h' = HST.get () in
    Parsers.PskIdentity.pskIdentity_valid h' sout pout_from;
    pout_to
  end

let main () : Tot C.exit_code = C.EXIT_SUCCESS
