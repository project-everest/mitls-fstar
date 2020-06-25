module Negotiation.Writers

friend Negotiation

open FStar.Bytes

open Mem
open TLS.Result
open TLSInfo
open TLSConstants
open HandshakeMessages

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

module LWP = LowParseWriters.Parsers
module Aux = Negotiation.Writers.Aux

open Extensions
open Negotiation

#reset-options "--z3cliopt smt.arith.nl=false"

#push-options "--z3rlimit 16 --query_stats"

let write_binder_ph'
  (#inv: LWP.memory_invariant)
  (tc: LWP.ptr Parsers.TicketContents13.lwp_ticketContents13 inv)
: LWP.Write unit LWP.emp lwp_pskBinderEntry (fun _ -> True) (fun _ _ out -> out == compute_binder_ph_new (LWP.deref_spec tc)) inv
=
  let c = LWP.deref CipherSuite.cipherSuite13_reader (LWP.access Parsers.TicketContents13.lwp_ticketContents13 Parsers.CipherSuite13.lwp_cipherSuite13 Parsers.TicketContents13.accessor_ticketContents13_cs tc) in
  let (CipherSuite13 _ h) = cipherSuite_of_cipherSuite13 c in
  let len : U32.t = Hacl.Hash.Definitions.hash_len h in
  LWP.put_vlbytes 32ul 255ul len (Seq.create (U32.v len) 0uy) (fun b ->
    B.fill b 0uy len
  );
  LWP.valid_synth _ _ _ _ _ Aux.valid_pskBinderEntry_intro

#pop-options

#push-options "--z3rlimit 64 --query_stats"

#restart-solver

(* implementation of the new spec *)

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
    let ph = compute_binder_ph_new (LP.contents Parsers.TicketContents13.ticketContents13_parser h sin pin) in
    if pout_to = LP.max_uint32
    then
      U32.v pout_from + LP.serialized_length pskBinderEntry_serializer ph > U32.v sout.LP.len
    else
      LP.valid_content_pos pskBinderEntry_parser h' sout pout_from ph pout_to
  )))
= let h0 = HST.get () in
  let ph = Ghost.hide (compute_binder_ph_new (LP.contents Parsers.TicketContents13.ticketContents13_parser h0 sin pin)) in
  let c = CipherSuite.cipherSuite13_reader sin (Parsers.TicketContents13.accessor_ticketContents13_cs sin pin) in
  let (CipherSuite13 _ h) = cipherSuite_of_cipherSuite13 c in
  let len : U32.t = Hacl.Hash.Definitions.hash_len h in
  if (1ul `U32.add` len) `U32.gt` (sout.LP.len `U32.sub` pout_from)
  then begin
    LP.serialized_length_eq pskBinderEntry_serializer (Ghost.reveal ph);
    pskBinderEntry_bytesize_eq (Ghost.reveal ph);
    LP.max_uint32
  end else begin
    let pout_payload = pout_from `U32.add` 1ul in
    // TODO: replace with a custom fill once target slice is replaced with the stash
    B.fill (B.sub sout.LP.base pout_payload len) 0uy len;
    pskBinderEntry_finalize sout pout_from len
  end

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
    let x = obfuscate_age_new now (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h sin pin) in
    B.modifies (LP.loc_slice_from sout pout_from) h h' /\ (
    if res = LP.max_uint32
    then U32.v pout_from + LP.serialized_length pskIdentity_serializer x > U32.v sout.LP.len
    else LP.valid_content_pos pskIdentity_parser h' sout pout_from x res
  )))
= let h = HST.get () in
  let x = Ghost.hide (obfuscate_age_new now (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h sin pin)) in
  LP.serialized_length_eq pskIdentity_serializer (Ghost.reveal x);
  pskIdentity_bytesize_eq (Ghost.reveal x);
  let sin_id = Parsers.ResumeInfo13.accessor_resumeInfo13_identity sin pin in
  pskIdentity_identity_bytesize_eq ((Ghost.reveal x).identity);
  LP.serialized_length_eq pskIdentity_identity_serializer ((Ghost.reveal x).identity);
  let pout_oage = LP.copy_weak _ pskIdentity_identity_jumper sin sin_id sout pout_from in
  if pout_oage = LP.max_uint32
  then LP.max_uint32
  else if 4ul `U32.gt` (sout.LP.len `U32.sub` pout_oage)
  then LP.max_uint32
  else begin
    let pin_tkt = Parsers.ResumeInfo13.accessor_resumeInfo13_ticket sin pin in
    let creation_time = LowParse.Low.Int.read_u32 sin (Parsers.TicketContents13.accessor_ticketContents13_creation_time sin pin_tkt) in
    let age = FStar.UInt32.((now -%^ creation_time) *%^ 1000ul) in
    let age_add = LowParse.Low.Int.read_u32 sin (Parsers.TicketContents13.accessor_ticketContents13_age_add sin pin_tkt) in
    let obfuscated_age = PSK.encode_age age age_add in
    let pout_to = LowParse.Low.Int.write_u32 obfuscated_age sout pout_oage in
    let h' = HST.get () in
    pskIdentity_valid h' sout pout_from;
    pout_to
  end

(* then, the writer *)

module LPW = LowParse.Low.Writers

let make_offeredPsks_identities
  (oidentities: option (list Parsers.PskIdentity.pskIdentity))
: GTot (option Parsers.OfferedPsks_identities.offeredPsks_identities)
= match oidentities with
  | Some identities ->
    if
      (let x = offeredPsks_identities_list_bytesize identities in 7 <= x && x <= 65535)
    then Some identities
    else None
  | _ -> None

inline_for_extraction
noextract
let write_offeredPsks_identities
  (#h0: HS.mem)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.olwriter Parsers.PskIdentity.pskIdentity_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter Parsers.OfferedPsks_identities.offeredPsks_identities_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_offeredPsks_identities (LPW.olwvalue w)
  })
= LPW.OWriter (Ghost.hide (make_offeredPsks_identities (LPW.olwvalue w))) (fun pout_from ->
    let f () : Lemma
      (requires (Some? (make_offeredPsks_identities (LPW.olwvalue w))))
      (ensures (
        match make_offeredPsks_identities (LPW.olwvalue w) with
        | None -> False
        | Some oi ->
          Some? (LPW.olwvalue w) /\
          LP.serialized_length Parsers.OfferedPsks_identities.offeredPsks_identities_serializer oi == 2 + LP.serialized_list_length Parsers.PskIdentity.pskIdentity_serializer (Some?.v (LPW.olwvalue w))
      ))
    = match make_offeredPsks_identities (LPW.olwvalue w) with
      | None -> ()
      | Some oi ->
        LP.serialized_length_eq Parsers.OfferedPsks_identities.offeredPsks_identities_serializer oi;
        Parsers.OfferedPsks_identities.offeredPsks_identities_bytesize_eq oi;
        Parsers.OfferedPsks_identities.offeredPsks_identities_list_bytesize_eq (Some?.v (LPW.olwvalue w))
    in
    assert (U32.v pout_from <= U32.v sout.LP.len);
    Classical.move_requires f ();
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else
      let res = LPW.olwrite w (pout_from `U32.add` 2ul) in
      if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res
      then
        res
      else begin
        let h = HST.get () in
        LP.valid_list_serialized_list_length Parsers.PskIdentity.pskIdentity_serializer h sout (pout_from `U32.add` 2ul) res;
        let len = res `U32.sub` (pout_from `U32.add` 2ul) in
        if len `U32.lt` 7ul || 65535ul `U32.lt` len
        then LP.max_uint32 `U32.sub` 1ul
        else begin
          Parsers.OfferedPsks_identities.finalize_offeredPsks_identities sout pout_from res;
          res
        end
      end
  )

let make_offeredPsks_binders
  (obinders: option (list Parsers.PskBinderEntry.pskBinderEntry))
: GTot (option Parsers.OfferedPsks_binders.offeredPsks_binders)
= match obinders with
  | Some binders ->
    if
      (let x = offeredPsks_binders_list_bytesize binders in 33 <= x && x <= 65535)
    then begin
      Some binders
    end
    else None
  | _ -> None

inline_for_extraction
noextract
let write_offeredPsks_binders
  (#h0: HS.mem)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.olwriter Parsers.PskBinderEntry.pskBinderEntry_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter Parsers.OfferedPsks_binders.offeredPsks_binders_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_offeredPsks_binders (LPW.olwvalue w)
  })
= LPW.OWriter (Ghost.hide (make_offeredPsks_binders (LPW.olwvalue w))) (fun pout_from ->
    let f () : Lemma
      (requires (Some? (make_offeredPsks_binders (LPW.olwvalue w))))
      (ensures (
        match make_offeredPsks_binders (LPW.olwvalue w) with
        | None -> False
        | Some oi ->
          Some? (LPW.olwvalue w) /\
          LP.serialized_length Parsers.OfferedPsks_binders.offeredPsks_binders_serializer oi == 2 + LP.serialized_list_length Parsers.PskBinderEntry.pskBinderEntry_serializer (Some?.v (LPW.olwvalue w))
      ))
    = match make_offeredPsks_binders (LPW.olwvalue w) with
      | None -> ()
      | Some oi ->
        LP.serialized_length_eq Parsers.OfferedPsks_binders.offeredPsks_binders_serializer oi;
        Parsers.OfferedPsks_binders.offeredPsks_binders_bytesize_eq oi;
        Parsers.OfferedPsks_binders.offeredPsks_binders_list_bytesize_eq (Some?.v (LPW.olwvalue w))
    in
    assert (U32.v pout_from <= U32.v sout.LP.len);
    Classical.move_requires f ();
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else
      let res = LPW.olwrite w (pout_from `U32.add` 2ul) in
      if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res
      then
        res
      else begin
        let h = HST.get () in
        LP.valid_list_serialized_list_length Parsers.PskBinderEntry.pskBinderEntry_serializer h sout (pout_from `U32.add` 2ul) res;
        let len = res `U32.sub` (pout_from `U32.add` 2ul) in
        if len `U32.lt` 33ul || 65535ul `U32.lt` len
        then LP.max_uint32 `U32.sub` 1ul
        else begin
          Parsers.OfferedPsks_binders.finalize_offeredPsks_binders sout pout_from res;
          res
        end
      end
  )

let make_preSharedKeyClientExtension
  (oi: option Parsers.OfferedPsks_identities.offeredPsks_identities)
  (ob: option Parsers.OfferedPsks_binders.offeredPsks_binders)
: GTot (option Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension)
= match oi, ob with
  | Some i, Some b -> Some ({ Parsers.OfferedPsks.identities = i; Parsers.OfferedPsks.binders = b; })
  | _ -> None

inline_for_extraction
noextract
let write_preSharedKeyClientExtension
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w_identities: LPW.owriter Parsers.OfferedPsks_identities.offeredPsks_identities_serializer h0 sout pout_from0)
  (w_binders: LPW.owriter Parsers.OfferedPsks_binders.offeredPsks_binders_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_preSharedKeyClientExtension (LPW.owvalue w_identities) (LPW.owvalue w_binders)
  })
= LPW.OWriter (Ghost.hide (make_preSharedKeyClientExtension (LPW.owvalue w_identities) (LPW.owvalue w_binders))) (fun pout_from ->
    Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_parser_serializer_eq ();
    let f () : Lemma
      (requires (Some? (make_preSharedKeyClientExtension (LPW.owvalue w_identities) (LPW.owvalue w_binders))))
      (ensures (
        match make_preSharedKeyClientExtension (LPW.owvalue w_identities) (LPW.owvalue w_binders) with
        | None -> False
        | Some w ->
          LP.serialized_length Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_serializer w ==
            LP.serialized_length Parsers.OfferedPsks_identities.offeredPsks_identities_serializer (Some?.v (LPW.owvalue w_identities)) +
            LP.serialized_length Parsers.OfferedPsks_binders.offeredPsks_binders_serializer (Some?.v (LPW.owvalue w_binders))
      ))
    = match make_preSharedKeyClientExtension (LPW.owvalue w_identities) (LPW.owvalue w_binders) with
      | None -> ()
      | Some w ->
        Parsers.OfferedPsks.offeredPsks_bytesize_eq w;
        LP.serialized_length_eq Parsers.OfferedPsks.offeredPsks_serializer w;
        Parsers.OfferedPsks_identities.offeredPsks_identities_bytesize_eq (Some?.v (LPW.owvalue w_identities));
        LP.serialized_length_eq Parsers.OfferedPsks_identities.offeredPsks_identities_serializer (Some?.v (LPW.owvalue w_identities));
        Parsers.OfferedPsks_binders.offeredPsks_binders_bytesize_eq (Some?.v (LPW.owvalue w_binders));
        LP.serialized_length_eq Parsers.OfferedPsks_binders.offeredPsks_binders_serializer (Some?.v (LPW.owvalue w_binders))
    in
    Classical.move_requires f ();
    let res1 = LPW.owrite w_identities pout_from in
    if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res1
    then res1
    else begin
      let res2 = LPW.owrite w_binders res1 in
      if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res2
      then
        res2
      else begin
        let h = HST.get () in
        Parsers.OfferedPsks.offeredPsks_valid h sout pout_from;
        res2
        end
      end
  )

let make_clientHelloExtension_CHE_pre_shared_key
  (o: option Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension)
: GTot (option clientHelloExtension_CHE_pre_shared_key)
= match o with
  | None -> None
  | Some x ->
    if
      (let l = Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_bytesize x in l <= 65535)
    then
      Some x
    else
      None

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_pre_shared_key
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.owriter Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter clientHelloExtension_CHE_pre_shared_key_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_clientHelloExtension_CHE_pre_shared_key (LPW.owvalue w)
  })
= LPW.OWriter (Ghost.hide (make_clientHelloExtension_CHE_pre_shared_key (LPW.owvalue w))) (fun pout_from ->
    Classical.forall_intro clientHelloExtension_CHE_pre_shared_key_bytesize_eq;
    Classical.forall_intro Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_serializer);
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_CHE_pre_shared_key_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else begin
      let res = LPW.owrite w (pout_from `U32.add` 2ul) in
      if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res
      then begin
        res
      end else
        let len = res `U32.sub` (pout_from `U32.add` 2ul) in
        if 65535ul `U32.lt` len
        then LP.max_uint32 `U32.sub` 1ul
        else begin
          clientHelloExtension_CHE_pre_shared_key_finalize sout pout_from res;
          res
        end
    end
  )

inline_for_extraction
let constr_clientHelloExtension_CHE_pre_shared_key
  (o: option clientHelloExtension_CHE_pre_shared_key)
: GTot (option clientHelloExtension)
= match o with
  | None -> None
  | Some x -> Some (CHE_pre_shared_key x)

inline_for_extraction
noextract
let write_constr_clientHelloExtension_CHE_pre_shared_key
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.owriter clientHelloExtension_CHE_pre_shared_key_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter clientHelloExtension_serializer h0 sout pout_from0 { LPW.owvalue y == constr_clientHelloExtension_CHE_pre_shared_key (LPW.owvalue w) } )
= LPW.OWriter (Ghost.hide (constr_clientHelloExtension_CHE_pre_shared_key (LPW.owvalue w))) (fun pout_from ->
    Classical.forall_intro clientHelloExtension_bytesize_eq;
    Classical.forall_intro clientHelloExtension_CHE_pre_shared_key_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_CHE_pre_shared_key_serializer);
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else begin
      let res = LPW.owrite w (pout_from `U32.add` 2ul) in
      if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res
      then begin
        res
      end else begin
        finalize_clientHelloExtension_pre_shared_key sout pout_from;
        res
      end
    end
  )

inline_for_extraction
noextract
let write_pskKeyExchangeModes
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.lwriter pskKeyExchangeMode_serializer h0 sout pout_from0 {
    let l = List.Tot.length (LPW.lwvalue w) in
    1 <= l /\ l <= 255
  })
: Tot (y: LPW.writer pskKeyExchangeModes_serializer h0 sout pout_from0 {
    LPW.wvalue y == LPW.lwvalue w
  })
= LPW.Writer (Ghost.hide (LPW.lwvalue w)) (fun pout_from ->
    Classical.forall_intro pskKeyExchangeModes_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq pskKeyExchangeModes_serializer);
    Classical.forall_intro (LP.serialized_length_eq pskKeyExchangeMode_serializer);
    Classical.forall_intro (LP.serialized_list_length_constant_size pskKeyExchangeMode_serializer);
    if 1ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else
      let res = LPW.lwrite w (pout_from `U32.add` 1ul) in
      if res = LP.max_uint32
      then begin
        res
      end
      else begin
        finalize_pskKeyExchangeModes sout pout_from res;
        res
      end
  )

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_psk_key_exchange_modes
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.writer pskKeyExchangeModes_serializer h0 sout pout_from0)
: Tot (y: LPW.writer clientHelloExtension_CHE_psk_key_exchange_modes_serializer h0 sout pout_from0 {
    LPW.wvalue y == LPW.wvalue w
  })
= LPW.Writer (Ghost.hide (LPW.wvalue w)) (fun pout_from ->
    Classical.forall_intro pskKeyExchangeModes_bytesize_eq;
    Classical.forall_intro clientHelloExtension_CHE_psk_key_exchange_modes_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq pskKeyExchangeModes_serializer);
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_CHE_psk_key_exchange_modes_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else
      let res = LPW.write w (pout_from `U32.add` 2ul) in
      if res = LP.max_uint32
      then res
      else begin
        clientHelloExtension_CHE_psk_key_exchange_modes_finalize sout pout_from res;
        res
      end
  )

inline_for_extraction
noextract
let write_constr_clientHelloExtension_CHE_psk_key_exchange_modes
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.writer clientHelloExtension_CHE_psk_key_exchange_modes_serializer h0 sout pout_from0)
: Tot (y: LPW.writer clientHelloExtension_serializer h0 sout pout_from0 { LPW.wvalue y == CHE_psk_key_exchange_modes (LPW.wvalue w) } )
= LPW.Writer (Ghost.hide (CHE_psk_key_exchange_modes (LPW.wvalue w))) (fun pout_from ->
    Classical.forall_intro clientHelloExtension_bytesize_eq;
    Classical.forall_intro clientHelloExtension_CHE_psk_key_exchange_modes_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_CHE_psk_key_exchange_modes_serializer);
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else begin
      let res = LPW.write w (pout_from `U32.add` 2ul) in
      if res = LP.max_uint32
      then begin
        res
      end else begin
        finalize_clientHelloExtension_psk_key_exchange_modes sout pout_from;
        res
      end
    end
  )

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data () : Tot (LP.leaf_writer_strong clientHelloExtension_CHE_early_data_serializer) =
  fun _ #rrel #rel sout pos ->
  clientHelloExtension_CHE_early_data_finalize sout pos;
  pos `U32.add` 2ul

inline_for_extraction
noextract
let write_constr_clientHelloExtension_CHE_early_data
  (h0: _)
  (sout: _)
  (pout_from0: _)
: Tot (y: LPW.writer clientHelloExtension_serializer h0 sout pout_from0 { LPW.wvalue y == CHE_early_data () })
= LPW.Writer (Ghost.hide (CHE_early_data ())) (fun pout_from ->
    Classical.forall_intro clientHelloExtension_bytesize_eq;
    Classical.forall_intro clientHelloExtension_CHE_early_data_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_CHE_early_data_serializer);
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else
      let res = LPW.write (LPW.write_leaf_cs (write_clientHelloExtension_CHE_early_data ()) h0 sout pout_from0 ()) (pout_from `U32.add` 2ul) in
      if res = LP.max_uint32
      then res
      else begin
        finalize_clientHelloExtension_early_data sout pout_from;
        res
      end
  )

#push-options "--z3rlimit 256 --query_stats --print_z3_statistics --max_ifuel 8 --initial_ifuel 8"

module L = FStar.List.Tot

inline_for_extraction
noextract
let write_final_extensions
  (#rrelcfg #relcfg: _)
  (scfg: LP.slice rrelcfg relcfg)
  (pcfg: U32.t)
  (edi: bool)
  (#rrel #rel: _)
  (sin: LP.slice rrel rel)
  (pin_from pin_to: U32.t)
  (now: U32.t)
  (h0: HS.mem)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from0: U32.t {
    LP.valid Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg /\
    LP.valid_list Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin_from pin_to /\
    U32.v pout_from0 <= U32.v sout.LP.len /\
    B.loc_disjoint (LP.loc_slice_from_to scfg pcfg (LP.get_valid_pos Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg)) (LP.loc_slice_from sout pout_from0) /\
    B.loc_disjoint (LP.loc_slice_from_to sin pin_from pin_to) (LP.loc_slice_from sout pout_from0)
  })
: Tot (y: LPW.olwriter Parsers.ClientHelloExtension.clientHelloExtension_serializer h0 sout pout_from0 {
    let cfg = LP.contents Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg in
    LPW.olwvalue y == option_of_result (final_extensions_new cfg edi (LP.contents_list Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin_from pin_to) now)
  })
= [@inline_let]
  let list_length_append (#t: Type) (l1 l2: list t) : Lemma (L.length (l1 `L.append` l2) == L.length l1 + L.length l2) [SMTPat (L.length (l1 `L.append`  l2))] = L.append_length l1 l2 in
  LPW.graccess Parsers.MiTLSConfig.accessor_miTLSConfig_max_version scfg pcfg _ _ _ `LPW.olwbind` (fun pmax_version ->
    LPW.read_leaf Parsers.ProtocolVersion.protocolVersion_reader scfg pmax_version _ _ _ `LPW.olwbind` (fun max_version ->
    LPW.olwriter_ifthenelse (max_version = TLS_1p3)
      (fun _ ->
        LPW.grlexistsb
          Parsers.ResumeInfo13.resumeInfo13_jumper
          allow_psk_resumption_new
          (fun #rrel #rel sl pos -> true) // currently constant, see Ticket.ticket_pskinfo
          sin pin_from pin_to
          _ _ _ `LPW.olwbind` (fun allow_psk_resumption ->
        LPW.grlexistsb
          Parsers.ResumeInfo13.resumeInfo13_jumper
          allow_dhe_resumption_new
          (fun #rrel #rel sl pos -> true) // currently constant, see Ticket.ticket_pskinfo)
          sin pin_from pin_to
          _ _ _ `LPW.olwbind` (fun allow_dhe_resumption ->
        LPW.olwriter_ifthenelse (allow_psk_resumption || allow_dhe_resumption)
          (fun _ ->
            [@inline_let]
            let psk_kex : LPW.lwriter _ _ _ _ =
              LPW.lwriter_append
                (LPW.lwriter_ifthenelse
                  allow_psk_resumption
                  (fun _ -> LPW.lwriter_singleton (LPW.write_leaf_cs pskKeyExchangeMode_writer h0 sout pout_from0 Psk_ke))
                  (fun _ -> LPW.lwriter_nil _ _ _ _))
                (LPW.lwriter_ifthenelse
                  allow_dhe_resumption
                  (fun _ -> LPW.lwriter_singleton (LPW.write_leaf_cs pskKeyExchangeMode_writer _ _ _ Psk_dhe_ke))
                  (fun _ -> LPW.lwriter_nil _ _ _ _))
            in
//            [@inline_let]
//            let _ = assert (let n = List.Tot.length (LPW.lwvalue psk_kex) in 1 <= n /\ n <= 2) in
            [@inline_let]
            let binders : LPW.lwriter _ _ _ _ =
              LPW.lwriter_list_map
                Parsers.ResumeInfo13.resumeInfo13_jumper
                Parsers.PskBinderEntry.pskBinderEntry_serializer
                (fun r -> compute_binder_ph_new r.Parsers.ResumeInfo13.ticket)
                sin pin_from pin_to
                h0
                sout pout_from0
                (fun pin ->
                  LPW.Writer (Ghost.hide (compute_binder_ph_new (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin).Parsers.ResumeInfo13.ticket)) (fun pout ->
                  write_binder_ph sin (Parsers.ResumeInfo13.accessor_resumeInfo13_ticket sin pin) sout pout
                ))
            in
            [@inline_let]
            let pskidentities : LPW.lwriter _ _ _ _ =
              LPW.lwriter_list_map
                Parsers.ResumeInfo13.resumeInfo13_jumper
                Parsers.PskIdentity.pskIdentity_serializer
                (obfuscate_age_new now)
                sin pin_from pin_to
                h0
                sout pout_from0
                (fun pin ->
                  LPW.Writer (Ghost.hide (obfuscate_age_new now (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin))) (fun pout ->
                  write_obfuscate_age now sin pin sout pout
                ))
            in
            [@inline_let]
            let ke : LPW.owriter _ _ _ _ =
              write_preSharedKeyClientExtension
                (write_offeredPsks_identities (LPW.olwriter_of_lwriter pskidentities))
                (write_offeredPsks_binders (LPW.olwriter_of_lwriter binders))
            in
            [@inline_let]
            let res : LPW.olwriter _ _ _ _ =
              LPW.olwriter_singleton
                (LPW.owriter_of_writer
                  (write_constr_clientHelloExtension_CHE_psk_key_exchange_modes
                    (write_clientHelloExtension_CHE_psk_key_exchange_modes
                      (write_pskKeyExchangeModes psk_kex)
                )))
              `LPW.olwriter_append`
              LPW.olwriter_ifthenelse
                edi
                (fun _ ->
                  LPW.olwriter_singleton
                    (LPW.owriter_of_writer
                      (write_constr_clientHelloExtension_CHE_early_data _ _ _)
                ))
                (fun _ -> LPW.olwriter_nil _ _ _ _)
              `LPW.olwriter_append`
              LPW.olwriter_singleton
                (write_constr_clientHelloExtension_CHE_pre_shared_key
                  (write_clientHelloExtension_CHE_pre_shared_key ke)
                )
            in
            res
          ) (fun _ ->
               (LPW.olwriter_singleton
                 (LPW.owriter_of_writer
                   (write_constr_clientHelloExtension_CHE_psk_key_exchange_modes
                     (write_clientHelloExtension_CHE_psk_key_exchange_modes
                       (write_pskKeyExchangeModes
                         (LPW.lwriter_append
                           (LPW.lwriter_singleton
                             (LPW.write_leaf_cs pskKeyExchangeMode_writer h0 sout pout_from0 Psk_ke)
                           )
                           (LPW.lwriter_singleton
                             (LPW.write_leaf_cs pskKeyExchangeMode_writer _ _ _ Psk_dhe_ke)
         ))))))))))
    ) (fun _ ->
      LPW.olwriter_nil Parsers.ClientHelloExtension.clientHelloExtension_serializer _ _ _
  )))

#pop-options

let test_write_final_extensions
  (#rrelcfg #relcfg: _)
  (scfg: LP.slice rrelcfg relcfg)
  (pcfg: U32.t)
  (edi: bool)
  (#rrel #rel: _)
  (sin: LP.slice rrel rel)
  (pin_from pin_to: U32.t)
  (now: U32.t)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from: U32.t)
: HST.Stack U32.t
  (requires (fun _ -> False))
  (ensures (fun _ _ _ -> True))
= let h0 = HST.get () in
  LPW.olwrite (write_final_extensions scfg pcfg edi sin pin_from pin_to now h0 sout pout_from) pout_from

open Negotiation.Version // for write_supportedVersions


let make_clientHelloExtension_CHE_signature_algorithms
  (o: option signatureSchemeList)
: GTot (option clientHelloExtension_CHE_signature_algorithms)
= match o with
  | None -> None
  | Some x ->
    if
      (let l = signatureSchemeList_bytesize x in l <= 65535)
    then
      Some x
    else
      None

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_signature_algorithms
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.owriter signatureSchemeList_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter clientHelloExtension_CHE_signature_algorithms_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_clientHelloExtension_CHE_signature_algorithms (LPW.owvalue w)
  })
= LPW.OWriter (Ghost.hide (make_clientHelloExtension_CHE_signature_algorithms (LPW.owvalue w))) (fun pout_from ->
    Classical.forall_intro clientHelloExtension_CHE_signature_algorithms_bytesize_eq;
    Classical.forall_intro signatureSchemeList_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq signatureSchemeList_serializer);
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_CHE_signature_algorithms_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else begin
      let res = LPW.owrite w (pout_from `U32.add` 2ul) in
      if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res
      then begin
        res
      end else
        let len = res `U32.sub` (pout_from `U32.add` 2ul) in
        if 65535ul `U32.lt` len
        then LP.max_uint32 `U32.sub` 1ul
        else begin
          clientHelloExtension_CHE_signature_algorithms_finalize sout pout_from res;
          res
        end
    end
  )

inline_for_extraction
let constr_clientHelloExtension_CHE_signature_algorithms
  (o: option clientHelloExtension_CHE_signature_algorithms)
: GTot (option clientHelloExtension)
= match o with
  | None -> None
  | Some x -> Some (CHE_signature_algorithms x)

inline_for_extraction
noextract
let write_constr_clientHelloExtension_CHE_signature_algorithms
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.owriter clientHelloExtension_CHE_signature_algorithms_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter clientHelloExtension_serializer h0 sout pout_from0 { LPW.owvalue y == constr_clientHelloExtension_CHE_signature_algorithms (LPW.owvalue w) } )
= LPW.OWriter (Ghost.hide (constr_clientHelloExtension_CHE_signature_algorithms (LPW.owvalue w))) (fun pout_from ->
    Classical.forall_intro clientHelloExtension_bytesize_eq;
    Classical.forall_intro clientHelloExtension_CHE_signature_algorithms_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_CHE_signature_algorithms_serializer);
    Classical.forall_intro (LP.serialized_length_eq clientHelloExtension_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else begin
      let res = LPW.owrite w (pout_from `U32.add` 2ul) in
      if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res
      then begin
        res
      end else begin
        finalize_clientHelloExtension_signature_algorithms sout pout_from;
        res
      end
    end
  )

inline_for_extraction
noextract
let write_sigalgs_extension
  (#rrelcfg #relcfg: _)
  (scfg: LP.slice rrelcfg relcfg)
  (pcfg: U32.t)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (sout_from0: U32.t)
  (h0: HS.mem {
    LP.valid Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg /\
    B.loc_disjoint (LP.loc_slice_from_to scfg pcfg (LP.get_valid_pos Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg)) (LP.loc_slice_from sout sout_from0)
  })
: Tot (
    w: LPW.olwriter clientHelloExtension_serializer h0 sout sout_from0 {
    let cfg = LP.contents Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg in
    LPW.olwvalue w == option_of_result (sigalgs_extension_new cfg)
  })
= LPW.graccess Parsers.MiTLSConfig.accessor_miTLSConfig_signature_algorithms scfg pcfg _ _ _ `LPW.olwbind` (fun pin_from ->
  LPW.olwriter_singleton (write_constr_clientHelloExtension_CHE_signature_algorithms (write_clientHelloExtension_CHE_signature_algorithms (LPW.owriter_of_writer (LPW.wjcopy signatureSchemeList_serializer signatureSchemeList_jumper scfg pin_from sout sout_from0 h0)))))
