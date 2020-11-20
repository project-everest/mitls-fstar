module Test
include Test.Aux
include TestSpecs

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LP = LowParse.Low.Base
module B = LowStar.Buffer
module LPW = LowParse.Low.Writers

#reset-options "--z3cliopt smt.arith.nl=false"

#push-options "--z3rlimit 64 --query_stats"

#restart-solver

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
    let ph = Ghost.hide (compute_binder_ph (LP.contents Parsers.TicketContents13.ticketContents13_parser h sin pin)) in
    if pout_to = LP.max_uint32
    then
      U32.v pout_from + LP.serialized_length Parsers.PskBinderEntry.pskBinderEntry_serializer ph > U32.v sout.LP.len
    else
      LP.valid_content_pos Parsers.PskBinderEntry.pskBinderEntry_parser h' sout pout_from ph pout_to
  )))
=
  let h0 = HST.get () in
  let ph = Ghost.hide (compute_binder_ph (LP.contents Parsers.TicketContents13.ticketContents13_parser h0 sin pin)) in
  let c = Parsers.CipherSuite13.cipherSuite13_reader sin (Parsers.TicketContents13.accessor_ticketContents13_cs sin pin) in
  let len : U32.t = hash_len c in
  if (1ul `U32.add` len) `U32.gt` (sout.LP.len `U32.sub` pout_from)
  then begin
    LP.serialized_length_eq Parsers.PskBinderEntry.pskBinderEntry_serializer (Ghost.reveal ph);
    Parsers.PskBinderEntry.pskBinderEntry_bytesize_eq (Ghost.reveal ph);
    LP.max_uint32
  end else begin
    let pout_payload = pout_from `U32.add` 1ul in
    // TODO: replace with a custom fill once target slice is replaced with the stash
    B.fill (B.sub sout.LP.base pout_payload len) 0uy len;
    Parsers.PskBinderEntry.pskBinderEntry_finalize sout pout_from len
  end

#restart-solver

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
    let x = obfuscate_age now (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h sin pin) in
    B.modifies (LP.loc_slice_from sout pout_from) h h' /\ (
    if res = LP.max_uint32
    then U32.v pout_from + LP.serialized_length Parsers.PskIdentity.pskIdentity_serializer x > U32.v sout.LP.len
    else LP.valid_content_pos Parsers.PskIdentity.pskIdentity_parser h' sout pout_from x res
  )))
= let h = HST.get () in
  let x = Ghost.hide (obfuscate_age now (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h sin pin)) in
  LP.serialized_length_eq Parsers.PskIdentity.pskIdentity_serializer (Ghost.reveal x);
  Parsers.PskIdentity.pskIdentity_bytesize_eq (Ghost.reveal x);
  let sin_id = Parsers.ResumeInfo13.accessor_resumeInfo13_identity sin pin in
  Parsers.PskIdentity.pskIdentity_identity_bytesize_eq ((Ghost.reveal x).Parsers.PskIdentity.identity);
  LP.serialized_length_eq Parsers.PskIdentity.pskIdentity_identity_serializer ((Ghost.reveal x).Parsers.PskIdentity.identity);
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

// #push-options "--z3rlimit 256 --query_stats --print_z3_statistics --max_ifuel 8 --initial_ifuel 8"
#push-options "--z3rlimit 32 --query_stats"

#restart-solver

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
: Tot (LPW.olwriter Parsers.ClientHelloExtension.clientHelloExtension_serializer h0 sout pout_from0)
= [@inline_let]
  let list_length_append (#t: Type) (l1 l2: list t) : Lemma (L.length (l1 `L.append` l2) == L.length l1 + L.length l2) [SMTPat (L.length (l1 `L.append`  l2))] = L.append_length l1 l2 in
  LPW.graccess Parsers.MiTLSConfig.accessor_miTLSConfig_max_version scfg pcfg _ _ _ `LPW.olwbind` (fun pmax_version ->
    LPW.read_leaf Parsers.ProtocolVersion.protocolVersion_reader scfg pmax_version _ _ _ `LPW.olwbind` (fun max_version ->
    LPW.olwriter_ifthenelse (max_version = Parsers.ProtocolVersion.TLS_1p3)
      (fun _ ->
        LPW.grlexistsb
          Parsers.ResumeInfo13.resumeInfo13_jumper
          (fun _ -> true)
          (fun #rrel #rel sl pos -> true) // currently constant, see Ticket.ticket_pskinfo
          sin pin_from pin_to
          _ _ _ `LPW.olwbind` (fun allow_psk_resumption ->
        LPW.grlexistsb
          Parsers.ResumeInfo13.resumeInfo13_jumper
          (fun _ -> true)
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
                  (fun _ -> LPW.lwriter_singleton (LPW.write_leaf_cs Parsers.PskKeyExchangeMode.pskKeyExchangeMode_writer h0 sout pout_from0 Parsers.PskKeyExchangeMode.Psk_ke))
                  (fun _ -> LPW.lwriter_nil _ _ _ _))
                (LPW.lwriter_ifthenelse
                  allow_dhe_resumption
                  (fun _ -> LPW.lwriter_singleton (LPW.write_leaf_cs Parsers.PskKeyExchangeMode.pskKeyExchangeMode_writer _ _ _ Parsers.PskKeyExchangeMode.Psk_dhe_ke))
                  (fun _ -> LPW.lwriter_nil _ _ _ _))
            in
//            [@inline_let]
//            let _ = assert (let n = List.Tot.length (LPW.lwvalue psk_kex) in 1 <= n /\ n <= 2) in
            [@inline_let]
            let binders : LPW.lwriter _ _ _ _ =
              LPW.lwriter_list_map
                Parsers.ResumeInfo13.resumeInfo13_jumper
                Parsers.PskBinderEntry.pskBinderEntry_serializer
                (fun r -> compute_binder_ph r.Parsers.ResumeInfo13.ticket)
                sin pin_from pin_to
                h0
                sout pout_from0
                (fun pin ->
                  LPW.Writer (Ghost.hide (compute_binder_ph (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin).Parsers.ResumeInfo13.ticket)) (fun pout ->
                  write_binder_ph sin (Parsers.ResumeInfo13.accessor_resumeInfo13_ticket sin pin) sout pout
                ))
            in
            [@inline_let]
            let pskidentities : LPW.lwriter _ _ _ _ =
              LPW.lwriter_list_map
                Parsers.ResumeInfo13.resumeInfo13_jumper
                Parsers.PskIdentity.pskIdentity_serializer
                (obfuscate_age now)
                sin pin_from pin_to
                h0
                sout pout_from0
                (fun pin ->
                  LPW.Writer (Ghost.hide (obfuscate_age now (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin))) (fun pout ->
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
                             (LPW.write_leaf_cs Parsers.PskKeyExchangeMode.pskKeyExchangeMode_writer h0 sout pout_from0 Parsers.PskKeyExchangeMode.Psk_ke)
                           )
                           (LPW.lwriter_singleton
                             (LPW.write_leaf_cs Parsers.PskKeyExchangeMode.pskKeyExchangeMode_writer _ _ _ Parsers.PskKeyExchangeMode.Psk_dhe_ke)
         ))))))))))
    ) (fun _ ->
      LPW.olwriter_nil Parsers.ClientHelloExtension.clientHelloExtension_serializer _ _ _
  )))

#pop-options

let test_write_final_extensions
  (scfg: LP.slice  (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pcfg: U32.t)
  (edi: bool)
  (sin: LP.slice  (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pin_from pin_to: U32.t)
  (now: U32.t)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from: U32.t)
: HST.Stack U32.t
  (requires (fun h0 ->
    LP.live_slice h0 sout /\
    U32.v sout.LP.len < U32.v LP.max_uint32 - 1 /\
    LP.valid Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg /\
    LP.valid_list Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin_from pin_to /\
    U32.v pout_from <= U32.v sout.LP.len /\
    B.loc_disjoint (LP.loc_slice_from_to scfg pcfg (LP.get_valid_pos Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg)) (LP.loc_slice_from sout pout_from) /\
    B.loc_disjoint (LP.loc_slice_from_to sin pin_from pin_to) (LP.loc_slice_from sout pout_from)
  ))
  (ensures (fun _ _ _ -> True))
= let h0 = HST.get () in
  LPW.olwrite (write_final_extensions scfg pcfg edi sin pin_from pin_to now h0 sout pout_from) pout_from

let main () : Tot C.exit_code = C.EXIT_SUCCESS
