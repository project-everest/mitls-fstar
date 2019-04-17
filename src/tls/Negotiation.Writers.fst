module Negotiation.Writers

friend Negotiation

open FStar.Error
open FStar.Bytes

open Mem
open TLSError
open TLSInfo
open TLSConstants
open HandshakeMessages

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

open Extensions
open Negotiation

#reset-options "--z3cliopt smt.arith.nl=false"

#push-options "--z3rlimit 16"

(* implementation of the new spec *)

module LPW = LowParse.Low.Writers

assume val write_binder_ph
  (#rrel #rel: _)
  (sin: LP.slice rrel rel)
  (pin: U32.t)
  (h0: HS.mem)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from: U32.t {
    LP.valid Parsers.TicketContents13.ticketContents13_parser h0 sin pin /\
    B.loc_disjoint (LP.loc_slice_from_to sin pin (LP.get_valid_pos Parsers.TicketContents13.ticketContents13_parser h0 sin pin)) (LP.loc_slice_from sout pout_from)
  })
: Tot (w: LPW.writer pskBinderEntry_serializer h0 sout pout_from {
  LPW.wvalue w == compute_binder_ph_new (LP.contents Parsers.TicketContents13.ticketContents13_parser h0 sin pin)
})

assume val write_obfuscate_age
  (now: U32.t)
  (#rrel #rel: _)
  (sin: LP.slice rrel rel)
  (pin: U32.t)
  (h0: HS.mem)
  (sout: LP.slice (LP.srel_of_buffer_srel (B.trivial_preorder _)) (LP.srel_of_buffer_srel (B.trivial_preorder _)))
  (pout_from: U32.t {
    LP.valid Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin /\
    B.loc_disjoint (LP.loc_slice_from_to sin pin (LP.get_valid_pos Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin)) (LP.loc_slice_from sout pout_from)
  })
: Tot (w: LPW.writer pskIdentity_serializer h0 sout pout_from { LPW.wvalue w == obfuscate_age_new now (LP.contents Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin) })

#pop-options

(* then, the writer *)

let make_offeredPsks_identities
  (oidentities: option (list Parsers.PskIdentity.pskIdentity))
: GTot (option Parsers.OfferedPsks_identities.offeredPsks_identities)
= match oidentities with
  | Some identities ->
    if
      check_offeredPsks_identities_list_bytesize identities
    then Some identities
    else None
  | _ -> None

assume val write_offeredPsks_identities
  (#h0: HS.mem)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.olwriter Parsers.PskIdentity.pskIdentity_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter Parsers.OfferedPsks_identities.offeredPsks_identities_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_offeredPsks_identities (LPW.olwvalue w)
  })

let make_offeredPsks_binders
  (obinders: option (list Parsers.PskBinderEntry.pskBinderEntry))
: GTot (option Parsers.OfferedPsks_binders.offeredPsks_binders)
= match obinders with
  | Some binders ->
    if
      check_offeredPsks_binders_list_bytesize binders
    then begin
      Some binders
    end
    else None
  | _ -> None

assume val write_offeredPsks_binders
  (#h0: HS.mem)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.olwriter Parsers.PskBinderEntry.pskBinderEntry_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter Parsers.OfferedPsks_binders.offeredPsks_binders_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_offeredPsks_binders (LPW.olwvalue w)
  })

let make_preSharedKeyClientExtension
  (oi: option Parsers.OfferedPsks_identities.offeredPsks_identities)
  (ob: option Parsers.OfferedPsks_binders.offeredPsks_binders)
: GTot (option Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension)
= match oi, ob with
  | Some i, Some b -> Some ({ Parsers.OfferedPsks.identities = i; Parsers.OfferedPsks.binders = b; })
  | _ -> None

#push-options "--z3rlimit 16"

assume val write_preSharedKeyClientExtension
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w_identities: LPW.owriter Parsers.OfferedPsks_identities.offeredPsks_identities_serializer h0 sout pout_from0) 
  (w_binders: LPW.owriter Parsers.OfferedPsks_binders.offeredPsks_binders_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_preSharedKeyClientExtension (LPW.owvalue w_identities) (LPW.owvalue w_binders)
  })

let make_clientHelloExtension_CHE_pre_shared_key
  (o: option Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension)
: GTot (option clientHelloExtension_CHE_pre_shared_key)
= match o with
  | None -> None
  | Some x ->
    if
      check_clientHelloExtension_CHE_pre_shared_key_bytesize x
    then
      Some x
    else
      None

assume val write_clientHelloExtension_CHE_pre_shared_key
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.owriter Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter clientHelloExtension_CHE_pre_shared_key_serializer h0 sout pout_from0 {
    LPW.owvalue y == make_clientHelloExtension_CHE_pre_shared_key (LPW.owvalue w)
  })

inline_for_extraction
let constr_clientHelloExtension_CHE_pre_shared_key
  (o: option clientHelloExtension_CHE_pre_shared_key)
: GTot (option clientHelloExtension)
= match o with
  | None -> None
  | Some x -> Some (CHE_pre_shared_key x)

assume val write_constr_clientHelloExtension_CHE_pre_shared_key
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.owriter clientHelloExtension_CHE_pre_shared_key_serializer h0 sout pout_from0)
: Tot (y: LPW.owriter clientHelloExtension_serializer h0 sout pout_from0 { LPW.owvalue y == constr_clientHelloExtension_CHE_pre_shared_key (LPW.owvalue w) } )

assume val write_pskKeyExchangeModes
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

assume val write_clientHelloExtension_CHE_psk_key_exchange_modes
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.writer pskKeyExchangeModes_serializer h0 sout pout_from0)
: Tot (y: LPW.writer clientHelloExtension_CHE_psk_key_exchange_modes_serializer h0 sout pout_from0 {
    LPW.wvalue y == LPW.wvalue w
  })

assume val write_constr_clientHelloExtension_CHE_psk_key_exchange_modes
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.writer clientHelloExtension_CHE_psk_key_exchange_modes_serializer h0 sout pout_from0)
: Tot (y: LPW.writer clientHelloExtension_serializer h0 sout pout_from0 { LPW.wvalue y == CHE_psk_key_exchange_modes (LPW.wvalue w) } )

assume val write_clientHelloExtension_CHE_early_data (_: unit) : Tot (LP.leaf_writer_strong clientHelloExtension_CHE_early_data_serializer)

assume val write_constr_clientHelloExtension_CHE_early_data
  (h0: _)
  (sout: _)
  (pout_from0: _)
: Tot (y: LPW.writer clientHelloExtension_serializer h0 sout pout_from0 { LPW.wvalue y == CHE_early_data () })

#push-options "--z3rlimit 64 --query_stats --log_queries --print_z3_statistics --max_ifuel 4 --initial_ifuel 4"

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
  True //  LPW.olwvalue y == option_of_result (final_extensions_new cfg edi (LP.contents_list Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin_from pin_to) now)
  })
= [@inline_let]
  let list_length_append (#t: Type) (l1 l2: list t) : Lemma (L.length (l1 `L.append` l2) == L.length l1 + L.length l2) [SMTPat (L.length (l1 `L.append`  l2))] = L.append_length l1 l2 in
  Negotiation.Version.read_config_maxVersion scfg pcfg _ _ _ `LPW.olwbind` (fun max_version ->
    LPW.olwriter_ifthenelse (max_version = TLS_1p3)
      (fun _ ->
        LPW.grlexistsb
          Parsers.ResumeInfo13.resumeInfo13_jumper
          allow_psk_resumption_new
          sin pin_from pin_to
          _ _ _
          (fun _ -> LPW.greader_tot _ _ _ true) // currently constant, see Ticket.ticket_pskinfo
          `LPW.olwbind` (fun allow_psk_resumption ->
        LPW.grlexistsb
          Parsers.ResumeInfo13.resumeInfo13_jumper
          allow_dhe_resumption_new
          sin pin_from pin_to
          _ _ _ 
          (fun _ -> LPW.greader_tot _ _ _ true) // currently constant, see Ticket.ticket_pskinfo)
          `LPW.olwbind` (fun allow_dhe_resumption ->
        LPW.olwriter_ifthenelse (allow_psk_resumption || allow_dhe_resumption)
          (fun _ ->
            [@inline_let]
            let psk_kex = // : LPW.lwriter _ _ _ _ =
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
            let binders = // : LPW.lwriter _ _ _ _ =
              LPW.lwriter_list_map
                Parsers.ResumeInfo13.resumeInfo13_jumper
                Parsers.PskBinderEntry.pskBinderEntry_serializer
                (fun r -> compute_binder_ph_new r.Parsers.ResumeInfo13.ticket)
                sin pin_from pin_to
                h0
                sout pout_from0
                (fun pin ->
                  LPW.graccess Parsers.ResumeInfo13.accessor_resumeInfo13_ticket sin pin _ _ _ `LPW.wbind` (fun pt -> write_binder_ph sin pt _ _ _)
                )
            in
            [@inline_let]
            let pskidentities = // : LPW.lwriter _ _ _ _ =
              LPW.lwriter_list_map
                Parsers.ResumeInfo13.resumeInfo13_jumper
                Parsers.PskIdentity.pskIdentity_serializer
                (obfuscate_age_new now)
                sin pin_from pin_to
                h0
                sout pout_from0
                (fun pin ->
                  write_obfuscate_age now sin pin _ _ _
                )
            in
            [@inline_let]
            let ke = // : LPW.owriter _ _ _ _ =
              write_preSharedKeyClientExtension
                (write_offeredPsks_identities (LPW.olwriter_of_lwriter pskidentities))
                (write_offeredPsks_binders (LPW.olwriter_of_lwriter binders))
            in
//            [@inline_let]
//            let res : LPW.olwriter _ _ _ _ =
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
//            in
//            res
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
  ))

inline_for_extraction
noextract
let write_final_extensions_post
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
: Lemma
  (let y = write_final_extensions scfg pcfg edi sin pin_from pin_to now h0 sout pout_from0 in
  let cfg = LP.contents Parsers.MiTLSConfig.miTLSConfig_parser h0 scfg pcfg in
  LPW.olwvalue y == option_of_result (final_extensions_new cfg edi (LP.contents_list Parsers.ResumeInfo13.resumeInfo13_parser h0 sin pin_from pin_to) now)
  )
= assert_norm (pow2 32 == 4294967296)

#pop-options

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

#pop-options

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
