module Test.Aux

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module LP = LowParse.Low.Base
module B = LowStar.Buffer
module LPW = LowParse.Low.Writers

(* Helpers that we could have automatically generated with EverParse *)

let make_offeredPsks_identities
  (oidentities: option (list Parsers.PskIdentity.pskIdentity))
: GTot (option Parsers.OfferedPsks_identities.offeredPsks_identities)
= match oidentities with
  | Some identities ->
    if
      (let x = Parsers.OfferedPsks_identities.offeredPsks_identities_list_bytesize identities in 7 <= x && x <= 65535)
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
: Tot (LPW.owriter Parsers.OfferedPsks_identities.offeredPsks_identities_serializer h0 sout pout_from0)
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
      (let x = Parsers.OfferedPsks_binders.offeredPsks_binders_list_bytesize binders in 33 <= x && x <= 65535)
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
: Tot (LPW.owriter Parsers.OfferedPsks_binders.offeredPsks_binders_serializer h0 sout pout_from0)
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
: Tot (LPW.owriter Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_serializer h0 sout pout_from0)
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
: GTot (option Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key)
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
: Tot (LPW.owriter Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key_serializer h0 sout pout_from0)
= LPW.OWriter (Ghost.hide (make_clientHelloExtension_CHE_pre_shared_key (LPW.owvalue w))) (fun pout_from ->
    Classical.forall_intro Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key_bytesize_eq;
    Classical.forall_intro Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq Parsers.PreSharedKeyClientExtension.preSharedKeyClientExtension_serializer);
    Classical.forall_intro (LP.serialized_length_eq Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key_serializer);
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
          Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key_finalize sout pout_from res;
          res
        end
    end
  )

inline_for_extraction
let constr_clientHelloExtension_CHE_pre_shared_key
  (o: option Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key)
: GTot (option Parsers.ClientHelloExtension.clientHelloExtension)
= match o with
  | None -> None
  | Some x -> Some (Parsers.ClientHelloExtension.CHE_pre_shared_key x)

inline_for_extraction
noextract
let write_constr_clientHelloExtension_CHE_pre_shared_key
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.owriter Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key_serializer h0 sout pout_from0)
: Tot (LPW.owriter Parsers.ClientHelloExtension.clientHelloExtension_serializer h0 sout pout_from0)
= LPW.OWriter (Ghost.hide (constr_clientHelloExtension_CHE_pre_shared_key (LPW.owvalue w))) (fun pout_from ->
    Classical.forall_intro Parsers.ClientHelloExtension.clientHelloExtension_bytesize_eq;
    Classical.forall_intro Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq Parsers.ClientHelloExtension.clientHelloExtension_CHE_pre_shared_key_serializer);
    Classical.forall_intro (LP.serialized_length_eq Parsers.ClientHelloExtension.clientHelloExtension_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else begin
      let res = LPW.owrite w (pout_from `U32.add` 2ul) in
      if (LP.max_uint32 `U32.sub` 1ul) `U32.lte` res
      then begin
        res
      end else begin
        Parsers.ClientHelloExtension.finalize_clientHelloExtension_pre_shared_key sout pout_from;
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
  (w: LPW.lwriter Parsers.PskKeyExchangeMode.pskKeyExchangeMode_serializer h0 sout pout_from0 {
    let l = List.Tot.length (LPW.lwvalue w) in
    1 <= l /\ l <= 255
  })
: Tot (LPW.writer Parsers.PskKeyExchangeModes.pskKeyExchangeModes_serializer h0 sout pout_from0)
= LPW.Writer (Ghost.hide (LPW.lwvalue w)) (fun pout_from ->
    Classical.forall_intro Parsers.PskKeyExchangeModes.pskKeyExchangeModes_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq Parsers.PskKeyExchangeModes.pskKeyExchangeModes_serializer);
    Classical.forall_intro (LP.serialized_length_eq Parsers.PskKeyExchangeMode.pskKeyExchangeMode_serializer);
    Classical.forall_intro (LP.serialized_list_length_constant_size Parsers.PskKeyExchangeMode.pskKeyExchangeMode_serializer);
    if 1ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else
      let res = LPW.lwrite w (pout_from `U32.add` 1ul) in
      if res = LP.max_uint32
      then begin
        res
      end
      else begin
        Parsers.PskKeyExchangeModes.finalize_pskKeyExchangeModes sout pout_from res;
        res
      end
  )

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_psk_key_exchange_modes
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.writer Parsers.PskKeyExchangeModes.pskKeyExchangeModes_serializer h0 sout pout_from0)
: Tot (LPW.writer Parsers.ClientHelloExtension.clientHelloExtension_CHE_psk_key_exchange_modes_serializer h0 sout pout_from0)
= LPW.Writer (Ghost.hide (LPW.wvalue w)) (fun pout_from ->
    Classical.forall_intro Parsers.PskKeyExchangeModes.pskKeyExchangeModes_bytesize_eq;
    Classical.forall_intro Parsers.ClientHelloExtension.clientHelloExtension_CHE_psk_key_exchange_modes_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq Parsers.PskKeyExchangeModes.pskKeyExchangeModes_serializer);
    Classical.forall_intro (LP.serialized_length_eq Parsers.ClientHelloExtension.clientHelloExtension_CHE_psk_key_exchange_modes_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else
      let res = LPW.write w (pout_from `U32.add` 2ul) in
      if res = LP.max_uint32
      then res
      else begin
        Parsers.ClientHelloExtension.clientHelloExtension_CHE_psk_key_exchange_modes_finalize sout pout_from res;
        res
      end
  )

inline_for_extraction
noextract
let write_constr_clientHelloExtension_CHE_psk_key_exchange_modes
  (#h0: _)
  (#sout: _)
  (#pout_from0: _)
  (w: LPW.writer Parsers.ClientHelloExtension.clientHelloExtension_CHE_psk_key_exchange_modes_serializer h0 sout pout_from0)
: Tot (LPW.writer Parsers.ClientHelloExtension.clientHelloExtension_serializer h0 sout pout_from0)
= LPW.Writer (Ghost.hide (Parsers.ClientHelloExtension.CHE_psk_key_exchange_modes (LPW.wvalue w))) (fun pout_from ->
    Classical.forall_intro Parsers.ClientHelloExtension.clientHelloExtension_bytesize_eq;
    Classical.forall_intro Parsers.ClientHelloExtension.clientHelloExtension_CHE_psk_key_exchange_modes_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq Parsers.ClientHelloExtension.clientHelloExtension_CHE_psk_key_exchange_modes_serializer);
    Classical.forall_intro (LP.serialized_length_eq Parsers.ClientHelloExtension.clientHelloExtension_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else begin
      let res = LPW.write w (pout_from `U32.add` 2ul) in
      if res = LP.max_uint32
      then begin
        res
      end else begin
        Parsers.ClientHelloExtension.finalize_clientHelloExtension_psk_key_exchange_modes sout pout_from;
        res
      end
    end
  )

inline_for_extraction
noextract
let write_clientHelloExtension_CHE_early_data () : Tot (LP.leaf_writer_strong Parsers.ClientHelloExtension.clientHelloExtension_CHE_early_data_serializer) =
  fun _ #rrel #rel sout pos ->
  Parsers.ClientHelloExtension.clientHelloExtension_CHE_early_data_finalize sout pos;
  pos `U32.add` 2ul

inline_for_extraction
noextract
let write_constr_clientHelloExtension_CHE_early_data
  (h0: _)
  (sout: _)
  (pout_from0: _)
: Tot (LPW.writer Parsers.ClientHelloExtension.clientHelloExtension_serializer h0 sout pout_from0)
= LPW.Writer (Ghost.hide (Parsers.ClientHelloExtension.CHE_early_data ())) (fun pout_from ->
    Classical.forall_intro Parsers.ClientHelloExtension.clientHelloExtension_bytesize_eq;
    Classical.forall_intro Parsers.ClientHelloExtension.clientHelloExtension_CHE_early_data_bytesize_eq;
    Classical.forall_intro (LP.serialized_length_eq Parsers.ClientHelloExtension.clientHelloExtension_CHE_early_data_serializer);
    Classical.forall_intro (LP.serialized_length_eq Parsers.ClientHelloExtension.clientHelloExtension_serializer);
    if 2ul `U32.gt` (sout.LP.len `U32.sub` pout_from)
    then LP.max_uint32
    else
      let res = LPW.write (LPW.write_leaf_cs (write_clientHelloExtension_CHE_early_data ()) h0 sout pout_from0 ()) (pout_from `U32.add` 2ul) in
      if res = LP.max_uint32
      then res
      else begin
        Parsers.ClientHelloExtension.finalize_clientHelloExtension_early_data sout pout_from;
        res
      end
  )
