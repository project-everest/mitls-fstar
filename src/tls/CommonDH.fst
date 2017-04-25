(*--build-config
options:--fstar_home ../../../FStar --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 --z3rlimit 20 --__temp_no_proj Handshake --__temp_no_proj Connection --use_hints --include ../../../FStar/ucontrib/CoreCrypto/fst/ --include ../../../FStar/ucontrib/Platform/fst/ --include ../../../hacl-star/secure_api/LowCProvider/fst --include ../../../kremlin/kremlib --include ../../../hacl-star/specs --include ../../../hacl-star/code/lib/kremlin --include ../../../hacl-star/code/bignum --include ../../../hacl-star/code/experimental/aesgcm --include ../../../hacl-star/code/poly1305 --include ../../../hacl-star/code/salsa-family --include ../../../hacl-star/secure_api/test --include ../../../hacl-star/secure_api/utils --include ../../../hacl-star/secure_api/vale --include ../../../hacl-star/secure_api/uf1cma --include ../../../hacl-star/secure_api/prf --include ../../../hacl-star/secure_api/aead --include ../../libs/ffi --include ../../../FStar/ulib/hyperstack --include ../../src/tls/ideal-flags;
--*)
(**
An abstract interface for Diffie-Hellman operations

When the key extraction stack is idealized (ideal_KEF), this module
records the honesty of shares using two layers of types: pre_share
is for syntactically valid shares (used in parsing modules) while
share is for registered shares (for which is_honest is defined).
*)
﻿module CommonDH

open FStar.HyperStack
open Platform.Bytes
open Platform.Error
open CoreCrypto
open Parse
open TLSError
open FStar.ST

module MR = FStar.Monotonic.RRef
module MM = MonotoneMap

(* A flag for runtime debugging of handshakelog data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
inline_for_extraction let cdh_debug = true
let discard (b:bool): ST unit (requires (fun _ -> True))
 (ensures (fun h0 _ h1 -> h0 == h1)) = ()
let print s = discard (IO.debug_print_string ("CDH| "^s^"\n"))
unfold let dbg : string -> ST unit (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1)) =
  if cdh_debug then print else (fun _ -> ())

type group =
  | FFDH of DHGroup.group
  | ECDH of ECGroup.group

private type pre_keyshare' =
  | KS_FF: g:DHGroup.group -> DHGroup.keyshare g -> pre_keyshare'
  | KS_EC: g:ECGroup.group -> ECGroup.keyshare g -> pre_keyshare'

type pre_keyshare (g:group) =
  ks:pre_keyshare'{(match g with
  | FFDH dhg -> KS_FF? ks /\ KS_FF?.g ks = dhg
  | ECDH ecg -> KS_EC? ks /\ KS_EC?.g ks = ecg)}

private type pre_share' =
  | S_FF: g:DHGroup.group -> DHGroup.share g -> pre_share'
  | S_EC: g:ECGroup.group -> ECGroup.share g -> pre_share'

type pre_share (g:group) =
  s:pre_share'{(match g with
  | FFDH dhg -> S_FF? s /\ S_FF?.g s = dhg
  | ECDH ecg -> S_EC? s /\ S_EC?.g s = ecg)}

type id = g:group & s:pre_share g
type honest (i:id) = bool

(* Global log of honestly generated DH shares *)
private let dh_region:rgn = new_region tls_tables_region
private type ideal_log = MM.t dh_region id honest (fun _ -> True)
private type share_table = (if Flags.ideal_KEF then ideal_log else unit)

abstract let share_log: share_table =
  (if Flags.ideal_KEF then
    MM.alloc #dh_region #id #honest #(fun _ -> True)
  else
    ())

type secret (g:group) = bytes

let namedGroup_of_group (g:group) : Tot (r:(option namedGroup)
  {Some? r <==> (ECDH? g \/ (FFDH? g /\ DHGroup.Named? (FFDH?._0 g)))}) =
  match g with
  | ECDH ec -> Some (SEC ec)
  | FFDH (DHGroup.Named ng) -> Some (FFDHE ng)
  | _ -> None

val group_of_namedGroup: ng:namedGroup -> Tot (r:option group
  {Some? r <==> (SEC? ng \/ FFDHE? ng)})
let group_of_namedGroup g =
  match g with
  | SEC ec    -> Some (ECDH ec)
  | FFDHE dhe -> Some (FFDH (DHGroup.Named dhe))
  | _ -> None

val default_group: group
let default_group = ECDH (CoreCrypto.ECC_P256)

type registered (i:id) =
  (if Flags.ideal_KEF then
    let log : ideal_log = share_log in
    MR.witnessed (MM.defined log i)
  else
    True)

type honest_share (i:id) =
  (if Flags.ideal_KEF then
    let log : ideal_log = share_log in
    MR.witnessed (MM.contains log i true)
  else False)

type dishonest_share (i:id) =
  (if Flags.ideal_KEF then
    let log : ideal_log = share_log in
    MR.witnessed (MM.contains log i false)
  else True)

val pre_pubshare: #g:group -> pre_keyshare g -> Tot (pre_share g)
let pre_pubshare #g ks =
  match g with
  | FFDH dhg -> let KS_FF _ ks = ks in S_FF dhg (DHGroup.pubshare #dhg ks)
  | ECDH ecg -> let KS_EC _ ks = ks in S_EC ecg (ECGroup.pubshare #ecg ks)

type share (g:group) = s:pre_share g{registered (|g, s|)}
type keyshare (g:group) = s:pre_keyshare g{registered (|g, pre_pubshare s|)}

let pubshare (#g:group) (s:keyshare g) : Tot (share g) =
  let gx = pre_pubshare s in
  cut(registered (|g, gx |)); gx

let is_honest (i:id) : ST bool
  (requires (fun h -> registered i))
  (ensures (fun h0 b h1 ->
    modifies_none h0 h1 /\
    (if Flags.ideal_KEF then
      let log : ideal_log = share_log in
      MM.contains log i b h1 /\
      (b ==> honest_share i) /\
      (not b ==> dishonest_share i)
    else b == false)))
  =
  if Flags.ideal_KEF then
   begin
    let log : ideal_log = share_log in
    let h = ST.get () in
    MR.m_recall log;
    MR.testify (MM.defined log i);
    cut(Some? (MM.sel (MR.m_sel h log) i));
    let b = Some?.v (MM.sel (MR.m_read log) i) in
    cut(MM.contains log i b h);
    MM.contains_stable log i b;
    MR.witness log (MM.contains log i b); b
   end
  else false

let lemma_honest_or_dishonest (i:id) : ST unit
  (requires (fun h -> registered i))
  (ensures (fun h0 _ h1 -> dishonest_share i \/ honest_share i))
  =
  if Flags.ideal_KEF then
   begin
    let log : ideal_log = share_log in
    let h = ST.get () in
    MR.m_recall log;
    MR.testify (MM.defined log i);
    cut(Some? (MM.sel (MR.m_sel h log) i));
    let b = Some?.v (MM.sel (MR.m_read log) i) in
    match b with
    | true ->
      cut(MM.contains log i true h);
      MM.contains_stable log i true;
      MR.witness log (MM.contains log i true)
    | false ->
      cut(MM.contains log i false h);
      MM.contains_stable log i false;
      MR.witness log (MM.contains log i false)
   end
  else ()

let lemma_honest_and_dishonest (i:id)
  : ST unit
  (requires (fun h0 -> registered i /\ honest_share i /\ dishonest_share i))
  (ensures (fun h0 _ h1 -> False))
  =
  if Flags.ideal_KEF then
   begin
    let h = ST.get () in
    let log : ideal_log = share_log in
    MR.m_recall log;
    MR.testify (MM.defined log i);
    MR.testify (MM.contains log i true);
    cut(true = Some?.v (MM.sel (MR.m_sel h log) i));
    MR.testify (MM.contains log i false);
    cut(false = Some?.v (MM.sel (MR.m_sel h log) i));
    cut(False)
   end
  else ()

// Reified versions of lemma_honest_and_dishonest
// ADL: I am not able to prove these, waiting for help from Nik
type absurd_honest (i:id{registered i /\ dishonest_share i}) = honest_share i
type absurd_dishonest (i:id{registered i /\ honest_share i}) = dishonest_share i
assume val lemma_honest_and_dishonest_tot: i:id{registered i /\ dishonest_share i} -> absurd_honest i -> Lemma (False)
assume val lemma_dishonest_and_honest_tot: i:id{registered i /\ honest_share i} -> absurd_dishonest i -> Lemma (False)

let lemma_dishonest_not_honest (i:id)
  : ST unit
  (requires (fun h0 -> registered i /\ dishonest_share i))
  (ensures (fun h0 _ h1 -> ~(honest_share i)))
  =
  if Flags.ideal_KEF then
   begin
    let j: i:id{registered i /\ dishonest_share i} = i in
    FStar.Classical.impl_intro (lemma_honest_and_dishonest_tot j);
    cut(honest_share i ==> False)
   end
  else ()

let lemma_honest_not_dishonest (i:id)
  : ST unit
  (requires (fun h0 -> registered i /\ honest_share i))
  (ensures (fun h0 _ h1 -> ~(dishonest_share i)))
  =
  if Flags.ideal_KEF then
   begin
    let j: i:id{registered i /\ honest_share i} = i in
    FStar.Classical.impl_intro (lemma_dishonest_and_honest_tot j);
    cut(dishonest_share i ==> False)
   end
  else ()

#set-options "--z3rlimit 100"
val keygen: g:group -> ST (keyshare g)
  (requires (fun h0 -> True))
  (ensures (fun h0 s h1 ->
    (if Flags.ideal_KEF then
      modifies_one dh_region h0 h1 /\
      honest_share (|g, pubshare s|)
     else
      modifies_none h0 h1)))
let rec keygen g =
  dbg ("Keygen on "^(if FFDH? g then "DHGroup" else "ECGroup"));
  let gx : pre_keyshare g =
    match g with
    | FFDH g -> KS_FF g (DHGroup.keygen g)
    | ECDH g -> KS_EC g (ECGroup.keygen g)
    in
  let gx : keyshare g =
   if Flags.ideal_KEF then
    begin
     let log : ideal_log = share_log in
     let i : id = (| g, pre_pubshare gx |) in
     MR.m_recall log;
     match MM.lookup log i with
     | None ->
       MM.extend log i true;
       cut(registered i); cut(honest_share i);
       let gx : keyshare g = gx in gx
     | Some _ -> // Bad luck, we generated the same share twice
       keygen g
    end
   else gx in
  gx

val dh_initiator: #g:group -> keyshare g -> share g -> ST (secret g)
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
let dh_initiator #g gx gy =
  dbg ("DH initiator on "^(if FFDH? g then "DHGroup" else "ECGroup"));
  match g with
  | FFDH g ->
    let KS_FF _ gx = gx in
    let S_FF _ gy = gy in
    DHGroup.dh_initiator #g gx gy
  | ECDH g ->
    let KS_EC _ gx = gx in
    let S_EC _ gy = gy in
    ECGroup.dh_initiator #g gx gy

val dh_responder: #g:group -> share g -> ST (share g * secret g)
  (requires (fun h0 -> True))
  (ensures (fun h0 (ks,s) h1 ->
    (if Flags.ideal_KEF then
      modifies_one dh_region h0 h1 /\
      honest_share (|g, ks|)
     else
      modifies_none h0 h1)))
let dh_responder #g gx =
  dbg ("DH responder on "^(if FFDH? g then "DHGroup" else "ECGroup"));
  let gy = keygen g in
  let gxy = dh_initiator #g gy gx in
  (pubshare #g gy, gxy)

#set-options "--z3rlimit 100"
let register (#g:group) (gx:pre_share g) : ST (share g)
(requires (fun h0 -> True))
(ensures (fun h0 s h1 ->
  (if Flags.ideal_KEF then
    modifies_one dh_region h0 h1
   else
    modifies_none h0 h1)))
  =
  if Flags.ideal_KEF then
   begin
    let log : ideal_log = share_log in
    let i : id = (| g, gx |) in
    MR.m_recall log;
    match MM.lookup log i with
    | None ->
      MM.extend log i false;
      cut(registered i);
      cut(dishonest_share i);
      gx
    | Some b ->
      cut(MR.witnessed (MM.defined log i));
      gx
   end
  else gx

val parse: g:group -> bytes -> Tot (option (pre_share g))
let parse g x =
  match g with
  | ECDH g ->
    (match ECGroup.parse_point g x with
    | None -> None | Some gx -> Some (S_EC g gx))
  | FFDH g ->
    let dhp = DHGroup.params_of_group g in
    if length x = length dhp.dh_p then Some (S_FF g x)
    else None

val parse_partial: bool -> bytes -> Tot (result ((g:group & pre_share g) * bytes))
let parse_partial ec p =
  if ec then
    begin
    match ECGroup.parse_partial p with
    | Correct((|g , s|), rem) ->
      Correct ((| ECDH g, S_EC g s |), rem)
    | Error z -> Error z
    end
  else
    begin
    match DHGroup.parse_partial p with
    | Correct((|g, s|), rem) ->
      Correct ((| FFDH g, S_FF g s |), rem)
    | Error z -> Error z
    end

// Serialize in KeyExchange message format
val serialize: #g:group -> pre_share g -> Tot bytes
let serialize #g s =
  match g with
  | FFDH g -> let S_FF _ s = s in DHGroup.serialize #g s
  | ECDH g -> let S_EC _ s = s in ECGroup.serialize #g s

// Serialize for keyShare extension
val serialize_raw: #g:group -> pre_share g -> Tot bytes
let serialize_raw #g s =
  match g with
  | FFDH g ->
    let S_FF _ s = s in
    let dhp = DHGroup.params_of_group g in
    DHGroup.serialize_public #g s (length dhp.dh_p)
  | ECDH g ->
    let S_EC _ s = s in
    ECGroup.serialize_point #g s

(*
val key_params: key -> Tot params
let key_params k =
  match k with
  | FFKey k -> FFP k.dh_params
  | ECKey k -> ECP k.ec_params

  let checkParams dhdb minSize (p:parameters) =
    match p with
    | DHP_P(dhp) ->
      begin match dhdb with
        | None -> Error (TLSError.AD_internal_error, "Not possible")
        | Some db ->
            (match DHGroup.checkParams db minSize dhp.dh_p dhp.dh_g with
            | Error(x) -> Error(x)
            | Correct(db, dhp) -> Correct(Some db, p))
      end
    | DHP_EC(ecp) -> correct (None, p)

let checkElement (p:parameters) (e:element) : option element  =
    match (p, e.dhe_p, e.dhe_ec) with
    | DHP_P(dhp), Some b, None ->
      begin match DHGroup.checkElement dhp b with
        | None -> None
        | Some x -> Some ({dhe_nil with dhe_p = Some x})
      end
    | DHP_EC(ecp), None, Some p ->
      begin match ECGroup.checkElement ecp p with
        | None -> None
        | Some p -> Some ({dhe_nil with dhe_ec = Some p})
      end
    | _ -> failwith "impossible"
*)




// TODO imported from TLSConstants, in a broken state
// This may not belong to CommonDH.

// TODO: replace "bytes" by either DH or ECDH parameters
// should that go elsewhere? YES.
(** KeyShare entry definition *)
type keyShareEntry =
  | Share: g:group{Some? (namedGroup_of_group g)} -> share g -> keyShareEntry
  | UnknownShare:
    ng:namedGroup { None? (group_of_namedGroup ng)} ->
    b:bytes{repr_bytes (length b) <= 2} -> keyShareEntry

(** ClientKeyShare definition *)
type clientKeyShare = l:list keyShareEntry{List.Tot.length l < 65536/4}

(** ServerKeyShare definition *)
type serverKeyShare = keyShareEntry

(** KeyShare definition *)
noeq type keyShare =
  | ClientKeyShare of clientKeyShare
  | ServerKeyShare of serverKeyShare

// the parsing/formatting moves to the private part of Extensions
(** Serializing function for a KeyShareEntry *)
val keyShareEntryBytes: keyShareEntry -> Tot (b:bytes{4 <= length b})
let keyShareEntryBytes = function
  | Share g s ->
    assume false; // TODO
    let Some ng = namedGroup_of_group g in
    let ng_bytes = namedGroupBytes ng in
    let b = serialize_raw #g s in
    ng_bytes @| vlbytes 2 b
  | UnknownShare ng b ->
    let ng_bytes = namedGroupBytes ng in
    ng_bytes @| vlbytes 2 b

(** Parsing function for a KeyShareEntry *)
val parseKeyShareEntry: pinverse_t keyShareEntryBytes
let parseKeyShareEntry b =
  assume false; // TODO registration
  let ng, key_exchange = split b 2 in
  match parseNamedGroup ng with
  | Correct ng ->
    begin
      match vlparse 2 key_exchange with
      | Correct ke ->
        (if SEC? ng || FFDHE? ng then
          let go = group_of_namedGroup ng in
          assert(SEC? ng \/ FFDHE? ng);
          assert(Some? go);
          let Some g = go in
          match parse g ke with
          | Some s -> Correct (Share g s)
          | None -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share value")
        else
          Correct (UnknownShare ng ke))
      | Error z ->
        Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entry")
    end
  | Error z -> Error z

(* TODO
(** Lemmas for KeyShare entries parsing/serializing inversions *)
val inverse_keyShareEntry: x:_ -> Lemma
  (requires True)
  (ensures lemma_inverse_g_f keyShareEntryBytes parseKeyShareEntry x)
  [SMTPat (parseKeyShareEntry (keyShareEntryBytes x))]
let inverse_keyShareEntry (ng, x) =
  let b = namedGroupBytes ng @| vlbytes 2 x in
  let b0,b1 = split b 2 in
  let vl,b = split b1 2 in
  vlparse_vlbytes 2 b;
  assert (Seq.equal vl (bytes_of_int 2 (length b)));
  assert (Seq.equal b0 (namedGroupBytes ng));
  assert (Seq.equal b x)

val pinverse_keyShareEntry: x:_ -> Lemma
  (requires True)
  (ensures lemma_pinverse_f_g Seq.equal keyShareEntryBytes parseKeyShareEntry x)
  [SMTPat (keyShareEntryBytes (Correct?._0 (parseKeyShareEntry x)))]
let pinverse_keyShareEntry x = ()
*)

// Choice: truncate when maximum length is exceeded
(** Serializing function for a list of KeyShareEntry *)
val keyShareEntriesBytes: list keyShareEntry -> Tot (b:bytes{2 <= length b /\ length b < 65538})
let keyShareEntriesBytes kes =
  let rec keyShareEntriesBytes_aux (b:bytes{length b < 65536}) (kes:list keyShareEntry): Tot (b:bytes{length b < 65536}) (decreases kes) =
  match kes with
  | [] -> b
  | ke::kes ->
    let b' = b @| keyShareEntryBytes ke in
    if length b' < 65536 then
      keyShareEntriesBytes_aux b' kes
    else b
  in
  let b = keyShareEntriesBytes_aux empty_bytes kes in
  lemma_repr_bytes_values (length b);
  vlbytes 2 b

(** Parsing function for a list KeyShareEntry *)
val parseKeyShareEntries: pinverse_t keyShareEntriesBytes
let parseKeyShareEntries b =
  let rec (aux: b:bytes -> list keyShareEntry -> Tot (result (list keyShareEntry)) (decreases (length b))) = fun b entries ->
    if length b > 0 then
      if length b >= 4 then
	let ng, data = split b 2 in
	match vlsplit 2 data with
	| Correct(kex, bytes) ->
	  begin
	  match parseKeyShareEntry (ng @| vlbytes 2 kex) with
	  | Correct entry -> aux bytes (entries @ [entry])
	  | Error z -> Error z
	  end
	| Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entry")
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse key share entries")
    else Correct entries in
  match vlparse 2 b with
  | Correct b -> aux b []
  | Error z   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entries")

(** Serializing function for a ClientKeyShare *)
val clientKeyShareBytes: clientKeyShare -> Tot (b:bytes{ 2 <= length b /\ length b < 65538 })
let clientKeyShareBytes cks = keyShareEntriesBytes cks

(** Parsing function for a ClientKeyShare *)
val parseClientKeyShare: b:bytes{ 2 <= length b /\ length b < 65538 }
  -> Tot (result clientKeyShare)
let parseClientKeyShare b =
  match parseKeyShareEntries b with
  | Correct kes ->
    if List.Tot.length kes < 65536/4
    then Correct kes
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse client key share entries")
  | Error z -> Error z

(** Serializing function for a ServerKeyShare *)
val serverKeyShareBytes: serverKeyShare -> Tot (b:bytes{ 4 <= length b })
let serverKeyShareBytes sks = keyShareEntryBytes sks

(** Parsing function for a ServerKeyShare *)
val parseServerKeyShare: pinverse_t serverKeyShareBytes
let parseServerKeyShare b = parseKeyShareEntry b

(** Serializing function for a KeyShare *)
let keyShareBytes = function
  | ClientKeyShare cks -> clientKeyShareBytes cks
  | ServerKeyShare sks -> serverKeyShareBytes sks

(** Parsing function for a KeyShare *)
val parseKeyShare: bool -> bytes -> Tot (result keyShare)
let parseKeyShare is_client b =
  if is_client then
    begin
    if 2 <= length b && length b < 65538 then
      begin
      match parseClientKeyShare b with
      | Correct kse -> Correct (ClientKeyShare kse)
      | Error z -> Error z
      end
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share")
    end
  else
    if 4 <= length b then
      begin
      match parseServerKeyShare b with
      | Correct ks -> Correct (ServerKeyShare ks)
      | Error z -> Error z
      end
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share")
