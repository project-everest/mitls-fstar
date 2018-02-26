(**
An abstract interface for Diffie-Hellman operations

When the key extraction stack is idealized (Flag.model), this module
records the honesty of shares using two layers of types: pre_share
is for syntactically valid shares (used in parsing modules) while
share is for registered shares (for which is_honest is defined).
*)
module CommonDH
module HST = FStar.HyperStack.ST //Added automatically

open Mem 
open FStar.Bytes
open FStar.Error
open CoreCrypto
open Parse
open TLSError

module MM = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap
module ST = FStar.HyperStack.ST

(* A flag for runtime debugging of cDH data.
   The F* normalizer will erase debug prints at extraction
   when this flag is set to false. *)
let discard (b:bool): ST unit (requires (fun _ -> True))
 (ensures (fun h0 _ h1 -> h0 == h1)) = ()
let print s = discard (IO.debug_print_string ("CDH| "^s^"\n"))
unfold let dbg : string -> ST unit (requires (fun _ -> True))
  (ensures (fun h0 _ h1 -> h0 == h1)) =
  if Flags.debug_CDH then print else (fun _ -> ())

type group' =
  | FFDH of DHGroup.group
  | ECDH of ECGroup.group

let group = group'
let is_ec g = ECDH? g

let string_of_group = function
  | FFDH g ->
    begin
    let open DHGroup in
    match g with
    | Named FFDHE2048 -> "FFDHE2048"
    | Named FFDHE3072 -> "FFDHE3072"
    | Named FFDHE4096 -> "FFDHE4096"
    | Named FFDHE6144 -> "FFDHE6144"
    | Named FFDHE8192 -> "FFDHE8192"
    | Explicit _      -> "Explicit group"
    end
  | ECDH g ->
    begin
    let open CoreCrypto in
    match g with
    | ECC_P256    -> "P256"
    | ECC_P384    -> "P384"
    | ECC_P521    -> "P521"
    | ECC_X25519  -> "X255519"
    | ECC_X448    -> "X448"
    end

private type pre_keyshare' =
  | KS_FF: g:DHGroup.group -> DHGroup.keyshare g -> pre_keyshare'
  | KS_EC: g:ECGroup.group -> ECGroup.keyshare g -> pre_keyshare'

let pre_keyshare (g:group) =
  ks:pre_keyshare'{(match g with
  | FFDH dhg -> KS_FF? ks /\ KS_FF?.g ks = dhg
  | ECDH ecg -> KS_EC? ks /\ KS_EC?.g ks = ecg)}

private type pre_share' =
  | S_FF: g:DHGroup.group -> DHGroup.share g -> pre_share'
  | S_EC: g:ECGroup.group -> ECGroup.share g -> pre_share'

let pre_share (g:group) =
  s:pre_share'{(match g with
  | FFDH dhg -> S_FF? s /\ S_FF?.g s = dhg
  | ECDH ecg -> S_EC? s /\ S_EC?.g s = ecg)}

let pre_pubshare #g ks =
  match g with
  | FFDH dhg -> let KS_FF _ ks = ks in S_FF dhg (DHGroup.pubshare #dhg ks)
  | ECDH ecg -> let KS_EC _ ks = ks in S_EC ecg (ECGroup.pubshare #ecg ks)

let namedGroup_of_group g =
  match g with
  | ECDH ec -> Some (SEC ec)
  | FFDH (DHGroup.Named ng) -> Some (FFDHE ng)
  | _ -> None

let lemma_namedGroup_of_group (g:group)
  : Lemma (Some? (namedGroup_of_group g) <==> (ECDH? g \/ (FFDH? g /\ DHGroup.Named? (FFDH?._0 g))))
  [SMTPat (namedGroup_of_group g)]
  = ()

let group_of_namedGroup g =
  match g with
  | SEC ec    -> Some (ECDH ec)
  | FFDHE dhe -> Some (FFDH (DHGroup.Named dhe))
  | _ -> None

let lemma_group_of_namedGroup (ng:namedGroup)
  : Lemma (Some? (group_of_namedGroup ng) <==> (SEC? ng \/ FFDHE? ng))
  [SMTPat (group_of_namedGroup ng)]
  = ()

let default_group = ECDH (CoreCrypto.ECC_P256)
 
let dh_region = new_region tls_tables_region
noeq type ilog_entry (i:pre_dhi) =
  | Honest of MM.t dh_region (pre_dhr i) (fun j -> bool) (fun _ -> True)
  | Corrupt

private type i_ilog = MM.t dh_region pre_dhi ilog_entry (fun _ -> True)
private type ishare_table = (if Flags.model then i_ilog else unit)
abstract let ilog: ishare_table =
  if Flags.model then MM.alloc () <: i_ilog else ()

type registered_dhi i =
  (if Flags.model then
    let log: i_ilog = ilog in
    witnessed (MM.defined log i)
  else True)

type fresh_dhi i h =
  (if Flags.model then
    let log: i_ilog = ilog in MM.fresh log i h
  else False)

type honest_dhi_st (log:i_ilog) (i:pre_dhi) (h:mem) =
  Some? (MM.sel (sel h log) i) /\ Honest? (Some?.v (MM.sel (sel h log) i))

let lemma_honest_dhi_stable (log:i_ilog) (i:pre_dhi)
  : Lemma (stable_on_t log (honest_dhi_st log i))
  = admit()

type honest_dhi i =
  (if Flags.model then
    let log: i_ilog = ilog in
    witnessed (honest_dhi_st log i)
  else False)

type corrupt_dhi_st (log:i_ilog) (i:pre_dhi) (h:mem) =
  Some? (MM.sel (sel h log) i) /\ Corrupt? (Some?.v (MM.sel (sel h log) i))

let lemma_corrupt_dhi_stable (log:i_ilog) (i:pre_dhi)
  : Lemma (stable_on_t log (corrupt_dhi_st log i))
  = admit()

type corrupt_dhi i =
  (if Flags.model then
    let log: i_ilog = ilog in
    witnessed (corrupt_dhi_st log i)
  else True)

let lemma_honest_corrupt (i:pre_dhi{registered_dhi i})
  : Lemma (honest_dhi i <==> ~(corrupt_dhi i))
  = admit()

let is_honest_dhi i =
  if Flags.model then
    let log: i_ilog = ilog in
    recall log;
    testify (MM.defined log i);
    lemma_honest_corrupt i;
    match MM.lookup log i with
    | Some (Corrupt) ->
      lemma_corrupt_dhi_stable log i;
      mr_witness log (corrupt_dhi_st log i);
      false
    | Some (Honest _) ->
      lemma_honest_dhi_stable log i;
      mr_witness log (honest_dhi_st log i);
      true
  else false

let ipubshare #g gx = pre_pubshare gx

type registered_dhr_st (#i:dhi) (log:i_ilog) (j:pre_dhr i) (h:mem) =
  corrupt_dhi_st log i h \/
  (honest_dhi_st log i h /\
    (let Some (Honest log') = MM.sel (sel h log) i in
      Some? (MM.sel (sel h log') j)))

type registered_dhr #i j =
  (if Flags.model then
    let log: i_ilog = ilog in
    witnessed (registered_dhr_st log j)
  else True)

type fresh_dhr #i j h =
  (if Flags.model then
    let log: i_ilog = ilog in
    honest_dhi_st log i h
    /\ (let Some (Honest log') = MM.sel (sel h log) i in
        None? (MM.sel (sel h log') j))
  else False)

type honest_dhr_st (#i:dhi) (log:i_ilog) (j:pre_dhr i) (h:mem) =
  honest_dhi_st log i h
  /\ (let Some (Honest log') = MM.sel (sel h log) i in
      Some? (MM.sel (sel h log') j)
      /\ Some?.v (MM.sel (sel h log') j) = true)

type honest_dhr #i j =
  (if Flags.model then
    let log: i_ilog = ilog in
    witnessed (honest_dhr_st log j)
  else False)

type corrupt_dhr_st (#i:dhi) (log:i_ilog) (j:pre_dhr i) (h:mem) =
  corrupt_dhi_st log i h \/
  (honest_dhi_st log i h /\
    (let Some (Honest log') = MM.sel (sel h log) i in
      Some? (MM.sel (sel h log') j)
      /\ Some?.v (MM.sel (sel h log') j) = false))

type corrupt_dhr #i j =
  (if Flags.model then
    let log: i_ilog = ilog in
    witnessed (corrupt_dhr_st log j)
  else True)

let lemma_honest_corrupt_dhr #i j = admit()

let is_honest_dhr #i j =
  if Flags.model then
    let log: i_ilog = ilog in
    recall log;
    lemma_honest_corrupt_dhr j;
    testify (registered_dhr_st log j);
    (match MM.lookup log i with
    | Some Corrupt ->
      assume(stable_on_t log (corrupt_dhr_st log j));
      mr_witness log (corrupt_dhr_st log j); false
    | Some (Honest log') ->
      (match MM.lookup log' j with
      | Some true ->
        assume(stable_on_t log (honest_dhr_st log j));
        mr_witness log (honest_dhr_st log j); true
      | Some false ->
        assume(stable_on_t log (corrupt_dhr_st log j));
        mr_witness log (corrupt_dhr_st log j); false))
  else false

private let raw_keygen (g:group) : ST (pre_keyshare g)
  (requires fun h0 -> True) (ensures fun h0 _ h1 -> h0 == h1)
  =
  assume false; // easier to deal with h0 == h1 than modifies_none h0 h1
  match g with
  | FFDH g -> KS_FF g (DHGroup.keygen g)
  | ECDH g -> KS_EC g (ECGroup.keygen g)

let rec keygen g =
  let h0 = get() in
  dbg ("Keygen (initiator) on "^string_of_group g);
  let x = raw_keygen g in
  if Flags.model then
    let log: i_ilog = ilog in
    recall log;
    let i : pre_dhi = (| g, pre_pubshare x |) in
    match MM.lookup log i with
    | Some _ -> keygen g
    | None ->
      assert(fresh_dhi i h0);
      let rlog = MM.alloc () in
      MM.extend log i (Honest rlog);
      lemma_honest_dhi_stable log i;
      assume false;//18-02-18 
      mr_witness log (honest_dhi_st log i);
      x
  else x

private let raw_dh_initiator (g:group) (x:pre_keyshare g) (gy:pre_share g)
  : ST (secret g) (requires fun h0 -> True) (ensures fun h0 _ h1 -> h0 == h1)
  =
  assume False; // h0 == h1 vs modifies_none
  dbg ("DH initiator on "^string_of_group g);
  match g with
  | FFDH g ->
    let KS_FF _ x = x in
    let S_FF _ gy = gy in
    DHGroup.dh_initiator #g x gy
  | ECDH g ->
    let KS_EC _ x = x in
    let S_EC _ gy = gy in
    ECGroup.dh_initiator #g x gy

let dh_initiator g x gy = raw_dh_initiator g x gy

let rec dh_responder g gx =
  dbg ("Keygen (responder) on "^string_of_group g);
  let i : dhi = (| g, gx |) in
  let y = raw_keygen g in
  let gy : pre_dhr i = pre_pubshare y in
  let h = get() in
  if Flags.model then
   begin
    let log: i_ilog = ilog in
    recall log;
    testify (MM.defined log i);
    lemma_honest_corrupt i;
    match MM.lookup log i with
    | Some Corrupt ->
      assert(corrupt_dhi_st log i h);
      lemma_corrupt_dhi_stable log i;
      mr_witness log (corrupt_dhi_st log i);
      assume(stable_on_t log (corrupt_dhr_st log gy));
      mr_witness log (corrupt_dhr_st log gy);
      assume(stable_on_t log (registered_dhr_st log gy));
      mr_witness log (registered_dhr_st log gy);
      lemma_honest_corrupt_dhr gy;
      (gy, raw_dh_initiator g y gx)
    | Some (Honest log') ->
      assert(honest_dhi_st log i h);
      lemma_honest_dhi_stable log i;
      mr_witness log (honest_dhi_st log i);
      match MM.lookup log' gy with
      | Some _ -> dh_responder g gx // Responder share collision
      | None ->
        assume(fresh_dhr gy h);// 18-02-18 
        MM.extend log' gy true;
        let h1 = get () in
        testify (honest_dhi_st log i);
        assert(honest_dhi_st log i h1);
        assume(honest_dhr_st log gy h1); // FIXME
        assume(stable_on_t log (honest_dhr_st log gy));
        mr_witness log (honest_dhr_st log gy);
        assume(stable_on_t log (registered_dhr_st log gy));
        mr_witness log (registered_dhr_st log gy);
        lemma_honest_corrupt_dhr gy;
        (gy, raw_dh_initiator g y gx)
   end
  else (gy, raw_dh_initiator g y gx)

/// When parsing gx, and unless gx is already registered,
/// we register it as dishonest.
/// The registration property is captured in the returned type.
/// Still missing details, e.g. functional correctness.

let register_dhi #g gx =
  if Flags.model then
    let log: i_ilog = ilog in
    let i = (| g, gx |) in
    recall log;
    if None? (MM.lookup log i) then MM.extend log i Corrupt;
    assume(stable_on_t log (MM.defined log i));
    mr_witness log (MM.defined log i); gx
  else gx

let register_dhr #g gx gy =
  if Flags.model then
    let log: i_ilog = ilog in
    let i : dhi = (| g, gx |) in
    let j : pre_dhr i = gx in
    recall log;
    testify (MM.defined log i);
    assume(stable_on_t log (registered_dhr_st log j));
    match is_honest_dhi i with
    | false ->
      testify (corrupt_dhi_st log i);
      mr_witness log (registered_dhr_st log j); j
    | true ->
      testify (honest_dhi_st log i);
      let Some (Honest log') = MM.lookup log i in
      recall log';
      if None? (MM.lookup log' j) then MM.extend log' j false;
      assume false;//18-02-18 
      mr_witness log (registered_dhr_st log j); j
  else gy

(*
let lemma_honest_or_dishonest (i:id) : ST unit
  (requires (fun h -> registered i))
  (ensures (fun h0 _ h1 -> honest_share i \/ dishonest_share i))
  =
  if Flags.model then
   begin
    let log : ideal_log = share_log in
    let h = get () in
    recall log;
    testify (MM.defined log i);
    cut(Some? (MM.sel (sel h log) i));
    let b = Some?.v (MM.sel !log) i) in
    match b with
    | true ->
      cut(MM.contains log i true h);
      MM.contains_stable log i true;
      mr_witness log (MM.contains log i true)
    | false ->
      cut(MM.contains log i false h);
      MM.contains_stable log i false;
      mr_witness log (MM.contains log i false)
   end
  else ()

let lemma_honest_and_dishonest (i:id)
  : ST unit
  (requires (fun h0 -> registered i /\ honest_share i /\ dishonest_share i))
  (ensures (fun h0 _ h1 -> False))
  =
  if Flags.model then
   begin
    let h = get () in
    let log : ideal_log = share_log in
    HST.recall log;
    HST.testify (MM.defined log i);
    HST.testify (MM.contains log i true);
    cut(true = Some?.v (MM.sel (sel h log) i));
    HST.testify (MM.contains log i false);
    cut(false = Some?.v (MM.sel (sel h log) i));
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
  if Flags.model then
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
  if Flags.model then
   begin
    let j: i:id{registered i /\ honest_share i} = i in
    FStar.Classical.impl_intro (lemma_dishonest_and_honest_tot j);
    cut(dishonest_share i ==> False)
   end
  else ()
*)


(* agile formatting; could be put in some other file *) 

#set-options "--z3rlimit 100"

let parse g x =
  match g with
  | ECDH g ->
    (match ECGroup.parse_point g x with
    | None -> None | Some gx -> Some (S_EC g gx))
  | FFDH g ->
    let dhp = DHGroup.params_of_group g in
    if length x = length dhp.dh_p then Some (S_FF g x)
    else None

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
let serialize #g s =
  match g with
  | FFDH g -> let S_FF _ s = s in DHGroup.serialize #g s
  | ECDH g -> let S_EC _ s = s in ECGroup.serialize #g s

// Serialize for keyShare extension
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

// 18-02-20 used in Extensions; to be replaced by QD 4.2.8 + group/namedGroup wrapper
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
private let rec keyShareEntriesBytes_aux (b:bytes{length b < 65536}) (kes:list keyShareEntry): Tot (b:bytes{length b < 65536}) (decreases kes) =
  match kes with
  | [] -> b
  | ke::kes ->
    let b' = b @| keyShareEntryBytes ke in
    if length b' < 65536 then
      keyShareEntriesBytes_aux b' kes
    else b

let keyShareEntriesBytes kes =
  let b = keyShareEntriesBytes_aux empty_bytes kes in
  lemma_repr_bytes_values (length b);
  vlbytes 2 b

(** Parsing function for a list KeyShareEntry *)
private let rec parseKeyShareEntries_aux (b:bytes) (entries:list keyShareEntry)
   : Tot (result (list keyShareEntry)) 
         (decreases (length b))
   = if length b > 0 then
      if length b >= 4 then
	let ng, data = split b 2 in
	match vlsplit 2 data with
	| Correct(kex, bytes) ->
	  begin
	  match parseKeyShareEntry (ng @| vlbytes 2 kex) with
	  | Correct entry -> parseKeyShareEntries_aux bytes (entries @ [entry])
	  | Error z -> Error z
	  end
	| Error z -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entry")
      else Error (AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Too few bytes to parse key share entries")
    else Correct entries
  
let parseKeyShareEntries b =
  match vlparse 2 b with
  | Correct b -> parseKeyShareEntries_aux b []
  | Error z   -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entries")

(** Serializing function for a ClientKeyShare *)
let clientKeyShareBytes cks = keyShareEntriesBytes cks

(** Parsing function for a ClientKeyShare *)
let parseClientKeyShare b =
  match parseKeyShareEntries b with
  | Correct kes ->
    if List.Tot.length kes < 65536/4
    then Correct kes
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse client key share entries")
  | Error z -> Error z

(** Serializing function for a ServerKeyShare *)
let serverKeyShareBytes sks = keyShareEntryBytes sks

(** Parsing function for a ServerKeyShare *)
let parseServerKeyShare b = parseKeyShareEntry b

(** Serializing function for a KeyShare *)
let keyShareBytes = function
  | ClientKeyShare cks -> clientKeyShareBytes cks
  | ServerKeyShare sks -> serverKeyShareBytes sks
  | HRRKeyShare ng -> namedGroupBytes ng

(** Parsing function for a KeyShare *)
let parseKeyShare msg b =
  match msg with
  | KS_HRR ->
    if length b = 2 then
      match parseNamedGroup b with
      | Correct ng -> Correct (HRRKeyShare ng)
      | Error z -> Error z
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "bad HRR key_share extension")
  | KS_ClientHello ->
    if 2 <= length b && length b < 65538 then
      begin
      match parseClientKeyShare b with
      | Correct kse -> Correct (ClientKeyShare kse)
      | Error z -> Error z
      end
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse client key share list")
  | KS_ServerHello ->
    if 4 <= length b then
      begin
      match parseServerKeyShare b with
      | Correct ks -> Correct (ServerKeyShare ks)
      | Error z -> Error z
      end
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse server key share")
