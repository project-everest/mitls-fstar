module CommonDH

open FStar.HyperStack
open FStar.Bytes
open FStar.Error
open CoreCrypto
open Parse
open TLSError
open FStar.HyperStack.ST

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MM = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap

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

let namedGroup_of_group (g:group): Tot (option namedGroup) =
  match g with
  | ECDH CoreCrypto.ECC_P256 -> Some SECP256R1
  | ECDH CoreCrypto.ECC_P384 -> Some SECP384R1
  | ECDH CoreCrypto.ECC_P521 -> Some SECP521R1
  | ECDH CoreCrypto.ECC_X25519 -> Some X25519
  | ECDH CoreCrypto.ECC_X448 -> Some X448
  | FFDH (DHGroup.Named DHGroup.FFDHE2048) -> Some FFDHE2048
  | FFDH (DHGroup.Named DHGroup.FFDHE3072) -> Some FFDHE3072
  | FFDH (DHGroup.Named DHGroup.FFDHE4096) -> Some FFDHE4096
  | FFDH (DHGroup.Named DHGroup.FFDHE6144) -> Some FFDHE6144
  | FFDH (DHGroup.Named DHGroup.FFDHE8192) -> Some FFDHE8192
  | _ -> None

let lemma_namedGroup_of_group (g:group)
  : Lemma (Some? (namedGroup_of_group g) <==> (ECDH? g \/ (FFDH? g /\ DHGroup.Named? (FFDH?._0 g))))
  [SMTPat (namedGroup_of_group g)]
  = ()

let group_of_namedGroup (ng:namedGroup): Tot (option group) =
  match ng with
  | SECP256R1 -> Some (ECDH CoreCrypto.ECC_P256)
  | SECP384R1 -> Some (ECDH CoreCrypto.ECC_P384)
  | SECP521R1 -> Some (ECDH CoreCrypto.ECC_P521)
  | X25519    -> Some (ECDH CoreCrypto.ECC_X25519)
  | X448      -> Some (ECDH CoreCrypto.ECC_X448)
  | FFDHE2048 -> Some (FFDH (DHGroup.Named DHGroup.FFDHE2048))
  | FFDHE3072 -> Some (FFDH (DHGroup.Named DHGroup.FFDHE3072))
  | FFDHE4096 -> Some (FFDH (DHGroup.Named DHGroup.FFDHE4096))
  | FFDHE6144 -> Some (FFDH (DHGroup.Named DHGroup.FFDHE6144))
  | FFDHE8192 -> Some (FFDH (DHGroup.Named DHGroup.FFDHE8192))
  | _         -> None

let is_ecdhe (ng:namedGroup): Tot bool = List.mem ng [ SECP256R1; SECP384R1; SECP521R1; X25519; X448 ]

let is_ffdhe (ng:namedGroup): Tot bool = List.mem ng [ FFDHE2048; FFDHE3072; FFDHE4096; FFDHE6144; FFDHE8192 ]

// let lemma_group_of_namedGroup (ng:namedGroup)
//   : Lemma (Some? (group_of_namedGroup ng) <==> (SEC? ng \/ FFDHE? ng))
//   [SMTPat (group_of_namedGroup ng)]
//   = ()

let default_group = ECDH (CoreCrypto.ECC_P256)

(* Global log of honestly generated DH shares *)
type honest (i:id) = bool
let dh_region = new_region tls_tables_region
private type ideal_log = MM.t dh_region id honest (fun _ -> True)
private type share_table = (if Flags.ideal_KEF then ideal_log else unit)

abstract let share_log: share_table =
  (if Flags.ideal_KEF then
    MM.alloc () <: ideal_log
  else
    ())

let registered i =
  (if Flags.ideal_KEF then
    let log : ideal_log = share_log in
    HST.witnessed (MM.defined log i)
  else
    True)

let honest_share i =
  (if Flags.ideal_KEF then
    let log : ideal_log = share_log in
    HST.witnessed (MM.contains log i true)
  else False)

let dishonest_share i =
  (if Flags.ideal_KEF then
    let log : ideal_log = share_log in
    HST.witnessed (MM.contains log i false)
  else True)

let pre_pubshare #g ks =
  match g with
  | FFDH dhg -> let KS_FF _ ks = ks in S_FF dhg (DHGroup.pubshare #dhg ks)
  | ECDH ecg -> let KS_EC _ ks = ks in S_EC ecg (ECGroup.pubshare #ecg ks)

let pubshare (#g:group) (s:keyshare g) : Tot (share g) =
  let gx = pre_pubshare s in
  cut(registered (|g, gx |)); gx

let is_honest i =
  if Flags.ideal_KEF then
   begin
    let log : ideal_log = share_log in
    let h = get () in
    HST.recall log;
    HST.testify (MM.defined log i);
    cut(Some? (MM.sel (HS.sel h log) i));
    let b = Some?.v (MM.sel (HST.op_Bang log) i) in
    cut(MM.contains log i b h);
    MM.contains_stable log i b;
    HST.mr_witness log (MM.contains log i b); b
   end
  else false

let lemma_honest_or_dishonest (i:id) : ST unit
  (requires (fun h -> registered i))
  (ensures (fun h0 _ h1 -> dishonest_share i \/ honest_share i))
  =
  if Flags.ideal_KEF then
   begin
    let log : ideal_log = share_log in
    let h = get () in
    HST.recall log;
    HST.testify (MM.defined log i);
    cut(Some? (MM.sel (HS.sel h log) i));
    let b = Some?.v (MM.sel (HST.op_Bang log) i) in
    match b with
    | true ->
      cut(MM.contains log i true h);
      MM.contains_stable log i true;
      HST.mr_witness log (MM.contains log i true)
    | false ->
      cut(MM.contains log i false h);
      MM.contains_stable log i false;
      HST.mr_witness log (MM.contains log i false)
   end
  else ()

let lemma_honest_and_dishonest (i:id)
  : ST unit
  (requires (fun h0 -> registered i /\ honest_share i /\ dishonest_share i))
  (ensures (fun h0 _ h1 -> False))
  =
  if Flags.ideal_KEF then
   begin
    let h = get () in
    let log : ideal_log = share_log in
    HST.recall log;
    HST.testify (MM.defined log i);
    HST.testify (MM.contains log i true);
    cut(true = Some?.v (MM.sel (HS.sel h log) i));
    HST.testify (MM.contains log i false);
    cut(false = Some?.v (MM.sel (HS.sel h log) i));
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
let rec keygen g =
  dbg ("Keygen on " ^ (string_of_group g));
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
     HST.recall log;
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

let dh_initiator #g gx gy =
  dbg ("DH initiator on " ^ (string_of_group g));
  match g with
  | FFDH g ->
    let KS_FF _ gx = gx in
    let S_FF _ gy = gy in
    DHGroup.dh_initiator #g gx gy
  | ECDH g ->
    let KS_EC _ gx = gx in
    let S_EC _ gy = gy in
    ECGroup.dh_initiator #g gx gy

let dh_responder #g gx =
  dbg ("DH responder on " ^ (string_of_group g));
  let gy = keygen g in
  let gxy = dh_initiator #g gy gx in
  (pubshare #g gy, gxy)

#set-options "--z3rlimit 100"
let register #g gx =
  if Flags.ideal_KEF then
   begin
    let log : ideal_log = share_log in
    let i : id = (| g, gx |) in
    HST.recall log;
    match MM.lookup log i with
    | None ->
      MM.extend log i false;
      cut(registered i);
      cut(dishonest_share i);
      gx
    | Some b ->
      cut(HST.witnessed (MM.defined log i));
      gx
   end
  else gx

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

let keyShareEntryBytes (k:keyShareEntry): bytes = 
  let open Format.KeyShareEntry in
  match k with 
  | Share g s -> (
    // cwinter: | Share g s was was marked as TODO; registration is not guaranteed.
    // assume false; // TODO
    let nng = Some?.v (namedGroup_of_group g) in
    let kex = (match s with | S_FF g x -> x) in
    let kse = { group=nng; key_exchange=kex; } in
    keyShareEntry_serializer32 kse)
  | UnknownShare ng b ->
    let kse = { group=ng; key_exchange=b; } in
    keyShareEntry_serializer32 kse
 

(** Parsing function for a KeyShareEntry *)
let parseKeyShareEntry b =
  // cwinter: this was marked as TODO?
  // assume false; // TODO registration
  let open Format.KeyShareEntry in
  let open Format.NamedGroup in
  let prsr = keyShareEntry_parser32 in
  match prsr b with
  | Some (x, _) ->
    assert (Some? (group_of_namedGroup x.group));
    let Some og = group_of_namedGroup x.group in
    if is_ffdhe x.group then
      let FFDH dhg = og in
      let (q:DHGroup.share dhg) = x.key_exchange in 
      let (ps:pre_share og) = S_FF dhg q in
      Correct (Share og ps)
    else if is_ecdhe x.group then
      let ECDH ecg = og in
      let Some (q:ECGroup.share ecg) = (ECGroup.parse_point ecg x.key_exchange) in
      let (ps:pre_share og) = S_EC ecg q in
      Correct (Share og ps)
    else
      Correct (UnknownShare x.group x.key_exchange)
  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse key share entry")
  

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
	let ng, data = split b 2ul in
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
    then Correct (ClientKeyShare kes)
    else Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse client key share entries")
  | Error z -> Error z

(** Serializing function for a ServerKeyShare *)
let serverKeyShareBytes sks = keyShareEntryBytes sks

(** Parsing function for a ServerKeyShare *)
let parseServerKeyShare b =
  match parseKeyShareEntry b with
  | Correct ks -> Correct (ServerKeyShare ks)
  | Error z -> Error z

let helloRetryKeyShareBytes (k:keyShare): Tot (b:bytes) = 
  let HRRKeyShare ng = k in
  namedGroup_serializer32 ng
  
let parseHelloRetryKeyShare (bs:bytes): Tot (result keyShare) =
  match namedGroup_parser32 bs with 
  | Some (ng, _) -> Correct (HRRKeyShare ng)
  | _ -> Error(AD_decode_error, perror __SOURCE_FILE__ __LINE__ "Failed to parse hello retry group")


(** Serializing function for a KeyShare *)
let keyShareBytes = function
  | ClientKeyShare cks -> clientKeyShareBytes cks
  | ServerKeyShare sks -> serverKeyShareBytes sks
  | HRRKeyShare ng -> namedGroupBytes ng
