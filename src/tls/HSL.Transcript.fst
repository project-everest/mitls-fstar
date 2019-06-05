module HSL.Transcript
open FStar.Integers
open FStar.HyperStack.ST
module List = FStar.List.Tot
module HS = FStar.HyperStack
module B = LowStar.Buffer
module G = FStar.Ghost

module HSM = Parsers.Handshake
module HSM12 = Parsers.Handshake12
module HSM13 = Parsers.Handshake13

module PV = Parsers.ProtocolVersion
module LP = LowParse.Low.Base
module IncHash = EverCrypt.Hash.Incremental

module R = MITLS.Repr
module R_HS = MITLS.Repr.Handshake

module R_CH = MITLS.Repr.ClientHello
module CH = Parsers.ClientHello

module R_SH = MITLS.Repr.ServerHello
module SH = Parsers.ServerHello

let is_hrr _ = false
let nego_version _ _ = admit ()

//Seems to be automatic
let serialize_max_size
  (#pk:_) (#t:_) (#p:LP.parser pk t) (s:LP.serializer p)
  (x:t)
: Lemma
  (requires (
    match pk.LP.parser_kind_high with
    | None -> False
    | Some n -> n < max_message_size
  ))
  (ensures (
    Seq.length (LP.serialize s x) < max_message_size
  ))
= ()

module LPSL = LowParse.Spec.List

assume
val serialize_list_max_size
  (#pk:_) (#t:_) (#p:LP.parser pk t) (s:LP.serializer p)
  (x:list t)
: Lemma
  (requires (
    LPSL.serialize_list_precond pk /\ (
    match pk.LP.parser_kind_high with
    | None -> False
    | Some n -> n < max_message_size
  )))
  (ensures (
    Seq.length (LP.serialize (LPSL.serialize_list _ s) x) <= List.Tot.length x * max_message_size
  ))
//  [SMTPat (Seq.length (LP.serialize (LPSL.serialize_list _ s) x))]

let serialize_client_hello (ch:CH.clientHello) =
  LP.serialize HSM.handshake_serializer (HSM.M_client_hello ch)

let serialize_server_hello (sh:SH.serverHello) =
  LP.serialize HSM.handshake_serializer (HSM.M_server_hello sh)

let serialize_retry (r:option retry)
  : GTot (b:bytes{Seq.length b < 2 * max_message_size })
  =
  match r with
  | None -> Seq.empty
  | Some (ht, sh) ->
    let ht = FStar.Bytes.hide ht in
    LP.serialize HSM.handshake_serializer (Parsers.Handshake.M_message_hash ht) `Seq.append`
    serialize_server_hello sh

let transcript_bytes (t:transcript_t)
  : GTot (b:bytes {
    Seq.length b <= (max_transcript_size + 4) * max_message_size
    })
  = match t with
  | Start r ->
    serialize_retry r

  | TruncatedClientHello r tch ->
    serialize_retry r `Seq.append`
    FStar.Bytes.reveal (PB.truncate_clientHello_bytes (HSM.M_client_hello tch))

  | ClientHello r ch ->
    serialize_retry r `Seq.append`
    serialize_client_hello ch
    
  | Transcript12 ch sh rest ->
    serialize_list_max_size HSM12.handshake12_serializer rest;
    serialize_client_hello ch `Seq.append`
    serialize_server_hello sh `Seq.append`
    LP.serialize (LPSL.serialize_list _ HSM12.handshake12_serializer) rest

  | Transcript13 retry ch sh rest ->
    serialize_list_max_size HSM13.handshake13_serializer rest;
    serialize_retry retry `Seq.append`
    serialize_client_hello ch `Seq.append`
    serialize_server_hello sh `Seq.append`
    LP.serialize (LPSL.serialize_list _ HSM13.handshake13_serializer) rest

let transcript_is_empty (t: transcript_t) : Tot bool = match t with
  | Start None -> true
  | _ -> false

let transcript_get_retry (t: transcript_t) : Tot (option retry) = match t with
  | Start r -> r
  | TruncatedClientHello r _ -> r
  | ClientHello r _ -> r
  | Transcript12 _ _ _ -> None
  | Transcript13 r _ _ _ -> r

let transcript_set_retry (t: transcript_t) (r: option retry { Transcript12? t ==> None? r }) : Tot transcript_t =
  match t with
  | Start _ -> Start r
  | TruncatedClientHello _ tch -> TruncatedClientHello r tch
  | ClientHello _ ch -> ClientHello r ch
  | Transcript12 ch sh rest -> Transcript12 ch sh rest
  | Transcript13 _ ch sh rest -> Transcript13 r ch sh rest

let transcript_script_bytes (t: transcript_t) : Lemma
  (transcript_bytes t `Seq.equal` (serialize_retry (transcript_get_retry t) `Seq.append` transcript_bytes (transcript_set_retry t None)))
= ()

let transcript_bytes_does_not_start_with_message_hash
  (t: transcript_t)
  (r: retry)
  (q: Seq.seq FStar.UInt8.t)
: Lemma
  (requires (transcript_get_retry t == None /\ transcript_bytes t == serialize_retry (Some r) `Seq.append` q))
  (ensures False)
= ()

let transcript_bytes_injective_retry
  (r1: option retry)
  (t1: transcript_t { transcript_get_retry t1 == None } )
  (r2: option retry)
  (t2: transcript_t { transcript_get_retry t2 == None } )
: Lemma
  (requires (serialize_retry r1 `Seq.append` transcript_bytes t1 == serialize_retry r2 `Seq.append` transcript_bytes t2))
  (ensures (r1 == r2 /\ transcript_bytes t1 `Seq.equal` transcript_bytes t2))
= match r1, r2 with
  | None, None ->
    assert (transcript_bytes t1 `Seq.equal` (Seq.empty `Seq.append` transcript_bytes t1));
    assert (transcript_bytes t2 `Seq.equal` (Seq.empty `Seq.append` transcript_bytes t2))
  | Some (ht1, sh1), Some (ht2, sh2) ->
    assert ((serialize_retry r1 `Seq.append` transcript_bytes t1) `Seq.equal` (LP.serialize HSM.handshake_serializer (HSM.M_message_hash (FStar.Bytes.hide ht1)) `Seq.append` (serialize_server_hello sh1 `Seq.append` transcript_bytes t1)));
    assert ((serialize_retry r2 `Seq.append` transcript_bytes t2) `Seq.equal` (LP.serialize HSM.handshake_serializer (HSM.M_message_hash (FStar.Bytes.hide ht2)) `Seq.append` (serialize_server_hello sh2 `Seq.append` transcript_bytes t2)));
    assume (r1 == r2 /\ transcript_bytes t1 == transcript_bytes t2)

let transcript_bytes_injective (t1 t2:transcript_t)
  : Lemma
    (requires
      transcript_bytes t1 `Seq.equal` transcript_bytes t2)
    (ensures
      t1 == t2)
  = // match t1 with
    // | Start r1 ->
    admit()        
      

noeq
type state (a:HashDef.hash_alg) = {
  region:Mem.rgn;
  loc: Ghost.erased B.loc;
  hash_state: IncHash.state a
}

let invariant (#a:HashDef.hash_alg) (s:state a) (tx:transcript_t) (h:HS.mem) =
  IncHash.hashes h s.hash_state (transcript_bytes tx) /\
  B.loc_region_only true s.region `B.loc_includes` Ghost.reveal s.loc /\
  Ghost.reveal s.loc == IncHash.footprint s.hash_state h /\
  B.loc_not_unused_in h `B.loc_includes` Ghost.reveal s.loc

let footprint (#a:HashDef.hash_alg) (s:state a) = Ghost.reveal s.loc

let elim_invariant #a s t h = ()

let region_of #a s = s.region

let frame_invariant (#a:_) (s:state a) (t: transcript_t) (h0 h1:HS.mem) (l:B.loc) =
  IncHash.modifies_disjoint_preserves l h0 h1 s.hash_state

#set-options "--max_fuel 0 --max_ifuel  1 --initial_ifuel  1"
let create r a =
  let h0 = get() in
  let s = IncHash.create_in a r in
  let h1 = get () in
  {region=r;
   loc=Ghost.hide (IncHash.footprint s h1);
   hash_state=s},
  Ghost.hide (Start None)

#set-options "--max_fuel 0 --max_ifuel  1 --initial_ifuel  1 --z3rlimit 20"

let extend (#a:_) (s:state a) (l:label_repr) (tx:G.erased transcript_t) =
  let h0 = HyperStack.ST.get() in
  match l with
  | LR_ClientHello #b ch ->
    admit(); // Working
    assume (C.qbuf_qual (C.as_qbuf b.R.base) = C.MUTABLE);

    // These three lemmas prove that the data in the subbuffer data is
    // the serialized data corresponding to the client hello that is being added
    R.reveal_valid();
    LP.valid_pos_valid_exact HSM.handshake_parser h0 (R.to_slice b) ch.R.start_pos ch.R.end_pos;
    LP.valid_exact_serialize HSM.handshake_serializer h0 (R.to_slice b) ch.R.start_pos ch.R.end_pos;

    let len = ch.R.end_pos - ch.R.start_pos in
    let data = C.sub b.R.base ch.R.start_pos len in

    assert_norm (pow2 32 < pow2 61);
    let st' = IncHash.update a s.hash_state (G.elift1 transcript_bytes tx) (C.to_buffer data) len in

    let tx' = G.hide (Some?.v (transition (G.reveal tx) (label_of_label_repr l))) in
    
    {s with hash_state = st'}, tx'

  | LR_ServerHello #b sh ->
    admit(); // Working
    assume (C.qbuf_qual (C.as_qbuf b.R.base) = C.MUTABLE);

    // assert (let Start retry = G.reveal tx in IncHash.hashes h0 s.hash_state (serialize_retry retry) );
    // assert (let Start retry = G.reveal tx in
    //   ClientHello retry (HSM.M_client_hello?._0 (R.value ch)) ==
    //   Some?.v (transition (G.reveal tx) (label_of_label_repr l)));


    // These three lemmas prove that the data in the subbuffer data is
    // the serialized data corresponding to the server hello that is being added
    R.reveal_valid();
    LP.valid_pos_valid_exact HSM.handshake_parser h0 (R.to_slice b) sh.R.start_pos sh.R.end_pos;
    LP.valid_exact_serialize HSM.handshake_serializer h0 (R.to_slice b) sh.R.start_pos sh.R.end_pos;

    let len = sh.R.end_pos - sh.R.start_pos in
    let data = C.sub b.R.base sh.R.start_pos len in

    // assert (C.as_seq h0 data == serialize_server_hello (HSM.M_server_hello?._0 (R.value sh)));


    assert_norm (pow2 32 < pow2 61);
    let st' = IncHash.update a s.hash_state (G.elift1 transcript_bytes tx) (C.to_buffer data) len in
    let h1 = HyperStack.ST.get() in

    let tx' = G.hide (Some?.v (transition (G.reveal tx) (label_of_label_repr l))) in

    LPSL.serialize_list_nil HSM12.handshake12_parser HSM12.handshake12_serializer;
    LPSL.serialize_list_nil HSM13.handshake13_parser HSM13.handshake13_serializer;
    assert ((transcript_bytes (G.reveal tx) `Seq.append` 
             serialize_server_hello (HSM.M_server_hello?._0 (R.value sh)))
        `Seq.equal`     
             transcript_bytes (G.reveal tx'));

    {s with hash_state = st'}, tx'

  | LR_TCH #b tch ->
    assume (C.qbuf_qual (C.as_qbuf b.R.base) = C.MUTABLE);

    // These three lemmas prove that the data in the subbuffer data is
    // the serialized data corresponding to the client hello that is being added
    R.reveal_valid();
    LP.valid_pos_valid_exact HSM.handshake_parser h0 (R.to_slice b) tch.R.start_pos tch.R.end_pos;
    LP.valid_exact_serialize HSM.handshake_serializer h0 (R.to_slice b) tch.R.start_pos tch.R.end_pos;
    // PB.truncate_clientHello_bytes_correct (R.value tch);

    // LP.valid_equiv 
    // let h0 = HyperStack.ST.get() in
    // assume (LP.valid HSM.handshake_parser h0 (R.to_slice b) tch.R.start_pos);
    // let end_pos = PB.binders_pos (R.to_slice b) tch.R.start_pos in

    admit()

    // let len = tch.R.end_pos - tch.R.start_pos in
    // let data = C.sub b.R.base tch.R.start_pos len in

    // assert_norm (pow2 32 < pow2 61);
    // let st' = IncHash.update a s.hash_state (G.elift1 transcript_bytes tx) (C.to_buffer data) len in

    // let tx' = G.hide (Some?.v (transition (G.reveal tx) (label_of_label_repr l))) in
    
    // {s with hash_state = st'}, tx'    

  | LR_CompleteTCH #b tch -> admit()

  | LR_HRR #b1 ch_tag #b2 hrr -> admit()

  | LR_HSM12 #b hs12 -> admit()

  | LR_HSM13 #b hs13 -> admit()

let transcript_hash (a:HashDef.hash_alg) (t:transcript_t) = Spec.Hash.hash a (transcript_bytes t)

let extract_hash (#a:_) (s:state a) 
  (tag:Hacl.Hash.Definitions.hash_t a)
  (tx:G.erased transcript_t)
  = IncHash.finish a s.hash_state (G.hide (transcript_bytes (G.reveal tx))) tag

