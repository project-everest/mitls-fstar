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

module R = MITLS.Repr
module R_HS = MITLS.Repr.Handshake

module R_CH = MITLS.Repr.ClientHello
module CH = Parsers.ClientHello

module R_SH = MITLS.Repr.ServerHello
module SH = Parsers.ServerHello
module CRF = EverCrypt.CRF
module TestCRF = Test.CRF

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
  [SMTPat (Seq.length (LP.serialize (LPSL.serialize_list _ s) x))]

let serialize_retry (r:option retry)
  : GTot (b:bytes{Seq.length b < 2 * max_message_size })
  =
  match r with
  | None -> Seq.empty
  | Some (ht, sh) ->
    let ht = FStar.Bytes.hide ht in
    LP.serialize HSM.handshake_serializer (Parsers.Handshake.M_message_hash ht) `Seq.append`
    LP.serialize SH.serverHello_serializer sh

let serialize_client_hello (ch:CH.clientHello) =
  LP.serialize HSM.handshake_serializer (HSM.M_client_hello ch)

let serialize_server_hello (sh:SH.serverHello) =
  LP.serialize HSM.handshake_serializer (HSM.M_server_hello sh)

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

let rec transcript_bytes_injective (t1 t2:transcript_t)
  : Lemma
    (transcript_bytes t1 `Seq.equal` transcript_bytes t2 ==>
     t1 == t2)
  = admit()
      

noeq
type state (a:HashDef.hash_alg) = {
  region:Mem.rgn;
  loc: Ghost.erased B.loc;
  hash_state: CRF.state a
}

let invariant (#a:HashDef.hash_alg) (s:state a) (tx:transcript_t) (h:HS.mem) =
  CRF.hashed h s.hash_state `Seq.equal` transcript_bytes tx /\
  B.loc_region_only true s.region `B.loc_includes` Ghost.reveal s.loc /\
  Ghost.reveal s.loc == CRF.footprint s.hash_state h /\
  B.loc_not_unused_in h `B.loc_includes` Ghost.reveal s.loc

let footprint (#a:HashDef.hash_alg) (s:state a) = Ghost.reveal s.loc

let elim_invariant #a s t h = ()

let region_of #a s = s.region

let frame_invariant (#a:_) (s:state a) (t: transcript_t) (h0 h1:HS.mem) (l:B.loc) =
  CRF.modifies_disjoint_preserves l h0 h1 s.hash_state

#set-options "--max_fuel 0 --max_ifuel  1 --initial_ifuel  1"
let create r a =
  let h0 = get() in
  let s = CRF.create_in a r in
  let h1 = get () in
  {region=r;
   loc=Ghost.hide (CRF.footprint s h1);
   hash_state=s},
  Ghost.hide (Start None)

let extend (#a:_) (s:state a) (l:label_repr) (tx:G.erased transcript_t) =
  match l with
  | LR_ClientHello #b ch ->
    let h0 = HyperStack.ST.get() in
    assert (let Start retry = G.reveal tx in CRF.hashes h0 s.hash_state (serialize_retry retry) );
    assert (let Start retry = G.reveal tx in
      ClientHello retry (HSM.M_client_hello?._0 (R.value ch)) ==
      Some?.v (transition (G.reveal tx) (label_of_label_repr l)));
    admit();
    // TODO: Call IncHash.update a s tx data len
    // where as_seq data == serialize CH.clientHello_serializer ch and len is its length
    G.hide (Some?.v (transition (G.reveal tx) (label_of_label_repr l)))
  | _ -> admit()

let transcript_hash (a:HashDef.hash_alg) (t:transcript_t)
  = Spec.Hash.hash a (transcript_bytes t)

let hashed (a:HashDef.hash_alg) (t:transcript_t) = 
  Model.CRF.hashed a (transcript_bytes t)
  
let extract_hash (#a:_) (s:state a) 
  (tag:Hacl.Hash.Definitions.hash_t a)
  (tx:G.erased transcript_t)
  = CRF.finish a s.hash_state (G.hide (transcript_bytes (G.reveal tx))) tag

let injectivity a t0 t1 =
  let b0 = Ghost.hide (transcript_bytes (Ghost.reveal t0)) in
  let b1 = Ghost.hide (transcript_bytes (Ghost.reveal t1)) in
  Model.CRF.injective a b0 b1;
  transcript_bytes_injective (Ghost.reveal t0) (Ghost.reveal t1)
