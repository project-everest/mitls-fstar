module ParsersAux.Binders.Aux

module LP = LowParse.Low
module LS = LowParse.SLow.List
module U32 = FStar.UInt32

module L = FStar.List.Tot
module H = Parsers.Handshake
module CH = Parsers.ClientHello
module CHE = Parsers.ClientHelloExtension
module Psks = Parsers.OfferedPsks
module ET = Parsers.ExtensionType
module CHEs = Parsers.ClientHelloExtensions
module HT = Parsers.HandshakeType

friend Parsers.OfferedPsks
friend Parsers.ClientHelloExtension_CHE_pre_shared_key
friend Parsers.PreSharedKeyClientExtension
friend Parsers.ClientHelloExtensions
friend Parsers.ClientHello
friend Parsers.Handshake_m_client_hello

open ParsersAux.Seq

let serialize_offeredPsks_eq
  o
= LP.serialize_synth_eq _ Psks.synth_offeredPsks Psks.offeredPsks'_serializer Psks.synth_offeredPsks_recip () o;
  LP.serialize_nondep_then_eq _ Psks.offeredPsks_identities_serializer () _ Psks.offeredPsks_binders_serializer (o.Psks.identities, o.Psks.binders)

let serialize_clientHelloExtension_CHE_pre_shared_key_eq
  o
= LP.serialize_synth_eq _ CHE.synth_clientHelloExtension_CHE_pre_shared_key CHE.clientHelloExtension_CHE_pre_shared_key'_serializer CHE.synth_clientHelloExtension_CHE_pre_shared_key_recip () o;
  Psks.offeredPsks_bytesize_eq o

let serialize_list_clientHelloExtension
  l
= LP.serialize (LP.serialize_list _ CHE.clientHelloExtension_serializer) l

let serialize_list_clientHelloExtension_eq
  l
= L.append_init_last l;
  LP.serialize_list_append _ CHE.clientHelloExtension_serializer (L.init l) [L.last l];
  LP.serialize_list_singleton _ CHE.clientHelloExtension_serializer (L.last l)

#push-options "--z3rlimit 16"

let rec serialize_list_eq_parser_fail
  (#k: LP.parser_kind)
  (#t: Type)
  (#p: LP.parser k t)
  (s: LP.serializer p { k.LP.parser_kind_subkind == Some LP.ParserStrong /\ k.LP.parser_kind_low > 0 })
  (l1 l2: list t)
  (b1 b2: LP.bytes)
: Lemma
  (requires (
    LP.serialize (LP.serialize_list _ s) l1 `Seq.append` b1 == LP.serialize (LP.serialize_list _ s) l2 `Seq.append` b2 /\
    LP.parse p b1 == None /\
    LP.parse p b2 == None
  ))
  (ensures (l1 == l2 /\ b1 == b2))
  (decreases (L.length l1))
= LP.serialize_list_nil _ s;
  assert (b1 `Seq.equal` (Seq.append Seq.empty b1));
  assert (b2 `Seq.equal` (Seq.append Seq.empty b2));
  if L.length l2 < L.length l1
  then serialize_list_eq_parser_fail s l2 l1 b2 b1
  else match l1, l2 with
  | [], [] -> ()
  | x1 :: l1', x2 :: l2' ->
    LP.serialize_list_cons _ s x1 l1' ;
    LP.serialize_list_cons _ s x2 l2' ;
    Seq.append_assoc (LP.serialize s x1) (LP.serialize (LP.serialize_list _ s) l1') b1;
    Seq.append_assoc (LP.serialize s x2) (LP.serialize (LP.serialize_list _ s) l2') b2;
    LP.serialize_strong_prefix s x1 x2 (LP.serialize (LP.serialize_list _ s) l1' `Seq.append` b1) (LP.serialize (LP.serialize_list _ s) l2' `Seq.append` b2);
    serialize_list_eq_parser_fail s l1' l2' b1 b2
  | [], x2 :: l2' ->
    LP.serialize_list_cons _ s x2 l2' ;
    LP.parse_strong_prefix p (LP.serialize s x2) b1

#pop-options

let serialize_list_clientHelloExtension_inj_prefix
  l1 l2 b1 b2
= serialize_list_eq_parser_fail CHE.clientHelloExtension_serializer l1 l2 b1 b2

let size32_list_clientHelloExtension
  l
= LS.size32_list CHE.clientHelloExtension_size32 () l

module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack

#push-options "--z3rlimit 16"

inline_for_extraction
let rec list_last_pos
  (#k: _)
  (#t: _)
  (#p: LP.parser k t)
  (s: LP.serializer p)
  (j: LP.jumper p)
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos pos' : U32.t)
  (l: Ghost.erased (list t))
: HST.Stack U32.t
  (requires (fun h ->
    k.LP.parser_kind_subkind == Some LP.ParserStrong /\
    k.LP.parser_kind_low > 0 /\
    LP.live_slice h sl /\
    U32.v pos <= U32.v pos' /\
    U32.v pos' <= U32.v sl.LP.len /\
    LP.bytes_of_slice_from_to h sl pos pos' `Seq.equal` LP.serialize (LP.serialize_list _ s) (Ghost.reveal l) /\
    Cons? (Ghost.reveal l)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + Seq.length (LP.serialize (LP.serialize_list _ s) (L.init (Ghost.reveal l))) == U32.v res
  ))
= let h0 = HST.get () in
  HST.push_frame ();
  let h1 = HST.get () in
  let bgleft = B.alloca (Ghost.hide ([] <: list t)) 1ul in
  let bgright = B.alloca l 1ul in
  let bpos1 = B.alloca pos 1ul in
  LP.serialize_list_nil _ s;
  let _ = C.Loops.do_while
    (fun h stop ->
      B.modifies (B.loc_region_only true (HS.get_tip h1)) h1 h /\
      B.live h bgleft /\
      B.live h bgright /\
      B.live h bpos1 /\ (
      let left = Ghost.reveal (Seq.index (B.as_seq h bgleft) 0) in
      let right = Ghost.reveal (Seq.index (B.as_seq h bgright) 0) in
      let pos1 = Seq.index (B.as_seq h bpos1) 0 in
      Ghost.reveal l == left `L.append` right /\
      U32.v pos + Seq.length (LP.serialize (LP.serialize_list _ s) left) == U32.v pos1 /\
      U32.v pos1 <= U32.v pos' /\
      LP.bytes_of_slice_from_to h0 sl pos1 pos' `Seq.equal` LP.serialize (LP.serialize_list _ s) right /\
      Cons? right /\
      (stop == true ==> L.length right == 1)
    ))
    (fun _ ->
      let pos1 = B.index bpos1 0ul in
      let gright = B.index bgright 0ul in
      LP.serialize_list_cons _ s (L.hd (Ghost.reveal gright)) (L.tl (Ghost.reveal gright));
      assert (LP.bytes_of_slice_from h0 sl pos1 `seq_starts_with` LP.bytes_of_slice_from_to h0 sl pos1 pos');
      let pos2 = jump_serializer s j sl pos1 (Ghost.hide (L.hd (Ghost.reveal gright))) in
      if pos2 = pos'
      then begin
        let f () : Lemma
          (Nil? (L.tl (Ghost.reveal gright)))
        = match L.tl (Ghost.reveal gright) with
          | [] -> ()
          | a :: q -> LP.serialize_list_cons _ s a q   
        in
        f ();
        true
      end else begin
        let gleft = B.index bgleft 0ul in
        B.upd bgleft 0ul (Ghost.hide (Ghost.reveal gleft `L.append` [L.hd (Ghost.reveal gright)]));
        B.upd bgright 0ul (Ghost.hide (L.tl (Ghost.reveal gright)));
        B.upd bpos1 0ul pos2;
        L.append_assoc (Ghost.reveal gleft) [L.hd (Ghost.reveal gright)] (L.tl (Ghost.reveal gright));
        LP.serialize_list_singleton _ s (L.hd (Ghost.reveal gright));
        LP.serialize_list_append _ s (Ghost.reveal gleft) [L.hd (Ghost.reveal gright)];
        false
      end
    )
  in
  let res = B.index bpos1 0ul in
  let h = HST.get () in
  L.init_last_def (Ghost.reveal (Seq.index (B.as_seq h bgleft) 0)) (L.hd (Ghost.reveal (Seq.index (B.as_seq h bgright) 0)));
  HST.pop_frame ();
  res

#pop-options

let list_clientHelloExtension_last_pos
  #rrel #rel sl pos pos' gl
= list_last_pos CHE.clientHelloExtension_serializer CHE.clientHelloExtension_jumper sl pos pos' gl

let clientHelloExtensions_list_bytesize_eq'
  l
= CHEs.clientHelloExtensions_list_bytesize_eq l

let serialize_clientHelloExtensions_eq
  l
= CHEs.clientHelloExtensions_list_bytesize_eq l;
  LP.serialized_list_length_eq_length_serialize_list CHE.clientHelloExtension_serializer l;
  LP.serialize_synth_eq _ CHEs.synth_clientHelloExtensions CHEs.clientHelloExtensions'_serializer CHEs.synth_clientHelloExtensions_recip () l

let serialize_clientHello_eq
  c
= LP.serialize_synth_eq _ CH.synth_clientHello CH.clientHello'_serializer CH.synth_clientHello_recip () c;
  LP.serialize_nondep_then_eq _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer (c.CH.version, c.CH.random);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer ((c.CH.version, c.CH.random), c.CH.session_id);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer (((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer) () _ CH.clientHello_compression_method_serializer ((((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites), c.CH.compression_method);
  LP.serialize_nondep_then_eq _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ (LP.serialize_nondep_then  _ Parsers.ProtocolVersion.protocolVersion_serializer () _ Parsers.Random.random_serializer) () _ Parsers.SessionID.sessionID_serializer) () _ CH.clientHello_cipher_suites_serializer) () _ CH.clientHello_compression_method_serializer) () _ CHEs.clientHelloExtensions_serializer (((((c.CH.version, c.CH.random), c.CH.session_id), c.CH.cipher_suites), c.CH.compression_method), c.CH.extensions)

let serialize_handshake_m_client_hello_eq
  c
= CH.clientHello_bytesize_eq c
