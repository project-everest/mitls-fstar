module ParsersAux.Binders

module LP = LowParse.Low.Base
module LI = LowParse.Spec.BoundedInt
module HS = FStar.HyperStack
module U32 = FStar.UInt32

(* ClientHello binders *)

module Seq = FStar.Seq
module L = FStar.List.Tot
module H = ParsersAux.Handshake
module CH = Parsers.ClientHello
module CHE = ParsersAux.ClientHelloExtension

module BY = FStar.Bytes

module B = LowStar.Monotonic.Buffer
module HST = FStar.HyperStack.ST

module Psks = Parsers.OfferedPsks

module ET = Parsers.ExtensionType
module CHEs = Parsers.ClientHelloExtensions
module HT = Parsers.HandshakeType

open ParsersAux.Binders.Aux

let offeredPsks_set_binders
  (o: Psks.offeredPsks)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Tot (o' : Psks.offeredPsks {
    o'.Psks.identities == o.Psks.identities /\
    o'.Psks.binders == b' /\
    Psks.offeredPsks_bytesize o' == Psks.offeredPsks_bytesize o
  })
= {
  Psks.identities = o.Psks.identities;
  Psks.binders = b';
}

let offeredPsks_binders_offset
  (o: Psks.offeredPsks)
: Tot (x: U32.t {
    let s = LP.serialize Psks.offeredPsks_serializer o in
    U32.v x < Seq.length s
  })
= serialize_offeredPsks_eq o;
  Psks.offeredPsks_identities_size32 o.Psks.identities

inline_for_extraction
let offeredPsks_binders_pos
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (x: Ghost.erased Psks.offeredPsks)
: HST.Stack U32.t
  (requires (fun h -> 
    let sq = LP.serialize Psks.offeredPsks_serializer (Ghost.reveal x) in
    LP.live_slice h sl /\
    U32.v pos <= U32.v sl.LP.len /\
    (LP.bytes_of_slice_from h sl pos `LP.seq_starts_with` sq)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + U32.v (offeredPsks_binders_offset (Ghost.reveal x)) == U32.v res
  ))
= serialize_offeredPsks_eq (Ghost.reveal x);
  let h = HST.get () in
  LP.jump_serializer Psks.offeredPsks_identities_serializer Psks.offeredPsks_identities_jumper sl pos (Ghost.hide (Ghost.reveal x).Psks.identities)

let truncate_offeredPsks
  (o: Psks.offeredPsks)
: GTot LP.bytes
= Seq.slice (LP.serialize Psks.offeredPsks_serializer o) 0 (U32.v (offeredPsks_binders_offset o))

let binders_offset_offeredPsks_set_binders
  (o: Psks.offeredPsks)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Lemma
  (let o' = offeredPsks_set_binders o b' in
  let off = offeredPsks_binders_offset o in
  let tr = truncate_offeredPsks o in
  offeredPsks_binders_offset o' == off /\
  truncate_offeredPsks o' `Seq.equal` tr /\
  LP.serialize Psks.offeredPsks_serializer o' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let o' = offeredPsks_set_binders o b' in
  let off = offeredPsks_binders_offset o in
  serialize_offeredPsks_eq o;
  serialize_offeredPsks_eq o'

let truncate_offeredPsks_eq_left
  (o: Psks.offeredPsks)
: Lemma
  (truncate_offeredPsks o `Seq.equal` LP.serialize Psks.offeredPsks_identities_serializer o.Psks.identities)
= serialize_offeredPsks_eq o

let clientHelloExtension_CHE_pre_shared_key_set_binders
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Tot (o' : CHE.clientHelloExtension_CHE_pre_shared_key {
    o'.Psks.identities == o.Psks.identities /\
    o'.Psks.binders == b' /\
    CHE.clientHelloExtension_CHE_pre_shared_key_bytesize o' == CHE.clientHelloExtension_CHE_pre_shared_key_bytesize o
  })
= offeredPsks_set_binders o b'

let clientHelloExtension_CHE_pre_shared_key_binders_offset
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
: Tot (x: U32.t {
    let s = LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o in
    U32.v x < Seq.length s
  })
= serialize_clientHelloExtension_CHE_pre_shared_key_eq o;
  2ul `U32.add` offeredPsks_binders_offset o

inline_for_extraction
let clientHelloExtension_CHE_pre_shared_key_binders_pos
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (x: Ghost.erased CHE.clientHelloExtension_CHE_pre_shared_key)
: HST.Stack U32.t
  (requires (fun h -> 
    let sq = LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer (Ghost.reveal x) in
    LP.live_slice h sl /\
    U32.v pos <= U32.v sl.LP.len /\
    (LP.bytes_of_slice_from h sl pos `LP.seq_starts_with` sq)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + U32.v (clientHelloExtension_CHE_pre_shared_key_binders_offset (Ghost.reveal x)) == U32.v res
  ))
= serialize_clientHelloExtension_CHE_pre_shared_key_eq (Ghost.reveal x);
  let h = HST.get () in
  let pos1 = LP.jump_serializer (LI.serialize_bounded_integer 2) (LP.jump_constant_size (LI.parse_bounded_integer 2) 2ul ()) sl pos (Ghost.hide (U32.uint_to_t (Psks.offeredPsks_bytesize (Ghost.reveal x)))) in
  offeredPsks_binders_pos sl pos1 (Ghost.hide (Ghost.reveal x))

let truncate_clientHelloExtension_CHE_pre_shared_key
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
: GTot LP.bytes
= Seq.slice (LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o) 0 (U32.v (clientHelloExtension_CHE_pre_shared_key_binders_offset o))

let binders_offset_clientHelloExtension_CHE_pre_shared_key_set_binders
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize o.Psks.binders })
: Lemma
  (let o' = clientHelloExtension_CHE_pre_shared_key_set_binders o b' in
  let off = clientHelloExtension_CHE_pre_shared_key_binders_offset o in
  let tr = truncate_clientHelloExtension_CHE_pre_shared_key o in
  clientHelloExtension_CHE_pre_shared_key_binders_offset o' == off /\
  truncate_clientHelloExtension_CHE_pre_shared_key o' `Seq.equal` tr /\
  LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer o' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let o' = clientHelloExtension_CHE_pre_shared_key_set_binders o b' in
  let off = clientHelloExtension_CHE_pre_shared_key_binders_offset o in
  serialize_clientHelloExtension_CHE_pre_shared_key_eq o;
  serialize_clientHelloExtension_CHE_pre_shared_key_eq o';
  binders_offset_offeredPsks_set_binders o b'

let truncate_clientHelloExtension_CHE_pre_shared_key_eq_left
  (o: CHE.clientHelloExtension_CHE_pre_shared_key)
: Lemma
  (truncate_clientHelloExtension_CHE_pre_shared_key o `Seq.equal` (LP.serialize (LI.serialize_bounded_integer 2) (U32.uint_to_t (Psks.offeredPsks_bytesize o)) `Seq.append` truncate_offeredPsks o))
= serialize_clientHelloExtension_CHE_pre_shared_key_eq o;
  truncate_offeredPsks_eq_left o

let truncate_clientHelloExtension_CHE_pre_shared_key_inj_binders_bytesize
  (o1 o2: CHE.clientHelloExtension_CHE_pre_shared_key)
: Lemma
  (requires (truncate_clientHelloExtension_CHE_pre_shared_key o1 == truncate_clientHelloExtension_CHE_pre_shared_key o2))
  (ensures (
    Psks.offeredPsks_binders_bytesize o1.Psks.binders == Psks.offeredPsks_binders_bytesize o2.Psks.binders
  ))
= truncate_clientHelloExtension_CHE_pre_shared_key_eq_left o1;
  truncate_clientHelloExtension_CHE_pre_shared_key_eq_left o2;
  LP.serialize_strong_prefix (LI.serialize_bounded_integer 2) (U32.uint_to_t (Psks.offeredPsks_bytesize o1)) (U32.uint_to_t (Psks.offeredPsks_bytesize o2)) (truncate_offeredPsks o1) (truncate_offeredPsks o2);
  assert (Seq.length (truncate_offeredPsks o1) == Seq.length (truncate_offeredPsks o2));  
  Psks.offeredPsks_identities_bytesize_eq o1.Psks.identities;
  Psks.offeredPsks_identities_bytesize_eq o2.Psks.identities

let clientHelloExtension_binders_offset
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
: Tot (x: U32.t { U32.v x < Seq.length (LP.serialize CHE.clientHelloExtension_serializer e) })
= CHE.clientHelloExtension_bytesize_eq e;
  CHE.serialize_clientHelloExtension_eq_pre_shared_key e;
  2ul `U32.add` clientHelloExtension_CHE_pre_shared_key_binders_offset (CHE.CHE_pre_shared_key?._0 e)

inline_for_extraction
let clientHelloExtension_binders_pos
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (x: Ghost.erased CHE.clientHelloExtension { CHE.CHE_pre_shared_key? (Ghost.reveal x) } )
: HST.Stack U32.t
  (requires (fun h -> 
    let sq = LP.serialize CHE.clientHelloExtension_serializer (Ghost.reveal x) in
    LP.live_slice h sl /\
    U32.v pos <= U32.v sl.LP.len /\
    (LP.bytes_of_slice_from h sl pos `LP.seq_starts_with` sq)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + U32.v (clientHelloExtension_binders_offset (Ghost.reveal x)) == U32.v res
  ))
= CHE.serialize_clientHelloExtension_eq_pre_shared_key (Ghost.reveal x);
  let h = HST.get () in
  let pos1 = LP.jump_serializer ET.extensionType_serializer ET.extensionType_jumper sl pos (Ghost.hide ET.Pre_shared_key) in
  clientHelloExtension_CHE_pre_shared_key_binders_pos sl pos1 (Ghost.hide (CHE.CHE_pre_shared_key?._0 (Ghost.reveal x)))

let truncate_clientHelloExtension
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
: GTot LP.bytes
= Seq.slice (LP.serialize CHE.clientHelloExtension_serializer e) 0 (U32.v (clientHelloExtension_binders_offset e))

let clientHelloExtension_set_binders
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 e).Psks.binders})
: Tot (e' : CHE.clientHelloExtension {
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    CHE.clientHelloExtension_bytesize e' == CHE.clientHelloExtension_bytesize e
  })
= CHE.CHE_pre_shared_key (clientHelloExtension_CHE_pre_shared_key_set_binders (CHE.CHE_pre_shared_key?._0 e) b')

let binders_offset_clientHelloExtension_set_binders
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 e).Psks.binders})
: Lemma
  (let e' = clientHelloExtension_set_binders e b' in
  let off = clientHelloExtension_binders_offset e in
  let tr = truncate_clientHelloExtension e in
  clientHelloExtension_binders_offset e' == off /\
  truncate_clientHelloExtension e' `Seq.equal` tr /\
  LP.serialize CHE.clientHelloExtension_serializer e' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let e' = clientHelloExtension_set_binders e b' in
  let off = clientHelloExtension_binders_offset e in
  CHE.serialize_clientHelloExtension_eq_pre_shared_key e;
  CHE.serialize_clientHelloExtension_eq_pre_shared_key e';
  binders_offset_clientHelloExtension_CHE_pre_shared_key_set_binders (CHE.CHE_pre_shared_key?._0 e) b'

let truncate_clientHelloExtension_eq_left
  (e: CHE.clientHelloExtension { CHE.CHE_pre_shared_key? e })
: Lemma
  (truncate_clientHelloExtension e `Seq.equal` (LP.serialize ET.extensionType_serializer ET.Pre_shared_key `Seq.append` truncate_clientHelloExtension_CHE_pre_shared_key (CHE.CHE_pre_shared_key?._0 e)))
= CHE.serialize_clientHelloExtension_eq_pre_shared_key e

let truncate_clientHelloExtension_inj_binders_bytesize
  (e1: CHE.clientHelloExtension { CHE.CHE_pre_shared_key? e1 })
  (e2: CHE.clientHelloExtension { CHE.CHE_pre_shared_key? e2 })
: Lemma
  (requires (truncate_clientHelloExtension e1 == truncate_clientHelloExtension e2))
  (ensures (
    Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 e1).Psks.binders == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 e2).Psks.binders
  ))
= truncate_clientHelloExtension_eq_left e1;
  truncate_clientHelloExtension_eq_left e2;
  let CHE.CHE_pre_shared_key o1 = e1 in
  let CHE.CHE_pre_shared_key o2 = e2 in
  LP.serialize_strong_prefix ET.extensionType_serializer ET.Pre_shared_key ET.Pre_shared_key (truncate_clientHelloExtension_CHE_pre_shared_key o1) (truncate_clientHelloExtension_CHE_pre_shared_key o2);
  truncate_clientHelloExtension_CHE_pre_shared_key_inj_binders_bytesize o1 o2

let parse_truncate_clientHelloExtension
  (e: CHE.clientHelloExtension { CHE.CHE_pre_shared_key? e })
: Lemma
  (LP.parse CHE.clientHelloExtension_parser (truncate_clientHelloExtension e) == None)
= LP.parse_truncate CHE.clientHelloExtension_serializer e (U32.v (clientHelloExtension_binders_offset e))

let rec clientHelloExtensions_list_bytesize_append
  (l1 l2: list CHE.clientHelloExtension)
: Lemma
  (CHEs.clientHelloExtensions_list_bytesize (l1 `L.append` l2) == CHEs.clientHelloExtensions_list_bytesize l1 + CHEs.clientHelloExtensions_list_bytesize l2)
= match l1 with
  | [] -> ()
  | _ :: q -> clientHelloExtensions_list_bytesize_append q l2

let list_clientHelloExtension_binders_offset
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l) /\
    CHEs.clientHelloExtensions_list_bytesize l <= 65535
  })
: Tot (x: U32.t { U32.v x < Seq.length (serialize_list_clientHelloExtension l) })
= serialize_list_clientHelloExtension_eq l;
  clientHelloExtensions_list_bytesize_eq' l;
  size32_list_clientHelloExtension (L.init l) `U32.add` clientHelloExtension_binders_offset (L.last l)

inline_for_extraction
let list_clientHelloExtension_binders_pos
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos pos': U32.t)
  (x: Ghost.erased (list CHE.clientHelloExtension) {
    Cons? (Ghost.reveal x) /\
    CHE.CHE_pre_shared_key? (L.last (Ghost.reveal x)) /\
    CHEs.clientHelloExtensions_list_bytesize (Ghost.reveal x) <= 65535
  } )
: HST.Stack U32.t
  (requires (fun h -> 
    let sq = serialize_list_clientHelloExtension (Ghost.reveal x) in
    LP.live_slice h sl /\
    U32.v pos <= U32.v pos' /\
    U32.v pos' <= U32.v sl.LP.len /\
    (LP.bytes_of_slice_from_to h sl pos pos' `Seq.equal` sq)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + U32.v (list_clientHelloExtension_binders_offset (Ghost.reveal x)) == U32.v res
  ))
= serialize_list_clientHelloExtension_eq (Ghost.reveal x);
  let h = HST.get () in
  let pos1 = list_clientHelloExtension_last_pos sl pos pos' x in
  assert (Seq.length (serialize_list_clientHelloExtension (Ghost.reveal x)) == U32.v pos' - U32.v pos);
  assert (Seq.length (serialize_list_clientHelloExtension (L.init (Ghost.reveal x))) == U32.v pos1 - U32.v pos);
  assert (LP.bytes_of_slice_from_to h sl pos1 pos' `Seq.equal` Seq.slice (LP.bytes_of_slice_from_to h sl pos pos') (U32.v pos1 - U32.v pos) (U32.v pos' - U32.v pos));
  clientHelloExtension_binders_pos sl pos1 (Ghost.hide (L.last (Ghost.reveal x)))

let truncate_list_clientHelloExtension
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l) /\
    CHEs.clientHelloExtensions_list_bytesize l <= 65535
  })
: GTot LP.bytes
= Seq.slice (serialize_list_clientHelloExtension l) 0 (U32.v (list_clientHelloExtension_binders_offset l))

let list_clientHelloExtension_set_binders
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders
  })
: Tot (l' : list CHE.clientHelloExtension {
    Cons? l' /\ (
    let e = L.last l in
    let e' = L.last l' in
    L.init l' = L.init l /\
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    CHEs.clientHelloExtensions_list_bytesize l' == CHEs.clientHelloExtensions_list_bytesize l
  )})
= L.append_init_last l;
  let lt = L.init l in
  let e = L.last l in
  let e' = clientHelloExtension_set_binders (L.last l) b' in
  let l' = lt `L.append` [e'] in
  L.init_last_def lt e' ;
  clientHelloExtensions_list_bytesize_append lt [e];
  clientHelloExtensions_list_bytesize_append lt [e'];
  l'

let binders_offset_list_clientHelloExtension_set_binders
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l) /\
    CHEs.clientHelloExtensions_list_bytesize l <= 65535
  })
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders})
: Lemma
  (
  let l' = list_clientHelloExtension_set_binders l b' in
  let off = list_clientHelloExtension_binders_offset l in
  let tr = truncate_list_clientHelloExtension l in
  list_clientHelloExtension_binders_offset l' == off /\
  truncate_list_clientHelloExtension l' `Seq.equal` tr /\
  serialize_list_clientHelloExtension l' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let l' = list_clientHelloExtension_set_binders l b' in
  let off = list_clientHelloExtension_binders_offset l in
  serialize_list_clientHelloExtension_eq l;
  serialize_list_clientHelloExtension_eq l';
  binders_offset_clientHelloExtension_set_binders (L.last l) b';
  clientHelloExtensions_list_bytesize_eq' l

let truncate_list_clientHelloExtension_eq_left
  (l: list CHE.clientHelloExtension {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l) /\
    CHEs.clientHelloExtensions_list_bytesize l <= 65535
  })
: Lemma
  (truncate_list_clientHelloExtension l `Seq.equal` (serialize_list_clientHelloExtension (L.init l) `Seq.append` truncate_clientHelloExtension (L.last l)))
= serialize_list_clientHelloExtension_eq l;
  clientHelloExtensions_list_bytesize_eq' l

let truncate_list_clientHelloExtension_inj_binders_bytesize
  (l1: list CHE.clientHelloExtension {
    Cons? l1 /\
    CHE.CHE_pre_shared_key? (L.last l1) /\
    CHEs.clientHelloExtensions_list_bytesize l1 <= 65535
  })
  (l2: list CHE.clientHelloExtension {
    Cons? l2 /\
    CHE.CHE_pre_shared_key? (L.last l2) /\
    CHEs.clientHelloExtensions_list_bytesize l2 <= 65535
  })
: Lemma
  (requires (truncate_list_clientHelloExtension l1 == truncate_list_clientHelloExtension l2))
  (ensures (
    Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l1)).Psks.binders == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l2)).Psks.binders
  ))
= truncate_list_clientHelloExtension_eq_left l1;
  truncate_list_clientHelloExtension_eq_left l2;
  parse_truncate_clientHelloExtension (L.last l1);
  parse_truncate_clientHelloExtension (L.last l2);
  serialize_list_clientHelloExtension_inj_prefix (L.init l1) (L.init l2) (truncate_clientHelloExtension (L.last l1)) (truncate_clientHelloExtension (L.last l2));
  truncate_clientHelloExtension_inj_binders_bytesize (L.last l1) (L.last l2)

let clientHelloExtensions_binders_offset
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Tot (x: U32.t { U32.v x < Seq.length (LP.serialize CHEs.clientHelloExtensions_serializer l) })
= serialize_clientHelloExtensions_eq l;
  clientHelloExtensions_list_bytesize_eq' l;
  2ul `U32.add` list_clientHelloExtension_binders_offset l

inline_for_extraction
let clientHelloExtensions_binders_pos
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (x: Ghost.erased CHEs.clientHelloExtensions {
    Cons? (Ghost.reveal x) /\
    CHE.CHE_pre_shared_key? (L.last (Ghost.reveal x))
  } )
: HST.Stack U32.t
  (requires (fun h -> 
    let sq = LP.serialize CHEs.clientHelloExtensions_serializer (Ghost.reveal x) in
    LP.live_slice h sl /\
    U32.v pos <= U32.v sl.LP.len /\
    (LP.bytes_of_slice_from h sl pos `LP.seq_starts_with` sq)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + U32.v (clientHelloExtensions_binders_offset (Ghost.reveal x)) == U32.v res
  ))
= serialize_clientHelloExtensions_eq (Ghost.reveal x);
  let h = HST.get () in
  let pos' = LP.jump_serializer CHEs.clientHelloExtensions_serializer CHEs.clientHelloExtensions_jumper sl pos x in
  let pos1 = LP.jump_serializer (LI.serialize_bounded_integer 2) (LP.jump_constant_size (LI.parse_bounded_integer 2) 2ul ()) sl pos (Ghost.hide (U32.uint_to_t
   (CHEs.clientHelloExtensions_list_bytesize (Ghost.reveal x)))) in
  list_clientHelloExtension_binders_pos sl pos1 pos' (Ghost.hide (Ghost.reveal x))

let truncate_clientHelloExtensions
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: GTot LP.bytes
= Seq.slice (LP.serialize CHEs.clientHelloExtensions_serializer l) 0 (U32.v (clientHelloExtensions_binders_offset l))

let clientHelloExtensions_set_binders
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders
  })
: Tot (l' : CHEs.clientHelloExtensions {
    Cons? l' /\ (
    let e = L.last l in
    let e' = L.last l' in
    L.init l' = L.init l /\
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    CHEs.clientHelloExtensions_bytesize l' == CHEs.clientHelloExtensions_bytesize l
  )})
= list_clientHelloExtension_set_binders l b'

let binders_offset_clientHelloExtensions_set_binders
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders})
: Lemma
  (let l' = clientHelloExtensions_set_binders l b' in
  let off = clientHelloExtensions_binders_offset l in
  let tr = truncate_clientHelloExtensions l in
  clientHelloExtensions_binders_offset l' == off /\
  truncate_clientHelloExtensions l' `Seq.equal` tr /\
  LP.serialize CHEs.clientHelloExtensions_serializer l' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let l' = clientHelloExtensions_set_binders l b' in
  serialize_clientHelloExtensions_eq l;
  serialize_clientHelloExtensions_eq l';
  binders_offset_list_clientHelloExtension_set_binders l b'

let truncate_clientHelloExtensions_eq_left
  (l: CHEs.clientHelloExtensions {
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Lemma
  (truncate_clientHelloExtensions l `Seq.equal` (LP.serialize (LI.serialize_bounded_integer 2) (U32.uint_to_t (CHEs.clientHelloExtensions_list_bytesize l)) `Seq.append` truncate_list_clientHelloExtension l))
= serialize_clientHelloExtensions_eq l

let truncate_clientHelloExtensions_inj_binders_bytesize
  (l1: CHEs.clientHelloExtensions {
    Cons? l1 /\
    CHE.CHE_pre_shared_key? (L.last l1)
  })
  (l2: CHEs.clientHelloExtensions {
    Cons? l2 /\
    CHE.CHE_pre_shared_key? (L.last l2)
  })
: Lemma
  (requires (truncate_clientHelloExtensions l1 == truncate_clientHelloExtensions l2))
  (ensures (
    Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l1)).Psks.binders == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l2)).Psks.binders
  ))
= truncate_clientHelloExtensions_eq_left l1;
  truncate_clientHelloExtensions_eq_left l2;
  LP.serialize_strong_prefix (LI.serialize_bounded_integer 2) (U32.uint_to_t (CHEs.clientHelloExtensions_list_bytesize l1)) (U32.uint_to_t (CHEs.clientHelloExtensions_list_bytesize l2)) (truncate_list_clientHelloExtension l1) (truncate_list_clientHelloExtension l2);
  truncate_list_clientHelloExtension_inj_binders_bytesize l1 l2

let clientHello_binders_offset
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Tot (x: U32.t { U32.v x < Seq.length (LP.serialize CH.clientHello_serializer c) })
= serialize_clientHello_eq c;
  Parsers.ProtocolVersion.protocolVersion_size32 c.CH.version `U32.add`
  Parsers.Random.random_size32 c.CH.random `U32.add`
  Parsers.SessionID.sessionID_size32 c.CH.session_id `U32.add`
  Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_size32 c.CH.cipher_suites `U32.add` Parsers.ClientHello_compression_methods.clientHello_compression_methods_size32 c.CH.compression_methods `U32.add`
  clientHelloExtensions_binders_offset c.CH.extensions

#push-options "--z3rlimit 32 --max_fuel 1 --max_ifuel 0"

inline_for_extraction
let clientHello_binders_pos
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (x: Ghost.erased CH.clientHello {
    let l = (Ghost.reveal x).CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  } )
: HST.Stack U32.t
  (requires (fun h -> 
    let sq = LP.serialize CH.clientHello_serializer (Ghost.reveal x) in
    LP.live_slice h sl /\
    U32.v pos <= U32.v sl.LP.len /\
    (LP.bytes_of_slice_from h sl pos `LP.seq_starts_with` sq)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + U32.v (clientHello_binders_offset (Ghost.reveal x)) == U32.v res
  ))
= serialize_clientHello_eq (Ghost.reveal x);
  let pos1 = LP.jump_serializer Parsers.ProtocolVersion.protocolVersion_serializer  Parsers.ProtocolVersion.protocolVersion_jumper sl pos (Ghost.hide (Ghost.reveal x).CH.version) in
  let pos2 = LP.jump_serializer Parsers.Random.random_serializer Parsers.Random.random_jumper sl pos1 (Ghost.hide (Ghost.reveal x).CH.random) in
  let pos3 = LP.jump_serializer Parsers.SessionID.sessionID_serializer Parsers.SessionID.sessionID_jumper sl pos2 (Ghost.hide (Ghost.reveal x).CH.session_id) in
  let pos4 = LP.jump_serializer CH.clientHello_cipher_suites_serializer CH.clientHello_cipher_suites_jumper sl pos3 (Ghost.hide (Ghost.reveal x).CH.cipher_suites) in
  let pos5 = LP.jump_serializer CH.clientHello_compression_methods_serializer CH.clientHello_compression_methods_jumper sl pos4 (Ghost.hide (Ghost.reveal x).CH.compression_methods) in
  clientHelloExtensions_binders_pos sl pos5 (Ghost.hide (Ghost.reveal x).CH.extensions)

#pop-options

let truncate_clientHello
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: GTot LP.bytes
= Seq.slice (LP.serialize CH.clientHello_serializer c) 0 (U32.v (clientHello_binders_offset c))

let clientHello_set_binders
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    let l = c.CH.extensions in
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders
  })
: Tot (c' : CH.clientHello {
    let l' = c'.CH.extensions in
    c'.CH.version == c.CH.version /\
    c'.CH.random == c.CH.random /\
    c'.CH.session_id == c.CH.session_id /\
    c'.CH.cipher_suites == c.CH.cipher_suites /\
    c'.CH.compression_methods == c.CH.compression_methods /\
    Cons? l' /\ (
    let l = c.CH.extensions in
    let e = L.last l in
    let e' = L.last l' in
    L.init l' = L.init l /\
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    CH.clientHello_bytesize c' == CH.clientHello_bytesize c
  )})
= {
    CH.version = c.CH.version;
    CH.random = c.CH.random;
    CH.session_id = c.CH.session_id;
    CH.cipher_suites = c.CH.cipher_suites;
    CH.compression_methods = c.CH.compression_methods;
    CH.extensions = clientHelloExtensions_set_binders c.CH.extensions b'
  }

#push-options "--z3rlimit 16"

let binders_offset_clientHello_set_binders
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    let l = c.CH.extensions in
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders})
: Lemma
  (let c' = clientHello_set_binders c b' in
  let off = clientHello_binders_offset c in
  let tr = truncate_clientHello c in
  clientHello_binders_offset c' == off /\
  truncate_clientHello c' `Seq.equal` tr /\
  LP.serialize CH.clientHello_serializer c' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let c' = clientHello_set_binders c b' in
  serialize_clientHello_eq c;
  serialize_clientHello_eq c';
  binders_offset_clientHelloExtensions_set_binders c.CH.extensions b'

let truncate_clientHello_eq_left
  (c: CH.clientHello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Lemma
  (truncate_clientHello c `Seq.equal` (
   LP.serialize Parsers.ProtocolVersion.protocolVersion_serializer c.CH.version `Seq.append` (
   LP.serialize Parsers.Random.random_serializer c.CH.random `Seq.append` (
   LP.serialize Parsers.SessionID.sessionID_serializer c.CH.session_id `Seq.append` (
   LP.serialize Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_serializer c.CH.cipher_suites  `Seq.append` (
   LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c.CH.compression_methods `Seq.append` (
   truncate_clientHelloExtensions c.CH.extensions
  )))))))
= serialize_clientHello_eq c

#pop-options

let truncate_clientHello_inj_binders_bytesize
  (c1: CH.clientHello {
    let l = c1.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (c2: CH.clientHello {
    let l = c2.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Lemma
  (requires (truncate_clientHello c1 == truncate_clientHello c2))
  (ensures (
    let l1 = c1.CH.extensions in
    let l2 = c2.CH.extensions in
    Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l1)).Psks.binders == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l2)).Psks.binders
  ))
= truncate_clientHello_eq_left c1;
  truncate_clientHello_eq_left c2;
  LP.serialize_strong_prefix Parsers.ProtocolVersion.protocolVersion_serializer c1.CH.version c2.CH.version
    (LP.serialize Parsers.Random.random_serializer c1.CH.random `Seq.append` (
      LP.serialize Parsers.SessionID.sessionID_serializer c1.CH.session_id `Seq.append` (
      LP.serialize Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_serializer c1.CH.cipher_suites  `Seq.append` (
      LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c1.CH.compression_methods `Seq.append` (
   truncate_clientHelloExtensions c1.CH.extensions
     )))))
     (LP.serialize Parsers.Random.random_serializer c2.CH.random `Seq.append` (
       LP.serialize Parsers.SessionID.sessionID_serializer c2.CH.session_id `Seq.append` (
       LP.serialize Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_serializer c2.CH.cipher_suites  `Seq.append` (
       LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c2.CH.compression_methods `Seq.append` (
       truncate_clientHelloExtensions c2.CH.extensions
   )))));
  LP.serialize_strong_prefix Parsers.Random.random_serializer c1.CH.random c2.CH.random
     (LP.serialize Parsers.SessionID.sessionID_serializer c1.CH.session_id `Seq.append` (
      LP.serialize Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_serializer c1.CH.cipher_suites  `Seq.append` (
      LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c1.CH.compression_methods `Seq.append` (
   truncate_clientHelloExtensions c1.CH.extensions
     ))))
     (LP.serialize Parsers.SessionID.sessionID_serializer c2.CH.session_id `Seq.append` (
       LP.serialize Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_serializer c2.CH.cipher_suites  `Seq.append` (
       LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c2.CH.compression_methods `Seq.append` (
       truncate_clientHelloExtensions c2.CH.extensions
   ))));
  LP.serialize_strong_prefix Parsers.SessionID.sessionID_serializer c1.CH.session_id c2.CH.session_id
     (LP.serialize Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_serializer c1.CH.cipher_suites  `Seq.append` (
      LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c1.CH.compression_methods `Seq.append` (
   truncate_clientHelloExtensions c1.CH.extensions
     )))
     (LP.serialize Parsers.ClientHello_cipher_suites.clientHello_cipher_suites_serializer c2.CH.cipher_suites  `Seq.append` (
       LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c2.CH.compression_methods `Seq.append` (
       truncate_clientHelloExtensions c2.CH.extensions
   )));
  LP.serialize_strong_prefix CH.clientHello_cipher_suites_serializer c1.CH.cipher_suites c2.CH.cipher_suites
     (LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c1.CH.compression_methods `Seq.append` (
   truncate_clientHelloExtensions c1.CH.extensions
     ))
     (LP.serialize Parsers.ClientHello_compression_methods.clientHello_compression_methods_serializer c2.CH.compression_methods `Seq.append` (
       truncate_clientHelloExtensions c2.CH.extensions
   ));
  LP.serialize_strong_prefix CH.clientHello_compression_methods_serializer c1.CH.compression_methods c2.CH.compression_methods
    (truncate_clientHelloExtensions c1.CH.extensions)
    (truncate_clientHelloExtensions c2.CH.extensions)
  ;
  truncate_clientHelloExtensions_inj_binders_bytesize c1.CH.extensions c2.CH.extensions

#push-options "--max_fuel 1 --max_ifuel 0"
let handshake_m_client_hello_binders_offset
  (c: H.handshake_m_client_hello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Tot (x: U32.t { U32.v x < Seq.length (LP.serialize H.handshake_m_client_hello_serializer c) })
= serialize_handshake_m_client_hello_eq c;
  3ul `U32.add` clientHello_binders_offset c
#pop-options

inline_for_extraction
let handshake_m_client_hello_binders_pos
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
  (c: Ghost.erased H.handshake_m_client_hello {
    let l = (Ghost.reveal c).CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: HST.Stack U32.t
  (requires (fun h -> 
    let sq = LP.serialize H.handshake_m_client_hello_serializer (Ghost.reveal c) in
    LP.live_slice h sl /\
    U32.v pos <= U32.v sl.LP.len /\
    (LP.bytes_of_slice_from h sl pos `LP.seq_starts_with` sq)
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    U32.v pos + U32.v (handshake_m_client_hello_binders_offset (Ghost.reveal c)) == U32.v res
  ))
= serialize_handshake_m_client_hello_eq (Ghost.reveal c);
  let pos1 = LP.jump_serializer (LI.serialize_bounded_integer 3) (LP.jump_constant_size (LI.parse_bounded_integer 3) 3ul ()) sl pos (Ghost.hide (U32.uint_to_t
   (CH.clientHello_bytesize (Ghost.reveal c)))) in
  clientHello_binders_pos sl pos1 (Ghost.hide (Ghost.reveal c))

let truncate_handshake_m_client_hello
  (c: H.handshake_m_client_hello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: GTot LP.bytes
= Seq.slice (LP.serialize H.handshake_m_client_hello_serializer c) 0 (U32.v (handshake_m_client_hello_binders_offset c))

let handshake_m_client_hello_set_binders
  (c: H.handshake_m_client_hello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    let l = c.CH.extensions in
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders
  })
: Tot (c' : H.handshake_m_client_hello {
    let l' = c'.CH.extensions in
    c'.CH.version == c.CH.version /\
    c'.CH.random == c.CH.random /\
    c'.CH.session_id == c.CH.session_id /\
    c'.CH.cipher_suites == c.CH.cipher_suites /\
    c'.CH.compression_methods == c.CH.compression_methods /\
    Cons? l' /\ (
    let l = c.CH.extensions in
    let e = L.last l in
    let e' = L.last l' in
    L.init l' = L.init l /\
    CHE.CHE_pre_shared_key? e' /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.identities == (CHE.CHE_pre_shared_key?._0 e).Psks.identities /\
    (CHE.CHE_pre_shared_key?._0 e').Psks.binders == b' /\
    H.handshake_m_client_hello_bytesize c' == H.handshake_m_client_hello_bytesize c
  )})
= clientHello_set_binders c b'

#push-options "--z3rlimit 16"

let binders_offset_handshake_m_client_hello_set_binders
  (c: H.handshake_m_client_hello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (b' : Psks.offeredPsks_binders {
    let l = c.CH.extensions in
    Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l)).Psks.binders})
: Lemma
  (let c' = handshake_m_client_hello_set_binders c b' in
  let off = handshake_m_client_hello_binders_offset c in
  let tr = truncate_handshake_m_client_hello c in
  handshake_m_client_hello_binders_offset c' == off /\
  truncate_handshake_m_client_hello c' `Seq.equal` tr /\
  LP.serialize H.handshake_m_client_hello_serializer c' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let c' = handshake_m_client_hello_set_binders c b' in
  serialize_handshake_m_client_hello_eq c;
  serialize_handshake_m_client_hello_eq c';
  binders_offset_clientHello_set_binders c b'

let truncate_handshake_m_client_hello_eq_left
  (c: H.handshake_m_client_hello {
    let l = c.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Lemma
  (truncate_handshake_m_client_hello c `Seq.equal` (
    LP.serialize (LI.serialize_bounded_integer 3) (U32.uint_to_t (CH.clientHello_bytesize c)) `Seq.append` (truncate_clientHello c)
  ))
= serialize_handshake_m_client_hello_eq c

let truncate_handshake_m_client_hello_inj_binders_bytesize
  (c1: H.handshake_m_client_hello {
    let l = c1.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
  (c2: H.handshake_m_client_hello {
    let l = c2.CH.extensions in
    Cons? l /\
    CHE.CHE_pre_shared_key? (L.last l)
  })
: Lemma
  (requires (truncate_handshake_m_client_hello c1 == truncate_handshake_m_client_hello c2))
  (ensures (
    let l1 = c1.CH.extensions in
    let l2 = c2.CH.extensions in
    Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l1)).Psks.binders == Psks.offeredPsks_binders_bytesize (CHE.CHE_pre_shared_key?._0 (L.last l2)).Psks.binders
  ))
= truncate_handshake_m_client_hello_eq_left c1;
  truncate_handshake_m_client_hello_eq_left c2;
  LP.serialize_strong_prefix (LI.serialize_bounded_integer 3) (U32.uint_to_t (CH.clientHello_bytesize c1)) (U32.uint_to_t (CH.clientHello_bytesize c2)) (truncate_clientHello c1) (truncate_clientHello c2);
  truncate_clientHello_inj_binders_bytesize c1 c2

let set_binders m b' =
  let c = H.M_client_hello?._0 m in
  H.M_client_hello (handshake_m_client_hello_set_binders c b')

let set_binders_bytesize m b' = ()

let binders_offset h =
  H.handshake_bytesize_eq h;
  H.serialize_handshake_eq_client_hello h;
  1ul `U32.add` handshake_m_client_hello_binders_offset (H.M_client_hello?._0 h)

let truncate_handshake
  (h: H.handshake {has_binders h})
: GTot LP.bytes
= Seq.slice (LP.serialize H.handshake_serializer h) 0 (U32.v (binders_offset h))

#push-options "--z3rlimit 16"

let binders_offset_handshake_set_binders
  (h: H.handshake {has_binders h})
  (b' : Psks.offeredPsks_binders { Psks.offeredPsks_binders_bytesize b' == Psks.offeredPsks_binders_bytesize (get_binders h)})
: Lemma
  (let h' = set_binders h b' in
  let off = binders_offset h in
  let tr = truncate_handshake h in
  binders_offset h' == off /\
  truncate_handshake h' `Seq.equal` tr /\
  LP.serialize H.handshake_serializer h' `Seq.equal`
  (tr `Seq.append` LP.serialize Psks.offeredPsks_binders_serializer b'))
= let h' = set_binders h b' in
  let off = binders_offset h in
  H.serialize_handshake_eq_client_hello h;
  H.serialize_handshake_eq_client_hello h';
  binders_offset_handshake_m_client_hello_set_binders (H.M_client_hello?._0 h) b'

#pop-options

let binders_offset_set_binder m b' = binders_offset_handshake_set_binders m b'

let parse_truncate_clientHello_bytes
  m
= LP.parse_truncate H.handshake_serializer m (U32.v (binders_offset m))

let truncate_clientHello_bytes_correct m =
  set_binders_get_binders m;
  binders_offset_handshake_set_binders m (get_binders m)

let truncate_clientHello_bytes_set_binders m b' = binders_offset_handshake_set_binders m b'

#set-options "--z3rlimit 16"

let truncate_handshake_eq_left
  (c: H.handshake { has_binders c })
: Lemma
  (truncate_handshake c `Seq.equal` (
    LP.serialize HT.handshakeType_serializer HT.Client_hello `Seq.append`
    truncate_handshake_m_client_hello (H.M_client_hello?._0 c)
  ))
= H.serialize_handshake_eq_client_hello c

let truncate_clientHello_bytes_inj_binders_bytesize m1 m2 =
  truncate_handshake_eq_left m1;
  truncate_handshake_eq_left m2;
  LP.serialize_strong_prefix HT.handshakeType_serializer HT.Client_hello HT.Client_hello (truncate_handshake_m_client_hello (H.M_client_hello?._0 m1)) (truncate_handshake_m_client_hello (H.M_client_hello?._0 m2));
  truncate_handshake_m_client_hello_inj_binders_bytesize (H.M_client_hello?._0 m1) (H.M_client_hello?._0 m2)

let binders_pos #rrel #rel sl pos =
  let h = HST.get () in
  let x = Ghost.hide (LP.contents H.handshake_parser h sl pos) in
  let gpos' = Ghost.hide (LP.get_valid_pos H.handshake_parser h sl pos) in 
  LP.valid_valid_exact H.handshake_parser h sl pos;
  LP.valid_exact_serialize H.handshake_serializer h sl pos (Ghost.reveal gpos');
  H.serialize_handshake_eq_client_hello (Ghost.reveal x);
  assert (LP.bytes_of_slice_from h sl pos `LP.seq_starts_with` LP.bytes_of_slice_from_to h sl pos (Ghost.reveal gpos'));
  let pos1 = LP.jump_serializer HT.handshakeType_serializer HT.handshakeType_jumper sl pos (Ghost.hide HT.Client_hello) in
  let res = handshake_m_client_hello_binders_pos sl pos1 (Ghost.hide (H.M_client_hello?._0 (Ghost.reveal x))) in
  set_binders_get_binders (Ghost.reveal x);
  truncate_clientHello_bytes_correct (Ghost.reveal x);
  LP.serialize_valid_exact Psks.offeredPsks_binders_serializer h sl (get_binders (Ghost.reveal x)) res (Ghost.reveal gpos');
  LP.valid_exact_valid Psks.offeredPsks_binders_parser h sl res (Ghost.reveal gpos');
  res

let rec build_canonical_list_binders (len: U32.t) (accu: list Parsers.PskBinderEntry.pskBinderEntry) : Pure (list Parsers.PskBinderEntry.pskBinderEntry)
  (requires (
    33 <= U32.v len /\
    U32.v len + Psks.offeredPsks_binders_list_bytesize accu <= 65535
  ))
  (ensures (fun y -> Psks.offeredPsks_binders_list_bytesize y == Psks.offeredPsks_binders_list_bytesize accu + U32.v len))
  (decreases (U32.v len))
= if len `U32.lt` 255ul
  then
    let binder : Parsers.PskBinderEntry.pskBinderEntry = FStar.Bytes.create (len `U32.sub` 1ul) 0uy in
    binder :: accu
  else
    let binder : Parsers.PskBinderEntry.pskBinderEntry = FStar.Bytes.create 221ul 0uy in
    build_canonical_list_binders (len `U32.sub` 222ul) (binder :: accu)

let build_canonical_binders len = build_canonical_list_binders (len `U32.sub` 2ul) []
