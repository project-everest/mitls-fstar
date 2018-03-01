module Format.NamedGroupList

open Format.NamedGroup

module LP = LowParse.SLow
module L = FStar.List.Tot


let bytesize (gs:namedGroupList): Tot nat = 2 + (op_Multiply Format.NamedGroup.bytesize (L.length gs))

private
let nglist_serializer = LP.serialize_list _ namedGroup_serializer

inline_for_extraction
let synth_namedGroupList
  (l:LP.parse_bounded_vldata_strong_t 2 65535 nglist_serializer)
  : Tot (l:namedGroupList)
  = [@inline_let]
    let l' : list namedGroup = l in
    [@inline_let]
    let _ = assume (1 <= L.length l' /\ L.length l' <= 32767) in
    l'

inline_for_extraction
let synth_namedGroupList_recip
  (l:namedGroupList)
  : Tot (l:LP.parse_bounded_vldata_strong_t 2 65535 nglist_serializer)
  = [@inline_let]
    let l' : list namedGroup = l in
    [@inline_let]
    let _ = assume (LP.parse_bounded_vldata_strong_pred 2 65535 nglist_serializer l') in
    l'

(* Parsers *)

inline_for_extraction
let namedGroupList_parser_kind' = LP.parse_bounded_vldata_kind 2 65535

let namedGroupList_parser_kind_metadata = namedGroupList_parser_kind'.LP.parser_kind_metadata

let namedGroupList_parser =
  assert_norm (namedGroupList_parser_kind' == namedGroupList_parser_kind);
  LP.parse_synth
    (LP.parse_bounded_vldata_strong 2 65535 nglist_serializer)
    synth_namedGroupList

inline_for_extraction
let namedGroupList_parser32: LP.parser32 namedGroupList_parser =
  assert_norm (namedGroupList_parser_kind' == namedGroupList_parser_kind);
  LP.parse32_synth
    _
    synth_namedGroupList
    (fun x -> synth_namedGroupList x)
    (LP.parse32_bounded_vldata_strong 2 2ul 65535 65535ul nglist_serializer (LP.parse32_list namedGroup_parser32))
    ()


(* Serialization *) 

let namedGroupList_serializer: LP.serializer namedGroupList_parser =
  assert_norm (namedGroupList_parser_kind' == namedGroupList_parser_kind);
  LP.serialize_synth
    _
    synth_namedGroupList
    (LP.serialize_bounded_vldata_strong 2 65535 (LP.serialize_list namedGroup_parser namedGroup_serializer))
    synth_namedGroupList_recip
    ()

inline_for_extraction
let namedGroupList_serializer32: LP.serializer32 namedGroupList_serializer =
  assert_norm (namedGroupList_parser_kind' == namedGroupList_parser_kind);
  LP.serialize32_synth
    _
    synth_namedGroupList
    _
    (LP.serialize32_bounded_vldata_strong 2 65535
      (LP.partial_serialize32_list _ namedGroup_serializer namedGroup_serializer32 ()))
    synth_namedGroupList_recip
    (fun x -> synth_namedGroupList_recip x)
    ()
