module Format.NamedGroupList

open Format.NamedGroup

module LP = LowParse.SLow.Base
module L = FStar.List.Tot


(* Types *) 

(* https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.2.7

    struct {
        NamedGroup namedGroup_list<2..2^16-1>;
    } NamedGroupList;
           
*)

type namedGroupList = l:list namedGroup {1 <= L.length l && L.length l <= 32767}

val bytesize (gs:namedGroupList): Tot nat

(* Parsers *)

let lenLength = 2
let minLength = 4     //QD eval of 2 + 2
let maxLength = 65537 //QD eval of 2 + 2^16 - 1 
let minCount = 1      //QD eval of  2 / NamedGroup.maxLength 
let maxCount = 32767  //QD eval of 65535 / NamedGroup.minLength 

type namedGroupList = l:list namedGroup {minCount <= L.length l && L.length l <= maxCount}

inline_for_extraction
val namedGroupList_parser_kind_metadata: LP.parser_kind_metadata_t

inline_for_extraction
let namedGroupList_parser_kind =
  LP.strong_parser_kind minLength maxLength namedGroupList_parser_kind_metadata

val namedGroupList_parser: LP.parser namedGroupList_parser_kind namedGroupList

inline_for_extraction
val namedGroupList_parser32: LP.parser32 namedGroupList_parser 


(* Serialization *) 

val namedGroupList_serializer: LP.serializer namedGroupList_parser 

inline_for_extraction
val namedGroupList_serializer32: LP.serializer32 namedGroupList_serializer
