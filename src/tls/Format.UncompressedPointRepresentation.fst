module Format.UncompressedPointRepresentation

open Format.Constants

module B = FStar.Bytes
module U32 = FStar.UInt32
module LP = LowParse.SLow

unfold type is_injective (#a:Type) (#b:Type) (f:a -> b) 
  = forall x y . f x == f y ==> x == y
 
unfold type is_injective_2 (#a:Type) (#b:Type) (f:a -> b) (x:a) (y:a)
  = f x == f y ==> x == y

(* Types *)

private 
type lbytes_pair (coordinate_length:coordinate_length_type) 
  = B.lbytes32 coordinate_length * B.lbytes32 coordinate_length
  // = (p:(B.lbytes32 coordinate_length * B.lbytes32 coordinate_length)
  //       {U32.(coordinate_length +^ coordinate_length <^ 512ul) /\
  //       U32.v coordinate_length + U32.v coordinate_length < 512 /\
  //       B.length (fst p) + B.length (snd p) < pow2 32 /\
  //       UInt.fits (B.length (fst p) + B.length (snd p)) 32})


(* Parsers *)

private
let lbytes_pair_parser_kind (coordinate_length:coordinate_length_type)
  : LP.parser_kind
  = let l = (UInt32.v coordinate_length) in
    LP.and_then_kind 
      (LP.total_constant_size_parser_kind l)
      (LP.total_constant_size_parser_kind l)

let lbytes_pair_parser (coordinate_length:coordinate_length_type)
  : LP.parser (lbytes_pair_parser_kind coordinate_length) (lbytes_pair coordinate_length)
  = let l = U32.v coordinate_length in
    LP.nondep_then
      (LP.parse_flbytes l)
      (LP.parse_flbytes l)

#reset-options "--using_facts_from '* -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
private
inline_for_extraction
let lbytes_pair_parser32 (coordinate_length:coordinate_length_type)
  : LP.parser32 (lbytes_pair_parser coordinate_length) 
  = let l = UInt32.v coordinate_length in
    LP.parse32_nondep_then
      (LP.parse32_flbytes l coordinate_length)
      (LP.parse32_flbytes l coordinate_length)
#reset-options

let uncompressedPointRepresentation_parser_kind (coordinate_length:coordinate_length_type) 
  = LP.and_then_kind
      constantByte_parser_kind
      (lbytes_pair_parser_kind coordinate_length)

private
inline_for_extraction
let ucp_of_uv (#n:coordinate_length_type) (p:(B.lbytes32 n) * (B.lbytes32 n))
  : uncompressedPointRepresentation n
  = { legacy_form = 4uy; x = (fst p); y = (snd p) }

private
inline_for_extraction
let uv_of_ucp (#n:coordinate_length_type) (x:uncompressedPointRepresentation n)
  : Tot (B.lbytes32 n * B.lbytes32  n)
  = (x.x, x.y)

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_ucp_of_uv_is_injective #l
  : Lemma (is_injective (ucp_of_uv #l))
  = ()

let lemma_ucp_of_uv_of_ucp #l 
  : Lemma (forall x . ucp_of_uv #l (uv_of_ucp #l x) == x)
  = lemma_ucp_of_uv_is_injective #l
#reset-options

let ucp_of_cuv #l (cuv:constantByte 4uy * lbytes_pair l): Tot (ucp:uncompressedPointRepresentation l) = let c, uv = cuv in ucp_of_uv uv
let cuv_of_ucp #l (ucp:uncompressedPointRepresentation l): Tot (cuv:constantByte 4uy * lbytes_pair l) = 4uy, (ucp.x, ucp.y)

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_ucp_of_cuv_is_injective #l
  : Lemma (is_injective (ucp_of_cuv #l))
  = ()

let lemma_ucp_of_cuv_of_ucp #l 
  : Lemma (forall x . ucp_of_cuv #l (cuv_of_ucp #l x) == x)
  = lemma_ucp_of_cuv_is_injective #l
#reset-options


let uncompressedPointRepresentation_parser (coordinate_length:coordinate_length_type)
  : LP.parser (uncompressedPointRepresentation_parser_kind coordinate_length) (uncompressedPointRepresentation coordinate_length) 
  = LP.parse_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      ucp_of_cuv

inline_for_extraction
let uncompressedPointRepresentation_parser32 (coordinate_length:coordinate_length_type)
  : LP.parser32 (uncompressedPointRepresentation_parser coordinate_length)
  = LP.parse32_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      ucp_of_cuv
      (fun x -> ucp_of_cuv x)
      (LP.parse32_nondep_then (constantByte_parser32 4uy) (lbytes_pair_parser32 coordinate_length))
      ()


(* Serializers *)

#reset-options "--using_facts_from '* -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16 --z3rlimit 10"
private
let lbytes_pair_serializer (coordinate_length:coordinate_length_type)
  : LP.serializer (lbytes_pair_parser coordinate_length) 
  = let l = U32.v coordinate_length in
    let p = LP.parse_flbytes l in
    let s = LP.serialize_flbytes l in
    LP.serialize_nondep_then p s () p s

#reset-options "--using_facts_from '* -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16 --z3rlimit 10"
private
inline_for_extraction
let lbytes_pair_serializer32 (coordinate_length:coordinate_length_type)
  : LP.serializer32 (lbytes_pair_serializer coordinate_length) 
  = let l = U32.v coordinate_length in
    LP.serialize32_nondep_then
      (LP.serialize32_flbytes l) ()
      (LP.serialize32_flbytes l) ()
#reset-options

#reset-options "--using_facts_from '* -FStar.Reflection -FStar.Tactics'"
let uncompressedPointRepresentation_serializer (coordinate_length:coordinate_length_type) 
  : LP.serializer (uncompressedPointRepresentation_parser coordinate_length)
  = let l = coordinate_length in
    lemma_ucp_of_cuv_is_injective #l;
    lemma_ucp_of_cuv_of_ucp #l;
    LP.serialize_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser l))
      ucp_of_cuv
      (LP.serialize_nondep_then 
        (constantByte_parser 4uy)
        (constantByte_serializer 4uy) 
        ()
        (lbytes_pair_parser l)
        (lbytes_pair_serializer l))
      cuv_of_ucp
      ()

inline_for_extraction
let uncompressedPointRepresentation_serializer32 (coordinate_length:coordinate_length_type) 
  : LP.serializer32 (uncompressedPointRepresentation_serializer coordinate_length)
  = let l = coordinate_length in
    lemma_ucp_of_cuv_is_injective #l;
    lemma_ucp_of_cuv_of_ucp #l;
    LP.serialize32_synth 
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser l))      
      ucp_of_cuv
      (LP.serialize_nondep_then (constantByte_parser 4uy) (constantByte_serializer 4uy) ()
                                (lbytes_pair_parser l) (lbytes_pair_serializer l))
      (LP.serialize32_nondep_then (constantByte_serializer32 4uy) ()
                                  (lbytes_pair_serializer32 l) ())
      cuv_of_ucp
      (fun x -> cuv_of_ucp x)
      ()
#reset-options
