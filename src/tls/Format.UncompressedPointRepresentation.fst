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
#reset-options

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16 --z3rlimit 10"
let lemma_ucp_of_uv_of_ucp #l 
  : Lemma (forall x . ucp_of_uv #l (uv_of_ucp #l x) == x)
  = lemma_ucp_of_uv_is_injective #l
#reset-options


let uncompressedPointRepresentation_parser (coordinate_length:coordinate_length_type)
  : LP.parser (uncompressedPointRepresentation_parser_kind coordinate_length) (uncompressedPointRepresentation coordinate_length) 
  = LP.parse_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      (fun (c, uv) -> ucp_of_uv uv)

inline_for_extraction
let uncompressedPointRepresentation_parser32 (coordinate_length:coordinate_length_type)
  : LP.parser32 (uncompressedPointRepresentation_parser coordinate_length)
  = LP.parse32_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      (fun (c, uv) -> ucp_of_uv uv)
      (fun (c, uv) -> ucp_of_uv uv)
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


let uncompressedPointRepresentation_serializer (coordinate_length:coordinate_length_type) 
  : LP.serializer (uncompressedPointRepresentation_parser coordinate_length)
  = lemma_ucp_of_uv_is_injective #coordinate_length;
    lemma_ucp_of_uv_of_ucp #coordinate_length;
    let l = U32.v coordinate_length in
    LP.serialize_synth
      (LP.nondep_then (constantByte_parser 4uy) (lbytes_pair_parser coordinate_length))
      (fun (c, uv) -> ucp_of_uv uv)
      (LP.serialize_nondep_then 
        (constantByte_parser 4uy)
        (constantByte_serializer 4uy) 
        ()
        (lbytes_pair_parser coordinate_length)
        (lbytes_pair_serializer coordinate_length))
      (fun ucp -> (ucp.legacy_form, (ucp.x, ucp.y)))
      ()

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16 --z3rlimit 10"
inline_for_extraction
let uncompressedPointRepresentation_serializer32 (coordinate_length:coordinate_length_type) 
  : LP.serializer32 (uncompressedPointRepresentation_serializer coordinate_length)
  = lemma_ucp_of_uv_is_injective #coordinate_length;
    lemma_ucp_of_uv_of_ucp #coordinate_length;
    lemma_constantByte_parser_is_strong 4uy;
    assert (LP.is_strong (constantByte_parser 4uy));
    assert (constantByte_parser_kind.LP.parser_kind_subkind == Some (LowParse.Spec.Base.ParserStrong));
    assert (Some? constantByte_parser_kind.LP.parser_kind_high); // cwinter: taramana, why can't it prove the following 2 assertions?
    assert (Some? (lbytes_pair_parser_kind coordinate_length).LP.parser_kind_high);
    match constantByte_parser_kind.LP.parser_kind_high, (lbytes_pair_parser_kind coordinate_length).LP.parser_kind_high with 
    | Some x, Some y -> assert (x + y < 4294967296);
    assert (LowParse.SLow.Combinators.serialize32_kind_precond constantByte_parser_kind (lbytes_pair_parser_kind coordinate_length));
    LP.serialize32_synth
      _
      (fun (c, uv) -> ucp_of_uv uv)
      _
      (LP.serialize32_nondep_then 
        (constantByte_serializer32 4uy) ()
        (lbytes_pair_serializer32 coordinate_length) ())
      (fun x -> 4uy, uv_of_ucp x)
      (fun x -> 4uy, uv_of_ucp x)
      ()
#reset-options
