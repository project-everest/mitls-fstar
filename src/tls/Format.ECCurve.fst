module Format.ECCurve

module B = FStar.Bytes
module LP = LowParse.SLow
module U8 = FStar.UInt8
module U16 = FStar.UInt16

open Format.LBytes1


(* Types *)

(*
    https://tools.ietf.org/html/rfc4492#section-5.4

    struct {
        opaque a <1..2^8-1>;
        opaque b <1..2^8-1>;
    } ECCurve;

*)


(* Parsers *)

private
inline_for_extraction
let ecCurve_of_lbytes (bs:lbytes_1 * lbytes_1)
  : Tot ecCurve
  = let b0, b1 = bs in
    { a = b0; b = b1 }

private
inline_for_extraction
let lbytes_of_ecCurve (c:ecCurve)
  : Tot (lbytes_1 * lbytes_1)
  = c.a, c.b

#reset-options "--using_facts_from '* -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_ecCurve_of_lbytes_is_injective () 
  : Lemma (LP.synth_injective ecCurve_of_lbytes) 
  = ()
#reset-options


(* Parsers *)

inline_for_extraction
let ecCurve_parser_kind' = 
  LP.and_then_kind lbytes_1_parser_kind lbytes_1_parser_kind

let ecCurve_parser_kind_metadata = ecCurve_parser_kind'.LP.parser_kind_metadata

let ecCurve_parser =
  lemma_ecCurve_of_lbytes_is_injective ();
  lbytes_1_parser `LP.nondep_then` lbytes_1_parser `LP.parse_synth` (fun xy -> ecCurve_of_lbytes xy)

let ecCurve_parser32 =
  lemma_ecCurve_of_lbytes_is_injective ();
  let pu8u8 = LP.nondep_then lbytes_1_parser lbytes_1_parser in
  let pu8u832 = LP.parse32_nondep_then lbytes_1_parser32 lbytes_1_parser32 in
  LP.parse32_synth pu8u8 ecCurve_of_lbytes (fun xy -> ecCurve_of_lbytes xy) pu8u832 ()


(* Serialization *) 

#reset-options "--using_facts_from '* -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_ecCurve_of_lbytes_of_ecCurve () 
  : Lemma (LP.synth_inverse ecCurve_of_lbytes lbytes_of_ecCurve)
  = ()
#reset-options

let ecCurve_serializer =
  lemma_ecCurve_of_lbytes_is_injective ();
  lemma_ecCurve_of_lbytes_of_ecCurve ();
  assert_norm (ecCurve_parser_kind'  == ecCurve_parser_kind);
  let pu8u8 : LP.parser ecCurve_parser_kind' _ = LP.nondep_then lbytes_1_parser lbytes_1_parser in
  let su8u8 : LP.serializer pu8u8 = LP.serialize_nondep_then lbytes_1_parser lbytes_1_serializer () lbytes_1_parser lbytes_1_serializer in
  LP.serialize_synth #ecCurve_parser_kind' #(lbytes_1 * lbytes_1) #ecCurve
    pu8u8 ecCurve_of_lbytes su8u8 lbytes_of_ecCurve ()

let ecCurve_serializer32 =
  lemma_ecCurve_of_lbytes_is_injective ();
  lemma_ecCurve_of_lbytes_of_ecCurve ();
  assert_norm (ecCurve_parser_kind'  == ecCurve_parser_kind);
  let pu8u8 = LP.nondep_then lbytes_1_parser lbytes_1_parser in
  let pu8u832 = LP.parse32_nondep_then lbytes_1_parser32 lbytes_1_parser32 in
  let su8u8 = LP.serialize_nondep_then lbytes_1_parser lbytes_1_serializer () lbytes_1_parser lbytes_1_serializer in
  let su8u832 = LP.serialize32_nondep_then lbytes_1_serializer32 () lbytes_1_serializer32 () in
  LP.serialize32_synth #ecCurve_parser_kind' #(lbytes_1 * lbytes_1) #ecCurve
    pu8u8 ecCurve_of_lbytes su8u8 su8u832 lbytes_of_ecCurve (fun x -> lbytes_of_ecCurve x) ()
