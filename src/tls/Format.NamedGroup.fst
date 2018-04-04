module Format.NamedGroup

module U16 = FStar.UInt16 
module U32 = FStar.UInt32
module L = FStar.List.Tot
module LP = LowParse.SLow
module CC = CoreCrypto
module B32 = FStar.Bytes

unfold type is_injective (#a:Type) (#b:Type) (f:a -> b) 
  = forall x y . f x == f y ==> x == y

unfold type is_injective_2 (#a:Type) (#b:Type) (f:a -> b) (x:a) (y:a)
  = f x == f y ==> x == y

private
inline_for_extraction
let namedGroup_of_u16 (x:U16.t): Tot namedGroup =
  match x with
  | 0x0017us -> SECP256R1
  | 0x0018us -> SECP384R1
  | 0x0019us -> SECP521R1
  | 0x001Dus -> X25519
  | 0x001Eus -> X448
  | 0x0100us -> FFDHE2048
  | 0x0101us -> FFDHE3072
  | 0x0102us -> FFDHE4096
  | 0x0103us -> FFDHE6144
  | 0x0104us -> FFDHE8192
  | u -> if      U16.(0x01FCus <=^ u && u <=^ 0x01FFus) then FFDHE_PRIVATE_USE u
         else if U16.(0xFE00us <=^ u && u <=^ 0xFEFFus) then ECDHE_PRIVATE_USE u
         else UNKNOWN u

private
inline_for_extraction
let u16_of_namedGroup (ng:namedGroup): Tot U16.t =
  match ng with
  | SECP256R1           -> 0x0017us
  | SECP384R1           -> 0x0018us
  | SECP521R1           -> 0x0019us
  | X25519              -> 0x001Dus
  | X448                -> 0x001Eus
  | FFDHE2048           -> 0x0100us
  | FFDHE3072           -> 0x0101us
  | FFDHE4096           -> 0x0102us
  | FFDHE6144           -> 0x0103us
  | FFDHE8192           -> 0x0104us
  | FFDHE_PRIVATE_USE u -> u
  | ECDHE_PRIVATE_USE u -> u
  | UNKNOWN u           -> u

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_namedGroup_of_u16_is_injective () 
  : Lemma (is_injective namedGroup_of_u16) 
  = ()

let lemma_namedGroup_of_u16_is_injective_2 (x:U16.t) (y:U16.t)
  : Lemma (is_injective_2 namedGroup_of_u16 x y) 
    [SMTPat (namedGroup_of_u16 x); SMTPat (namedGroup_of_u16 y)]
  = ()
#reset-options


(* Parsers *)

let namedGroup_parser_kind_metadata = LP.parse_u16_kind.LP.parser_kind_metadata

let namedGroup_parser =
  lemma_namedGroup_of_u16_is_injective ();
  LP.parse_u16 `LP.parse_synth` namedGroup_of_u16 

let namedGroup_parser32 =
  lemma_namedGroup_of_u16_is_injective ();
  LP.parse32_synth LP.parse_u16 namedGroup_of_u16 (fun x -> namedGroup_of_u16 x) LP.parse32_u16 ()


(* Serialization *) 

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16 --z3rlimit 10"
let lemma_namedGroup_of_u16_of_namedGroup () 
  : Lemma (forall x . namedGroup_of_u16 (u16_of_namedGroup x) == x)
  = ()
#reset-options


let namedGroup_serializer =
  lemma_namedGroup_of_u16_is_injective ();
  lemma_namedGroup_of_u16_of_namedGroup ();
  LP.serialize_synth #namedGroup_parser_kind #U16.t #namedGroup
    LP.parse_u16 namedGroup_of_u16 LP.serialize_u16 u16_of_namedGroup ()

let namedGroup_serializer32 =
  lemma_namedGroup_of_u16_is_injective ();
  lemma_namedGroup_of_u16_of_namedGroup ();
  LP.serialize32_synth #namedGroup_parser_kind #U16.t #namedGroup
    LP.parse_u16 namedGroup_of_u16 LP.serialize_u16 LP.serialize32_u16 u16_of_namedGroup (fun x -> u16_of_namedGroup x) ()

let lemma_namedGroup_parser_is_strong ()
  : Lemma (LP.is_strong namedGroup_parser)
  = ()
