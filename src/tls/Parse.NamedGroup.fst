module Parse.NamedGroup

module U16 = FStar.UInt16 
module U32 = FStar.UInt32
module L = FStar.List.Tot
module LP = LowParse.SLow
module CC = CoreCrypto
module B32 = FStar.Bytes

// let bytes32 = B32.bytes
// let bytes32_n (n:U32.t) = b:bytes32{B32.len b = n}
// let index32 (b:bytes32) (i:U32.t{U32.lt i (B32.len b)}) = B32.get b i

unfold type is_injective (#a:Type) (#b:Type) (f:a -> b) 
  = forall x y . f x == f y ==> x == y

unfold type is_injective_2 (#a:Type) (#b:Type) (f:a -> b) (x:a) (y:a)
  = f x == f y ==> x == y


(* Types *)

(* 
   https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#negotiated-groups 

   enum {

       /* Elliptic Curve Groups (ECDHE) */
       secp256r1(0x0017), secp384r1(0x0018), secp521r1(0x0019),
       x25519(0x001D), x448(0x001E),

       /* Finite Field Groups (DHE) */
       ffdhe2048(0x0100), ffdhe3072(0x0101), ffdhe4096(0x0102),
       ffdhe6144(0x0103), ffdhe8192(0x0104),

       /* Reserved Code Points */
       ffdhe_private_use(0x01FC..0x01FF),
       ecdhe_private_use(0xFE00..0xFEFF),
       (0xFFFF)
   } NamedGroup;

*)
 
type named_group =
  (* Elliptic Curve Groups (ECDHE) *)
  | SECP256R1 // == CC.ECC_P256
  | SECP384R1 // == CC.ECC_P384
  | SECP521R1 // == CC.ECC_P521
  | X25519    // == CC.ECC_X25519
  | X448      // == CC.ECC_X448

  (* Finite Field Groups (DHE) *)
  | FFDHE2048
  | FFDHE3072
  | FFDHE4096
  | FFDHE6144
  | FFDHE8192

  (* Reserved Code Points *)
  | FFDHE_PRIVATE_USE of (u:U16.t{U16.(0x01FCus <=^ u && u <=^ 0x01FFus)})
  | ECDHE_PRIVATE_USE of (u:U16.t{U16.(0xFE00us <=^ u && u <=^ 0xFEFFus)})

  | UNKNOWN of (u:U16.t{
      not (L.mem u [ 0x0017us; 0x0018us; 0x0019us; 0x001Dus; 
                     0x001Eus; 0x0100us; 0x0101us; 0x0102us; 0x0103us; 0x0104us]) /\ 
      not U16.(0x01FCus <=^ u && u <=^ 0x01FFus) /\
      not U16.(0xFE00us <=^ u && u <=^ 0xFEFFus)})

let is_ecdhe (ng:named_group): Tot bool = List.mem ng [ SECP256R1; SECP384R1; SECP521R1; X25519; X448 ]

let is_ffdhe (ng:named_group): Tot bool = List.mem ng [ FFDHE2048; FFDHE3072; FFDHE4096; FFDHE6144; FFDHE8192 ]

let is_ecffdhe (ng:named_group): Tot bool = is_ecdhe ng || is_ffdhe ng

type ecffdhe_group = ng:named_group{is_ecffdhe ng}

inline_for_extraction
let named_group_of_u16 (x:U16.t): Tot named_group =
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

inline_for_extraction
let u16_of_named_group (ng:named_group): Tot U16.t =
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

#set-options "--z3rlimit 50"
let lemma_named_group_of_u16_is_injective () 
  : Lemma (is_injective named_group_of_u16) 
  = ()

let lemma_named_group_of_u16_is_injective_2 (x:U16.t) (y:U16.t)
  : Lemma (is_injective_2 named_group_of_u16 x y) 
    [SMTPat (named_group_of_u16 x); SMTPat (named_group_of_u16 y)]
  = ()
#reset-options


(* Parsers *)

let named_group_parser_kind = LP.parse_u16_kind

let named_group_parser: LP.parser named_group_parser_kind named_group =
  lemma_named_group_of_u16_is_injective ();
  LP.parse_u16 `LP.parse_synth` named_group_of_u16 

inline_for_extraction
let named_group_parser32: LP.parser32 named_group_parser =
  lemma_named_group_of_u16_is_injective ();
  LP.parse32_synth LP.parse_u16 named_group_of_u16 named_group_of_u16 LP.parse32_u16 ()


(* Validators? *)


(* Serialization *) 

let named_group_serializer: LP.serializer named_group_parser = 
  LP.serialize_synth #named_group_parser_kind #U16.t #named_group
    LP.parse_u16 named_group_of_u16 LP.serialize_u16 u16_of_named_group ()

inline_for_extraction
let named_group_serializer32: LP.serializer32 named_group_serializer = 
  LP.serialize32_synth #named_group_parser_kind #U16.t #named_group
    LP.parse_u16 named_group_of_u16 LP.serialize_u16 LP.serialize32_u16 u16_of_named_group u16_of_named_group ()
