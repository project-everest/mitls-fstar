module Format.KeyShareEntry

open Format.NamedGroup
open Format.UncompressedPointRepresentation

module B = FStar.Bytes
module LP = LowParse.SLow
module U32 = FStar.UInt32


(* Types *)

(* 
   https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#rfc.section.4.2.8

   struct {
       NamedGroup group;
       opaque key_exchange<1..2^16-1>;
   } KeyShareEntry;


   https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#ffdhe-param
   
   Diffie-Hellman [DH] parameters for both clients and servers are encoded in the 
   opaque key_exchange field of a KeyShareEntry in a KeyShare structure. The opaque
   value contains the Diffie-Hellman public value (Y = g^X mod p) for the specified
   group (see [RFC7919] for group definitions) encoded as a big-endian integer
   and padded to the left with zeros to the size of p in bytes.


   https://tlswg.github.io/tls13-spec/draft-ietf-tls-tls13.html#ecdhe-param
   
   ECDHE parameters for both clients and servers are encoded in the the opaque 
   key_exchange field of a KeyShareEntry in a KeyShare structure. 
   For secp256r1, secp384r1 and secp521r1, the contents are the serialized value
   of the following struct:
   
     struct {
         uint8 legacy_form = 4;
         opaque X[coordinate_length];
         opaque Y[coordinate_length];
     } UncompressedPointRepresentation;

*)


type keyShareEntry = {
  group        : namedGroup; 
  key_exchange : B.bytes; // (bs:B.bytes{1 <= B.length bs && B.length bs <= 65535});
}


(* Parsers, validators *)

inline_for_extraction
let synth_keyShareEntry (r:namedGroup * B.bytes): Tot keyShareEntry = { group=(fst r); key_exchange=(snd r) }

inline_for_extraction
let unsynth_keyShareEntry (e:keyShareEntry): Tot (namedGroup * B.bytes) = e.group, e.key_exchange

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_synth_keyShareEntry_is_injective () 
  : Lemma (is_injective synth_keyShareEntry) 
  = ()
#reset-options

let keyShareEntry_parser_kind = LP.and_then_kind namedGroup_parser_kind (LP.parse_bounded_vldata_kind 1 65535)

let keyShareEntry_parser: LP.parser keyShareEntry_parser_kind keyShareEntry =
  lemma_synth_keyShareEntry_is_injective ();
  LP.parse_synth 
    (namedGroup_parser `LP.nondep_then` (LP.parse_bounded_vlbytes 1 65535))
    synth_keyShareEntry

inline_for_extraction
let keyShareEntry_parser32: LP.parser32 keyShareEntry_parser =
  lemma_synth_keyShareEntry_is_injective ();
  LP.parse32_synth
    _
    synth_keyShareEntry
    (fun x -> synth_keyShareEntry x)
    (LP.parse32_nondep_then namedGroup_parser32 (LP.parse32_bounded_vlbytes 1 1ul 65535 65535ul))
    ()
    

(* Serialization *)

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics' --max_fuel 16 --initial_fuel 16 --max_ifuel 16 --initial_ifuel 16"
let lemma_synth_keyShareEntry_of_unsynth_keyShareEntry () 
  : Lemma (forall x . synth_keyShareEntry (unsynth_keyShareEntry x) == x)
  = ()
#reset-options

let keyShareEntry_serializer: LP.serializer keyShareEntry_parser =
  lemma_synth_keyShareEntry_is_injective ();
  lemma_synth_keyShareEntry_of_unsynth_keyShareEntry ();
  LP.serialize_synth
    _
    synth_keyShareEntry
    (LP.serialize_nondep_then _ namedGroup_serializer ()
                              _ (LP.serialize_bounded_vlbytes 1 65535))
    unsynth_keyShareEntry
    ()

inline_for_extraction
let keyShareEntry_serializer32: LP.serializer32 keyShareEntry_serializer =
  lemma_synth_keyShareEntry_is_injective ();
  lemma_synth_keyShareEntry_of_unsynth_keyShareEntry ();
  LP.serialize32_synth
    _
    synth_keyShareEntry
    (LP.serialize_nondep_then _ namedGroup_serializer ()
                              _ (LP.serialize_bounded_vlbytes 1 65535))
    (LP.serialize32_nondep_then namedGroup_serializer32 ()
                                (LP.serialize32_bounded_vlbytes 1 65535) ())
    unsynth_keyShareEntry
    unsynth_keyShareEntry
    ()
   
