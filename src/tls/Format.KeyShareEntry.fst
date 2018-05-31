module Format.KeyShareEntry

open Format.NamedGroup
open Format.UncompressedPointRepresentation

module B = FStar.Bytes
module LP = LowParse.SLow
module U32 = FStar.UInt32


(* Parsers, validators *)

inline_for_extraction
let synth_keyShareEntry (r:namedGroup * (LowParse.Spec.Bytes.parse_bounded_vlbytes_t 1 65535)): Tot keyShareEntry = { group=(fst r); key_exchange=(snd r) }

inline_for_extraction
let unsynth_keyShareEntry (e:keyShareEntry): Tot (namedGroup * (LowParse.Spec.Bytes.parse_bounded_vlbytes_t 1 65535)) = e.group, e.key_exchange

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics'"
let lemma_synth_keyShareEntry_is_injective () 
  : Lemma (LP.synth_injective synth_keyShareEntry) 
  = LP.synth_injective_intro synth_keyShareEntry
#reset-options

inline_for_extraction
let keyShareEntry_parser_kind' =
  LP.and_then_kind namedGroup_parser_kind (LP.parse_bounded_vldata_kind 1 65535)

let keyShareEntry_parser_kind_metadata = keyShareEntry_parser_kind'.LP.parser_kind_metadata

#reset-options "--using_facts_from '* -FStar.Reflection -FStar.Tactics'"

let keyShareEntry_parser =
  lemma_synth_keyShareEntry_is_injective ();
  assert_norm (keyShareEntry_parser_kind' == keyShareEntry_parser_kind);
  LP.parse_synth 
    (namedGroup_parser `LP.nondep_then` (LP.parse_bounded_vlbytes 1 65535))
    synth_keyShareEntry

let keyShareEntry_parser32 =
  lemma_synth_keyShareEntry_is_injective ();
  assert_norm (keyShareEntry_parser_kind' == keyShareEntry_parser_kind);
  LP.parse32_synth
    _
    synth_keyShareEntry
    (fun x -> synth_keyShareEntry x)
    (LP.parse32_nondep_then namedGroup_parser32 (LP.parse32_bounded_vlbytes 1 1ul 65535 65535ul))
    ()
    

(* Serialization *)

#reset-options "--using_facts_from '* -LowParse -FStar.Reflection -FStar.Tactics'"
let lemma_synth_keyShareEntry_of_unsynth_keyShareEntry () 
  : Lemma (LP.synth_inverse synth_keyShareEntry unsynth_keyShareEntry)
  = LP.synth_inverse_intro synth_keyShareEntry unsynth_keyShareEntry
#reset-options

#reset-options "--using_facts_from '* -FStar.Reflection -FStar.Tactics'"
let keyShareEntry_serializer =
  lemma_synth_keyShareEntry_is_injective ();
  lemma_synth_keyShareEntry_of_unsynth_keyShareEntry ();
  assert_norm (keyShareEntry_parser_kind' == keyShareEntry_parser_kind);
  LP.serialize_synth
    _
    synth_keyShareEntry
    (LP.serialize_nondep_then _ namedGroup_serializer ()
                              _ (LP.serialize_bounded_vlbytes 1 65535))
    unsynth_keyShareEntry
    ()

let keyShareEntry_serializer32: LP.serializer32 keyShareEntry_serializer =
  lemma_synth_keyShareEntry_is_injective ();
  lemma_synth_keyShareEntry_of_unsynth_keyShareEntry ();
  assert_norm (keyShareEntry_parser_kind' == keyShareEntry_parser_kind);
  LP.serialize32_synth
    (LP.nondep_then namedGroup_parser (LP.parse_bounded_vlbytes 1 65535))
    synth_keyShareEntry
    (LP.serialize_nondep_then namedGroup_parser namedGroup_serializer ()
                              (LP.parse_bounded_vlbytes 1 65535) (LP.serialize_bounded_vlbytes 1 65535))
    (LP.serialize32_nondep_then namedGroup_serializer32 () 
                                (LP.serialize32_bounded_vlbytes 1 65535) ())
    unsynth_keyShareEntry
    (fun x -> unsynth_keyShareEntry x)
    ()
#reset-options
