module ParsersAux.ClientHelloExtension
open Parsers.ClientHelloExtension

module Seq = FStar.Seq
module LP = LowParse.Spec
module ET = Parsers.ExtensionType

friend Parsers.ClientHelloExtension
friend Parsers.ExtensionType

#push-options "--z3rlimit 20 --max_fuel 1 --max_ifuel 0"
let serialize_clientHelloExtension_eq_pre_shared_key e =
  assert_norm (LP.parse_dsum_kind (LP.get_parser_kind ET.extensionType_repr_parser) clientHelloExtension_sum parse_clientHelloExtension_cases (LP.get_parser_kind clientHelloExtension_CHE_default_parser) == clientHelloExtension_parser_kind);
  assert (LP.dsum_tag_of_data clientHelloExtension_sum e == LP.Known (known_extensionType_as_enum_key ET.Pre_shared_key));
  LP.serialize_dsum_eq clientHelloExtension_sum ET.extensionType_repr_serializer _ serialize_clientHelloExtension_cases _ clientHelloExtension_CHE_default_serializer e;
  ET.lemma_synth_extensionType_inj ();
  ET.lemma_synth_extensionType_inv ();
  LP.serialize_synth_eq _ ET.synth_extensionType ET.serialize_maybe_extensionType_key ET.synth_extensionType_inv () (known_extensionType_as_enum_key ET.Pre_shared_key)
#pop-options
