module ParsersAux.ClientHelloExtension
include Parsers.ClientHelloExtension

module Seq = FStar.Seq
module LP = LowParse.Spec.Base
module ET = Parsers.ExtensionType

val serialize_clientHelloExtension_eq_pre_shared_key
  (e: clientHelloExtension {CHE_pre_shared_key? e})
: Lemma
  (LP.serialize clientHelloExtension_serializer e ==
   LP.serialize ET.extensionType_serializer ET.Pre_shared_key `Seq.append`
   LP.serialize clientHelloExtension_CHE_pre_shared_key_serializer (CHE_pre_shared_key?._0 e))
