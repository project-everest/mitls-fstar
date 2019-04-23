module ParsersAux.ClientHelloExtension
include Parsers.ClientHelloExtension

module Seq = FStar.Seq
module LP = LowParse.Low.Base
module CHE = Parsers.ClientHelloExtension
module ET = Parsers.ExtensionType

val serialize_clientHelloExtension_eq_pre_shared_key
  (e: CHE.clientHelloExtension {CHE.CHE_pre_shared_key? e})
: Lemma
  (LP.serialize CHE.clientHelloExtension_serializer e ==
   LP.serialize ET.extensionType_serializer ET.Pre_shared_key `Seq.append`
   LP.serialize CHE.clientHelloExtension_CHE_pre_shared_key_serializer (CHE.CHE_pre_shared_key?._0 e))
