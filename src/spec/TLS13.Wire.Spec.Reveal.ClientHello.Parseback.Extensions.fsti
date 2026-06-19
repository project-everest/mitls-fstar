module TLS13.Wire.Spec.Reveal.ClientHello.Parseback.Extensions

module B = TLS13.Bytes
module Seq = FStar.Seq
module LP = LowParse.Spec
module GHN = TLS13.Wire.Generated.HostName
module GSNM = TLS13.Wire.Generated.ServerName
module GSNL = TLS13.Wire.Generated.ServerNameList
module GSNE = TLS13.Wire.Generated.ExtensionClientHello_extension_data_server_name
module GKSEKE = TLS13.Wire.Generated.KeyShareEntry_key_exchange
module GNG = TLS13.Wire.Generated.NamedGroup
module GKSE = TLS13.Wire.Generated.KeyShareEntry
module GSS = TLS13.Wire.Generated.SignatureScheme
module GPV = TLS13.Wire.Generated.ProtocolVersion
module GECH = TLS13.Wire.Generated.ExtensionClientHello

val lemma_lp_sg_extension ()
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer (GECH.Extension_data_supported_groups [GNG.X25519]))
                     (B.of_list [0uy; 0x0auy; 0uy; 4uy; 0uy; 2uy; 0uy; 0x1duy]))

val lemma_lp_sa_extension ()
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer
                        (GECH.Extension_data_signature_algorithms [GSS.Rsa_pss_rsae_sha256]))
                     (B.of_list [0uy; 0x0duy; 0uy; 4uy; 0uy; 2uy; 0x08uy; 0x04uy]))

val lemma_lp_sv_extension ()
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer
                        (GECH.Extension_data_supported_versions [GPV.TLS_1p3]))
                     (B.of_list [0uy; 0x2buy; 0uy; 3uy; 2uy; 0x03uy; 0x04uy]))

val lemma_lp_ks_extension (key: GKSEKE.keyShareEntry_key_exchange{Seq.length key == 32})
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer
                        (GECH.Extension_data_key_share ([ { GKSE.group = GNG.X25519; GKSE.key_exchange = key } ])))
                     (Seq.append (B.of_list [0uy; 0x33uy; 0uy; 38uy; 0uy; 36uy; 0uy; 0x1duy; 0uy; 32uy]) key))

val mk_snl (hn: GHN.hostName{Seq.length hn <= 255}) : GSNL.serverNameList

val mk_sne (hn: GHN.hostName{Seq.length hn <= 255})
  : GSNE.extensionClientHello_extension_data_server_name

val lemma_mk_snl_shape (hn: GHN.hostName{Seq.length hn <= 255})
  : Lemma (mk_snl hn == [GSNM.Name_host_name hn])

val lemma_mk_sne_shape (hn: GHN.hostName{Seq.length hn <= 255})
  : Lemma (mk_sne hn == [GSNM.Name_host_name hn])

val lemma_lp_sn_extension (hn: GHN.hostName{Seq.length hn <= 255 /\ Seq.length hn > 0})
  : Lemma (Seq.equal (LP.serialize GECH.extensionClientHello_serializer
                        (GECH.Extension_data_server_name (mk_sne hn)))
                     (TLS13.Wire.Spec.Reveal.ClientHello.client_hello_server_name_extension_bytes hn))
