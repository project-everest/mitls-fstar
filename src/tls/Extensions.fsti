(* Copyright (C) 2012--2017 Microsoft Research and INRIA *)
(**
This modules defines TLS 1.3 Extensions. 

@summary: TLS 1.3 Extensions. 
*)
module Extensions

open Platform.Bytes
open Platform.Error
open TLSError
open TLSConstants
open TLSInfo
//open CoreCrypto

(** RFC 4.2 'Extension' Table *)

noeq type preEarlyDataIndication : Type0 =
  { ped_configuration_id: configurationId;
    ped_cipher_suite:valid_cipher_suite;
    ped_extensions:list extension;
    ped_context:b:bytes{length b < 256};
    //ped_early_data_type:earlyDataType;
    }
and earlyDataIndication =
  | ClientEarlyDataIndication of preEarlyDataIndication
  | ServerEarlyDataIndication

(* SI: ToDo cookie payload *)
and cookie = 
  | Cookie

and supportedVersions = 
  | SupportedVersions 

(* SI: we currently only define Mandatory-to-Implement Extensions as listed in RFC 8.2. 
   Labels in the variants below are: 
     M  - "MUST implement"
     AF - "MUST ... when offering applicable features"

   Non-{M,AF} extension commented-out for now.*)
and extension =
  | E_server_name of list serverName (* M, AF *)
(*| E_max_fragment_length 
  | E_client_certificate_url 
  | E_status_request 
  | E_user_mapping 
  | E_cert_type *)
  | E_supported_groups of list namedGroup (* M, AF *)
  | E_signature_algorithms of (list sigHashAlg) (* M, AF *)  
(*| E_use_srtp 
  | E_heartbeat 
  | E_application_layer_protocol_negotiation
  | E_signed_certifcate_timestamp 
  | E_client_certificate_type 
  | E_padding *)
  | E_key_share of CommonDH.keyShare (* M, AF *)
  | E_pre_shared_key of PSK.preSharedKey (* M, AF *)
(*| E_psk_key_exchange_modes *)
  | E_early_data of earlyDataIndication
  | E_cookie of cookie (* M *)
  | E_supported_versions of supportedVersions (* M, AF *) 
(*| E_certificate_authorities 
  | E_oid_filters *)
  | E_unknown_extension of (lbytes 2 * bytes) (** to return unimplemented or unknow extensions. *)

(** Extension equality *)
val sameExt : extension -> extension -> bool 

(** Extension serialize. *)
val extensionHeaderBytes: extension -> Tot bytes

type canFail (a:Type) =
| ExFail of alertDescription * string
| ExOK of list a


val extension_depth : (ext: extension) -> Tot nat
val extensions_depth : (exts:list extension) -> Tot nat

val extensionBytes: role -> ext:extension -> Tot bytes
  (decreases (extension_depth ext))
val extensionsBytes: role -> cl:list extension -> Tot (b:bytes{length b <= 2 + 65535})
  (decreases (extensions_depth cl))
  
val parseExtension: r:role -> b:bytes -> Tot (result extension) (decreases (length b))
val parseExtensions: r:role -> b:bytes -> Tot (result (list extension)) (decreases (length b))

val parseOptExtensions: r:role -> data:bytes -> Tot (result (option (list extension)))

val list_valid_cs_is_list_cs: (l:valid_cipher_suites) ->  Tot (list cipherSuite) 

val prepareExtensions: protocolVersion -> (k:valid_cipher_suites{List.Tot.length k < 256}) -> bool -> bool -> list sigHashAlg -> list (x:namedGroup{SEC? x \/ FFDHE? x}) -> option (cVerifyData * sVerifyData) -> (option CommonDH.keyShare) -> Tot (l:list extension{List.Tot.length l < 256})

val negotiateClientExtensions: protocolVersion -> config -> option (list extension) -> option (list extension) -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> Tot (result (negotiatedExtensions))

val clientToNegotiatedExtension: config -> cipherSuite -> option (cVerifyData * sVerifyData) -> bool -> negotiatedExtensions -> extension -> Tot negotiatedExtensions

val negotiateServerExtensions: protocolVersion -> option (list extension) -> valid_cipher_suites -> config -> cipherSuite -> option (cVerifyData*sVerifyData) -> option CommonDH.keyShare -> bool -> Tot (result (option (list extension)))

val default_sigHashAlg: protocolVersion -> cipherSuite -> ML (l:list sigHashAlg{List.Tot.length l <= 1})
