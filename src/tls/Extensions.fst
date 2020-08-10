(* Copyright (C) 2012--2017 Microsoft Research and INRIA *)
module Extensions

(*
#push-options "--admit_smt_queries true"

let cext_of_custom_aux ((n, e):custom_extension) : clientHelloExtension =
  CHE_Unknown_extensionType n e

let cext_of_custom el =
  let el = List.Tot.map cext_of_custom_aux el in
  assume(Parsers.ClientHelloExtensions.clientHelloExtensions_list_bytesize el <= 32000);
  el

let eext_of_custom_aux ((n, e):custom_extension) =
  assume(Parsers.EncryptedExtensions.encryptedExtensions_list_bytesize el <= 32000);
  EE_Unknown_extensionType n e

let eext_of_custom el =
  List.Tot.map eext_of_custom_aux el in

let custom_of_cext_aux = function
  | CHE_Unknown_extensionType n e -> Some (n,e)
  | _ -> None

let custom_of_cext el =
  // 19-06-17 we miss bytelength-counting maps; we'll get rid of this code anyway.
  List.Tot.choose custom_of_cext_aux el

let custom_of_eext_aux = function
  | EE_Unknown_extensionType n e -> Some (n,e)
  | _ -> None

let custom_of_eext el =
  List.Tot.choose custom_of_eext_aux el

#pop-options
*)

let clientHelloExtension_of_tagged_unknown_extension (Payload_Unknown_extensionType tg pl) = 
  CHE_Unknown_extensionType tg pl
let encryptedExtension_of_tagged_unknown_extension (Payload_Unknown_extensionType tg pl) = 
  EE_Unknown_extensionType tg pl

module HS = FStar.HyperStack
module LP = LowParse.Low
module U32 = FStar.UInt32

friend Parsers.ClientHelloExtension
friend Parsers.TaggedUnknownExtension
friend Parsers.ClientHelloExtension_CHE_default
friend Parsers.TaggedUnknownExtension_payload_default

#push-options "--z3rlimit 16"

let valid_clientHelloExtension_of_tagged_unknown_extension
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos: U32.t)
: Lemma
  (requires (LP.valid taggedUnknownExtension_parser h sl pos))
  (ensures (LP.valid_content_pos clientHelloExtension_parser h sl pos (clientHelloExtension_of_tagged_unknown_extension (LP.contents taggedUnknownExtension_parser h sl pos)) (LP.get_valid_pos taggedUnknownExtension_parser h sl pos)))
= 
  assert_norm (LP.parse_dsum_kind (LP.get_parser_kind extensionType_repr_parser) taggedUnknownExtension_sum parse_taggedUnknownExtension_cases (LP.get_parser_kind taggedUnknownExtension_payload_default_parser) == taggedUnknownExtension_parser_kind);
  LP.valid_dsum_elim_unknown h taggedUnknownExtension_sum extensionType_repr_parser parse_taggedUnknownExtension_cases taggedUnknownExtension_payload_default_parser sl pos;
  assert_norm (taggedUnknownExtension_payload_default_parser == clientHelloExtension_CHE_default_parser);
  assert_norm (LP.parse_dsum_kind (LP.get_parser_kind extensionType_repr_parser) clientHelloExtension_sum parse_clientHelloExtension_cases (LP.get_parser_kind clientHelloExtension_CHE_default_parser) == clientHelloExtension_parser_kind);
  LP.valid_dsum_intro_unknown h clientHelloExtension_sum extensionType_repr_parser parse_clientHelloExtension_cases clientHelloExtension_CHE_default_parser sl pos

#pop-options

let clientHelloExtensions_of_unknownExtensions_list l = 
  List.Tot.map clientHelloExtension_of_tagged_unknown_extension l

let clientHelloExtensions_of_unknownExtensions l = 
  clientHelloExtensions_of_unknownExtensions_list l

let encryptedExtensions_of_unknownExtensions l = List.Tot.map encryptedExtension_of_tagged_unknown_extension l

#push-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 0"
let rec valid_list_clientHelloExtensions_of_tagged_unknown_extensions'
  (h: HS.mem)
  (#rrel #rel: _)
  (sl: LP.slice rrel rel)
  (pos pos': U32.t)
: Lemma
  (requires (LP.valid_list taggedUnknownExtension_parser h sl pos pos'))
  (ensures (
    LP.valid_list clientHelloExtension_parser h sl pos pos' /\
    LP.contents_list clientHelloExtension_parser h sl pos pos' == clientHelloExtensions_of_unknownExtensions_list (LP.contents_list taggedUnknownExtension_parser h sl pos pos')
  ))
  (decreases (U32.v pos' - U32.v pos))
= if pos = pos'
  then begin
    LP.valid_list_nil taggedUnknownExtension_parser h sl pos;
    LP.valid_list_nil clientHelloExtension_parser h sl pos
  end else begin
    LP.valid_list_cons_recip taggedUnknownExtension_parser h sl pos pos' ;
    valid_clientHelloExtension_of_tagged_unknown_extension h sl pos;
    let pos1 = LP.get_valid_pos taggedUnknownExtension_parser h sl pos in
    valid_list_clientHelloExtensions_of_tagged_unknown_extensions' h sl pos1 pos' ;
    LP.valid_list_cons clientHelloExtension_parser h sl pos pos'
  end
#pop-options

let valid_list_clientHelloExtensions_of_tagged_unknown_extensions = valid_list_clientHelloExtensions_of_tagged_unknown_extensions'


let bindersLen che =
  match List.Tot.find CHE_pre_shared_key? che with
  | None -> 0ul
  | Some (CHE_pre_shared_key psk) -> 
    Parsers.OfferedPsks_binders.offeredPsks_binders_size32 psk.binders
