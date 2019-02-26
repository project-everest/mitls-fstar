(* Copyright (C) 2012--2017 Microsoft Research and INRIA *)
module Extensions

#set-options "--admit_smt_queries true"

let cext_of_custom_aux ((n, e):custom_extension) : clientHelloExtension =
  CHE_Unknown_extensionType n e

let cext_of_custom el =
  List.Tot.map cext_of_custom_aux el

let eext_of_custom_aux ((n, e):custom_extension) =
  EE_Unknown_extensionType n e

let eext_of_custom el =
  List.Tot.map eext_of_custom_aux el

let custom_of_cext_aux = function
  | CHE_Unknown_extensionType n e -> Some (n,e)
  | _ -> None

let custom_of_cext el =
  List.Tot.choose custom_of_cext_aux el

let custom_of_eext_aux = function
  | EE_Unknown_extensionType n e -> Some (n,e)
  | _ -> None

let custom_of_eext el =
  List.Tot.choose custom_of_eext_aux el

let bindersLen_aux = function
  | CHE_pre_shared_key psk -> true
  | _ -> false

let bindersLen che =
  match List.Tot.find bindersLen_aux che with
  | None -> 0ul
  | Some (CHE_pre_shared_key psk) ->
    Parsers.OfferedPsks_binders.offeredPsks_binders_size32 psk.binders

