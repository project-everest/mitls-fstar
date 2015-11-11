module CommonDH
//open Seq
open Bytes
open Error
open TLSConstants
open CoreKeys

type element = {
 dhe_p :  DHGroup.elt option;
 dhe_ec :  ECGroup.point option;
}

let dhe_nil = {
 dhe_p = None;
 dhe_ec = None;
}

type secret = 
  | Key of bytes

type parameters =
| DHP_P of dhparams
| DHP_EC of ecdhparams

exception Invalid_DH

let get_p (e:element) =
    match e with
    | {dhe_p = Some x; dhe_ec = None } -> x
    | _ -> raise Invalid_DH

let get_ec (e:element) =
    match e with
    | {dhe_p = None; dhe_ec = Some x } -> x
    | _ -> raise Invalid_DH

let serializeKX (p:parameters) (e:element) : bytes =
    match p with
    | DHP_P(dhp) -> (vlbytes 2 dhp.dhp) @| (vlbytes 2 dhp.dhg) @| (vlbytes 2 (get_p e))
    | DHP_EC(ecp) ->
           abyte 3uy (* Named curve *)
        @| ECGroup.curve_id ecp
        @| ECGroup.serialize_point ecp (get_ec e)

let checkParams dhdb minSize (p:parameters) =
    match p with
    | DHP_P(dhp) ->
      begin match dhdb with
        | None -> Error (TLSError.AD_internal_error, "Not possible")
        | Some db -> 
            (match DHGroup.checkParams db minSize dhp.dhp dhp.dhg with
            | Error(x) -> Error(x)
            | Correct(db, dhp) -> Correct(Some db, p))
      end
    | DHP_EC(ecp) -> correct (None, p)

let checkElement (p:parameters) (e:element) :  element option =
    match (p, e.dhe_p, e.dhe_ec) with
    | DHP_P(dhp), Some b, None ->
      begin match DHGroup.checkElement dhp b with
        | None -> None
        | Some x -> Some ({dhe_nil with dhe_p = Some x})
      end
    | DHP_EC(ecp), None, Some p ->
      begin match ECGroup.checkElement ecp p with
        | None -> None
        | Some p -> Some ({dhe_nil with dhe_ec = Some p})
      end
    | _ -> failwith "impossible"

let parse (p:parameters) (b:bytes) =
    match p with
    | DHP_P(dhp) -> Some ({dhe_nil with dhe_p = Some b})
    | DHP_EC(ecp) ->
      begin match ECGroup.parse_point ecp b with
        | None -> None
        | Some ecp -> Some ({dhe_nil with dhe_ec = Some ecp})
      end
