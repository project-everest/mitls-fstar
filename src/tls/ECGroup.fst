module ECGroup

open FStar.Error
open TLSError
open Mem
open Parse

module B = FStar.Bytes
module LB = LowStar.Buffer
module EC = EverCrypt
module LP = LowParse.SLow.Base

type ec_all_curve =
  | EC_CORE of group
  | EC_UNKNOWN of (n:nat{B.repr_bytes n <= 2})
  | EC_EXPLICIT_PRIME
  | EC_EXPLICIT_BINARY

// FIXME eqtype is a lie but the idealization needs equality of keyshares
let _key g = assume false; EC.ecdh_state

let pubshare #g k =
  match k with
  | KS_CC p _ -> S_CC p
  | KS_X25519 k -> S_X25519 (TLS.Curve25519.pubshare k)
  | KS_X448 p _ -> S_X448 p

#reset-options "--using_facts_from '* -LowParse'"
let keygen g =
  match g with
  | EverCrypt.ECC_X25519 -> KS_X25519 (TLS.Curve25519.keygen ())
  | EverCrypt.ECC_X448 ->
    let s = Random.sample32 56ul in
    let p = Random.sample32 56ul in
    KS_X448 p s
  | _ ->
    push_frame ();
    let l = FStar.UInt32.uint_to_t (bytelen g) in
    let xb = LB.alloca 0uy l in
    let yb = LB.alloca 0uy l in
    assume false; // FIXME EverCrypt framing
    let st = EC.ecdh_load_curve g in
    EC.ecdh_keygen st xb yb;
    let p : point g = { ecx = B.of_buffer l xb; ecy = B.of_buffer l yb } in
    pop_frame ();
    KS_CC p st

let dh_initiator #g gx gy =
  match g with
  | EverCrypt.ECC_X25519 ->
    let KS_X25519 (p,s) = gx in
    let S_X25519 gy = gy in
    TLS.Curve25519.mul s gy
  | EverCrypt.ECC_X448 ->
    let KS_X448 p s = gx in
    s // TODO BEWARE
  | _ ->
    let KS_CC _ st = gx in
    let S_CC gy = gy in
    push_frame ();
    let l = UInt32.uint_to_t (bytelen g) in
    let xb = LB.alloca 0uy l in
    let yb = LB.alloca 0uy l in
    let rb = LB.alloca 0uy l in
    B.store_bytes gy.ecx xb;
    B.store_bytes gy.ecy yb;
    assume false; // FIXME EverCrypt framing
    let ol = EC.ecdh_compute st xb yb rb in
    let r = B.of_buffer ol rb in
    EC.ecdh_free_curve st;
    pop_frame (); r
    
#reset-options

// cwinter: parse_curve, parse_point, and parse_partial really describe
// one parser for one datatype of the shape
// { ECCurveType, ECNamedGroup (or NamedCurve), UncompressedPointRepresentation or raw bytes }
// but I can't figure out whether that type has a name in the RFCs
// (I don't think so, because 'namedcurve' in ECParameters only contains the 
// curve name, no further parameters).
val parse_curve: B.bytes -> Tot (option group)
let parse_curve b =
  if (B.length b < 1) then None else (
    let open Parsers.ECCurveType.EcCurveType in  
    let open Format.NamedGroup in
    match ecCurveType_parser32 b with // <- parse_curve == ecCurveType_parser and-then named_group_parser
    | Some (Parsers.ECCurveType.EcCurveType.NAMED_CURVE, _) -> 
      let ty, id = B.split b 1ul in
      (match namedGroup_parser32 id with
       | Some (SECP256R1, _) -> Some EC.ECC_P256
       | Some (SECP384R1, _) -> Some EC.ECC_P384
       | Some (SECP521R1, _) -> Some EC.ECC_P521
       | Some (X25519, _   ) -> Some EC.ECC_X25519
       | Some (X448, _     ) -> Some EC.ECC_X448
       | _                   -> None)
    | _ -> None)

#reset-options "--using_facts_from '* -LowParse'"
let parse_point g b =
  // parser for flat bytes or uncompressedPointPepresentation
  match g with
  | EC.ECC_X448 -> (
      let (p:LP.parser32 _) = LowParse.SLow.parse32_flbytes 56 56ul in
      match p b with
      | Some (bs, _) -> Some (S_X448 bs)
      | _ -> None)
  | EC.ECC_X25519 -> (
      let (p:LP.parser32 _) = LowParse.SLow.parse32_flbytes 32 32ul in
      match p b with
      | Some (bs, _) -> Some (S_X25519 bs)
      | _ -> None)
  | _ ->
      let open Format.UncompressedPointRepresentation in
      let cl = UInt32.uint_to_t (bytelen g) in
      match (uncompressedPointRepresentation_parser32 cl) b with
      | Some (ucpr, _) -> 
          let e = { ecx = ucpr.x; ecy = ucpr.y } in Some (S_CC e)
    | _ -> None

let parse_partial payload =
    // This really means:
    // ecCurveType_parser and-then 
    // namedGroup_parser (or NamedCurve) and-then
    // ( uncompressedPointRepresentation_parser or flbytes_parser )
    // We should rewrite it using parser combinators
    if B.length payload >= 7 then
      let (curve, point) = B.split payload 3ul in
      match parse_curve curve with
      
      | None -> fatal Decode_error (perror __SOURCE_FILE__ __LINE__ "Unsupported curve")
      | Some(ecp) ->
        match vlsplit 1 point with
        | Error(z) -> Error(z)
        | Correct(x) ->
           let rawpoint, rem = x in
           match parse_point ecp rawpoint with
           | None -> fatal Decode_error (perror __SOURCE_FILE__ __LINE__ ("Invalid EC point received:"^(FStar.Bytes.print_bytes rawpoint)))
           | Some p -> Correct ((| ecp, p |),rem)
    else fatal Decode_error (perror __SOURCE_FILE__ __LINE__ "")

open FStar.Mul

#reset-options "--using_facts_from '* -LowParse'"
(* Assumes uncompressed point format for now (04||ecx||ecy) *)
let serialize_point #g s =
  match g with
  | EC.ECC_X25519 ->
    let S_X25519 p = s in     
    let r = LowParse.SLow.serialize32_flbytes (bytelen g) p in
    assume (B.length r = bytelen g);
    r
  | EC.ECC_X448 ->
    let S_X448 p = s in    
    let r = LowParse.SLow.serialize32_flbytes (bytelen g) p in
    assume (B.length r = bytelen g);
    r
  | _ ->
    let S_CC e = s in
    let open Format.UncompressedPointRepresentation in    
    let l = B.length e.ecx in
    let (l32:coordinate_length_type) = UInt32.uint_to_t l in
    let (ucp:uncompressedPointRepresentation l32) = { legacy_form = 4uy; x = e.ecx; y = e.ecy } in
    let x = (uncompressedPointRepresentation_serializer32 l32) ucp in
    assume (B.length x = 2 * (bytelen g) + 1);
    x

let curve_id g : Tot (B.lbytes 2) =
  let open Format.NamedGroup in
  let r = namedGroup_serializer32 ( // <- curve_id == namedGroup_serializer
    match g with
    | EC.ECC_P256   -> SECP256R1
    | EC.ECC_P384   -> SECP384R1
    | EC.ECC_P521   -> SECP521R1
    | EC.ECC_X25519 -> X25519
    | EC.ECC_X448   -> X448) in
  assume (B.length r = 2);
  r

let serialize #g ecdh_Y =
  let open FStar.Bytes in
  let ty = abyte 3z in
  let id = curve_id g in
  let e = serialize_point ecdh_Y in
  lemma_repr_bytes_values (length e);
  assert (repr_bytes (length e) <= 1);
  let ve = vlbytes 1 e in
  ty @| id @| ve
