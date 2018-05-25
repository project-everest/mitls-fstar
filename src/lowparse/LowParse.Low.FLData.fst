module LowParse.Low.FLData
include LowParse.Low.Combinators
include LowParse.Spec.FLData

module B = FStar.Buffer
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

#set-options "--z3rlimit 32"

inline_for_extraction
let validate32_fldata
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (v: validator32 p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz /\ sz > 0 } ) // TODO: solve the sz = 0 case with liveness preservation
: Tot (validator32 (parse_fldata p sz))
= fun input len ->
  let len0 = B.index len 0ul in
  if len0 `U32.lt` sz32
  then false
  else begin
    let input0 = B.index input 0ul in
    B.upd input 0ul (B.sub input0 0ul sz32) ;
    B.upd len 0ul sz32;
    if v input len
    then
      let len1 = B.index len 0ul in
      if len1 = 0ul
      then begin
        B.upd input 0ul (B.offset input0 sz32);
        B.upd len 0ul (len0 `U32.sub` sz32);
        true
      end else
        false
    else false
  end

#reset-options

inline_for_extraction
let validate32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (v: validator32 p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz /\ sz > 0 } ) // TODO: solve the sz = 0 case with liveness preservation
: Tot (validator32 (parse_fldata_strong s sz))
= fun input len -> validate32_fldata v sz sz32 input len

inline_for_extraction
let validate_nochk32_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator_nochk32 (parse_fldata p sz))
= validate_nochk32_constant_size (parse_fldata p sz) sz32 ()

inline_for_extraction
let validate_nochk32_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (validator_nochk32 (parse_fldata_strong s sz))
= validate_nochk32_constant_size (parse_fldata_strong s sz) sz32 ()

inline_for_extraction
let accessor_fldata
  (#k: parser_kind)
  (#t: Type0)
  (p: parser k t)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (accessor (parse_fldata p sz) p (fun x y -> x == y))
= fun x ->
  let h = HST.get () in // TODO: WHY WHY WHY is this necessary?
  B.sub x 0ul sz32

inline_for_extraction
let accessor_fldata_strong
  (#k: parser_kind)
  (#t: Type0)
  (#p: parser k t)
  (s: serializer p)
  (sz: nat)
  (sz32: U32.t { U32.v sz32 == sz } )
: Tot (accessor (parse_fldata_strong s sz) p (fun x y -> x == y))
= fun x -> accessor_fldata p sz sz32 x

