module LowParseExample5
include LowParseExample5.Aux

module LPC = LowParse.Spec.Combinators
module LPV = LowParse.Low.VLData
module LPI = LowParse.Low.Int
module LP = LowParse.Low.Base

module U32 = FStar.UInt32
module U16 = FStar.UInt16
module I32 = FStar.Int32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

#reset-options "--z3rlimit 64  --z3cliopt smt.arith.nl=false --z3cliopt smt.case_split=3"
// --using_facts_from '* -FStar.Kremlin.Endianness -LowParse.BigEndian -LowParse.BigEndianImpl.* -LowParse.Math -FStar.Math.*'"

noextract
let vltest () : HST.Stack unit (fun _ -> True) (fun _ _ _ -> True) =
  HST.push_frame ();
  let b : LP.buffer8 = B.alloca 0uy 12ul in
//  assert (B.len b == 8ul);
  let j = LPI.serialize32_u16_fail b 12l 4l 18us in
  let j = LPI.serialize32_u16_fail b 12l j 42us in
  let j = LPI.serialize32_u32_fail b 12l j 1729ul in  
  let h = HST.get () in
  let k = LPV.serialize32_bounded_vldata_strong_size 8 8 serialize_t b 4l j in
  let h' = HST.get () in
  assert (
    let v = ({ inner = ({ left = 18us; right = 42us; }); last = 1729ul;}) in
    LP.contains_valid_serialized_data_or_fail h serialize_t b 4l v j
  );
  assert (k == true);
  assert (
    let v = ({ inner = ({ left = 18us; right = 42us; }); last = 1729ul;}) in
    LPV.parse_bounded_vldata_strong_pred 8 8 serialize_t v /\
    LP.contains_valid_serialized_data_or_fail h' (LPV.serialize_bounded_vldata_strong 8 8 serialize_t) b 3l v j /\
    True
  );
  HST.pop_frame ()

let main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
   HST.Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
=
  fun _ _ ->
  HST.push_frame ();
  let b : LP.buffer8 = B.alloca 0uy 8ul in
//  assert (B.len b == 8ul);
  let j = LPI.serialize32_u16_fail b 8l 0l 18us in
  let j = LPI.serialize32_u16_fail b 8l j 42us in
  let j = LPI.serialize32_u32_fail b 8l j 1729ul in
  let h = HST.get () in
  assert (LP.contains_valid_serialized_data_or_fail h serialize_t b 0l ({ inner = ({ left = 18us; right = 42us; }); last = 1729ul;}) j);
  HST.pop_frame ();
  C.EXIT_SUCCESS
