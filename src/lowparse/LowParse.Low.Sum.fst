module LowParse.Low.Sum
include LowParse.Low.Enum
include LowParse.Spec.Sum

module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module I32 = FStar.Int32
module Cast = FStar.Int.Cast

#reset-options "--z3rlimit 64 --z3cliopt smt.arith.nl=false --query_stats --initial_ifuel 1 --max_ifuel 1"
// --smtencoding.elim_box true --smtencoding.l_arith_repr native"

inline_for_extraction
let validate32_sum_aux
  (t: sum)
  (#kt: parser_kind)
  (#p: parser kt (sum_repr_type t))
  (v: validator32 p)
  (p32: parser32 p)
  (pc: ((x: sum_key t) -> Tot (k: parser_kind & parser k (sum_type_of_tag t x))))
  (pc32: ((x: sum_key t) -> Tot (validator32 (dsnd (pc x)))))
//  (destr: dep_maybe_enum_destr_t (sum_enum t)  
: Tot (validator32 (parse_sum t p pc))
= fun input len ->
  let h = HST.get () in
  parse_sum_eq'' t p pc (B.as_seq h input);
  let len_after_tag = v input len in
  if len_after_tag `I32.lt` 0l
  then len_after_tag
  else begin
    let h1 = HST.get () in
    let k' = p32 input in
    let off = Cast.int32_to_uint32 (len `I32.sub` len_after_tag) in
    let input_k = B.offset input off in
    assert (U32.v off == I32.v len - I32.v len_after_tag);
    assert (parse p (B.as_seq h input) == Some (k', U32.v off));
    let k = maybe_enum_key_of_repr (sum_enum t) k' in
    match k with
    | Known k ->
      synth_sum_case_injective t k;
      let h2 = HST.get () in
      let res = validate32_synth (pc32 k) (synth_sum_case t k) () input_k len_after_tag in
      assert (B.as_seq h1 input == B.as_seq h input);
      assert (B.as_seq h2 input == B.as_seq h input);
      assert (B.as_seq h2 input_k == B.as_seq h input_k);
      admit ();
      res
(*      
      if res `I32.lt` 0l
      then
        res
      else begin
        admit ();
        res
      end
*)      
    | _ -> (-1l)
  end
