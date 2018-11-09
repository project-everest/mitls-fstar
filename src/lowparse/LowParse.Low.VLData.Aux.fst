module LowParse.Low.VLData.Aux
open LowParse.Low.Combinators

module B = LowStar.Buffer
module E = LowParse.BigEndianImpl.Low
module HST = FStar.HyperStack.ST

inline_for_extraction
let read_bounded_integer_1 _ : (leaf_reader (parse_bounded_integer 1)) =
  decode_bounded_integer_injective 1;
  make_total_constant_size_reader 1 1ul #(bounded_integer 1) (decode_bounded_integer 1) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_1 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

inline_for_extraction
let read_bounded_integer_2 _ : (leaf_reader (parse_bounded_integer 2)) =
  decode_bounded_integer_injective 2;
  make_total_constant_size_reader 2 2ul #(bounded_integer 2) (decode_bounded_integer 2) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_2 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

inline_for_extraction
let read_bounded_integer_3 _ : (leaf_reader (parse_bounded_integer 3)) =
  decode_bounded_integer_injective 3;
  make_total_constant_size_reader 3 3ul #(bounded_integer 3) (decode_bounded_integer 3) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_3 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

inline_for_extraction
let read_bounded_integer_4 _ : (leaf_reader (parse_bounded_integer 4)) =
  decode_bounded_integer_injective 4;
  make_total_constant_size_reader 4 4ul #(bounded_integer 4) (decode_bounded_integer 4) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_4 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )
