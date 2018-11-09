module LowParse.Low.VLData.Aux
open LowParse.Low.Combinators

module B = LowStar.Buffer
module E = LowParse.BigEndianImpl.Low
module HST = FStar.HyperStack.ST

let read_bounded_integer_1 _ : (leaf_reader (parse_bounded_integer 1)) =
  decode_bounded_integer_injective 1;
  make_total_constant_size_reader 1 1ul #(bounded_integer 1) (decode_bounded_integer 1) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_1 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

let read_bounded_integer_2 _ : (leaf_reader (parse_bounded_integer 2)) =
  decode_bounded_integer_injective 2;
  make_total_constant_size_reader 2 2ul #(bounded_integer 2) (decode_bounded_integer 2) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_2 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

let read_bounded_integer_3 _ : (leaf_reader (parse_bounded_integer 3)) =
  decode_bounded_integer_injective 3;
  make_total_constant_size_reader 3 3ul #(bounded_integer 3) (decode_bounded_integer 3) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_3 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

let read_bounded_integer_4 _ : (leaf_reader (parse_bounded_integer 4)) =
  decode_bounded_integer_injective 4;
  make_total_constant_size_reader 4 4ul #(bounded_integer 4) (decode_bounded_integer 4) () (fun input ->
    let h = HST.get () in
    let r = E.be_to_n_4 _ _ (E.u32 ()) input in
    E.lemma_be_to_n_is_bounded (B.as_seq h input);
    r
  )

inline_for_extraction
let serialize32_bounded_integer_1 () : Tot (serializer32 (serialize_bounded_integer 1)) =
  fun (v: bounded_integer 1) out ->
  let out' = B.sub out 0ul 1ul in
  E.n_to_be_1 _ _ (E.u32 ()) v out';
  1ul

inline_for_extraction
let serialize32_bounded_integer_2 () : Tot (serializer32 (serialize_bounded_integer 2)) =
  fun (v: bounded_integer 2) out ->
  let out' = B.sub out 0ul 2ul in
  E.n_to_be_2 _ _ (E.u32 ()) v out';
  2ul

inline_for_extraction
let serialize32_bounded_integer_3 () : Tot (serializer32 (serialize_bounded_integer 3)) =
  fun (v: bounded_integer 3) out ->
  let out' = B.sub out 0ul 3ul in
  E.n_to_be_3 _ _ (E.u32 ()) v out';
  3ul

inline_for_extraction
let serialize32_bounded_integer_4 () : Tot (serializer32 (serialize_bounded_integer 4)) =
  fun (v: bounded_integer 4) out ->
  let out' = B.sub out 0ul 4ul in
  E.n_to_be_4 _ _ (E.u32 ()) v out';
  4ul

let write_bounded_integer_1 _ = leaf_writer_strong_of_serializer32 (serialize32_bounded_integer_1 ()) ()

let write_bounded_integer_2 _ = leaf_writer_strong_of_serializer32 (serialize32_bounded_integer_2 ()) ()

let write_bounded_integer_3 _ = leaf_writer_strong_of_serializer32 (serialize32_bounded_integer_3 ()) ()

let write_bounded_integer_4 _ = leaf_writer_strong_of_serializer32 (serialize32_bounded_integer_4 ()) ()
