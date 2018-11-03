module LowParse.SLow.VLData.Header

friend LowParse.Spec.VLData.Header

module Seq = FStar.Seq
module U32 = FStar.UInt32
module E = LowParse.BigEndianImpl.SLow
module B32 = LowParse.Bytes32

let serialize32_bounded_integer_1
= (fun (input: bounded_integer 1) ->
    let b = E.n_to_be_1 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 1) input res } ))
  )

let serialize32_bounded_integer_2
= (fun (input: bounded_integer 2) ->
    let b = E.n_to_be_2 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 2) input res } ))
  )

let serialize32_bounded_integer_3
= (fun (input: bounded_integer 3) ->
    let b = E.n_to_be_3 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 3) input res } ))
  )

let serialize32_bounded_integer_4
= (fun (input: bounded_integer 4) ->
    let b = E.n_to_be_4 _ _ (E.u32 ()) input in
    (b <: (res: B32.bytes { serializer32_correct (serialize_bounded_integer 4) input res } ))
  )

let decode32_bounded_integer_1 b
= let r = E.be_to_n_1 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 1 { r == decode_bounded_integer 1 (B32.reveal b) } ))

let decode32_bounded_integer_2 b
= let r = E.be_to_n_2 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 2 { r == decode_bounded_integer 2 (B32.reveal b) } ))

let decode32_bounded_integer_3 b
= let r = E.be_to_n_3 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 3 { r == decode_bounded_integer 3 (B32.reveal b) } ))

let decode32_bounded_integer_4 b
= let r = E.be_to_n_4 _ _ (E.u32 ()) b in
  E.lemma_be_to_n_is_bounded (B32.reveal b);
  (r <: (r: bounded_integer 4 { r == decode_bounded_integer 4 (B32.reveal b) } ))

