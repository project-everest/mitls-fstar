module LowParse.SLow.Sum
include LowParse.Spec.Sum
include LowParse.SLow.Enum

module B32 = FStar.Bytes
module U32 = FStar.UInt32

#set-options "--z3rlimit 16"

inline_for_extraction
let parse32_sum_gen
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (pc x))))
: Tot (parser32 (parse_sum t p pc))
= fun (input: bytes32) -> ((
    match p32 input with
    | Some (tg, consumed_tg) ->
      let input' = b32slice input consumed_tg (B32.len input) in 
      begin match pc32 tg input' with
      | Some (d, consumed_d) ->
        // FIXME: implicit arguments are not inferred because (synth_tagged_union_data ...) is Tot instead of GTot
        assert (parse (parse_synth #_ #_ #(sum_type t) (pc tg) (synth_tagged_union_data (sum_tag_of_data t) tg)) (B32.reveal input') == Some (d, U32.v consumed_d));
        Some (d, U32.add consumed_tg consumed_d)
      | _ -> None
      end
    | _ -> None
  )
  <: (res: option (sum_type t * U32.t) { parser32_correct (parse_sum t p pc) input res } )
  )

(*
module Seq = FStar.Seq

#set-options "--z3rlimit 32"

let parse32_sum_gen_correct
  (#kt: parser_kind)
  (t: sum)
  (#p: parser kt (sum_repr_type t))
  (p32: parser32 (parse_enum_key p (sum_enum t)))
  (#k: parser_kind)
  (#pc: ((x: sum_key t) -> Tot (parser k (sum_cases t x))))
  (pc32: ((x: sum_key t) -> Tot (parser32 (pc x))))
  (input: bytes32)
: Lemma
  (parser32_correct (parse_sum t p pc) input (parse32_sum_gen' t p32 pc32 input))
=  match p32 input with
  | Some (tg, consumed_tg) ->
    assert (parse (parse_enum_key p (sum_enum t)) (B32.reveal input) == Some (tg, U32.v consumed_tg));
    let input' = b32slice input consumed_tg (B32.len input) in
    assert (B32.reveal input' == Seq.slice (B32.reveal input) (U32.v consumed_tg) (B32.length input));
    let ptg : parser k (refine_with_tag (sum_tag_of_data t) tg) = pc tg in
    begin match pc32 tg input' with
    | Some (d, consumed_d) ->
      assert (parse ptg (B32.reveal input') == Some (d, U32.v consumed_d));
      // FIXME: implicit arguments are not inferred because (synth_tagged_union_data ...) is Tot instead of GTot
      assert (parse (parse_synth #_ #_ #(sum_type t) ptg  (synth_tagged_union_data (sum_tag_of_data t) tg)) (B32.reveal input') == Some (d, U32.v consumed_d));
      ()
    | None -> 
      assert (parse ptg (B32.reveal input') == None);
      ()
    end
  | None -> ()

