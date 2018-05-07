module LowParseExample

#reset-options "--using_facts_from '* -LowParse +LowParse.Spec.Base +LowParse.SLow.Base'"

let f (input: FStar.Bytes.bytes) : Pure (option (LowParseExample.Aux.t * FStar.UInt32.t))
  (requires True)
  (ensures (fun res ->
    match res with
    | None -> True
    | Some (_, consumed) -> FStar.UInt32.v consumed <= FStar.Bytes.length input
  ))
= [@inline_let]
  let res = LowParseExample.Aux.parse32_t input in
  [@inline_let]
  let _ = LowParse.SLow.Base.parser32_consumes LowParseExample.Aux.parse32_t input in
  res

let g (input: FStar.Bytes.bytes) : Tot (option (LowParse.SLow.array LowParseExample.Aux.t 18 * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t_array input

let j (input: FStar.Bytes.bytes) : Tot (option (LowParse.SLow.vlarray LowParseExample.Aux.t 5 7 * FStar.UInt32.t)) =
  LowParseExample.Aux.parse32_t_vlarray input

let m (x: LowParseExample.Aux.t) : Tot FStar.Bytes.bytes =
  LowParseExample.Aux.serialize32_t x

let s (x: LowParse.SLow.array LowParseExample.Aux.t 18) : Tot FStar.Bytes.bytes =
  LowParseExample.Aux.serialize32_t_array x

let main () : Tot FStar.Int32.t = 0l
