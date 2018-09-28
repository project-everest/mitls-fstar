module LowParseExample6

open FStar.HyperStack.ST
open FStar.Bytes
open FStar.HyperStack.IO
open FStar.Printf

module AUX = LowParseExample6.Aux

#reset-options "--using_facts_from '* -LowParse +LowParse.Spec.Base +LowParse.SLow.Base'"

let f (input: FStar.Bytes.bytes) : Pure (option (AUX.t * FStar.UInt32.t))
  (requires True)
  (ensures (fun res ->
    match res with
    | None -> True
    | Some (_, consumed) -> FStar.UInt32.v consumed <= FStar.Bytes.length input
  ))
= [@inline_let]
  let res = AUX.parse32_t input in
  [@inline_let]
  let _ = LowParse.SLow.Base.parser32_consumes AUX.parse32_t input in
  res

(*
let m (x: AUX.t) : Tot FStar.Bytes.bytes =
  AUX.serialize32_t x
*)

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) ->
  Stack C.exit_code (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  push_frame ();
//  test ();
  pop_frame ();
  C.EXIT_SUCCESS
