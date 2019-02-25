module TestPair
module P = Pair
open LowParse.MLow
module U8 = FStar.UInt8
module FB = LowStar.FreezableBuffer
module LM = LowParseExampleMono

assume val buf :
  s:slice FB.freezable_preorder FB.freezable_preorder{
    FB.recallable s.base /\
    UInt32.v (s.len) >= 4 /\
    FB.witnessed s.base (FB.w_pred 4)
  }
let irepr #t #k (p:parser k t) = LM.irepr p buf

module LPI = LowParse.Spec.AllIntegers

open FStar.HyperStack.ST
assume val havoc : unit -> Stack unit (fun h -> True) (fun _ _ _ -> True)

let read_components (i:irepr P.pair_parser)
  : Stack (UInt32.t * UInt32.t)
    (requires fun h ->
      True)
    (ensures fun h0 x h1 ->
      True)
  = LM.recall_valid i;
    let x = P.accessor_pair_fst buf (IRepr?.pos i) in
    havoc();
    LM.recall_valid i;
    let y : UInt32.t = P.accessor_pair_snd buf (IRepr?.pos i) in
    x, y

module B = LowStar.Buffer
assume val frozen_until (f:FB.fbuffer)
  : Stack UInt32.t
    (requires fun h ->
      FB.recallable f \/ B.live h f)
    (ensures fun h0 x h1 ->
      h0 == h1 /\
      FB.get_w (B.as_seq h0 f) == UInt32.v x)

let read_components2 (i:irepr P.pair_parser)
  : Stack (irepr LPI.parse_u32 * irepr LPI.parse_u16)
    (requires fun h ->
      True)
    (ensures fun h0 x h1 ->
      True)
  = LM.recall_valid i;
    let x = P.accessor_pair_fst buf (IRepr?.pos i) in
    FB.recall_w_default buf.base;
    assert (UInt32.v x >= 4);
    let h = get () in
    let len = frozen_until buf.base in
    assert (FStar.UInt32.(get_valid_pos LPI.parse_u32 h buf x <=^ len));
    let x : irepr LPI.parse_u32 = LM.witness_valid buf x in

    havoc();

    LM.recall_valid i;
    let y : UInt32.t = P.accessor_pair_snd buf (IRepr?.pos i) in
    FB.recall_w_default buf.base;
    assert (UInt32.v y >= 4);
    let h = get () in
    let len = frozen_until buf.base in
    assert (FStar.UInt32.(get_valid_pos LPI.parse_u16 h buf y <=^ len));
    let y : irepr LPI.parse_u16 = LM.witness_valid buf y in
    x, y
