module Crypto.AE
open Crypto.AEAD

module U8 = FStar.UInt8
module Seq = FStar.Seq
module EC = EverCrypt.AEAD
module SC = Spec.AEAD
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module EE = EverCrypt.Error
module G = FStar.Ghost
module F = Flags
module Cast = Crypto.Util.IntCast
module E = EverCrypt
module ES = EverCrypt.Specs

friend Crypto.AEAD

let encrypt
  #a #phi s plain plain_len cipher
= let h0 = HST.get () in
  assume (F.model == false);
  begin
    let iv = B.sub cipher 0ul iv_len in
    let h1 = HST.get () in
    Cast.live_to_buf_sec8 iv h1;
    Random.sample_buffer iv_len (Cast.to_buf_sec8 iv);
    Cast.loc_buffer_to_buf_sec8 iv;
    let h2 = HST.get () in
    frame_invariant h0 s (B.loc_buffer cipher) h2;
    encrypt s plain plain_len cipher
  end
