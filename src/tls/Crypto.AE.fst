module Crypto.AE
open Crypto.AEAD

module U8 = FStar.UInt8
module Seq = FStar.Seq
module EC = EverCrypt.AEAD
module SC = Spec.Agile.AEAD
module B = LowStar.Buffer
module U32 = FStar.UInt32
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module EE = EverCrypt.Error
module G = FStar.Ghost
module F = Flags
module E = EverCrypt
module ES = EverCrypt.Specs
module Model = Model.AE
module MU = Model.Utils

friend Crypto.AEAD // needed because of the definition of state for model

open Declassify

let encrypt #a #phi s plain plain_len cipher = 
  let h0 = HST.get () in
  if F.model
  then begin
    let s : Model.state a phi = s in
    let plain_s = MU.get_buffer plain plain_len in
    let cipher_len = iv_len `U32.add` plain_len `U32.add` tag_len a in
    let h1 = HST.get () in
    Model.frame_invariant h0 s B.loc_none h1;
    let cipher_s = Model.encrypt s plain_s in
    let h2 = HST.get () in
    MU.put_buffer cipher cipher_len cipher_s;
    let h3 = HST.get () in
    Model.frame_invariant h2 s (B.loc_buffer cipher) h3
  end else begin
    let iv = B.sub cipher 0ul iv_len in
    Random.sample_secret_buffer iv_len iv;
    let h2 = HST.get () in
    frame_invariant h0 s (B.loc_buffer cipher) h2;
    encrypt s plain plain_len cipher
  end
