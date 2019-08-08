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
module Model = Model.AE
module MU = Model.Utils
module Cast = Crypto.Util.IntCast

friend Crypto.AEAD // needed because of the definition of state for model

let encrypt
  #a #phi s plain plain_len cipher
= let h0 = HST.get () in
  if F.model
  then begin
    let s : Model.state a (mphi phi) = s in
    let plain_s = MU.get_buffer plain plain_len in
    let plain_s_sec = Cast.to_seq_sec8 plain_s in
    let cipher_len = iv_len `U32.add` plain_len `U32.add` tag_len a in
    let h1 = HST.get () in
    Model.frame_invariant h0 s B.loc_none h1;
    Cast.to_seq_uint8_to_seq_sec8 plain_s;
    let cipher_s_sec = Model.encrypt s plain_s_sec in
    let h2 = HST.get () in
    Cast.live_to_buf_sec8 cipher h2;
    MU.put_buffer (Cast.to_buf_sec8 cipher) cipher_len cipher_s_sec;
    let h3 = HST.get () in
    Cast.loc_buffer_to_buf_sec8 cipher;
    Cast.to_seq_sec8_as_seq_gsub h3 cipher 0ul iv_len;
    Cast.to_seq_sec8_as_seq_gsub h3 cipher iv_len (B.len cipher `U32.sub` iv_len);
    Model.frame_invariant h2 s (B.loc_buffer cipher) h3;
    EE.Success
  end else begin
    let iv = B.sub cipher 0ul iv_len in
    let h1 = HST.get () in
    Cast.live_to_buf_sec8 iv h1;
    Random.sample_secret_buffer iv_len (Cast.to_buf_sec8 iv);
    Cast.loc_buffer_to_buf_sec8 iv;
    let h2 = HST.get () in
    frame_invariant h0 s (B.loc_buffer cipher) h2;
    encrypt s plain plain_len cipher
  end
