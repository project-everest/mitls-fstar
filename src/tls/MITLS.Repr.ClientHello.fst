(*
  Copyright 2015--2019 INRIA and Microsoft Corporation

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.

  Authors: T. Ramananandro, A. Rastogi, N. Swamy
*)
module MITLS.Repr.ClientHello
(* Summary:

   This module encapsulates wire-format representations of
   Parsers.ClientHello messages.

   Its main type, `repr b` is an instance of MITLS.Repr.repr
   instantiated with clientHello_parser
*)
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = LowParse.Repr
module CH = Parsers.ClientHello
module C = LowStar.ConstBuffer
module R_CHE = MITLS.Repr.ClientHelloExtensions
open FStar.Integers
open FStar.HyperStack.ST

let ptr = R.repr_ptr_p CH.clientHello CH.clientHello_parser
let pos (b:R.const_slice) = R.repr_pos_p CH.clientHello b CH.clientHello_parser

/// Reader for the protocol version
///   returns a value, since this is a leaf reader
let version (p:ptr)
  : Stack Parsers.ProtocolVersion.protocolVersion
    (requires R.valid p)
    (ensures fun h0 pv h1 ->
      B.modifies B.loc_none h0 h1 /\
      pv == (R.value p).CH.version)
  = R.reveal_valid();
    let b = R.temp_slice_of_repr_ptr p in
    let pos = CH.accessor_clientHello_version b 0ul in
    Parsers.ProtocolVersion.protocolVersion_reader b pos

/// To read a field from a positional repr,
/// just use the pointer reader
let pos_version (#b:R.const_slice) (r:pos b)
  : Stack Parsers.ProtocolVersion.protocolVersion
    (requires R.repr_pos_valid r)
    (ensures fun h0 pv h1 ->
      B.modifies B.loc_none h0 h1 /\
      pv == (R.value_pos r).CH.version)
  = version (R.as_ptr r)

/// Accessor for the extensions
///    returns a pointer, since it is a variable-length field
///    and offsets to enable positional representations
inline_for_extraction
private
let extensions' (p:ptr)
  : Stack (R_CHE.ptr & uint_32 & uint_32)
    (requires R.valid p)
    (ensures fun h0 (e_ptr, pos, len) h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid e_ptr h1 /\
      R.value e_ptr == (R.value p).CH.extensions /\
      (R.Ptr?.b e_ptr `C.const_sub_buffer pos len` (R.Ptr?.b p)))
  = R.reveal_valid();
    let b = R.temp_slice_of_repr_ptr p in
    let pos = CH.accessor_clientHello_extensions b 0ul in
    let pos_to = Parsers.ClientHelloExtensions.clientHelloExtensions_jumper b pos in
    let e_ptr = R.mk b pos pos_to Parsers.ClientHelloExtensions.clientHelloExtensions_parser32 in
    e_ptr,
    pos,
    pos_to - pos

/// Accessor for the extensions
///    returns a pointer, since it is a variable-length field
let extensions (p:ptr)
  : Stack R_CHE.ptr
    (requires R.valid p)
    (ensures fun h0 e_ptr h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.valid e_ptr h1 /\
      R.value e_ptr == (R.value p).CH.extensions /\
      e_ptr `R.sub_ptr` p)
  =  let e_ptr, _, _ = extensions' p in e_ptr

/// Just for demo purposes: to access a field from a positional repr,
/// just use the pointer accessor
let pos_extensions (#b:R.const_slice) (r:pos b)
  : Stack (R_CHE.pos b)
    (requires R.repr_pos_valid r)
    (ensures fun h0 es h1 ->
      B.modifies B.loc_none h0 h1 /\
      R.repr_pos_valid es h1)
  = let p, pos, len = extensions' (R.as_ptr r) in
    let open R in
    R.as_repr_pos b (r.start_pos + pos) (r.start_pos + pos + len) p
