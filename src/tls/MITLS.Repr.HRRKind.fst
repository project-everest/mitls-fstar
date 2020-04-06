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
module MITLS.Repr.HRRKind
(* Summary:

   This module encapsulates wire-format representations of
   Parsers.ServerHello messages.

   Its main type, `repr b` is an instance of MITLS.Repr.repr
   instantiated with serverHello_parser
*)
module LP = LowParse.Low.Base
module R = LowParse.Repr
include Parsers.HRRKind
module HRK = Parsers.HRRKind

let t = HRK.hRRKind
let ptr = R.repr_ptr_p t HRK.hRRKind_parser
let pos (b:R.const_buffer) = R.repr_pos_p t b HRK.hRRKind_parser

let field_cipherSuite =
  R.FieldReader
    HRK.accessor_hRRKind_cipher_suite
    Parsers.CipherSuite.cipherSuite_reader
