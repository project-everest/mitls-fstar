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
module MITLS.Repr.SHKind
module LP = LowParse.Low.Base
module R = LowParse.Repr
include Parsers.SHKind
module SHK = Parsers.SHKind

let t = SHK.sHKind
let ptr = R.repr_ptr_p t SHK.sHKind_parser
let pos (b:R.const_buffer) = R.repr_pos_p t b SHK.sHKind_parser

let field_cipherSuite =
  R.FieldReader
    SHK.accessor_sHKind_cipher_suite
    Parsers.CipherSuite.cipherSuite_reader
