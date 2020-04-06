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
module R = LowParse.Repr
module CH = Parsers.ClientHello


let ptr = R.repr_ptr_p CH.clientHello CH.clientHello_parser
let stable_ptr = p:ptr { R.is_stable_in_region p }
let pos (b:R.const_buffer) = R.repr_pos_p CH.clientHello b CH.clientHello_parser

/// Reader for the protocol version
unfold
let version_reader =
  R.FieldReader
    CH.accessor_clientHello_version
    Parsers.ProtocolVersion.protocolVersion_reader

/// Accessor for the extensions
unfold
let extensions_field =
  R.FieldAccessor CH.accessor_clientHello_extensions
                  Parsers.ClientHelloExtensions.clientHelloExtensions_jumper
                  Parsers.ClientHelloExtensions.clientHelloExtensions_parser32
