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
module MITLS.Repr.CertificateRequest13
(* Summary:

   This module encapsulates wire-format representations of
   Parsers.CertificateRequest13.certificateRequest13

*)
module LP = LowParse.Low.Base
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module R = LowParse.Repr
module CR13 = Parsers.CertificateRequest13

let ptr = R.repr_ptr_p _ CR13.certificateRequest13_parser
let pos (b:R.const_slice) = R.repr_pos_p _ b CR13.certificateRequest13_parser
