(* Copyright (C) 2012--2018 Microsoft Research and INRIA *)
module MiTLS.Cert
open MiTLS

open FStar.Bytes
open FStar.Error

open MiTLS.TLSError
open MiTLS.TLSConstants
open MiTLS.Extensions // defining cert, cert13, chain
module Parse = MiTLS.Parse
open MiTLS.Parse
 
let rec certificateListBytes = function
  | [] -> empty_bytes
  | crt :: rest ->
    lemma_repr_bytes_values (length crt);
    // 2018.03.10 SZ: Can't prove this without refinining [chain]
    assume (UInt.size (3 + length crt + length (certificateListBytes rest)) UInt32.n);
    vlbytes 3 crt @| certificateListBytes rest

let rec certificateListBytes13 = function
  | [] -> empty_bytes
  | (crt, exts) :: rest ->
    lemma_repr_bytes_values (length crt);
    // 2018.03.10 SZ: Can't prove this without refinining [chain13]
    assume (UInt.size (3 + length crt + length (extensionsBytes exts) + length (certificateListBytes13 rest)) UInt32.n);
    vlbytes 3 crt @| extensionsBytes exts @| certificateListBytes13 rest

let rec parseCertificateList b =
  if length b = 0 then Correct [] else
  
  if length b < 3 then fatal Bad_certificate "not enough bytes (certificate length)" else
  match vlsplit 3 b with
  | Error _ -> fatal Bad_certificate "not enough bytes (certificate)"
  | Correct (x) -> (
    let c, r = x in
    match parseCertificateList r with
    | Error z -> Error z
    | Correct cs -> lemma_repr_bytes_values (length c); Correct (c::cs) )

#set-options "--z3rlimit 50" 
let rec parseCertificateList13 b =
  if length b = 0 then Correct [] else
  if length b < 3 then fatal Bad_certificate "not enough bytes (certificate length)" else
  match vlsplit 3 b with
  | Error _ -> fatal Bad_certificate "not enough bytes (certificate)"
  | Correct (x) -> (
    let c, r = x in 
    if length r < 2 then fatal Bad_certificate "not enough bytes (extension length" else
    match vlsplit 2 r with
    | Error _ -> fatal Bad_certificate "not enough bytes (extension list)"
    | Correct (x) -> (
      let e, r = x in
      match parseExtensions EM_Certificate (vlbytes 2 e) with
      | Error z -> Error z
      | Correct (exts,_) -> (
        match parseCertificateList13 r with
        | Error z -> Error z
        | Correct x ->
          if bindersLen exts = 0 then
          begin
            lemma_repr_bytes_values (length c);
            lemma_repr_bytes_values (length (extensionListBytes exts));
            Correct ((c,exts) :: x)
          end
          else fatal Bad_certificate "unexpected extension" )))

#set-options "--z3rlimit 100 --max_ifuel 4"

let rec lemma_parseCertificateList_length b =
  if length b < 3 then ()
  else
    match parseCertificateList b with
    | Correct (hd::tl) ->
      begin
      match vlsplit 3 b with
      | Correct (x) -> 
        let c, r = x in
        lemma_parseCertificateList_length r
      | _ -> ()
      end
    | _ -> ()
