(* ------------------------------------------------------------------------ *)
open Bytes
open CoreKeys

(* ------------------------------------------------------------------------ *)
type skey = dhskey
type pkey = dhpkey

(* ------------------------------------------------------------------------ *)
(* EVP compute_key performs its checks *)
let check_element (pbytes:bytes) (gbytes:bytes) (ebytes:bytes) =
  true 

(* To-Do *)
let check_params (pbytes:bytes) (gbytes:bytes) =
  true 

(* ------------------------------------------------------------------------ *)
let gen_params () : dhparams =
    let pr = Evp.DH.genparams 1024 80 in
    let x:dhparams = {p = abytes pr.p; g = abytes pr.g; q = None} in
    x

(* ------------------------------------------------------------------------ *)
let gen_key (dh : dhparams) : skey * pkey =
    let k = Evp.DH.genkey {p = cbytes dh.p; g = cbytes dh.g} in
    (match k.k_private with
      Some pk ->  (abytes pk,dh)
     |None -> failwith "Evp.DH.genkey returned an empty private key"),
    (abytes k.k_public,dh) 
(* ------------------------------------------------------------------------ *)
let agreement (dh : dhparams) (x : dhsbytes) (y : dhpbytes) : bytes =
    let d = Evp.DH.create () in
    Evp.DH.setkey d {
      k_params  = { p = cbytes dh.p; g = cbytes dh.g; };
      k_public  = cbytes y;
      k_private = None; };
    let k = Evp.DH.compute d (cbytes x) in
    Evp.DH.fini d; abytes k

(* ------------------------------------------------------------------------ *)
let const_PEM_DH_PARAMETERS_HEADER = "DH PARAMETERS"

let dhparams = "-----BEGIN DH PARAMETERS-----\
MIIBBwKBgQCctCTvtt225fYth0f8s/s+3K27xVqzrDf4fvgrmLj7OGSoJlghp6pQ\
8nEGD+8jRQWak9JMrz1OlQ00YnaYuHb9QyO92O5ZVoBTXcZ07EUycXCWPmJaXUm2\
X9XGm5BGhfncqc354ixfrt/+oi9h1PscSfiJvjC0rAjtfcE5xVHMNwKBgE/5q47Z\
JhFd6fQhUYfiVyNuolP6z0FCZKrmLa9C6UgPLVTfEEOiW6KsCFh5uiCNYcINDZnb\
lInlgrHXG2tlv4/QNCXmXBQeUBkVM+4EXOl2ZciEvFv2zAlkUig/CUcLGo/OwsJV\
c8o7MMjRcCH7fDi4BIAzdEKdDYB7uEqnGJgn\
-----END DH PARAMETERS-----"

(* ------------------------------------------------------------------------ *)
let save_params_to_file (file : string) (dh : dhparams) =
    failwith "DH unimplemented"
(*
    let filestream = new FileStream(file, FileMode.Create, FileAccess.Write) in

    try
        try
            save_params filestream dh
            true
        finally
            filestream.Close()
    with _ ->
        false
*)
(* ------------------------------------------------------------------------ *)
let load_params_from_file (file : string) : dhparams option =
    failwith "DH unimplemented"
(*
    let filestream = new FileStream(file, FileMode.Open, FileAccess.Read) in

    try
        try
            Some (load_params filestream)
        finally
            filestream.Close()
    with _ -> None
*)

(* ------------------------------------------------------------------------ *)
let load_default_params () =
    failwith "DH unimplemented"
(*
    try
        load_params (new MemoryStream(Encoding.ASCII.GetBytes(dhparams), false))
    with _ ->
        failwith "cannot load default DH parameters"
*)
