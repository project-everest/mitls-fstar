module Bytes = struct

  type byte = char
  type bytes = string

  let abytes x = x
  let cbytes x = x

end

module CoreKeys = struct

  open Bytes

  type modulus  = bytes
  type exponent = bytes

  type rsapkey = modulus * exponent
  type rsaskey = modulus * exponent

  type dsaparams = { p : bytes; q : bytes; g : bytes; }

  type dsapkey = bytes * dsaparams
  type dsaskey = bytes * dsaparams

  type dhparams = { p : bytes; g : bytes; q: bytes option }

  type dhpbytes = bytes
  type dhsbytes = bytes

  type dhpkey = dhpbytes * dhparams
  type dhskey = dhsbytes * dhparams

end

module CoreACiphers = struct 

(* -------------------------------------------------------------------- *)
  open Bytes
  open Evp.RSA

(* -------------------------------------------------------------------- *)
  type modulus  = bytes
  type exponent = bytes

(* -------------------------------------------------------------------- *)
  type sk = RSASKey of CoreKeys.rsaskey
  type pk = RSAPKey of CoreKeys.rsapkey

  type plain = bytes
  type ctxt  = bytes

  let gen_key () = 
    let k  = Evp.RSA.genkey 2048 65537 in
    let pk = RSAPKey (abytes k.k_mod, abytes k.k_pub_exp) in
    match k.k_prv_exp with 
    | Some sk -> (RSASKey (abytes k.k_mod,abytes sk),pk)
    | None -> failwith "RSA_generate_key returned an empty private key"

(* -------------------------------------------------------------------- *)
  let encrypt_pkcs1 (RSAPKey (m, e)) (x : plain) =
    let r = create () in
    setkey r { k_mod = cbytes m; k_pub_exp = cbytes e; k_prv_exp = None; };
    let y = abytes (encrypt r false PD_PKCS1 (cbytes x)) in
    fini r; y

(* -------------------------------------------------------------------- *)
  let decrypt_pkcs1 (RSASKey (m, e)) (x : ctxt) =
    let r = create () in
    setkey r { k_mod = cbytes m; k_pub_exp = cbytes e; k_prv_exp = Some (cbytes e); };
    let y = abytes (decrypt r true PD_PKCS1 (cbytes x)) in
    fini r; Some y

end

module CoreHMac = struct

  open Bytes

  type engine = HMac of CoreCrypto.hmac
  type key    = bytes

  let name (HMac engine) =
    engine.hm_name

  let mac (HMac engine) (b : bytes) =
    abytes (engine.hm_process(cbytes b))

  let md5engine    (k : key) = HMac (CoreCrypto.hmac "MD5"    (cbytes k))
  let sha1engine   (k : key) = HMac (CoreCrypto.hmac "SHA1"   (cbytes k))
  let sha256engine (k : key) = HMac (CoreCrypto.hmac "SHA256" (cbytes k))
  let sha384engine (k : key) = HMac (CoreCrypto.hmac "SHA384" (cbytes k))
  let sha512engine (k : key) = HMac (CoreCrypto.hmac "SHA512" (cbytes k))

  let dohmac (factory : key -> engine) (k : key) (data : bytes) =
    mac (factory k) data

  let md5    (k : key) (data : bytes) = dohmac md5engine    k data
  let sha1   (k : key) (data : bytes) = dohmac sha1engine   k data
  let sha256 (k : key) (data : bytes) = dohmac sha256engine k data
  let sha384 (k : key) (data : bytes) = dohmac sha384engine k data
  let sha512 (k : key) (data : bytes) = dohmac sha512engine k data

end

module CoreRandom = struct

  let rng = Random.self_init ()

(* -------------------------------------------------------------------- *)
  let random (i : int) =
    if i < 0 then
      invalid_arg "length must be non-negative";

    let s = String.create i in

    for i = 0 to i-1 do
      s.[i] <- char_of_int (Random.int 256)
    done;

    Bytes.abytes s

end

module CoreCiphers = struct 

  open Bytes
  open CoreCrypto

(* -------------------------------------------------------------------- *)
  type key = bytes
  type iv  = bytes

(* -------------------------------------------------------------------- *)
  let encrypt cipher omode key plain =
    let engine = blockcipher ForEncryption cipher omode (cbytes key) in
    abytes (engine.bc_process (cbytes plain))

(* -------------------------------------------------------------------- *)
  let decrypt cipher omode key encrypted =
    let engine = CoreCrypto.blockcipher ForDecryption cipher omode (cbytes key) in
    abytes (engine.bc_process (cbytes encrypted))

(* -------------------------------------------------------------------- *)
  let aes_cbc_encrypt key iv plain     = encrypt AES (Some (CBC (cbytes iv))) key plain
  let aes_cbc_decrypt key iv encrypted = decrypt AES (Some (CBC (cbytes iv))) key encrypted

(* -------------------------------------------------------------------- *)
  let des3_cbc_encrypt key iv plain     = encrypt DES3 (Some (CBC (cbytes iv))) key plain
  let des3_cbc_decrypt key iv encrypted = decrypt DES3 (Some (CBC (cbytes iv))) key encrypted

(* -------------------------------------------------------------------- *)
  type rc4engine = RC4Engine of streamcipher

  let rc4create (key : key) =
    RC4Engine (CoreCrypto.streamcipher ForEncryption RC4 (cbytes key))

  let rc4process (RC4Engine engine) (input : bytes) =
    abytes (engine.sc_process (cbytes input))

  let aes_gcm_encrypt (key:key) (iv:iv) (ad:bytes) (plain:bytes) = failwith "unimplemented"
  let aes_gcm_decrypt (key:key) (iv:iv) (ad:bytes) (plain:bytes) = failwith "unimplemented"

end

module CoreHash = struct 

  open Bytes
    
  type engine = Engine of string * Evp.MD.md

  (* -------------------------------------------------------------------- *)
  let name (Engine (name, m)) =
    name

  let digest (Engine (name, m)) b = 
    let e = Evp.MD.create m in
    Evp.MD.update e (cbytes b);
    let h = Evp.MD.final e in
    Evp.MD.fini e; abytes h

  (* -------------------------------------------------------------------- *)
  let md5engine    () = Engine ("MD5"   , Evp.MD.md5    ())
  let sha1engine   () = Engine ("SHA1"  , Evp.MD.sha1   ())
  let sha256engine () = Engine ("SHA256", Evp.MD.sha256 ())
  let sha384engine () = Engine ("SHA384", Evp.MD.sha384 ())
  let sha512engine () = Engine ("SHA512", Evp.MD.sha512 ())

  (* -------------------------------------------------------------------- *)
  let md5    b = digest (md5engine    ()) b
  let sha1   b = digest (sha1engine   ()) b
  let sha256 b = digest (sha256engine ()) b
  let sha384 b = digest (sha384engine ()) b
  let sha512 b = digest (sha512engine ()) b

end

module CoreSig = struct 

  open Bytes

(* ------------------------------------------------------------------------ *)
  type sighash =
    | SH_MD5
    | SH_SHA1
    | SH_SHA256
    | SH_SHA384

  type sigalg =
    | CORE_SA_RSA
    | CORE_SA_DSA

(* ------------------------------------------------------------------------ *)
  type sigskey =
    | SK_RSA of CoreKeys.rsaskey
    | SK_DSA of CoreKeys.dsaskey

  type sigpkey =
    | PK_RSA of CoreKeys.rsapkey
    | PK_DSA of CoreKeys.dsapkey

  let sigalg_of_skey = function
    | SK_RSA _ -> CORE_SA_RSA
    | SK_DSA _ -> CORE_SA_DSA

  let sigalg_of_pkey = function
    | PK_RSA _ -> CORE_SA_RSA
    | PK_DSA _ -> CORE_SA_DSA

(* -------------------------------------------------------------------- *)
  type text = bytes
  type sigv = bytes

(* -------------------------------------------------------------------- *)
  let gen = function
    | CORE_SA_RSA -> begin
      let k  = Evp.RSA.genkey 2048 65537 in
      let pk = PK_RSA (abytes k.k_mod, abytes k.k_pub_exp) in

      match k.k_prv_exp with 
      | Some sk -> (pk, SK_RSA (abytes k.k_mod,abytes sk))
      | None -> failwith "RSA_generate_key returned an empty private key"
    end

    | CORE_SA_DSA -> begin
      let p = Evp.DSA.genparams 2048 in
      let k = Evp.DSA.genkey p in

      let pr : CoreKeys.dsaparams = {
	p = abytes p.p; g = abytes p.g; q = abytes p.q;
      } in

      let pk = PK_DSA (abytes k.k_public, pr) in

      match k.k_private with 
      | Some sk -> (pk, SK_DSA (abytes sk, pr))
      | None -> failwith "DSA_generate_key returned an empty private key"
    end

(* -------------------------------------------------------------------- *)
  let sign ag k t =
    match k with 
    | SK_RSA (m, sk) -> 
       let r = Evp.RSA.create () in

       Evp.RSA.setkey r
         { k_mod     = cbytes m;
           k_pub_exp = cbytes sk;
           k_prv_exp = Some (cbytes sk); };

       let h = 
         match ag with 
         | None
         | Some SH_SHA1   -> Evp.RSA.sign r Evp.RSA.SHA1   (cbytes t)
         | Some SH_MD5    -> Evp.RSA.sign r Evp.RSA.MD5    (cbytes t)
         | Some SH_SHA256 -> Evp.RSA.sign r Evp.RSA.SHA256 (cbytes t)
         | Some SH_SHA384 -> Evp.RSA.sign r Evp.RSA.SHA384 (cbytes t)

       in Evp.RSA.fini r; abytes h

    | SK_DSA(sk, pr) -> 
       let r = Evp.DSA.create () in

       Evp.DSA.setkey r
         { k_params  = { p= cbytes pr.p; q = cbytes pr.q; g = cbytes pr.g}; 
           k_public  = cbytes sk;
           k_private = Some (cbytes sk); };

       let h = Evp.DSA.sign r (cbytes t) in

       Evp.DSA.fini r; abytes h

(* -------------------------------------------------------------------- *)
  let verify ag k t h = 
    match k with 
    | PK_RSA (m, pk) ->   
       let r = Evp.RSA.create () in

       Evp.RSA.setkey r {
         k_mod     = cbytes m;
         k_pub_exp = cbytes pk;
         k_prv_exp = None; };

       let b = 
         match ag with 
         | None
         | Some SH_SHA1   -> Evp.RSA.verify r Evp.RSA.SHA1   (cbytes t) (cbytes h)
         | Some SH_MD5    -> Evp.RSA.verify r Evp.RSA.MD5    (cbytes t) (cbytes h)
         | Some SH_SHA256 -> Evp.RSA.verify r Evp.RSA.SHA256 (cbytes t) (cbytes h)
         | Some SH_SHA384 -> Evp.RSA.verify r Evp.RSA.SHA384 (cbytes t) (cbytes h)

       in Evp.RSA.fini r; b   

    | PK_DSA (pk, pr) -> 
       let r = Evp.DSA.create () in

       Evp.DSA.setkey r {
         k_params  = { p = cbytes pr.p; q = cbytes pr.q; g = cbytes pr.g; };
         k_public  = cbytes pk;
         k_private = None; };

       let b = Evp.DSA.verify r (cbytes t) (cbytes h) in

       Evp.DSA.fini r; b

end

module CoreDH = struct
    
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

end
