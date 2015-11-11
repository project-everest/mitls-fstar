(* -------------------------------------------------------------------- *)
open Bytes

(* -------------------------------------------------------------------- *)
type key       = cbytes
type iv        = cbytes
type direction = ForEncryption | ForDecryption
type cipher    = AES | DES3
type mode      = CBC of iv
type scipher   = RC4

(* -------------------------------------------------------------------- *)
exception CannotLoadProvider of string
exception NoMessageDigest    of string
exception NoBlockCipher      of cipher * mode option
exception NoStreamCipher     of scipher
exception NoHMac             of string

(* -------------------------------------------------------------------- *)
type blockcipher = {
  bc_name      : string;
  bc_direction : direction;
  bc_blocksize : int;
  bc_process   : cbytes -> cbytes
}

(* ------------------------------------------------------------------------ *)
type streamcipher = {
  sc_name      : string;
  sc_direction : direction;
  sc_process   : cbytes -> cbytes
}

(* ------------------------------------------------------------------------ *)
type hmac = {
  hm_name    : string;
  hm_process : cbytes -> cbytes
}

type messagedigest = {
  md_name   : string;
  md_digest : cbytes -> cbytes
}

(* -------------------------------------------------------------------- *)
let blockcipher (d : direction) (c : cipher) (m : mode option) (k : key) = 
  let alg = 
    match c, m with
    | DES3, None          -> Evp.CIPHER.des_ede3
    | DES3, Some (CBC iv) -> Evp.CIPHER.des_ede3_cbc

    | AES , None when String.length k = (256 / 8) -> Evp.CIPHER.aes_256_ecb
    | AES , Some (CBC iv) when String.length k = (256 / 8) -> Evp.CIPHER.aes_256_cbc

    | AES , None when String.length k = (128 / 8) -> Evp.CIPHER.aes_128_ecb
    | AES , Some (CBC iv) when String.length k = (128 / 8) -> Evp.CIPHER.aes_128_cbc

    | _ -> raise (NoBlockCipher (c, m)) in

  let engine = Evp.CIPHER.create (alg ()) (d = ForEncryption) in

  Evp.CIPHER.set_key engine k;

  (match m with
   | Some (CBC iv) -> Evp.CIPHER.set_iv engine iv
   | None -> ());

  { bc_name      = "bc-undefined-name"; 
    bc_direction = d;
    bc_blocksize = Evp.CIPHER.block_size engine;
    bc_process   = Evp.CIPHER.process engine; }

(* -------------------------------------------------------------------- *)
let md_typeofname (name : string) =
  match name with
  | "MD5"    -> Some (Evp.MD.md5    ())
  | "SHA1"   -> Some (Evp.MD.sha1   ())
  | "SHA256" -> Some (Evp.MD.sha256 ())
  | "SHA384" -> Some (Evp.MD.sha384 ())
  | "SHA512" -> Some (Evp.MD.sha512 ()) 
  | _        -> None

(* -------------------------------------------------------------------- *)
let message_digest (name : string) =
  match md_typeofname name with
  | None -> raise (NoMessageDigest name)

  | Some type_ ->
    let engine    = Evp.MD.create type_ in
    let process b = Evp.MD.update engine b; Evp.MD.final engine in

    { md_name = name; md_digest = process; }

(* -------------------------------------------------------------------- *)
let streamcipher (d : direction) (RC4 : scipher) (k : key) =
  let engine = Evp.CIPHER.create (Evp.CIPHER.rc4 ()) (d = ForEncryption) in

  Evp.CIPHER.set_key engine k;

  { sc_name      = "RC4";
    sc_direction = d;
    sc_process   = Evp.CIPHER.process engine; }

(* -------------------------------------------------------------------- *)
let hmac (name : string) (k : key) =
  match md_typeofname name with
  | None -> raise (NoHMac name)

  | Some type_ ->
    { hm_name    = name;
      hm_process = fun b -> Evp.HMAC.hmac type_ k b; }
