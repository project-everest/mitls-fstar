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

