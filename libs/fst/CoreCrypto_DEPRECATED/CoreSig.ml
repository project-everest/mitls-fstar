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
