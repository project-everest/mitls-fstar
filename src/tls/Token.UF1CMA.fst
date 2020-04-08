(* Idealizing derived authentication tokens; independent of TLS, used for TLS 1.2 Finished message payloads. *)
module Token.UF1CMA

//TODO use this file instead of TLSPRF

open FStar.Bytes
open Mem

noeq type concrete_key =
  | MAC: u:info -> k:keyrepr u -> concrete_key

let concrete_key_info k = k.u
let concrete_key_repr k = k.k

let create ip _ _ i u =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert(Spec.Agile.HMAC.keysized u.alg (Spec.Hash.Definitions.hash_length u.alg));
  let kv: keyrepr u = Random.sample32 (Hacl.Hash.Definitions.hash_len u.alg) in
  let ck = MAC u kv in
  let k : ir_key ip i =
    if is_safe i then
      let region: Mem.subrgn u.parent = new_region u.parent in
      assert(~(is_tls_rgn u.parent));
      let log: log_t #ip i u region = ralloc region None in
      IdealKey ck region log
    else
      RealKey ck in
  k <: key ip i

let coerceT (ip: ipkg) (ha_of_i: ip.Pkg.t -> ha) (good_of_i: ip.Pkg.t -> bool)
  (i: ip.Pkg.t {ip.Pkg.registered i /\ ~(safe i)})
  (u: info {u.alg = ha_of_i i /\ u.good == good_of_i i})
  (kv: lbytes32 (keylen u)) : GTot (key ip i)
  =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert(Spec.Agile.HMAC.keysized u.alg (Spec.Hash.Definitions.hash_length u.alg));
  let ck = MAC u kv in
  if model then
    let k : ir_key ip i = RealKey ck in k
  else ck


let coerce ip _ _ i u kv =
  assert_norm (pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125);
  assert(Spec.Agile.HMAC.keysized u.alg (Spec.Hash.Definitions.hash_length u.alg));
  let ck = MAC u kv in
  if model then
    let k : ir_key ip i = RealKey ck in k
  else ck

let token #ip #i k =
  let MAC _ t = get_key k in
  if is_safe i then
    (let IdealKey _ _ log = k <: ir_key ip i in
    log := Some ());
  t

let verify #ip #i k t =
  let MAC _ t' = get_key k in
  let verified = (t = t') in
  if is_safe i then
    // We use the log to correct any verification errors
    let IdealKey _ _ log = k <: ir_key ip i in
    match !log with
    | Some () -> verified
    | None    ->
      assume false; //18-01-04 TODO how can this fail otherwise?
      false
  else
    verified
