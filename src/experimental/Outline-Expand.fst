(*
KID
Expand

Extract
AEAD
Finished
(...)

Expand.KDF
KeySchedule
*)

// remaining issues:

// how to share instances? 
// use a global table for sharing <--$--- or for statically preventing double-generation. 
// where is the table? Callee or caller?


(** Consistent safety predicate on the indexes of all derived materials *)
module KID
let rec safe = function
  | Expand_salt src -> safe src 
  | ...


(** Handling secrets and their derived materials, generically *)
module Expand  

type repr (i:id) = lbytes (hashLen i)
abstract type secret (i:id) = repr i

val create: #i:id {safe s} -> secret i 
val coerce: #i:id {~safe s} -> repr i -> Tot (secret i)
val leak: #i:src {~safe s} -> Tot (repr i)


type derepr (i:id) = lbytes (idLen i)
abstract type dekey (i:id) = derepr i

// called *only* by Expand.KDF; would be private except for modular circularity with Expand.KDF
// must memoize the ideal sampling to match the PRF assumption.
// expansion need not be restricted, as therer is no way to extract representations at safe indexes. 
val expand: #src:id -> secret src -> dekey i
val deleak: #i:id {~safe i} -> derived i -> derepr i

// how to verify separation? 
// program an injective function from the derived index to the parent index (determining the PRF instance) and a unique label (the domain of the PRF) 


(** Sample module using expanded key materials *) 
module Extract, etc...

type salt (i:id)
val salt_create
val salt_coerce

let extract ikm salt = 
  if safe_ikm ikm 
  then Expand.create 
  else Expand.coerce 


(** Continuation of Expand, this time with specific derivations for all kinds of keyed functionalities *)
module Expand.KDF 

val expand_secret: #i:src -> secret i -> secret (Expand_secret i)

val expand_ikm: ...

// we have a perfect step as we set ideal_salt, 
// justified by expanding the two branches and checking that their code is identical
let expand_salt #i s =
  if safe (Expand_salt i)  // possibly conditioned on some salt idealization flag
  then Salt.create (Expand_salt #i) // randomly sampled, here rather than in Expand
  else Salt.coerce (Expand_salt #i) (Expand.deleak (Secret.expand ...)) // either computed or randomly sampled, then leaked/coerced (noop)

(* other styles we consider:
val expand_salt
let expand_salt #i s =
  if safe i
  then Salt.create (Expand_salt #i) 
  else 
    let k = hkdf_expand (hashAlg i) (leak s) "SALT" hv? (saltLen i) ... in 
    Salt.coerce (Expand_salt #i) 

let expand_salt #i s =
  let salt0 = Secret.expand .... in // either computed or freshly sampled
  if safe i 
  then Salt.create (Expand_salt #i) 
  else Salt.coerce (Expand_salt #i) (Secret.leak salt0)
*) 


module KeySchedule

...
  let ikm = ... in 
  let early_secret = Extract.extract_0 ikm in
  let early_salt = Expand.KDF.expand_salt early_secret in 
  let hs_secret = Extract.extract_1 ikm early_salt in
  ...
