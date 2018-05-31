module Flags

assume val model: bool // scaffolding

let t = b:bool {b ==> model} 
assume val ideal_KEF: t
assume val ideal_Nonce: t
assume val ideal_Sig: t
assume val ideal_PMS: t
assume val ideal_PRF: t
assume val ideal_AEAD: t
assume val ideal_HMAC: t // see HMAC.UFCMA

assume val flag_Raw:  b:bool{b ==> model}
assume val flag_KDF:  d:nat -> b:bool{b ==> model}
assume val flag_KEF0: d:nat -> b:bool{b ==> model /\ flag_KDF d ==> b}
assume val flag_PRF1: d:nat -> b:bool{flag_KEF0 d ==> b /\ b ==> model}
assume val flag_ODH:  d:nat -> b:bool {flag_PRF1 d ==> b /\ b ==> model}
assume val flag_KEF2: d:nat -> b:bool{flag_KDF d ==> b /\ b ==> model}

// debug printing flags, one per module; 
// the refinement enables us to leak secrets for printing.

let real = b:bool {b ==> ~model}
assume val debug: real 
assume val debug_CDH: real
assume val debug_Epochs: real
assume val debug_FFI: real
assume val debug_HS: real
assume val debug_HSL: real
assume val debug_KS: real
assume val debug_NGO: real
assume val debug_QUIC: real
assume val debug_Record: real
assume val debug_TLS: real
