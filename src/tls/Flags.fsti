module Flags

inline_for_extraction val model: bool // scaffolding

let t = b:bool {b ==> model} 
inline_for_extraction val ideal_KEF: t
inline_for_extraction val ideal_Nonce: t
inline_for_extraction val ideal_Sig: t
inline_for_extraction val ideal_PMS: t
inline_for_extraction val ideal_PRF: t
inline_for_extraction val ideal_AEAD: t
inline_for_extraction val ideal_HMAC: t // see HMAC.UFCMA

inline_for_extraction val flag_Raw:  b:bool{b ==> model}
inline_for_extraction val flag_KDF:  d:nat -> b:bool{b ==> model}
inline_for_extraction val flag_KEF0: d:nat -> b:bool{b ==> model /\ flag_KDF d ==> b}
inline_for_extraction val flag_PRF1: d:nat -> b:bool{flag_KEF0 d ==> b /\ b ==> model}
inline_for_extraction val flag_ODH:  d:nat -> b:bool {flag_PRF1 d ==> b /\ b ==> model}
inline_for_extraction val flag_KEF2: d:nat -> b:bool{flag_KDF d ==> b /\ b ==> model}

// debug printing flags, one per module; 
// the refinement enables us to leak secrets for printing.

let real = b:bool {b ==> ~model}
inline_for_extraction val debug: real 
inline_for_extraction val debug_CDH: real
inline_for_extraction val debug_Epochs: real
inline_for_extraction val debug_FFI: real
inline_for_extraction val debug_HS: real
inline_for_extraction val debug_HSL: real
inline_for_extraction val debug_KS: real
inline_for_extraction val debug_NGO: real
inline_for_extraction val debug_QUIC: real
inline_for_extraction val debug_Record: real
inline_for_extraction val debug_TLS: real
