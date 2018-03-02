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
