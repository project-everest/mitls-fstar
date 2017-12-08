module Flags

assume val model: bool // scaffolding
assume val ideal_KEF : bool
assume val ideal_Nonce : bool
assume val ideal_Sig : bool
assume val ideal_PMS : bool
assume val ideal_PRF : bool
assume val ideal_AEAD: bool

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

