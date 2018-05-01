module Flags

inline_for_extraction let model = false

inline_for_extraction let ideal_KEF = false
inline_for_extraction let ideal_Nonce = false
inline_for_extraction let ideal_Sig = false
inline_for_extraction let ideal_PMS = false
inline_for_extraction let ideal_PRF = false
inline_for_extraction let ideal_AEAD = false
inline_for_extraction let ideal_HMAC = false

inline_for_extraction let flag_Raw = false
inline_for_extraction let flag_KDF (d:nat) = false
inline_for_extraction let flag_KEF0 (d:nat) = false
inline_for_extraction let flag_PRF1 (d:nat) = false
inline_for_extraction let flag_ODH (d:nat) = false
inline_for_extraction let flag_KEF2 (d:nat) = false
