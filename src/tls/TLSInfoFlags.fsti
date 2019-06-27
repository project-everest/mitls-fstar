module TLSInfoFlags

open TLSConstants

// -------------------------------------------------------------------
// Pre Master Secret indexes

// Placeholder for overhaul of 1.2 indexes
type pmsId = PMS.pms

inline_for_extraction val strongKEX: pmsId -> Tot bool

// -------------------------------------------------------------------
// Master Secret indexes and their properties

// CF postv1, move strength predicates --> TLSConstants
// ``kefAlg is a strong randomness extractor, despite all other kefAlgs'', guarding idealization in KEF

inline_for_extraction val strongKEF: kefAlg_t -> Tot bool

// guarding idealizations for KDF and VerifyData (see PRF.fs)
inline_for_extraction val strongKDF: kdfAlg_t -> Tot bool
inline_for_extraction val strongVD: vdAlg_t -> Tot bool
