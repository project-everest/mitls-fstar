module MiTLS.TLSInfoFlags
open MiTLS

open MiTLS.TLSConstants

type pmsId = PMS.pms

inline_for_extraction let strongKEX (_: pmsId) = false
inline_for_extraction let strongKEF (_: kefAlg_t) = false
inline_for_extraction let strongKDF (_: kdfAlg_t) = false
inline_for_extraction let strongVD (_: vdAlg_t) = false
