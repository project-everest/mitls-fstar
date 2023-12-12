module MiTLS.Specializations.Providers.AEAD
open MiTLS
type provider =
  | OpenSSLProvider
  | LowProvider
  | LowCProvider

inline_for_extraction 
let use_provider () : Tot provider =
  LowCProvider

