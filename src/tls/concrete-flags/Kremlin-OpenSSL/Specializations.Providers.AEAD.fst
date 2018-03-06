module Specializations.Providers.AEAD

type provider =
  | OpenSSLProvider
  | LowProvider
  | LowCProvider

inline_for_extraction
let use_provider () : Tot provider =
  OpenSSLProvider

