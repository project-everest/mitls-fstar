module MiTLS.Specializations.Providers.AEAD
open MiTLS

type provider =
  | OpenSSLProvider
  | LowProvider
  | LowCProvider

assume val use_provider : unit -> Tot provider

