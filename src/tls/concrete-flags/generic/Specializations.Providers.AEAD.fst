module Specializations.Providers.AEAD

type provider =
  | OpenSSLProvider
  | LowProvider
  | LowCProvider

assume val use_provider : unit -> Tot provider

