module TLS13.Impl.Server.Driver.LocalLengths

module SZ = FStar.SizeT

let lemma_size_add_value
  (x y:SZ.t)
  : Lemma
      (requires SZ.fits (SZ.v x + SZ.v y))
      (ensures SZ.v (SZ.add x y) == SZ.v x + SZ.v y)
=
  ()

let lemma_certificate_fragment_length_fits
  (chain_len:SZ.t)
  : Lemma
      (requires SZ.v chain_len <= 16610)
      (ensures SZ.fits (SZ.v chain_len + 13))
=
  ()

let lemma_certificate_network_length_fits
  (chain_len fragment_len:SZ.t)
  : Lemma
      (requires
        SZ.v chain_len <= 16610 /\
        SZ.v fragment_len == 13 + SZ.v chain_len)
      (ensures SZ.fits (SZ.v fragment_len + 22))
=
  ()

let lemma_certificate_verify_network_length_fits
  (signature_len fragment_len:SZ.t)
  : Lemma
      (requires
        SZ.v signature_len <= 4096 /\
        SZ.v fragment_len == SZ.v signature_len + 8)
      (ensures SZ.fits (SZ.v fragment_len + 22))
=
  ()

let lemma_certificate_verify_fragment_length_fits
  (signature_len:SZ.t)
  : Lemma
      (requires SZ.v signature_len <= 4096)
      (ensures SZ.fits (SZ.v signature_len + 8))
=
  ()
