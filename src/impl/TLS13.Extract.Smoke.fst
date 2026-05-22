module TLS13.Extract.Smoke

module U8 = FStar.UInt8
module U16 = FStar.UInt16

let tls13_version_major (_:unit) : U8.t =
  3uy

let tls13_version_minor (_:unit) : U8.t =
  4uy

let tls13_chacha20_poly1305_sha256 (_:unit) : U16.t =
  0x1303us
