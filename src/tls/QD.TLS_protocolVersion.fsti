module QD.TLS_protocolVersion

open FStar.Bytes
open TLSError
open Parse

type protocolVersion' =
  | SSL_3p0
  | TLS_1p0
  | TLS_1p1
  | TLS_1p2
  | TLS_1p3
  | Unknown_protocolVersion of (v:UInt16.t{v <> 768us /\ v <> 769us /\ v <> 770us /\ v <> 771us /\ v <> 772us})

type protocolVersion = v:protocolVersion'{~(Unknown_protocolVersion? v)}

inline_for_extraction val protocolVersion_bytes: protocolVersion' -> Tot (lbytes 2)
inline_for_extraction val parse_protocolVersion': lbytes 2 -> result protocolVersion'
inline_for_extraction val parse_protocolVersion: lbytes 2 -> result protocolVersion

val inverse_protocolVersion' (x:_) : Lemma
  (requires True)
  (ensures lemma_inverse_g_f protocolVersion_bytes parse_protocolVersion' x)

val pinverse_protocolVersion' (x:_) : Lemma
  (requires True)
  (ensures lemma_pinverse_f_g equal protocolVersion_bytes parse_protocolVersion' x)
