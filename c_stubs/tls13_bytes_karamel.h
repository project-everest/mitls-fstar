#ifndef TLS13_BYTES_KARAMEL_H
#define TLS13_BYTES_KARAMEL_H

/*
 * TLS13.Bytes.empty is proof/spec-level in F*, but KaRaMeL can still emit
 * references to it from proof-erased local-event records. Provide a per-C-file
 * immutable nil node once the generated Prims_list__uint8_t type is available.
 */

#if defined(__GNUC__) || defined(__clang__)
#define TLS13_BYTES_KARAMEL_UNUSED __attribute__((unused))
#else
#define TLS13_BYTES_KARAMEL_UNUSED
#endif

#endif /* TLS13_BYTES_KARAMEL_H */

#if defined(Prims_Nil) && !defined(TLS13_BYTES_KARAMEL_EMPTY_DEFINED)
#define TLS13_BYTES_KARAMEL_EMPTY_DEFINED
static TLS13_BYTES_KARAMEL_UNUSED Prims_list__uint8_t tls13_bytes_karamel_empty = { .tag = Prims_Nil };
#define TLS13_Bytes_empty (&tls13_bytes_karamel_empty)
#endif
