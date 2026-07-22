#ifndef TLS13_BYTES_KARAMEL_H
#define TLS13_BYTES_KARAMEL_H

/*
 * TLS13.Bytes.empty is proof/spec-level in F*, but KaRaMeL can still emit
 * references to it from proof-erased local-event records. Delay construction
 * until each use site, after KaRaMeL has declared Prims_list__uint8_t.
 */

#define TLS13_Bytes_empty \
  (&(Prims_list__uint8_t){ .tag = Prims_Nil })

#endif /* TLS13_BYTES_KARAMEL_H */
