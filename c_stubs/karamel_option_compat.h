#ifndef KARAMEL_OPTION_COMPAT_H
#define KARAMEL_OPTION_COMPAT_H

/*
 * KaRaMeL deduplicates structurally-identical tag enums and emits a single
 * canonical name for the option (None | Some) tag.  Depending on the set of
 * types in the bundle, that canonical name may be a generated module's tag
 * (e.g. TLS13_Wire_Generated_ProtocolNameList_{None,Some}) rather than
 * FStar_Pervasives_Native_{None,Some}.  The hand-written C bindings below refer
 * to the standard FStar names, so provide them here.
 *
 * Option tags are always encoded with None = 0 and Some = 1 (KaRaMeL numbers
 * constructors in declaration order, and FStar's option is `None | Some`), so
 * these values are stable regardless of which type wins canonicalization.  The
 * #ifndef guards keep this a no-op when KaRaMeL does emit the FStar names.
 */
#ifndef FStar_Pervasives_Native_None
#define FStar_Pervasives_Native_None 0
#endif
#ifndef FStar_Pervasives_Native_Some
#define FStar_Pervasives_Native_Some 1
#endif

#endif /* KARAMEL_OPTION_COMPAT_H */
