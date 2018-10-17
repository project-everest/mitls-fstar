Here we store the RFC specifications of all data formats, and we
automatically generate their Low* specifications and implementations
using QuackyDucky, calling into LowParse.

The name of each RFC file should be: Namespace.rfc

Then, if you do: make Namespace.rfc.gen, then their corresponding
specifications and implementations will be generated at:
generated/Namespace.Parse_* (TODO: remove this .Parse_ thing, once
capitalization of module names if QuackyDucky is made correct.)

Parsers.rfc: the merged RFC for TLS 1.2, TLS 1.3 and everything else
supported by miTLS at the same time.

Parsers.HKDF.rfc: a sample for HKDF, which is independent.
