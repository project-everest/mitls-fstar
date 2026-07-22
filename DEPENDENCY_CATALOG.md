# F* Root Dependency Catalog

This catalog records the project-local dependency closures computed with
`fstar.exe --dep full` from:

- `src/impl/TLS13.System.Temporal.fst`
- `src/impl/TLS13.Impl.Client.Driver.fst`
- `src/impl/TLS13.Impl.Server.Driver.fst`

The scans use the root `Makefile` include paths, cache policy, and extraction
selector. The counted source universe is `common/`, `generated/`, `src/spec/`,
and `src/impl/`; F*, Pulse, LowParse, and other toolchain libraries are external.

## Result

The project-local universe contains **246 modules in 432 `.fst`/`.fsti`
files**. The maintained TLS closure contains **243 modules in 429 files**.
The other three modules are sample-owned common code listed below.

| Root | Modules | Files |
| --- | ---: | ---: |
| Temporal theorem | 243 | 429 |
| Client executable | 166 | 285 |
| Server executable | 170 | 294 |
| All three roots | 243 | 429 |

The temporal theorem already reaches the complete maintained TLS closure. The
client and server roots remain explicit in `ROOT_FILES` because they are the
executable entry points and define the intended build surface.

## Reachable sources by area

| Area | Temporal | Client | Server | Combined |
| --- | ---: | ---: | ---: | ---: |
| `common/` | 7 / 7 | 6 / 6 | 6 / 6 | 7 / 7 |
| `generated/` | 77 / 154 | 77 / 154 | 77 / 154 | 77 / 154 |
| `src/spec/assumptions/` | 2 / 2 | 2 / 2 | 2 / 2 | 2 / 2 |
| `src/spec/common/` | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 |
| `src/spec/core/` | 18 / 19 | 18 / 19 | 18 / 19 | 18 / 19 |
| `src/spec/properties/` | 36 / 64 | 16 / 26 | 16 / 26 | 36 / 64 |
| `src/impl/` | 102 / 182 | 46 / 77 | 50 / 86 | 102 / 182 |
| **Total** | **243 / 429** | **166 / 285** | **170 / 294** | **243 / 429** |

Each cell is `modules / files`. An implementation and its interface count as
one module and two files.

The seven reachable common modules are:

- `Common.ProtocolEndpoint`
- `Common.ProtocolImplementation`
- `Common.StateMachine`
- `Common.TCP`
- `Common.Temporal`
- `Common.WireFormat`
- `Common.WireFormatStateMachine`

## Active generated wire codecs

Alert, ChangeCipherSpec, and complete outer-record framing now use the generated
code directly rather than a proof-only correspondence layer.

- Pure Alert and ChangeCipherSpec parsing/serialization in
  `TLS13.Wire.Spec` use the generated parsers and serializers.
- Runtime Alert and ChangeCipherSpec parsing uses the generated validators and
  readers. Active semantics additionally reject unknown alert values and require
  the ChangeCipherSpec payload to be exactly `0x01`, since the generated
  one-byte structure alone does not enforce that constant.
- Close-notify serialization uses the generated Alert writer.
- Pure record parsing/serialization uses the generated `TLSCiphertext` codec.
- Runtime ordinary-record acceptance is gated by the generated
  `TLSCiphertext` validator and requires exact input consumption. Active
  semantics additionally require the TLS 1.2 legacy-record version `0x0303` and
  the record-size bound.
- Complete ApplicationData, ClientHello, and ServerHello outer records use the
  shared generated `TLSCiphertext` writer. The five-byte ApplicationData header
  used as AEAD additional data remains a small constructor because it must be
  produced before the ciphertext exists.
- The explicit RFC compatibility path accepting a ClientHello Handshake record
  with legacy version `0x0301` remains outside generated validation; all normal
  `0x0303` records pass through it.

The seven generated codec modules involved are:

- `TLS13.Wire.Generated.AlertLevel`
- `TLS13.Wire.Generated.Alert`
- `TLS13.Wire.Generated.ChangeCipherSpec`
- `TLS13.Wire.Generated.TLSPlaintext`
- `TLS13.Wire.Generated.TLSPlaintext_fragment`
- `TLS13.Wire.Generated.TLSCiphertext`
- `TLS13.Wire.Generated.TLSCiphertext_encrypted_record`

Encryption itself remains state-dependent and separate from framing:
`TLS13.Record.Spec.seal` and `open_record` consume the negotiated traffic keys
and sequence state, while the generated codec validates or writes the resulting
outer record.

Unknown extensions do not use a standalone `UnknownExtension` codec. Each
length-delimited extension envelope in `tls.qd.rfc` has its own `default:
opaque` branch:

- `ExtensionClientHello_extension_data_default`
- `ExtensionServerHello_extension_data_default`
- `ExtensionEncryptedExtensions_extension_data_default`
- `ExtensionCertificate_extension_data_default`

This preserves the extension payload exactly inside the envelope's existing
two-byte length. A standalone `UnknownExtension<0..2^16-1>` there would add an
incorrect second length prefix.

## Removed as unreachable

The dependency analysis identified these seven modules as unreachable from all
three TLS roots, and they were removed:

- `TLS13.Wire.Generated.UnknownExtension`
- `TLS13.Extract.Smoke`
- `TLS13.Impl.Driver.PairingValidByteTrace`
- `TLS13.Impl.Serializer.CertificateVerify`
- `TLS13.MachineTypes`
- `TLS13.X509`
- `TLS13.ConnectionState.ProtectedWireSkipWrappers`

The orphaned `test/unit/test_extract_smoke.c` harness was removed with
`TLS13.Extract.Smoke`.

## Shared sample-only modules

These three modules are outside the TLS closure but remain because independent
sample Makefiles import them:

- `Common.FileTransfer`
- `Common.ProtocolDriver`
- `Common.TCP.History`

They support the calculator, TFTP, YMODEM, and FTP samples and are not roots of
the main TLS Makefile.

## Reproduction

The main `.depend` rule invokes `--dep full` on `ROOT_FILES`. A single-root scan
can be reproduced with the same `FSTAR_DEP_OPTIONS` and `FSTAR_FLAGS`, for
example:

```sh
tools/everparse/opt/FStar/bin/fstar.exe <project F* flags> \
  --dep full \
  src/impl/TLS13.System.Temporal.fst \
  --output_deps_to tls13-temporal.depend
```
