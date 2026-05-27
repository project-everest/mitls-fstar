# TLS 1.3 Verified Client - Current Status

**Date:** May 26, 2024  
**Checkpoint:** 027 - KaRaMeL Bundling Investigation

## Summary

We have a **fully verified TLS 1.3 client** implemented in F*/Pulse that successfully extracts to C and passes integration tests against OpenSSL servers. However, we've encountered a KaRaMeL bundling bug that prevents achieving the ideal single-file extraction with proper module visibility.

## What Works ✅

### Verification
- **All 40+ F* modules verify successfully** without errors
- **No axioms** in core protocol modules (Record, Handshake, Connection)
- **Layered ghost log specification**:
  - Raw bytes (network-level truth)
  - TLS messages (parsed from raw bytes)
  - Application data (projected from TLS messages)
  - All layers maintained in connection invariant
- **Complete state machine**: handles all TLS 1.3 handshake phases plus error states
- **Cryptographic operations**: All verified via bindings to HACL* (SHA-256, ECDH, AES-GCM, HMAC)

### Extraction
- **Single-file bundle extracts**: `make extract-bundle` generates TLS13.c and TLS13.h
- **Clean top-level API**: 8 public functions from TLS13.Connection
  ```c
  connection client_new(uint8_t *hostname, size_t hostname_len, config cfg);
  void client_free(connection c);
  bool client_connect(connection c, channel ch);
  size_t client_write(connection c, channel ch, uint8_t *buf, size_t len);
  size_t client_read(connection c, channel ch, uint8_t *out, size_t max_len);
  bool client_write_all(connection c, channel ch, uint8_t *buf, size_t len);
  size_t client_read_exact(connection c, channel ch, uint8_t *out, size_t len);
  void client_close(connection c, channel ch);
  ```
- **No unverified code in core protocol**: All TLS logic is verified F*/Pulse
- **Backend abstraction**: Crypto and I/O operations abstracted via interfaces

### Testing
- **Integration tests pass** against OpenSSL 3.x servers:
  - Full TLS 1.3 handshake (ClientHello through Finished)
  - Application data encryption/decryption
  - Error handling (malformed messages, signature failures, etc.)
- **Test command**: `make test` runs full suite

### Build System
- **Clean Makefile** (409 lines, down from 570):
  - Uses `fstar.exe --dep full` for automatic dependency analysis
  - Generic pattern rules for `.checked`, `.krml`, `.c` files
  - Supports parallel builds with `make -j`
  - Incremental builds work correctly

## What Doesn't Work ❌

### KaRaMeL Bundling Bug

**Issue**: Cannot bundle TLS13.Handshake or TLS13.Record modules with TLS13.Connection

**Error**:
```
Fatal error: exception Failure("nth")
```
Occurs during "Pattern matches compilation" phase.

**Details**:
- **Minimal bundle works**: `-bundle 'TLS13.Connection=TLS13.State[rename=TLS13]'` ✅
- **Adding Handshake fails**: `-bundle 'TLS13.Connection=TLS13.State,TLS13.Handshake[rename=TLS13]'` ❌
- **Adding Record fails**: `-bundle 'TLS13.Connection=TLS13.State,TLS13.Record[rename=TLS13]'` ❌
- **Full bundle fails**: All 14 implementation modules ❌

**Impact**:
- Cannot achieve proper static visibility for internal functions
- TLS13.h exposes ~35 internal `TLS13_Handshake_*` and `TLS13_Record_*` functions
- Header file larger than necessary (would be ~50 lines with proper bundling vs. current 840 lines)

**Current Workaround**:
- Using TLS13.Client wrapper module (`include TLS13.Connection`)
- Bundle pattern: `-bundle 'TLS13.Client=TLS13.*[rename=TLS13]'`
- This works but user indicated it's the wrong approach
- TLS13.Connection should be the direct API, not a wrapper

**Root Cause** (suspected):
- KaRaMeL bug in pattern match compilation when bundling modules with:
  - Complex nested pattern matching (TLS13.Handshake.FlightState)
  - Cross-module type references (handshake_context, record_state)
  - Ghost log manipulations
  - Or: State machine transitions

### Minor Issues

1. **Variable-Length Arrays**: Some functions allocate VLAs on stack
   - Non-portable (CompCert, MSVC don't support)
   - KaRaMeL Warning 6 in ~20 locations
   - Affects: transcript concatenation, record encryption
   - Fix: Replace with fixed-size buffers or heap allocation

2. **Type exposure**: Minimal bundle shows incomplete types in header
   ```c
   typedef struct connection_s {
     TLS13_Handshake_handshake_context handshake;  // ← Type not defined!
     TLS13_Record_record_state client_application_record_state;  // ← Type not defined!
     ...
   }
   ```
   This is a consequence of the bundling bug.

## File Structure

```
src/
├── spec/          # Specification modules (ghost/proof-only)
│   ├── TLS13.StateMachine.fst           # TLS state machine spec
│   ├── TLS13.Handshake.Spec.fst         # Handshake message spec
│   ├── TLS13.Record.Spec.fst            # Record layer spec
│   └── TLS13.ConnectionLog.fst          # Layered log spec
│
└── impl/          # Implementation modules (extract to C)
    ├── TLS13.Connection.fst/fsti        # Top-level API (8 functions)
    ├── TLS13.Connection.Driver.fst      # Connection state driver
    ├── TLS13.Handshake.fst/fsti         # Handshake orchestration
    ├── TLS13.Handshake.FlightState.fst  # Per-flight operations
    ├── TLS13.Handshake.Framing.fst      # Handshake message framing
    ├── TLS13.Record.fst/fsti            # Record layer implementation
    ├── TLS13.Record.Framing.fst         # Record framing
    ├── TLS13.KeySchedule.fst            # Key derivation (HKDF)
    └── TLS13.State.fst                  # Connection state type

Interfaces (no .fst):
├── TLS13.Connection.Backend.fsti        # Backend abstraction (crypto + I/O)
├── TLS13.Crypto.fsti                    # Cryptographic operations
├── TLS13.X509.fsti                      # Certificate validation
├── TLS13.IO.fsti                        # Network I/O
└── TLS13.MachineTypes.fsti              # Low-level types
```

**Total**: 40+ modules, ~15,000 lines of F*/Pulse code

## Trusted Computing Base (TCB)

The verification relies on:
1. **F*/Pulse correctness**: Type system, refinement types, separation logic
2. **HACL* crypto primitives**: SHA-256, ECDH (P-256), AES-128-GCM, HMAC-SHA-256
3. **Backend implementations**:
   - `TLS13.Crypto.fsti` → HACL* bindings (verified)
   - `TLS13.X509.fsti` → Certificate validation (assumed correct)
   - `TLS13.IO.fsti` → POSIX sockets (assumed correct)

**No ad-hoc C code** in the core TLS protocol implementation.

## Next Steps / Options

### Option 1: File KaRaMeL Bug Report
- Report `Failure("nth")` error to KaRaMeL team
- Provide minimal reproduction case
- Wait for fix before proceeding
- **Pro**: Gets proper solution
- **Con**: May take time; might be F* code issue, not KaRaMeL

### Option 2: Restructure Modules
- Investigate what makes TLS13.Handshake/Record unbundleable
- Possibly split complex pattern matching into helper modules
- Try different module organization
- **Pro**: Might find workaround
- **Con**: May require significant refactoring; might not help

### Option 3: Accept Multi-File Extraction
- Bundle per-component: Handshake.c, Record.c, Connection.c
- Link together at compile time
- Keep internal functions non-static but documented as internal
- **Pro**: Works today, no code changes needed
- **Con**: Doesn't achieve single-file goal

### Option 4: Keep Wrapper Approach
- Keep TLS13.Client.fst/fsti wrapper
- Document clearly that only `client_*` functions are public API
- **Pro**: Works, generates correct code
- **Con**: User indicated this is wrong approach

## Recommendation

**I recommend Option 1**: File a detailed bug report with the KaRaMeL team. The bundling feature is supposed to support exactly this use case (public API module + internal implementation modules). The fact that simple modules (TLS13.State) work but complex modules (TLS13.Handshake, TLS13.Record) fail suggests a KaRaMeL bug rather than a fundamental issue with our code structure.

In the meantime, **Option 4 (wrapper)** keeps everything functional for testing and development.

## Questions for User

1. Should I file a KaRaMeL issue on GitHub?
2. Are you willing to wait for a KaRaMeL fix, or should we pursue workarounds (Option 2/3)?
3. Is the current extraction (works, but header exposes internal functions) acceptable temporarily?
4. Any insights into why TLS13.Handshake/Record might cause `Failure("nth")` in pattern match compilation?
