# KaRaMeL Bundling Bug - Reporting Guide

## Bug Summary

**Error**: `Fatal error: exception Failure("nth")` during KaRaMeL pattern match compilation

**Component**: KaRaMeL (F* to C extraction tool)

**Impact**: Prevents single-file bundling of TLS 1.3 implementation, requiring workaround with multiple .c files

## Reproduction

### Prerequisites

```bash
# F* and KaRaMeL are included as submodules
git clone --recursive https://github.com/FStarLang/agentic-tls.git
cd agentic-tls
```

### Steps to Reproduce

1. **Verify all F* modules** (confirms code is valid):
   ```bash
   make verify
   ```
   Expected: All 40+ modules verify successfully

2. **Attempt full bundle extraction**:
   ```bash
   make extract-krml
   krml \
     -tmpdir _extract/bundle \
     -skip-compilation \
     -warn-error -2-9-17 \
     -bundle 'TLS13.Connection=TLS13.Connection.Driver,TLS13.Connection.StateDriver,TLS13.State,TLS13.Handshake,TLS13.Handshake.Driver,TLS13.Handshake.ByteDriver,TLS13.Handshake.FlightState,TLS13.Handshake.Framing,TLS13.Handshake.Transcript,TLS13.KeySchedule,TLS13.Record,TLS13.Record.Framing[rename=TLS13]' \
     -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims,Spec.*,TLS13.Bytes,TLS13.Parse,TLS13.Connection.Log' \
     -no-prefix 'TLS13.Connection' \
     _output/*.krml
   ```

3. **Observe crash**:
   ```
   ✔ [Monomorphization] ⏱️ 201ms
   ✔ [Inlining] ⏱️ 134ms
   ✔ [Pattern matches compilation] ⏱️ 167ms
   Fatal error: exception Failure("nth")
   ```

### Minimal Test

Attempted to create minimal reproduction in `bug-reports/karamel-bundle-nth-failure/`:
- **Result**: Simple pattern matching examples do NOT trigger the bug
- **Conclusion**: Bug is specific to complexity of TLS13 modules, not simple nested patterns

### Incremental Testing

To isolate which module triggers the bug:

```bash
# This works (bundles TLS13.Connection + State only):
krml -bundle 'TLS13.Connection=TLS13.Connection.Driver,TLS13.Connection.StateDriver,TLS13.State[rename=TLS13]' ...

# This crashes (adding TLS13.Handshake):
krml -bundle 'TLS13.Connection=...,TLS13.Handshake[rename=TLS13]' ...

# This crashes (adding TLS13.Record):  
krml -bundle 'TLS13.Connection=...,TLS13.Record[rename=TLS13]' ...

# This crashes (adding TLS13.KeySchedule):
krml -bundle 'TLS13.Connection=...,TLS13.KeySchedule[rename=TLS13]' ...
```

## Problematic Modules

The crash occurs when bundling any of these modules:
- `TLS13.Handshake.FlightState` (~2000 lines, complex nested pattern matching)
- `TLS13.Record` (pattern matching on message types)
- `TLS13.KeySchedule` (pattern matching on handshake states)

## Environment

- **F* version**: 2fe560bbae17fe8a855b0dcf462db18ec37edc02 (included in repo)
- **KaRaMeL version**: 3611ae497bb5ab8ae83207428c8a915653bd761c (included in repo)
- **OS**: Linux
- **Build**: Standard F* + KaRaMeL build from source

## Workaround

Hybrid bundling approach:
- Bundle simple modules (Connection, State, drivers)
- Leave complex pattern-matching modules as separate .c files
- Result: Clean public API but multiple C files instead of single file

See `Makefile` target `extract-bundle` (line 167-179) for working extraction.

## Impact

- ❌ Cannot create single-file TLS13.c/TLS13.h bundle
- ✅ Can extract to multiple .c files with clean public API header
- ✅ Verified code still extracts and compiles correctly
- ⚠️ Internal functions from separate .c files appear in headers (KaRaMeL limitation)

## Additional Information

Full technical investigation: See `BUNDLING_ISSUE.md` in repository root

Working extraction: `make extract-bundle` produces working multi-file output

Documentation:
- `STATUS_SUMMARY.md` - Complete project status
- `_extract/bundle/README.md` - API documentation  
- `bug-reports/karamel-bundle-nth-failure/` - Minimal reproduction attempt

## Suggested Fix

Investigation needed in KaRaMeL's pattern match compilation phase (`nth` function call that fails suggests list/array indexing issue, possibly during pattern matrix construction or decision tree generation).

The fact that simple patterns work but complex nested patterns crash suggests:
- Possible off-by-one error in pattern compilation
- Incorrect calculation of pattern depth/arity
- Missing bounds check on pattern matrix operations
