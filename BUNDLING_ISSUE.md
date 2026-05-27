# KaRaMeL Bundling Issue

## Problem

Cannot properly bundle TLS13 implementation modules using KaRaMeL's `-bundle` flag. The goal is to have TLS13.Connection as the public API module, with all other implementation modules (Handshake, Record, KeySchedule, etc.) bundled as internal/static functions.

## Error

```
Fatal error: exception Failure("nth")
```

This error occurs during the "Pattern matches compilation" phase of KaRaMeL extraction.

## Investigation Results

### What Works ✅

**Minimal bundle with TLS13.State only:**
```bash
krml -bundle 'TLS13.Connection=TLS13.State[rename=TLS13]' \
  TLS13_Connection.krml TLS13_State.krml ...
```
✅ Succeeds, generates TLS13.c and TLS13.h

### What Fails ❌

**Adding TLS13.Handshake:**
```bash
krml -bundle 'TLS13.Connection=TLS13.State,TLS13.Handshake[rename=TLS13]' \
  TLS13_Connection.krml TLS13_State.krml TLS13_Handshake.krml ...
```
❌ Fatal error: exception Failure("nth")

**Adding TLS13.Record:**
```bash
krml -bundle 'TLS13.Connection=TLS13.State,TLS13.Record[rename=TLS13]' \
  TLS13_Connection.krml TLS13_State.krml TLS13_Record.krml ...
```
❌ Fatal error: exception Failure("nth")

**Full bundle (all modules):**
```bash
krml -bundle 'TLS13.Connection=TLS13.Connection.Driver,TLS13.Connection.StateDriver,TLS13.Handshake,TLS13.Handshake.ByteDriver,...[rename=TLS13]' \
  (all .krml files)
```
❌ Fatal error: exception Failure("nth")

## Analysis

1. **Error occurs during pattern match compilation**, suggesting an issue with how KaRaMeL translates pattern matches in bundled modules.

2. **TLS13.State bundles successfully** but is a simple module with basic types. TLS13.Handshake and TLS13.Record have:
   - Complex state machines
   - Nested pattern matching
   - Ghost log manipulations
   - Cross-module type references

3. **No KaRaMeL version issues** - using commit 2fe560bbae17fe8a855b0dcf462db18ec37edc02

4. **F* modules verify correctly** - the issue is purely in KaRaMeL bundling, not in F* verification.

## Current Workaround

The Makefile currently uses the old approach with a TLS13.Client wrapper module:
- TLS13.Client.fst/fsti wraps TLS13.Connection via `include`
- `-bundle 'TLS13.Client=TLS13.*[rename=TLS13]'`
- This works but exposes ~35 internal TLS13_* functions in the header
- **User indicated this is incorrect** - TLS13.Connection should be the direct API

## Possible Solutions

### Option A: Fix KaRaMeL Bug
- File issue with KaRaMeL team
- Debug the "nth" failure in Pattern matches compilation phase
- Requires understanding KaRaMeL internals

### Option B: Restructure Modules
- Investigate what makes TLS13.Handshake and TLS13.Record unbundleable
- Possibly split complex pattern matching into separate helper modules
- May require significant refactoring

### Option C: Different Bundling Strategy
- Use multiple bundles instead of single bundle
- Extract as separate .c files and link together
- Defeats the purpose of single-file bundle

### Option D: Accept Current State
- Keep TLS13.Client wrapper (goes against user's directive)
- Document that internal TLS13_* functions should not be called
- Not ideal but functional

## Recommendation

**Report to user** that we hit a KaRaMeL bundling bug. The current extraction works and generates correct C code, but cannot achieve the desired single-file bundle with proper static visibility for internal modules. Need guidance on:
1. Should we file a KaRaMeL bug report and wait for fix?
2. Should we restructure modules to avoid the bug?
3. Should we accept multi-file extraction instead?
