# KaRaMeL Bundle Bug: Failure("nth") in Pattern Matches Compilation

## Summary

KaRaMeL crashes with `Fatal error: exception Failure("nth")` during the "Pattern matches compilation" phase when bundling modules that contain nested pattern matching.

## Environment

- **KaRaMeL version**: 3611ae497bb5ab8ae83207428c8a915653bd761c (and 2fe560bbae17fe8a855b0dcf462db18ec37edc02)
- **F* version**: (as installed with KaRaMeL)
- **OS**: Linux

## Bug Description

When using the `-bundle` flag to combine modules, KaRaMeL successfully processes:
- Monomorphization
- Inlining  
- Pattern matches compilation (starts)

But then crashes with:
```
✔ [Pattern matches compilation] ⏱️ 167ms
Fatal error: exception Failure("nth")
```

## Reproduction

This minimal example demonstrates the issue:

### Files

**Simple.State.fst** - Simple state type (bundles successfully)

**Simple.Internal.fst** - Module with nested pattern matching (causes crash when bundled)

**Simple.API.fst** - Top-level module using Simple.Internal

### Steps to Reproduce

1. Verify the F* modules:
```bash
fstar.exe --cache_checked_modules --cache_dir _cache Simple.State.fst
fstar.exe --cache_checked_modules --cache_dir _cache Simple.Internal.fst
fstar.exe --cache_checked_modules --cache_dir _cache Simple.API.fst
```

2. Extract to .krml:
```bash
fstar.exe --codegen krml --extract_module Simple.State --odir _output Simple.State.fst
fstar.exe --codegen krml --extract_module Simple.Internal --odir _output Simple.Internal.fst
fstar.exe --codegen krml --extract_module Simple.API --odir _output Simple.API.fst
```

3. Try bundling (THIS WORKS):
```bash
krml -tmpdir _extract -skip-compilation \
  -bundle 'Simple.API=Simple.State[rename=Simple]' \
  _output/Simple_API.krml _output/Simple_State.krml _output/Simple_Internal.krml
```

4. Try bundling with Simple.Internal (THIS CRASHES):
```bash
krml -tmpdir _extract -skip-compilation \
  -bundle 'Simple.API=Simple.State,Simple.Internal[rename=Simple]' \
  _output/Simple_API.krml _output/Simple_State.krml _output/Simple_Internal.krml
```

**Result**: 
```
✔ [Monomorphization] ⏱️ ...ms
✔ [Inlining] ⏱️ ...ms
✔ [Pattern matches compilation] ⏱️ ...ms
Fatal error: exception Failure("nth")
```

## Workaround

Do not include modules with complex nested pattern matching in the bundle pattern. Let them compile to separate C files:

```bash
# This works - Simple.Internal becomes a separate .c file
krml -tmpdir _extract -skip-compilation \
  -bundle 'Simple.API=Simple.State[rename=Simple]' \
  _output/Simple_API.krml _output/Simple_State.krml _output/Simple_Internal.krml
```

## Expected Behavior

KaRaMeL should successfully bundle Simple.Internal with Simple.API, marking Simple.Internal's functions as static (internal to the bundle).

## Actual Behavior

KaRaMeL crashes during pattern match compilation with `Failure("nth")`.

## Impact

This prevents proper use of the bundling feature for projects with realistic pattern matching code. It forces exposure of internal functions in headers and prevents achieving a clean single-file bundle.

## Real-World Context

Discovered while trying to bundle a verified TLS 1.3 implementation:
- TLS13.Connection (API) + TLS13.Handshake (internal) → crash
- TLS13.Connection (API) + TLS13.Record (internal) → crash
- TLS13.Connection (API) + TLS13.State (simple types) → works

The TLS13.Handshake and TLS13.Record modules have complex nested pattern matching similar to Simple.Internal in this reproduction case.
