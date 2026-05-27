# KaRaMeL Bundle Bug - Attempted Minimal Reproduction

## Summary

Attempted to create a minimal reproduction of the `Failure("nth")` error encountered when bundling TLS13 modules, but the bug **does not reproduce** with simple pattern matching.

## What We Tried

Created three simple F* modules with pattern matching:
- `Simple.State` - Basic state type
- `Simple.Internal` - Module with nested pattern matching  
- `Simple.API` - Top-level module using Simple.Internal

### Result

**Both bundle approaches work:**
- `-bundle 'Simple.API=Simple.State[rename=Simple]'` ✅ Works
- `-bundle 'Simple.API=Simple.State,Simple.Internal[rename=Simple]'` ✅ Works

## Conclusion

The `Failure("nth")` bug is **NOT** triggered by simple nested pattern matching. It requires something more complex present in the TLS13 codebase:

### Known Triggers (from TLS project)
- `-bundle 'TLS13.Connection=...,TLS13.Handshake,...'` ❌ Crashes
- `-bundle 'TLS13.Connection=...,TLS13.Record,...'` ❌ Crashes  
- `-bundle 'TLS13.Connection=...,TLS13.KeySchedule,...'` ❌ Crashes

### Possible Causes

The bug likely requires one or more of:
1. **Very deep nesting** of pattern matches (TLS13.Handshake.FlightState has complex multi-level matching)
2. **Large modules** (TLS13.Handshake.FlightState is ~2000 lines)
3. **Specific pattern combinations** not captured in this simple example
4. **Cross-module type dependencies** in pattern matching contexts
5. **Ghost/erased** values in pattern matching
6. **Refinement types** in pattern branches

## Recommendation

To properly report this bug to the KaRaMeL team, use the **actual TLS13 modules** as the reproduction case rather than a simplified example. The bug appears specific to the complexity/structure of that real-world code.

## Files in This Directory

- `Simple.State.fst` - Simple state module (bundles fine)
- `Simple.Internal.fst` - Pattern matching module (bundles fine) 
- `Simple.API.fst` - API module (bundles fine)
- `reproduce.sh` - Script that shows both bundles work
- `README.md` - Original expectations (bug doesn't reproduce here)
- `UNABLE_TO_REPRODUCE.md` - This file

## Next Steps

For bug reporting, point to the actual TLS13 code:
- Location: `/home/nswamy/workspace/agentic-tls/src/impl/`
- Problematic modules: `TLS13.Handshake.FlightState.fst`, `TLS13.Record.fst`
- Working example: Full TLS13 project with reproduction instructions in main repository
