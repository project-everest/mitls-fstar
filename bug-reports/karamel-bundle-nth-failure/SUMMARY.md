# Summary: KaRaMeL Bundle Bug Investigation

## The Bug

When trying to bundle TLS13 implementation modules with KaRaMeL:

```bash
krml -bundle 'TLS13.Connection=TLS13.Handshake,...[rename=TLS13]' ...
```

KaRaMeL crashes with:
```
✔ [Pattern matches compilation] ⏱️ 167ms  
Fatal error: exception Failure("nth")
```

## Attempted Minimal Reproduction

Created simple F* modules (`Simple.State`, `Simple.Internal`, `Simple.API`) with pattern matching - **bug does NOT reproduce**.

## Actual Reproduction

The bug **only** occurs with the real TLS13 code. To reproduce:

1. Clone: https://github.com/FStarLang/agentic-tls  
2. Navigate to: `/home/nswamy/workspace/agentic-tls`
3. Run: `make verify` (verifies all modules)
4. Run: `make extract-bundle`

This will attempt the failing bundle command. See `Makefile` line 168 for exact krml invocation.

## Files

- `Simple.*.fst` - Simple test modules (don't trigger bug)
- `reproduce.sh` - Script showing simple modules work
- `README.md` - Original bug description  
- `UNABLE_TO_REPRODUCE.md` - Details on why simple case doesn't trigger bug
- `SUMMARY.md` - This file

## Recommendation

Report bug using full TLS13 project as reproduction, not simplified example.
