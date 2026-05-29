# Calc Sample - Design Notes

## Request Dispatcher - COMPLETE ✅

The `process_request` function in `Calc.Server.fst` is now **fully implemented** for all 6 operations:

- Tag 0 = Push (parses 4-byte value, checks stack not full)
- Tag 1 = Peek (checks stack not empty)
- Tag 2 = Add (checks stack has >= 2 elements)
- Tag 3 = Sub (checks stack has >= 2 elements)
- Tag 4 = Mul (checks stack has >= 2 elements)
- Tag 5 = Div (checks stack has >= 2 elements)
- Other tags = Error response

Each operation checks its precondition and either:
- Calls the appropriate handler (process_push, process_peek, etc.) if precondition met
- Returns Error response via write_error_response if precondition fails

## Error Handling - Current Limitation

### The `step_log_X_pre` Pattern

Each operation has a `step_log_X_pre` predicate that checks if the operation can execute:
- `step_log_push_pre`: stack size < 10
- `step_log_peek_pre`: stack size > 0
- `step_log_add_pre`, etc.: stack size >= 2

These are **preconditions**, not part of the state machine itself.

### Why This Matters

When an operation fails its precondition (e.g., Add on a stack with <2 elements):
1. The dispatcher returns an Error response (via `write_error_response`)
2. **BUT** the ghost log is NOT updated properly

The issue: `write_error_response` doesn't take the server state or update the ghost log. It just writes error bytes to the response buffer.

### Why We Can't Fix This Easily

To properly handle errors in the ghost log, we would need:

1. **Calc.Spec.step to return Error responses**
   - Currently returns `None` on invalid operations
   - Should return `Some (state, Error)` instead
   - This affects the entire state machine semantics

2. **step_log_error function**
   - Would append Error to responses without changing state
   - But log_consistent requires running Calc.Spec.step
   - Which currently doesn't produce Error responses

### Proper Fix (Future Work)

To handle errors correctly in the ghost log:

1. Update `Calc.Spec.step` to return `Some (state, Error)` instead of `None`
2. Update `Calc.Spec.run` to handle Error responses
3. Add `step_log_error` function to Calc.Log
4. Add consistency and evolution lemmas for error transitions
5. Update handlers to call `step_log_error` when preconditions fail

This is a significant redesign but would make the error handling architecturally sound.

### Current Status

**What works:**
- All 6 operations fully implemented and verified (0 admits)
- Complete wire-to-semantic proofs for successful operations
- Dispatcher checks preconditions and routes to correct handlers
- Error responses returned when preconditions fail

**What doesn't work:**
- Error responses are not reflected in the ghost log
- No wire-to-semantic correspondence proof for error cases
- `write_error_response` doesn't update ghost state

**For TLS application:**
- This pattern is sufficient if error handling is managed at a higher layer
- TLS could have separate error handling that doesn't go through the verified path
- OR: TLS could implement the proper fix described above

## Architectural Question Raised

**User's insight**: Why do we need step_log_X_pre preconditions at all? The state machine should handle all transitions including errors.

**Answer**: You're absolutely right. The current design with preconditions is architecturally limiting. A proper state machine would:
- Accept all operations
- Return Error when preconditions aren't met
- Have this reflected in the state transition

The step_log_X_pre pattern is a compromise that makes proofs easier but limits expressiveness.

## Conclusion

The calc_sample demonstrates the **happy path** methodology completely (0 admits). Error handling architecture needs redesign for completeness. This is a known limitation, not a methodology failure.

For TLS: Decide whether to:
1. Accept error handling at a higher layer (pragmatic)
2. Implement full error state machine (architecturally pure)
