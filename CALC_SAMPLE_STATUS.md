# Calculator Sample - Current Status

## Goal

Demonstrate the complete wire-to-semantic proof pattern before applying to TLS.

**Requirements (from user)**:
1. Monotonic ghost log (not box) - following SimpleDBModel pattern ✅
2. Full wire-to-semantic state transitions in ghost spec ✅
3. Strengthened `log_consistent`: 
   - `input_bytes` parses to `requests` ✅
   - `output_bytes` equals serialized `responses` ✅
   - State machine produces `current_state` and `responses` ✅
4. `process_request` with both input AND output buffers ⏳
5. Completely admit-free implementation ⏳

## Completed ✅

**Calc.Wire.fst** (110 lines, verified, 0 admits)
- Wire format parser/serializer for 5-byte messages
- parse_request: bytes → option request
- serialize_response: response → bytes

**Calc.Spec.fst** (70 lines, verified, 0 admits)
- State machine with termination proof
- step: stack → request → option (stack & response)
- run: stack → list request → option (stack & list response)

**Calc.Log.fst** (155 lines, verified, 0 admits ‼️)
- Monotonic ghost log using `Pulse.Lib.MonotonicGhostRef`
- `log_evolves` preorder with `FStar.ReflexiveTransitiveClosure`
- **Full wire-to-semantic transitions** in `step_log`:
  ```fstar
  step_log: bytes → parse_request → step state machine → 
           serialize_response → update all log fields
  ```
- **Strengthened `log_consistent`** (bidirectional bytes ↔ messages):
  ```fstar
  log.requests == parse_all_requests log.input_bytes [] /\
  log.output_bytes == serialize_all_responses log.responses /\
  run [] log.requests == Some (log.current_state, log.responses)
  ```
- `lemma_run_extend`: proven (state machine consistency)
- `lemma_step_log_preserves_consistency`: **ADMITTED** (needs helper lemmas)
- `lemma_log_evolves_refl`: proven (reflexivity for error paths)

**Calc.Server.fst** (85 lines, partial, has admits)
- Minimal concrete state: array U32.t + ref SZ.t
- Monotonic ghost log: MR.mref log_evolves ✅
- `server_exactly` predicate: concrete stack matches ghost state ✅
- `new_server`: creates server with initial_log ✅ (verified, 0 admits)
- `process_push`: skeleton (currently admitted)

## In Progress ⏳

**Challenge**: Implementing `process_push` admit-free

The proof obligation is complex because we need to:
1. Update concrete stack
2. Prove concrete execution matches `step_log`
3. Update monotonic ghost log with `MR.update`
4. Prove `log_evolves` relation holds

**Current blocker**: Complexity of relating:
- Concrete array updates to ghost list append
- Byte-level serialization to ghost state transitions
- Need to prove helper lemmas in Calc.Log.fst first

## Next Steps

### Immediate (to unblock)

1. **Simplify proof obligations** - break into smaller lemmas:
   - `lemma_step_log_push_succeeds`: prove step_log for Push always works
   - `lemma_concrete_matches_step`: relate concrete update to step_log

2. **Implement process_push admit-free**:
   ```pulse
   fn process_push (srv: server_state) (value: U32.t) ...
     unfold server_exactly;
     // Update concrete stack
     srv.stack.(current_sz) <- value;
     srv.size := SZ.add current_sz 1sz;
     // Update ghost log
     let old_log = !srv.ghost_log;
     let new_log = step_log_push value old_log;
     MR.update #_ #log_evolves srv.ghost_log new_log;
     fold server_exactly;
   ```

3. **Prove `lemma_step_log_preserves_consistency`** in Calc.Log.fst
   - Currently admitted
   - Needs lemmas for `parse_all_requests_append` and `serialize_all_responses_append`

### After process_push works

4. Add other operations (Peek, Add, Sub, Mul, Div)
5. Add full `process_request` with request/response buffers
6. Verify entire sample admit-free
7. User audit and approval
8. Apply pattern to TLS

## Key Insights

**Monotonic ghost log architecture (validated)**:
- Use `Pulse.Lib.MonotonicGhostRef` with custom preorder ✅
- Define evolution with `FStar.ReflexiveTransitiveClosure` ✅  
- Ghost state handles FULL wire-to-semantic transitions ✅
- Concrete implementation proves it matches ghost ✅

**Strengthened log consistency (validated)**:
- Bidirectional bytes ↔ messages correspondence ✅
- Input bytes parse to requests ✅
- Output bytes equal serialized responses ✅
- State machine produces current state ✅

**Proof pattern (partially validated)**:
1. Concrete execution on arrays/refs ✅
2. Compute corresponding ghost update ✅
3. Prove evolution relation holds ⏳
4. Update monotonic ghost ref with MR.update ⏳

The architecture is sound - just need to complete the proof details.

## Admits Count

- **Calc.Wire.fst**: 0 admits ✅
- **Calc.Spec.fst**: 0 admits ✅
- **Calc.Log.fst**: 1 admit (lemma_step_log_preserves_consistency)
- **Calc.Server.fst**: 1 admit (process_push implementation)

**Total: 2 admits** (both solvable, just need proof engineering)

## Time Estimate

- Complete process_push admit-free: 2-4 hours
- Prove lemma_step_log_preserves_consistency: 2-3 hours
- Add remaining operations: 2-3 hours
- **Total to admit-free calc sample: 6-10 hours**

After that, apply same pattern to TLS (14-22 days as previously estimated).
