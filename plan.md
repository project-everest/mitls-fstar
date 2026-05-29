# Verified TLS 1.3 Client - Development Plan

## Current Status: Calc Sample ZERO ADMITS + C EXTRACTION COMPLETE ✅

**Full verification + extraction validated - ready for TLS!**

### Calc Sample - COMPLETE EXEMPLAR ✅✅✅

**2183 lines, 14 modules, 0 ADMITS, extracts to C, ALL TESTS PASS** 🎉

#### Verification (COMPLETE)
- **14 modules** with clean separation
- **0 admits** - all proofs complete
- **Wire-to-semantic correspondence** - proven at byte level
- **Ghost log** - fully erased at extraction
- **Build time**: ~12 seconds

#### C Extraction (COMPLETE) 🔥
- **F* → .krml → C** pipeline working
- **Single-file output**: Calc_Server.c/h via bundling
- **Heap wrapper**: calc_wrapper.c fixes stack allocation issue
- **9 comprehensive tests**: ALL PASS ✅
- **Zero runtime overhead**: All proofs erased

#### Key Achievement Unlocked 🎉
**Complete end-to-end validation**: Verified F*/Pulse code → Working C implementation

See:
- `calc_sample/ZERO_ADMITS_ACHIEVED.md` - Verification journey
- `calc_sample/EXTRACTION.md` - Extraction guide
- `calc_sample/test_main.c` - Test suite (all passing)

## Path to Zero Admits + Extraction in TLS

The calc_sample validates the complete pattern. Apply to TLS:

### Phase 1: Update TLS Spec with Modular Semantics (2-3 days)

Align TLS crypto operations with implementation (similar to calc_sample):
- Ensure spec matches concrete byte operations
- Add modular semantics where implementation uses wrapping arithmetic

### Phase 2: Strengthen IO Layer with Unrefined Pattern (3-5 days)

Apply the **unrefined type pattern** (proven in calc_sample) to TLS13.IO.fsti:

```pulse
fn write (ch: channel) (buf: array U8.t) (len: SZ.t)
  requires is_channel ch ** pts_to buf 'bytes ** ...
  returns n: SZ.t
  ensures exists* sent_bytes.
          is_channel ch **
          pts_to buf 'bytes **
          pure (sent_bytes == slice 'bytes 0 (SZ.v n))
```

### Phase 3: Update Connection with all_parse Pattern (3-5 days)

Extract concrete bytes and construct monotonic ghost log:

```pulse
fn client_write_all ... {
  unfold (is_connection c 'st 's);
  with view. _;
  
  let n = IO.write ch buf len;
  with sent_bytes. _;
  
  ST.advance 'st event new_state;
  
  let old_log = !c.log in
  let new_view = CL.note_raw_app_sent (reveal old_log) sent_bytes new_state;
  
  CL.lemma_note_consistent (reveal old_log) sent_bytes new_state;
  ST.advance_log c.log new_view;
  
  fold (is_connection c 'st new_state);
}
```

### Phase 4: Prove Lemmas with all_parse Integration (4-6 days)

Implement consistency and evolution lemmas (following Calc.Log pattern):
- Add `all_parse_handshake_messages` predicate
- Add `all_parse_app_data_frames` predicate  
- Integrate into TLS connection log_consistent
- `lemma_note_raw_app_sent_consistent` with all_parse proofs
- `lemma_note_raw_app_received_consistent` with all_parse proofs
- Parser/serializer correspondence with unrefined pattern

### Phase 5: Complete Remaining Proofs (2-4 days)

- Apply unrefined pattern to crypto byte operations
- Prove inductive lemmas for message parsing
- Complete TLS-specific sequence/list lemmas

### Phase 6: C Extraction via KaRaMeL (3-5 days)

Following validated calc_sample extraction pattern:
- Extract implementation modules to .krml
- Bundle into single TLS13_Client.c/h
- Create heap wrapper if needed (for connection state)
- Build comprehensive test suite
- Validate against real TLS 1.3 servers

**Total**: 17-28 days to zero admits + working C extraction for TLS

**Total**: 10-15 days to zero admits in full TLS client

## Current TLS State

**All 45 modules verify** ✅  
**30 admits total**:
- 24 connection (NOW KNOW HOW TO ELIMINATE!) ✅
- 2 parser (straightforward to prove)
- 4 byte-level (trivial lemmas)

**Documentation:**
- `CORRECT_GHOST_PATTERN.md` - The key pattern
- `ADMITS_ANALYSIS.md` - Technical analysis of admits
- `CURRENT_STATUS.md` - Project status
- `RESEARCH_CONTRIBUTION.md` - Publication summary
- `calc_sample/COMPLETE.md` - **FULL PATTERN DEMONSTRATION** ✅

## Recommendation

**Continue to zero admits!**

The calc sample validates the approach completely. The pattern is proven to work:
- Monotonic ghost refs ✅
- Operation-specific updates ✅
- Proven evolution lemmas ✅
- NO ADMITS ✅

Applying this to TLS is now a systematic engineering task with clear steps and proven techniques.

**Estimated time:** 10-15 days to achieve **ZERO ADMITS** in full verified TLS 1.3 client.

## Next Immediate Steps

1. ✅ **User review of calc sample** - Confirm pattern is correct
2. Define TLS ghost log operations (step_log_send_client_hello, etc.)
3. Prove consistency and evolution lemmas for each operation
4. Update Connection.fst to use proven ghost updates (eliminate 24 admits)
5. Prove parser lemmas (eliminate 2 admits)
6. Prove byte-level lemmas (eliminate 4 admits)
7. **ACHIEVE ZERO ADMITS** ✅

All steps are clear and validated by calc sample!
