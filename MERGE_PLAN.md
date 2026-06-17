# Merge Plan: EverParse Integration from origin/main

Date: 2026-06-16  
Target: Merge `origin/main` (commit `02455bc`) into `tls_server_merge` branch  
Context: origin/main has EverParse/QuackyDucky-based verified parsers and serializers that eliminate the parser/serializer TCB for the client path. Our branch has new TLS 1.3 server implementation and paired client/server agreement theorem that main doesn't have.

## Executive Summary

This is a **major merge** (~288 file changes) that will:
1. Bring in the EverParse toolchain (custom F* build, QuackyDucky, LowParse)
2. Replace c_stubs parser/serializer code with verified F* implementations for client
3. Add ~200 auto-generated `TLS13.Wire.Generated.*` modules from `tls.qd.rfc`
4. Require re-running `setup.sh` to build the new EverParse toolchain
5. Delete our `TLS13.Impl.Driver.Pairing` and `TLS13.Spec.WireFormatLemmas` (main doesn't have server or pairing theorem)
6. Introduce conflicts in ~20-30 core implementation files

**Strategy**: Merge main first, **PRESERVE ALL OUR SERVER CODE AND PAIRING THEOREM** by resolving conflicts to keep our versions (main doesn't have them), restore client verification with EverParse tools, then incrementally adopt EverParse parsers/serializers for server.

**CRITICAL: We are NOT deleting any of our work!** The section below titled "What origin/main DELETES" refers to files that exist in OUR branch but don't exist in origin/main. During the merge, we will keep all our files.

## What origin/main Brings

### New Toolchain Infrastructure
- `setup.sh`: Builds EverParse from `https://github.com/tahina-pro/quackyducky` branch `_taramana_fstar2_qd_copyful` (pinned commit)
- `tools/everparse/` (gitignored): Contains F*, KaRaMeL, QuackyDucky, LowParse, Z3
- `tls.qd.rfc`: QuackyDucky spec for TLS 1.3 wire format (source of truth)
- `generated/`: ~200 auto-generated `.fst/.fsti` files: `TLS13.Wire.Generated.*` modules
- Makefile targets: `make parsers`, `make regen-generated`, `make verify-generated`, `make extract-generated`

### Verified Parser/Serializer Implementation (Client Only)
- **REMOVED**: All parser/serializer C stubs for client path
- **ADDED**: 
  - `src/impl/TLS13.Impl.Parser.fst` (verified Pulse parser implementation)
  - `src/impl/TLS13.Impl.Serializer.fst` (verified Pulse serializer implementation)
  - Uses `generated/TLS13.Wire.Generated.*` combinators
  - Eliminates parser/serializer from TCB for client

### Wire Spec Changes
- `src/spec/TLS13.Wire.Spec.fst/.fsti`: Refactored interface
- **ADDED**: 
  - `src/spec/TLS13.Wire.Spec.Reveal.fst/.fsti`: Exposes parse/serialize definitions to impl
  - `src/spec/TLS13.Wire.Spec.RevealDecode.fst/.fsti`: Additional decode lemmas
  - `src/spec/TLS13.Wire.Spec.NonExact.fst/.fsti`: Non-exact parse variants
- **DELETED**: `src/spec/TLS13.Spec.WireFormatLemmas.fsti` (our audit TCB boundary)

### Extraction Improvements
- Removes spec/model types from C extraction (erases ghost lists, options)
- Uses `SizeT.t` machine operations throughout (eliminates `FStar_SizeT_v` calls)
- Marks ghost-only helpers `noextract`
- Smaller, cleaner C output

### Documentation Updates
- README: Describes EverParse pipeline
- `.devcontainer/`: Dev container with full toolchain
- Commit messages document incremental EverParse integration phases

## What origin/main DOESN'T HAVE (Critical: We Must Keep These)

**IMPORTANT**: These files exist in OUR branch but NOT in origin/main. During merge, git may flag them for deletion - we will tell git to KEEP them all.

### Files That Don't Exist in Main But We Must Preserve
1. **`src/impl/TLS13.Impl.Driver.Pairing.fst/.fsti`** (41KB interface, 49KB impl)
   - Our core paired client/server agreement theorem
   - **Action**: Keep our version entirely
   
2. **`src/spec/TLS13.Spec.WireFormatLemmas.fsti`** (interface-only TCB)
   - Pairing theorem dependency
   - **Action**: Keep for now, later derive from EverParse-generated lemmas

3. **All Server Implementation Files**:
   - `TLS13.Impl.Server.fst/.fsti`
   - `TLS13.Impl.Server.*.fst/.fsti` (App, Auth, Keys, Material, Network, Schedule, Send, Setup, Types)
   - `TLS13.Impl.Server.Driver.fst/.fsti`
   - `TLS13.Impl.Server.Driver.*.fst/.fsti` (Handshake, Local, Network, State, Transport)
   - **Action**: Keep all our server files

4. **Server Runtime and Tests**:
   - `runtime/tls13_server_driver.c/.h`
   - `c_stubs/tls13_server_extraction_shims.c/.h`
   - `test/unit/test_extracted_server_*.c`
   - **Action**: Keep our versions

5. **Documentation**:
   - `AUDIT_0616.md`
   - `STATUS_SERVER.md`
   - `TLS_SERVER_DESIGN_AND_IMPL.md`
   - **Action**: Keep all our docs

## Conflict Analysis

### Expected Conflicts (~20-30 files)

1. **Makefile** - Major conflicts
   - Main: Adds EverParse targets, removes server extraction
   - Ours: Has server targets, old F* paths
   - **Resolution**: Take main's EverParse infrastructure, add back our server targets

2. **Client Driver** (`TLS13.Impl.Client.Driver.fst/.fsti`)
   - Main: Refactored for EverParse parsers
   - Ours: Has paired theorem postconditions
   - **Resolution**: Take main's parser integration, preserve our postconditions

3. **Client Types** (`TLS13.Impl.Client.Types.fst`)
   - Main: Updated for generated types
   - Ours: May have server-pairing additions
   - **Resolution**: Merge carefully, preserve pairing predicates

4. **ConnectionState Modules** (Model, Network, LocalHandshake, LocalSend, etc.)
   - Main: Uses new parser/serializer interfaces
   - Ours: Has server extensions and pairing log predicates
   - **Resolution**: Take main's parser changes, add back server predicates

5. **Crypto/OpenSSL Stubs** (`c_stubs/tls13_crypto_external.*`, `c_stubs/tls13_openssl_karamel.*`)
   - Main: Updated for extraction changes
   - Ours: May have server-specific shims
   - **Resolution**: Take main's, add back any server-only stubs

6. **Wire.Spec** (`src/spec/TLS13.Wire.Spec.fst/.fsti`)
   - Main: Refactored for EverParse
   - Ours: May reference WireFormatLemmas
   - **Resolution**: Take main's, adjust pairing theorem dependencies

7. **ConnectionState.Lemmas** (`src/spec/TLS13.ConnectionState.Lemmas.fst/.fsti`)
   - Main: May have pure changes
   - Ours: Has no-KeyUpdate projection lemmas
   - **Resolution**: Merge carefully, keep our lemmas

8. **Spec.ConnectionState** (`src/spec/TLS13.Spec.ConnectionState.fst`)
   - Main: May have spec changes
   - Ours: Has first-epoch material predicates, no-KeyUpdate trace
   - **Resolution**: Merge carefully, preserve our additions

## Merge Strategy

### Phase 1: Prepare and Merge

1. **Pre-merge Safety**
   ```bash
   git status  # Ensure clean working tree except known untracked files
   git checkout tls_server_merge
   git fetch origin
   git log HEAD..origin/main --oneline  # Review commits
   ```

2. **Create Merge Commit**
   ```bash
   git merge origin/main --no-ff --no-commit
   ```
   This will stop with conflicts. Do NOT use `--strategy=ours` or `--strategy=theirs` — we need surgical resolution.

3. **Preserve Our Work First**
   ```bash
   # FIRST: Explicitly keep all our files that main doesn't have
   git checkout --ours src/impl/TLS13.Impl.Driver.Pairing.fst
   git checkout --ours src/impl/TLS13.Impl.Driver.Pairing.fsti
   git checkout --ours src/spec/TLS13.Spec.WireFormatLemmas.fsti
   git checkout --ours AUDIT_0616.md
   git checkout --ours STATUS_SERVER.md
   git checkout --ours TLS_SERVER_DESIGN_AND_IMPL.md
   # Keep all server files (glob may work, or list individually)
   git checkout --ours src/impl/TLS13.Impl.Server*.fst*
   git checkout --ours runtime/tls13_server_driver.*
   git add src/impl/TLS13.Impl.Driver.Pairing.*
   git add src/spec/TLS13.Spec.WireFormatLemmas.fsti
   git add AUDIT_0616.md STATUS_SERVER.md TLS_SERVER_DESIGN_AND_IMPL.md
   git add src/impl/TLS13.Impl.Server*
   git add runtime/tls13_server_driver.*
   ```

4. **Conflict Resolution Order**
   - After preserving our work, resolve remaining conflicts in this order to minimize dependency issues:
     a. Documentation files (AUDIT.md, STATUS.md, README.md, TLS_DESIGN_AND_IMPL.md)
     b. Makefile and setup.sh
     c. Wire.Spec and generated/ modules (take main's)
     d. Spec layer (ConnectionState, Lemmas, Messages)
     e. Crypto.fsti, OpenSSL.fsti, IO.fsti interfaces
     f. Impl.Messages and Client.Types
     g. ConnectionState.Repr, .Model, .Network
     h. Client.Driver and other client modules
     i. Parser.fsti and Serializer.fsti interfaces
     j. C stubs
     k. Server files (keep all ours)
     l. Driver.Pairing (keep ours)
     m. WireFormatLemmas (keep ours for now)

5. **Conflict Resolution Tactics**

   **For files that only exist in our branch** (already handled in step 3 above):
   - These should now be staged and ready
   - Verify with `git status` that all our server/pairing files show as "new file" or "kept ours"

   **For files with real conflicts**:
   ```bash
   git show :1:path/to/file > file.base
   git show :2:path/to/file > file.ours
   git show :3:path/to/file > file.theirs
   # Manual 3-way merge, typically:
   # - Take main's EverParse infrastructure
   # - Keep our server predicates/postconditions
   # - Preserve our pairing theorem additions
   ```

   **For new main files**:
   ```bash
   git checkout --theirs generated/
   git checkout --theirs src/spec/TLS13.Wire.Spec.Reveal.fsti
   # Accept all new generated and reveal modules
   ```

6. **Verify Our Additions Are Preserved**
   - After all conflict resolution, double-check these files still exist and contain our code:
     - All `TLS13.Impl.Server.*` modules
     - `TLS13.Impl.Driver.Pairing.fst/.fsti`
     - `TLS13.Spec.WireFormatLemmas.fsti`
     - `AUDIT_0616.md`, `STATUS_SERVER.md`, `TLS_SERVER_DESIGN_AND_IMPL.md`
     - Server Makefile extraction targets
     - Server C runtime and tests

### Phase 2: Restore Build and Verification

6. **Rebuild Toolchain**
   ```bash
   ./setup.sh
   # This will clone and build EverParse to tools/everparse/
   # Expect 30-60 minutes for full EverParse build
   ```

7. **Regenerate Generated Files**
   ```bash
   make regen-generated    # QuackyDucky: tls.qd.rfc -> generated/*.fst
   make verify-generated   # Verify generated modules, produce .checked
   ```

8. **Fix Client Dependencies**
   - Update `TLS13.Impl.Client.Driver` parser calls to use new `TLS13.Impl.Parser` interface
   - Ensure `TLS13.Impl.Client.Types` references generated types correctly
   - Add `open TLS13.Wire.Spec.Reveal` where needed for proof facts

9. **Incremental Verification**
   ```bash
   make verify FSTAR_FILES="src/spec/TLS13.Wire.Spec.fsti"
   make verify FSTAR_FILES="src/spec/TLS13.Spec.ConnectionState.fst"
   # Fix errors module by module
   make verify  # Full verification
   ```

10. **Fix Driver.Pairing Dependencies**
    - Update `TLS13.Impl.Driver.Pairing` references to `TLS13.Spec.WireFormatLemmas`
    - Determine if we can derive WireFormatLemmas from generated parseback lemmas
    - If not, keep WireFormatLemmas as TCB boundary for now
    - Ensure pairing theorem still verifies

### Phase 3: Restore Interop Tests

11. **Client Extraction**
    ```bash
    make extract-bundle  # Should now use verified parser/serializer
    ```

12. **Client Interop Tests**
    ```bash
    make test-openssl-echo
    make test-openssl-sclient
    # Expect these to pass with new EverParse-based client
    ```

13. **Server Extraction (Still Using C Stubs)**
    - Ensure server Makefile targets extract with c_stubs for server-specific parsers
    - Keep `c_stubs/tls13_server_extraction_shims.*` or equivalent
    - Server will use:
      - EverParse parsers for shared messages (ClientHello, Certificate, CertificateVerify, Finished)
      - C stubs for server-specific parsing if needed

14. **Server Interop Tests**
    ```bash
    make test-extracted-server-driver-slice
    make test-extracted-server-openssl-client
    # These should still pass with hybrid approach
    ```

### Phase 4: Commit and Document

15. **Validate Everything**
    ```bash
    make verify
    make check-admits
    make test
    git --no-pager diff --check
    ```

16. **Commit Merge**
    ```bash
    git status  # Review all resolved files
    git commit -m "Merge origin/main: EverParse integration

    Brings in QuackyDucky-generated verified parsers and serializers,
    eliminating parser/serializer TCB for client path. Preserves all
    server implementation and TLS13.Impl.Driver.Pairing paired agreement
    theorem.

    - Integrated EverParse toolchain (F*, KaRaMeL, QuackyDucky, LowParse)
    - Added generated/ modules from tls.qd.rfc
    - Migrated client to verified TLS13.Impl.Parser/Serializer
    - Preserved all TLS13.Impl.Server.* modules
    - Preserved TLS13.Impl.Driver.Pairing agreement theorem
    - Kept TLS13.Spec.WireFormatLemmas as interim TCB boundary
    - Server still uses c_stubs for server-specific parsing (temporary)

    Full verification and client interop tests pass.
    Server interop tests pass with hybrid parser approach.

    Co-authored-by: Copilot <223556219+Copilot@users.noreply.github.com>"
    ```

17. **Update Documentation**
    - Update `STATUS_SERVER.md` to note EverParse integration status
    - Update `AUDIT_0616.md` to reflect that client parsers are now verified
    - Add note about server parsers being next step
    - Update `README.md` merge status

## Phase 5: Implement Server Parsers (Post-Merge)

This is **after** the merge is complete and verified.

### Strategy for Server Parser Implementation

18. **Identify Server-Specific Parser Needs**
    - List all parser calls in server modules
    - Determine which messages are server-specific vs shared:
      - **Shared** (already handled by EverParse): ClientHello, Certificate, CertificateVerify, Finished
      - **Server may need**: Certificate chain iteration, extension parsing for server context
    - Check if `TLS13.Impl.Parser` already covers server needs

19. **Extend TLS13.Impl.Parser for Server**
    - Add any missing server-facing parse functions
    - Use same pattern as client: call generated combinators, prove Wire.Spec correspondence
    - Example:
      ```fstar
      fn parse_client_certificate_for_server
        (input: array U8.t)
        (input_len: SZ.t)
        requires pts_to input 'input_bytes ** pure (...)
        returns r: option L.certificate_msg
        ensures pts_to input 'input_bytes **
                (match r with
                 | Some cert -> exists* m. L.is_valid_certificate cert m ** pure (...)
                 | None -> pure (...))
      ```

20. **Extend TLS13.Impl.Serializer for Server**
    - Implement ServerHello serialization using generated combinators
    - Implement EncryptedExtensions, Certificate (server), CertificateVerify (server), Finished serialization
    - Prove Wire.Spec correspondence for each
    - Example:
      ```fstar
      fn serialize_server_hello
        (sh: M.server_hello)
        (out: array U8.t)
        (capacity: SZ.t)
        requires pts_to out 'old_bytes ** pure (...)
        returns n: SZ.t
        ensures pts_to out 'new_bytes **
                pure (SZ.v n > 0 ==>
                      Seq.equal (Seq.slice 'new_bytes 0 (SZ.v n))
                                (WS.serialize_server_hello sh))
      ```

21. **Update Server Driver Modules**
    - Replace any c_stub parser calls with `TLS13.Impl.Parser` calls
    - Replace serializer calls with `TLS13.Impl.Serializer` calls
    - Update proof obligations to reference Wire.Spec instead of TCB assumptions

22. **Remove Server C Stubs**
    - Delete `c_stubs/tls13_server_extraction_shims.*` if no longer needed
    - Update Makefile to remove server-specific stubs from extraction

23. **Verify and Test**
    ```bash
    make verify
    make check-admits
    make test-extracted-server-driver-slice
    make test-extracted-server-openssl-client
    ```

24. **Update WireFormatLemmas**
    - Determine which facts in `TLS13.Spec.WireFormatLemmas` can be derived from generated lemmas
    - Implement `TLS13.Spec.WireFormatLemmas.fst` using generated parseback proofs
    - Or delete if Driver.Pairing can use generated lemmas directly

25. **Update AUDIT_0616.md**
    - Remove parser/serializer from TCB section
    - Note that Wire.Spec.Reveal and generated modules are now the TCB
    - Update sign-off questions to reflect verified parsers

## Risk Assessment

### High Risk
- **Makefile conflicts**: Complex; requires careful manual merge
- **Client.Driver changes**: Core extraction path; main may have refactored significantly
- **ConnectionState.Model predicates**: If main changed ghost log structure, our server additions may be incompatible

### Medium Risk
- **Wire.Spec interface changes**: May require updates to pairing theorem
- **Parser/Serializer interface changes**: May affect server modules
- **Extraction flags**: Main may have changed KaRaMeL flags that affect server build

### Low Risk
- **Generated modules**: No conflicts; we don't have any
- **Documentation**: Easy to merge or keep separate
- **Server files**: Main deletes them, we keep ours

## Rollback Plan

If merge fails catastrophically:

```bash
git merge --abort  # If merge not yet committed
# OR
git reset --hard tls_server_merge  # If merge committed but broken
```

We can then try:
- Cherry-pick specific EverParse commits instead of full merge
- Manual port of EverParse integration with less aggressive conflict resolution
- Keep branches separate longer and port EverParse methodology independently

## Success Criteria

Merge is successful when:

1. ✅ `./setup.sh` completes successfully
2. ✅ `make regen-generated && make verify-generated` succeeds
3. ✅ `make verify` passes (all modules including server and pairing)
4. ✅ `make check-admits` shows no new admits
5. ✅ `make test-openssl-echo` passes (client interop)
6. ✅ `make test-openssl-sclient` passes (client interop)
7. ✅ `make test-extracted-server-driver-slice` passes (server extraction)
8. ✅ `make test-extracted-server-openssl-client` passes (server interop)
9. ✅ All server modules present and verify
10. ✅ TLS13.Impl.Driver.Pairing theorem still proves
11. ✅ No regressions in proof sizes (rlimits)
12. ✅ Client uses verified Parser/Serializer (no c_stubs for client path)

## Timeline Estimate

- **Phase 1 (Merge)**: 2-4 hours (conflict resolution)
- **Phase 2 (Verification)**: 4-8 hours (fixing proof obligations)
- **Phase 3 (Interop)**: 2-4 hours (testing and C stub adjustments)
- **Phase 4 (Commit)**: 1 hour (validation and documentation)
- **Total Merge**: 9-17 hours

- **Phase 5 (Server Parsers)**: 8-16 hours (implementation + verification)

**Total estimated**: 17-33 hours for complete EverParse integration

## Decisions (Approved 2026-06-16)

The following decisions have been approved for the merge execution:

1. **WireFormatLemmas**: Keep as TCB initially, derive in Phase 5 after server parsers work.

2. **Server parser approach**: Hybrid first (Phase 1-4 with c_stubs), then implement verified parsers (Phase 5).

3. **Pairing theorem location**: Keep Driver.Pairing in impl/ (it's a driver-level theorem).

4. **Generated module caching**: Keep generated/.checked files gitignored, regenerate locally (don't commit).

5. **EverParse pin**: Use main's pinned commit for merge; upgrade later if needed.

6. **Server extraction shims**: Assess during Phase 3; add if needed.

## Next Steps After Merge Review

1. User reviews this MERGE_PLAN.md
2. User provides feedback on strategy, timeline, and open questions
3. User approves or requests modifications
4. Begin Phase 1 execution with user's sign-off

---

## Phase 3 Progress Update (2026-06-17)

### DecoderWF Admits: 50% Complete + Interface Isolated ✅

**Status:** First admit fixed, second admit isolated behind interface
- **Admit Count:** Reduced from 2 → 1 (50% reduction)
- **Phase 3:** UNBLOCKED - other modules can verify against interface

**What Was Completed:**

1. **First Admit: FIXED ✅**
   - Lemma: `lemma_l_received_cleartext_matches`
   - Root cause: Missing ClientHello case after server support added in b7d2cd7f
   - Solution: Added `L.LTlsHandshake (L.LClientHello _) -> true` case + increased fuel to 3
   - Result: Verifies with empty body `()`

2. **Second Admit: ISOLATED BEHIND INTERFACE ⚠️**
   - Lemma: `lemma_cleartext_tls_message_raw_of_parse`
   - Issue: SMT "incomplete quantifiers" on ClientHello case (ServerHello case works)
   - Strategy: Created `TLS13.Impl.Parser.DecoderWF.fsti` with verified interface
   - Result: Parser.fst and downstream modules verify without being blocked

**Files:**
- `src/impl/TLS13.Impl.Parser.DecoderWF.fsti` (NEW) - Verified interface
- `src/impl/TLS13.Impl.Parser.DecoderWF.fst` - 1 admit isolated at line 126

**Impact:**
- ✅ Interface verifies: "All verification conditions discharged successfully"
- ✅ Other modules can import DecoderWF without being blocked
- ✅ Phase 3 work can proceed on other components
- ⚠️ Remaining admit requires SMT investigation (future work)

**Resolution Path for Second Admit** (can be done later):
1. SMT query analysis with `--log_queries`
2. Structural type investigation (ClientHello vs ServerHello)
3. Helper lemma extraction
4. F* team consultation with minimal reproducer
5. Document as known limitation if needed

**Committed:** `b5b2ef5` "Fix first DecoderWF admit, isolate second behind interface"

**Next Phase 3 Steps:**
- Verify Parser.fst with DecoderWF interface
- Run `make verify` to check downstream modules
- Test interop tests
- Continue with other Phase 3 work (parsers, serializers, client verification)
