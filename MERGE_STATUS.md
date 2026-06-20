# Merge Status: EverParse Integration

**Date**: 2026-06-16  
**Branch**: tls_server_merge  
**Merging**: origin/main (commit 02455bc)  
**Status**: IN PROGRESS - Phase 1 partially complete

## What Has Been Done

### 1. Merge Initiated
- Ran `git merge origin/main --no-ff --no-commit`
- Found 12 conflicted files as expected

### 2. Conflicts Resolved (5/12)
✅ **TLS_SERVER.md**: Deleted (kept main's deletion, we have STATUS_SERVER.md)  
✅ **c_stubs/tls13_connection_backend.h**: Later removed after parser/serializer extraction wiring
✅ **Makefile**: Resolved by taking main's EverParse infrastructure and keeping our SERVER_DRIVER_BUNDLE sections  
✅ **c_stubs/tls13_crypto_external.h**: Took main's (erased option types, simplified signatures)  
✅ **c_stubs/tls13_openssl_karamel.c**: Took main's (erased FStar.Pervasives.Native options)  

### 3. Remaining Conflicts (7/12)

These need manual resolution because they involve:
- Server predicates we added
- Pairing theorem dependencies  
- Wire.Spec changes for WireFormatLemmas

**Files**:
1. `src/impl/TLS13.Impl.Client.Types.fst` (2 conflicts)
2. `src/impl/TLS13.Impl.ConnectionState.Bounds.fsti` (1 conflict)
3. `src/impl/TLS13.Impl.ConnectionState.Model.fsti` (2 conflicts)
4. `src/impl/TLS13.Impl.ConnectionState.Repr.fsti` (1 conflict)
5. `src/impl/TLS13.Record.fst` (1 conflict)
6. `src/impl/TLS13.Record.fsti` (1 conflict)
7. `src/spec/TLS13.Wire.Spec.fst` (2 conflicts)

**Total**: 11 conflict blocks

## Resolution Strategy for Remaining Files

### General Approach
For each file:
1. Extract three versions: base, ours, theirs
2. Identify what changed:
   - **Theirs (main)**: EverParse parser integration, extraction improvements
   - **Ours**: Server predicates, pairing theorem additions
3. Merge:
   - Take their EverParse changes
   - Add back our server/pairing predicates
   - Update any conflicting definitions to use both changes

### Specific Files

#### src/impl/TLS13.Impl.Client.Types.fst
**Expected conflicts**: 
- Main: References to generated types, new parser postconditions
- Ours: May have server-related client type extensions

**Resolution**: Take main's parser changes, check if we added server-specific client predicates and keep them.

#### src/impl/TLS13.Impl.ConnectionState.Model.fsti
**Expected conflicts**:
- Main: May have changed ghost log structure or model predicates
- Ours: Added server-specific model predicates, pairing log predicates

**Resolution**: CRITICAL - carefully merge both. Server predicates and paired log predicates must be preserved.

#### src/impl/TLS13.Impl.ConnectionState.Repr.fsti
**Expected conflicts**:
- Main: May have changed connection_state representation
- Ours: May have added server-specific repr fields

**Resolution**: Check if representation changed; if so, update server code to match new repr.

#### src/impl/TLS13.Impl.ConnectionState.Bounds.fsti
**Expected conflicts**:
- Main: May have added/changed bounds for new parser types
- Ours: May have server-specific bounds

**Resolution**: Merge both bounds.

#### src/impl/TLS13.Record.fst/.fsti
**Expected conflicts**:
- Main: Uses new parser/serializer interfaces
- Ours: May have server-specific record handling

**Resolution**: Take main's parser changes, add back any server-specific record functions.

#### src/spec/TLS13.Wire.Spec.fst
**Expected conflicts**:
- Main: Refactored for EverParse, moved definitions to Reveal modules
- Ours: May reference WireFormatLemmas, have parseback additions

**Resolution**: Take main's refactoring, ensure our WireFormatLemmas still has what it needs (or adjust WireFormatLemmas to use main's new structure).

## Next Steps to Complete Phase 1

### Step 1: Resolve Remaining Conflicts

For each file listed above:

```bash
# Example for Client.Types.fst:
git show :1:src/impl/TLS13.Impl.Client.Types.fst > /tmp/base.fst
git show :2:src/impl/TLS13.Impl.Client.Types.fst > /tmp/ours.fst  
git show :3:src/impl/TLS13.Impl.Client.Types.fst > /tmp/theirs.fst

# Manual 3-way merge using editor
# Produce resolved version
cp /tmp/resolved.fst src/impl/TLS13.Impl.Client.Types.fst
git add src/impl/TLS13.Impl.Client.Types.fst
```

### Step 2: Verify Our Key Files Are Present

After all conflicts resolved:

```bash
# These must exist:
ls -la src/impl/TLS13.Impl.Driver.Pairing.fsti
ls -la src/impl/TLS13.Impl.Server.Driver.fsti
ls -la src/spec/TLS13.Spec.WireFormatLemmas.fsti
ls -la AUDIT_0616.md STATUS_SERVER.md TLS_SERVER_DESIGN_AND_IMPL.md

# Check server files
ls -la src/impl/TLS13.Impl.Server*.fst*
ls -la runtime/tls13_server_driver.*
```

### Step 3: Complete Merge Commit

```bash
git status  # Should show all conflicts resolved
git commit -m "Merge origin/main: EverParse integration

... (use commit message from MERGE_PLAN.md)"
```

## Next Steps: Phase 2-5

After merge commit completes, proceed with MERGE_PLAN.md phases 2-5:

- **Phase 2**: ./setup.sh, make regen-generated, make verify-generated, fix verification
- **Phase 3**: Make client/server interop tests pass
- **Phase 4**: Validate and document
- **Phase 5**: Implement verified server parsers

## Current Git State

```bash
$ git status --short | head -20
M  Makefile
D  TLS_SERVER.md
M  c_stubs/tls13_connection_backend.h
M  c_stubs/tls13_crypto_external.h
M  c_stubs/tls13_openssl_karamel.c
UU src/impl/TLS13.Impl.Client.Types.fst
UU src/impl/TLS13.Impl.ConnectionState.Bounds.fsti
UU src/impl/TLS13.Impl.ConnectionState.Model.fsti
UU src/impl/TLS13.Impl.ConnectionState.Repr.fsti
UU src/impl/TLS13.Record.fst
UU src/impl/TLS13.Record.fsti
UU src/spec/TLS13.Wire.Spec.fst
... (plus ~220 new files from generated/)
```

The merge is ready to continue with manual resolution of the 7 remaining F* files.
