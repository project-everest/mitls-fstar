# Why Are Internal TLS13_* Functions Exposed in the Bundle Header?

## The Question
The bundle header (TLS13.h) exposes ~35 internal functions with `TLS13_*` prefixes (like `TLS13_Handshake_send_client_hello`) in addition to the 8 public `client_*` functions. Why are these exposed? What component calls them?

## The Answer

**Short answer**: Nothing outside the bundle should call them. They are exposed because F*'s module system requires separate interfaces (.fsti files), and KaRaMeL generates non-static functions for cross-module calls even when all modules are bundled into a single .c file.

## Detailed Explanation

### 1. F* Module Structure
Our TLS implementation is structured as multiple F* modules:
- `TLS13.Client` (public API)
- `TLS13.Connection` (connection management)
- `TLS13.Handshake` (handshake logic)
- `TLS13.Record` (record layer)
- etc.

Each module has its own `.fsti` interface file that declares what functions are visible to other F* modules.

### 2. Cross-Module Calls
`TLS13.Connection` imports and calls functions from `TLS13.Handshake`:
```fstar
module HD = TLS13.Handshake.Driver
module HS = TLS13.Handshake

// Connection calls Handshake functions
HS.send_client_hello ctx ch
```

### 3. KaRaMeL's Bundling Behavior
When we bundle with:
```
-bundle 'TLS13.Client=TLS13.*[rename=TLS13]'
```

KaRaMeL:
- ✅ Bundles all `TLS13.*` modules into a single `TLS13.c` file
- ✅ Removes the `TLS13_Client_` prefix from TLS13.Client functions  
- ❌ Does NOT make internal module functions `static` (only 23 static functions out of 137 total)

**Why?** Because each F* module had a separate `.fsti` interface, KaRaMeL treats them as separate compilation units and generates non-static functions for their exported symbols.

### 4. What Should Call These Functions?
**NOTHING.** The internal `TLS13_*` functions are implementation details of the bundled TLS13.c file. They exist for:
- Cross-module calls **within** the bundle (Connection → Handshake, etc.)
- Structural separation in the F* code

External code should **only** call the 8 `client_*` functions.

### 5. Ideal vs. Actual State

**Ideal**: All `TLS13_*` functions would be `static` in TLS13.c, visible only internally.

**Actual**: They're exposed in TLS13.h because KaRaMeL's bundling doesn't automatically staticize functions from multi-module F* code.

**Mitigation**: Clear documentation that these are internal, and using `extract-bundle` as the only extraction mechanism makes it clear this is a single-file artifact.

## Resolution

- ✅ Removed `extract-connection` (multi-file) to avoid confusion
- ✅ Updated README.md to clearly explain these are internal
- ✅ Fixed Makefile to only extract modules with .fst implementations
- 📝 Documented that only `client_*` functions should be called by external code

The bundle is correct and safe - the exposed internal functions are just an artifact of F*'s module system meeting KaRaMeL's bundling model.
