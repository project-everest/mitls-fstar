---
name: deviteration
description: Iterate fast on F*/Pulse proofs by admitting every definition except the one being edited. Use when a single proof module takes minutes to re-verify and that cycle time is dominating development.
---

# Fast proof iteration

## The problem

Large F*/Pulse proof modules take minutes to re-verify. The instinctive fix —
"split the file into smaller modules behind `.fsti` interfaces" — is usually
**wrong**, and it is expensive to discover that after doing the work.

## Measure before restructuring

Three numbers tell you what to do. Take them with a **warm dependency cache**
(all `.checked` files present except the one for the file under test):

| Run | Flags | What it measures |
|---|---|---|
| Full | *(none)* | Baseline |
| One definition | `--admit_except 'Module.def'` | Fixed cost + that definition's SMT |
| No SMT | `--admit_smt_queries true` | Fixed cost alone (elaboration + loading deps) |

Measured on ATLAS (mitls-fstar), single-threaded:

| File | Lines | Full | One def | No SMT |
|---|---|---|---|---|
| `TLS13.Impl.ConnectionState.Network.fst` (Pulse) | 4382 | 3m16s | 58s | 44s |
| `TLS13.ConnectionState.ProtectedWireClientFinishedInversion.fst` | 4166 | 6m56s | 2m30s | 19s |

### Reading the numbers

**Fixed cost was only 19–45s.** Elaboration and dependency loading are not the
problem; SMT is, and SMT time is attached to *individual definitions*.

Therefore:

- **Splitting the file does not help.** The proof obligations move to another
  module but do not shrink, and each new module re-pays the fixed cost. You can
  easily make the total *worse*.
- **What is worth splitting is a monolithic lemma.** In the second file above,
  one lemma (`lemma_client_side_cf`, at `z3rlimit 400`) accounted for 2m11s of
  the 6m56s. A lemma that needs a high rlimit is the real target: break it into
  smaller lemmas each provable at low rlimit.
- **For iteration, admit everything else.** 3.4x–20x, immediately, with no
  restructuring at all.

If instead you measure a *large* fixed cost, the diagnosis flips: the module has
too many/too heavy dependencies, and splitting (or trimming `open`s) is
justified. Measure, don't assume.

## The iteration loop

```bash
# Working on one lemma or one Pulse fn:
fstar.exe <flags> --admit_except 'Module.the_definition' Module.fst

# Structural check only — no SMT at all.  Catches syntax, binder scoping and
# (for Pulse) slprop framing errors.  Fastest possible signal.
fstar.exe <flags> --admit_smt_queries true Module.fst
```

`--admit_except` accepts `Module.name` or `(Module.name, goal_id)` to target a
single goal within a definition.

Both work on **Pulse `fn`s**, not just pure F* lemmas.

An important and useful asymmetry: `--admit_except` admits only *SMT queries*.
Pulse **elaboration** errors — binder scoping, `unfold`/`fold` mismatches,
slprop framing, "Cannot check relation with uvars" — are still reported for
*every* definition in the file. So a `quick` run is a full structural check of
the whole module plus a full proof of the one definition you name. You are not
flying as blind as "admit everything else" suggests.

The DEF-less form is the best first move after any edit to a Pulse file: Pulse
framing errors are common, and finding them in 20–45s instead of 3 minutes
changes how you work.

### Wire it into the build

Worth a `make` target, because two details are easy to get wrong:

```make
QUICK_CACHE = _cache_quick

quick:
	@rm -rf $(QUICK_CACHE)
	@cp -r --reflink=auto $(CACHE_DIR) $(QUICK_CACHE) 2>/dev/null \
	  || cp -r $(CACHE_DIR) $(QUICK_CACHE)
	@rm -f $(QUICK_CACHE)/$(notdir $(FILE)).checked
	$(FSTAR) --cache_dir $(QUICK_CACHE) \
	  $(if $(DEF),--admit_except '$(DEF)',--admit_smt_queries true) \
	  $(FILE)
	@rm -f $(QUICK_CACHE)/$(notdir $(FILE)).checked
```

## Two traps

**1. Never let an admitting run write the shared cache.**

This is the important one. `--admit_except` and `--admit_smt_queries` still
produce a `.checked` file, and a partially-admitted `.checked` is
*indistinguishable* from a real one. If it lands in the shared cache, every
downstream module is then verified against admitted facts, and the build stays
green while proving nothing.

Always redirect to a scratch `--cache_dir` seeded from the real one. Copying is
cheap (334MB in 0.38s with `--reflink=auto` on a CoW filesystem; use plain `cp`
as fallback). Keep exactly one command — the real `make verify` — as the only
writer of the real cache.

**2. Don't let `make` regenerate the dependency graph on every cycle.**

`.depend` is invalidated by editing *any* source file, and regenerating it via
`--dep full` cost ~2.5min here — dwarfing the ~1min cycle the whole technique
exists to provide. The first `make quick` measured 3m30s for what should have
been 1m0s, entirely because of this.

The quick target uses no rule from `.depend`, so exclude it from the include:

```make
DEPEND_EXCLUDED_GOALS := clean ... quick
ifeq (,$(filter $(DEPEND_EXCLUDED_GOALS),$(MAKECMDGOALS)))
include .depend
endif
```

## Things that did not work

Recording these so they are not re-tried.

- **`--use_hints` / `--record_hints`.** Unusable with the F* build shipped in
  this project's `tools/everparse`. Recording is fine, but *replay* fails with
  duplicate Z3 declarations:

  ```
  Unexpected output from Z3:
    (error "line 833 column 45: invalid declaration, function
     'Prims.op_AmpAmp' (with the given signature) already declared")
  ```

  It fails even on a 370-line module, with and without `--ext fly_deps`, so it
  is not a scale or extension-interaction issue. Worth re-testing after a
  toolchain upgrade — hints would help a lot, since they would speed up the
  *unedited* definitions in a file, which `--admit_except` skips entirely rather
  than checking cheaply.

- **`--split_queries always`.** F* warns when it splits queries implicitly,
  which suggested wasted work (try whole query → fail → split → retry). Measured
  no difference: 2m33s vs 2m30s. Still valuable for *localizing* an error, just
  not for speed.

## Discipline

`--admit_except` admits real proof obligations, so it is a development aid only:

- Run the full, unadmitted build before every commit, and at every phase boundary.
- Never commit on the strength of a `quick` run.
- Keep a zero-admit check (e.g. `make admit-count`) in the gate, so genuine
  `admit()`s in source can't hide either.
