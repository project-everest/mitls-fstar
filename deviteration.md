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

## Diagnose with `--query_stats` before theorising

A cancelled (resource-exhausted) query reports whatever proof obligation it
happened to be working on when the budget ran out. That message is frequently
unrelated to the real problem.

A real example: `HTTP.Wire.Length.fst` reported

```
Subtyping check failed; expected type `uint_t 16`, got `Prims.nat`
```

which looks like a missing bound on a `pow2 16` term. Two fixes aimed at
`pow2` normalisation were wasted. `--query_stats` showed the truth in one line:

```
failed {reason-unknown=unknown because canceled} ... rlimit 5 (used rlimit 5.000)
```

The definition was simply still at F*'s default `rlimit 5`, while every
neighbour in the same file ran at 20–300.

**Rule: run `--query_stats` first, always.** It tells you (a) which query,
(b) whether it *failed* or was *cancelled*, and (c) how much budget it actually
used. Only (b) distinguishes "my proof is wrong" from "my proof is too big",
and the two need opposite responses.

## SMT context weight: when splitting *does* help

The measurements above show that splitting a file rarely helps, because the
*fixed* cost (elaboration, loading deps) is small. That is still true. But there
is a second effect they do not capture: **every preceding definition in a module
is in the SMT context of the queries that follow it.**

Observed repeatedly during the Z3 4.15.3 upgrade: a lemma with an empty (`()`)
proof verified in 25s–1m34s in a standalone probe module, yet was cancelled at
the same rlimit inside its 2300–4200-line home module. Nothing about the lemma
changed; only the ambient context did.

The effect is sharper than "big file, slow proof" suggests. When
`lemma_client_control_change_progress` was moved into a new module, it *still*
failed — until the one neighbouring lemma that had been moved with it was left
behind. A single extra lemma **statement** in scope was the difference between
proved and cancelled.

So the two diagnoses are distinguished as follows:

| Symptom | Diagnosis | Fix |
|---|---|---|
| High `--admit_smt_queries true` time | Heavy dependencies | Trim `open`s / split the file |
| Definition proves standalone, is cancelled in place | SMT context weight | Move that definition, **and only its minimal prerequisites**, into a new small module |
| Definition cancelled at `rlimit 5` while neighbours use 20+ | Never given a budget | Match the file's own convention |

When factoring for context weight, move the *minimum*. Carrying a neighbour
along can defeat the whole exercise.

## Solver upgrades: watch for divergence, not just failure

When changing Z3 versions, the dangerous regression is not a proof that fails —
it is a proof that **never returns**.

`rlimit` bounds Z3's search, but the counter does not advance in every solver
phase. A query that sends Z3's arithmetic solver into a non-terminating
search is therefore *never cancelled*: the build hangs indefinitely rather than
reporting an error. During the 4.15.3 upgrade one 151-line Pulse module
(`Calc.Impl.Peek`) went from 14.8s to over 49 minutes with no output, holding up
the entire sample build. `--query_stats` under a `timeout` identified the query
immediately: the last one printed is the one that hung.

Two practical consequences:

- **A hanging build is a proof bug, not a slow machine.** Check for it with
  `ps -eo pid,etime,args | grep -E 'fstar.exe|z3-'`. A single `z3-<version>`
  process with a large elapsed time names the file, and `--query_stats` under
  `timeout` names the query.
- **Non-linear arithmetic is the usual culprit.** The fix is the one the F*
  manual already recommends: get the arithmetic out of the big VC. Prove it as a
  standalone pure lemma, one substitution per step, and call that lemma. In the
  case above, hoisting a big-endian decode (`be_to_n (slice b 1 5) == U32.v v`)
  out of a Pulse `fn` into a pure lemma in a small module took the module from
  a 49-minute hang to 5.8s.

**`.checked` files do not record the Z3 version.** Changing `--z3version` alone
does not invalidate the cache, so an incremental build will pass instantly while
still trusting proofs certified by the *old* solver. Wipe every `_cache` (the
root one and each sample's) before believing a solver-upgrade result.

Verified by A/B on a warm cache: the same `fstar.exe` invocation with
`--z3version 4.15.3`, with `--z3version 4.13.3`, and with no `--z3version` at
all loads the identical `.checked` file without complaint. Do not put the solver
version into a `.checked` cache key — it buys nothing and only causes misses.

## Cache a derived artefact under a hash of the artefact, not of its source

A `.checked` file is validated against the **digest of the `.fst`/`.fsti` it was
produced from**. Under `--already_cached` a mismatch is not a silent re-check,
it is a hard build failure:

```
Warning 241: ... .checked is stale (digest mismatch for <source>)
Error 317:   Expected <source> to already be checked.
```

Read that pair literally. `digest mismatch for <source>` names the file whose
*content* differs from what the cache recorded — it is not a statement about
flags, the solver, or the F* version (those produce a different message,
"has incorrect version").

CI caches the verification of the committed `generated/TLS13.Wire.Generated.*`
modules. The key originally hashed `tls.qd.rfc`, the QuackyDucky input those
modules are generated *from*. That is one level too high: regeneration is not
bit-reproducible across EverParse builds, and a merge can take `generated/` from
one side while `tls.qd.rfc` matches the other. `agentic` and `chromium` ended up
with byte-identical `tls.qd.rfc` and *different* `OfferedVersion.fsti`, so a PR
from `chromium` restored `agentic`'s tarball under a colliding key and died on
Error 317 — with no local repro, because locally the cache is always self-made.

The rule: **key the cache on the exact bytes the cached artefact was derived
from.** Here that is `hashFiles('generated/**')` plus the toolchain pin. If the
sources are committed, hash the sources; hash the upstream generator input only
when nothing downstream of it is committed.

## A green local build proves nothing if the toolchain has drifted

`tools/everparse` is gitignored, so nothing forces it to agree with the commit
pinned in `scripts/build-everparse.sh`. When the pin was bumped, a checkout that
already had a toolchain kept the old one, and every local proof was checked
against the wrong F*/Pulse, for weeks, with no signal of any kind.

Nothing in the build notices. `--version` reports a coarse date tag
(`F* 2026.07.19~dev`) that says nothing about which commit was built and is
identical across every commit of a given day, so it neither confirms nor refutes
that a tree matches the pin. The `.checked` cache does record the F* build, but
it reacts to a mismatch by silently re-verifying rather than warning. And the
sources under `tools/everparse` look right, because they *are* a consistent
checkout -- just of the wrong commit.

The only reliable identity for an F* build is the commit it was built from:

```
git -C tools/everparse rev-parse HEAD
git -C tools/everparse/opt/FStar rev-parse HEAD
```

The symptom was a CI failure in a single module that would not reproduce
locally, on any branch, from a cold cache. Hours went into hunting a phantom
OOM and a phantom cache bug before the toolchain itself was suspected. The
lesson generalises past this one pin: when CI and a local tree disagree about a
*proof*, suspect the prover before the proof.

`make check-toolchain` now asserts `EVERPARSE_HOME` is at the pinned commit and
fails the build otherwise (`CHECK_EVERPARSE_PIN=0` to bypass deliberately). When
the pin moves, rebuild **and delete every `_cache`, `generated/*.checked` and
`generated/.checked.stamp`** — the stamp in particular will otherwise convince
make that the generated modules are still verified.

## A missing build-graph edge is the same failure, one layer down

The toolchain-drift bug above is an instance of a general shape: **a build step
that is silently skipped looks exactly like a build step that had nothing to
do.** It happened again in the Chromium overlay, and this time it reached as far
as a shippable artefact.

`third_party/atlas/BUILD.gn` linked the extracted engine the obvious way:

```gn
lib_dirs = [ "lib" ]
libs = [ "atlas_tls13_client_engine" ]
```

GN turns a short `libs` entry into a bare `-l` flag and **does not create a
dependency edge for it** — the name is a linker search term, not a file. So
ninja never learned that `chrome` depends on `libatlas_tls13_client_engine.a`.
Rebuilding and reinstalling the verified engine reported `ninja: no work to do`
and left the previously linked browser untouched.

The tell was a date, not an error. The installed archive was current; the
`chrome` supposedly packaged with it was five days and twenty-one `src/impl`
commits old, including a restructure of the drain loop. Every command in the
chain had exited 0. `make chromium-demo-bundle` would have shipped a browser
linked against a stale verified engine — the demo would have *worked*, and
demonstrated the wrong code.

The fix is to name the file where ninja is looking:

```gn
inputs = [ "lib/libatlas_tls13_client_engine.a" ]
libs = [ rebase_path("lib/libatlas_tls13_client_engine.a", root_build_dir) ]
```

Two things generalise:

- **`libs` is not a dependency in any build system that resolves it by search
  path.** The same hole exists in Make (`-lfoo` in `LDFLAGS` is not a
  prerequisite), CMake without an imported target, and Bazel `linkopts`. If a
  build input is named by a search term rather than a path, assume it is
  unwatched until proven otherwise.
- **Test the edge, not the build.** A successful rebuild proves nothing, because
  editing the build file forces work regardless. Touch *only* the dependency and
  check that the dependent is rebuilt:

  ```bash
  touch third_party/atlas/lib/libatlas_tls13_client_engine.a
  autoninja -C out/atlas chrome     # must do work, not "no work to do"
  ```

  Before the fix: no-op. After: 894 steps and a relinked `chrome`.

Note also that `install_chromium_overlay.py` uses `shutil.copy2`, which
*preserves* mtime. Copying a freshly built archive can therefore leave it
looking older than the binary that consumed it — timestamps are evidence, but
only once you know which tool set them.

## Pulse: an unmeasured `while` is divergent

Pulse `while` loops now take an optional `decreases` measure, and the choice is
not cosmetic — it decides the loop's *effect*:

| Loop | Effect | Allowed in |
|---|---|---|
| `while` with `decreases` | `stt` | plain `fn` |
| `while` without `decreases` | `stt_div` | `divergent fn` only |

An unmeasured loop inside a plain `fn` fails, but the message names neither
`while` nor `decreases`:

```
* Error 228 at ...(54,2-99,3):
  - Tactic failed
  - Cannot compose computations in this divergent block:
  - This computation has effect: 'stt_div'
  - The continuation has effect: 'stt'
```

The range is the whole `while`; `stt_div` is the loop and `stt` is whatever
follows it. Pulse *can* lift the continuation to `stt_div`, but refuses when a
post-hint is present — so the error appears exactly on functions that carry an
`ensures`, i.e. all of ours. `divergent fn` silences it; adding the measure is
better, because a fuel-bounded loop is terminating and there is no reason to put
its callers on the divergent fragment.

One constraint on the measure: **it may not contain an `if`.** The purifier that
rewrites `!r` into its ghost value descends into applications but not into match
branches, so `decreases (if !keep_going then SZ.v !remaining + 1 else 0)` leaves
the reads unelaborated and fails with a confusing "`!remaining` has type `fn
requires ... returns ...`". Restructure instead so the measure is a plain read:
in `TLS13.Impl.Client.DrainLoop`, dropping the separate `keep_going` flag and
having every exit path zero the fuel made the measure just `SZ.v !remaining`.

## Four levers that cut the build 13%

A full profiling round (cold `verify`, `--query_stats`, plus a shim recording
wall time and peak RSS per `fstar.exe` invocation) took the build from 10377s to
9009s of CPU. Ranked by what they teach:

**1. Never pair `--z3refresh` with `--split_queries always` (-742s, -7.2%).**
The tell is a module burning hundreds of seconds across hundreds of queries at a
*used rlimit near zero* — `receive_application_data` spent 185.8s over 371
queries for a total used rlimit of 70, i.e. 0.19 per query. That is not solving.
`--z3refresh` starts a fresh Z3 per query; combined with a flag that multiplies
the number of queries, every split query pays process startup plus a re-parse of
the whole context. All 13 `--z3refresh` sites in the repo were paired this way.
Removing them left the query count *identical* at 36143 — proof that the change
was VC-neutral — while SMT time fell 4999s to 4520s and peak RSS fell ~600MB.

**2. `#restart-solver` roughly every 800 lines in big modules (-335s).**
Look for a monotonic ramp in cost-per-query against position in the file.
`TLS13.Impl.Parser.fst` ran 78, 68, 127, 108, 148, 117, 144, 221, 177, 320 ms
per query across its ten deciles — 4x degradation with no change in goal
difficulty. That is accumulated solver state, and it is why a 7278-line module
with only two `#push-options` sites is slow. Tuning the interval on that module:
no restarts 501.5s, 4 restarts 372.6s, 8 restarts 337.9s, 14 restarts 327.7s.
The knee is near 800 lines; below that the extra context re-sends eat the gain.
Not every big module ramps — `ConnectionState.Lemmas` peaks in the middle
(specific costly lemmas) and `Impl.ConnectionState.Queries` is flat (its cost is
Pulse elaboration, not SMT), so measure per module before inserting.

**3. `assert_norm` never needed fuel (-98s in one 165-line file).**
`TLS13.Wire.Spec.Reveal.CertificateVerify` carried `--initial_fuel 50
--max_fuel 50` at six sites and fuel 100 at a seventh, to prove a 34-byte
literal equals `append` of a 33-byte literal and a zero byte — by enumerating
all 34 indices in a match. The fuel existed only to unfold `List.length` 34
times, which `assert_norm` does by normalization at fuel 0. Replacing the
enumeration with one induction (`seq_of_list` distributes over `append`) took
the file from 99.2s to 9.0s and 165 lines to 131, with the `.fsti` untouched.

**4. Transparent quantified predicates in an `.fsti` are a cascade waiting to
happen (-106s in one module).** Profile the worst single query, don't guess:

```bash
fstar.exe ... --log_queries --query_stats Module.fst      # writes queries-*.smt2
z3 smt.qi.profile=true queries-Module-5.smt2 2> qi.txt
awk '/\[quantifier_instances\]/ {t[$2]+=$4} END {for(n in t) printf "%9d %s\n",t[n],n}' \
  qi.txt | sort -rn | head
```

For `lemma_finish_strong` (134.2s in a *single* query) this showed one predicate
equation firing 3,085,362 times, twelve times the next quantifier and in exact
1:1 lockstep with a nested quantifier interpretation — a cascade, not hard work.
The predicate was a transparent `let ... : prop` in an `.fsti`: a sixteen-variable
existential nesting a `forall` and two `exists` over `L.memP`. Transparent and in
an interface means its equation is in every downstream context. Marking it
`[@@"opaque_to_smt"]` needed *no other change in the defining module* — nothing
there required the unfolding, so all three million instantiations were waste —
and exactly one consumer needed a `reveal_opaque`.

The general shape: a 1:1 count between a definition's `equation_` and an
`l_quant_interp_`, with the fuel-instrumented axioms of whatever the body
iterates over trailing behind it.

After all four, SMT is 43% of the build and the frontend/Pulse elaboration is
57%. Further gains have to come from splitting the big Pulse modules
(`Impl.ConnectionState.Queries` is 78% non-SMT, `LocalHandshake` 72%), not from
the solver.

## Things that did not work

Recording these so they are not re-tried.

- **`--ext context_pruning`.** Not in `FSTAR_FLAGS`, so it looked like a free
  repo-wide win. A/B on `ConnectionState.ServerCanonicalShape`: 117.5s without,
  116.5s with. No effect — either already on by default or inapplicable here.

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
