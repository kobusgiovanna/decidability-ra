# On the Decidability of Verification under Release/Acquire

A Lean 4 mechanization of the reduction from Post's Correspondence Problem (PCP)
to state reachability for RMW-free programs under Release/Acquire (RA), from
*On the Decidability of Verification under Release/Acquire*. 
We have guided Claude AI in formalizing this result, following the paper proof. 
It covers Section 3 of the paper
(the reduction: the program of Fig. 7, soundness and completeness, and all of
Lemmas 3.1-3.13), together with the definitions of Section 2 it builds on and
Appendices A (the semantics of the pseudocode) and B (the proofs of
Section 3). Section 4 (bounded context switches) is not covered.

It is fully proved, with no `sorry` and only Lean's three standard axioms (see
[What the proof relies on](#what-the-proof-relies-on)).

## The main theorem

```lean
theorem reduction (I : PCPInstance) : I.HasSolution ↔ (ConcProg I).ReachesFinal
```

(`RAUndecidability/Reduction/Main.lean`). `I.HasSolution` says that the PCP
instance `I` has a solution; `ConcProg I` is the concurrent program of Fig. 7
built from `I`; `ReachesFinal` says that some RA-consistent execution of it
reaches its final state, every thread having run to completion. The two
directions are Lemma 3.3 (`completeness`) and Lemma 3.1 (`soundness`).

Undecidability of RA reachability, the paper's Theorem 1.1, follows from this
together with the undecidability of PCP and the computability of
`I ↦ ConcProg I`; neither of those is mechanized here.

## What the proof relies on

* **Axioms.** The results depend only on Lean's three standard axioms,
  `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry`, no
  `axiom` declaration and no `native_decide`; see
  [Verifying the results](#verifying-the-results).
* **Lean and Mathlib.** Lean `v4.33.1` and Mathlib `v4.33.1` (pinned in
  `lake-manifest.json`).
* **Definitions taken from Lean and Mathlib.** The statement is built from:
  natural numbers `ℕ` and `Fin n` (event indices, PCP indices, the mod-4
  counters); `List` (words, and PCP's tiles); `Option`, `Sum`, `Prod` and
  `Bool`; `Finset`, `Fintype` and `Finite` (the finite set of events of an
  execution, finiteness of the domains and of a program's states);
  `Relation.TransGen` (happens-before, `hb = (po ∪ rf)⁺`); and
  `IsStrictTotalOrder` (`po` and `mo` are total orders).
* **The pseudocode's expressions.** Appendix A's command language is defined
  in Lean (`RAUndecidability/ProgramSemantics/`), but its expressions and
  guards are Lean functions: each thread provides `eval`, `evalB` and `evalV`
  (`RAUndecidability/Reduction/Threads.lean`), so that, for example,
  `c ← (c + 1) mod 4` is addition in `Fin 4` and `aux = ⊥` is a Lean
  `Option` test. These functions, and the thread programs themselves (laid out
  line by line next to Fig. 7), are what must be checked against the paper by
  reading.

## Differences from the paper

* **Termination.** In the paper, a sequential program is an LTS over event
  labels, and a thread's final state is entered by the transition of its last
  event. Here, termination is an explicit symbol `term`: a sequential program
  is an LTS over event labels and `term`, the final state is entered exactly
  by `term`-transitions (taken when the thread's code can silently reach
  `term`), and an execution reaches the final state when each thread's word
  followed by `term` does. Both definitions make a non-empty word reach the
  final state exactly when the thread can run to completion after emitting it;
  they differ only on the empty word.
* **No read-modify-writes.** The paper's Section 2 allows RMW events; here
  events are reads and writes only, as the reduction concerns RMW-free
  programs, so the atomicity axiom does not arise. Executions have finitely
  many events.
* **Indices.** Event indices are 0-based: `nthWrite t x 0` is the paper's
  `w_1(t, x)`. Inequalities such as `i < j - 1` are stated as `i + 1 < j`.

## Paper ↔ Lean correspondence

Each paper statement or definition points to one
Lean declaration, whose docstring begins with the corresponding **Paper:**
reference; intermediate results are omitted. Where the paper states a lemma
for a list of cases (Lemmas 3.2 and 3.11), the Lean statement quantifies over
that list, written out in the paper's order next to it. Line links point into
the current sources.

### Main result

| Paper | Lean | Location |
|---|---|---|
| §3.3, ¶ Reduction (Lemmas 3.1 + 3.3): `I` has a solution iff `ConcProg I` has an execution in which all threads reach their final state | `reduction` | [Reduction/Main.lean:30](RAUndecidability/Reduction/Main.lean#L30) |

### Definitions

| Paper | Lean | Location |
|---|---|---|
| §2.1, ¶ Labeled Transition Systems | `LTS` | [Defs/Program.lean:67](RAUndecidability/Defs/Program.lean#L67) |
| §2.1, ¶ Labeled Transition Systems (words) | `Word` | [Defs/Program.lean:85](RAUndecidability/Defs/Program.lean#L85) |
| §2.1, ¶ Event labels | `EventLabel` | [Defs/Program.lean:143](RAUndecidability/Defs/Program.lean#L143) |
| §2.1, ¶ Sequential programs (see Termination, above) | `SequentialProgram` | [Defs/Program.lean:200](RAUndecidability/Defs/Program.lean#L200) |
| §2.1, ¶ Concurrent programs | `ConcurrentProgram` | [Defs/Program.lean:217](RAUndecidability/Defs/Program.lean#L217) |
| §2.2, ¶ Events | `Event` | [Defs/Execution.lean:36](RAUndecidability/Defs/Execution.lean#L36) |
| §2.2, ¶ Execution graphs | `ExecutionGraph` | [Defs/Execution.lean:80](RAUndecidability/Defs/Execution.lean#L80) |
| §2.2, ¶ Release/Acquire semantics (hb) | `ExecutionGraph.hb` | [Defs/Execution.lean:121](RAUndecidability/Defs/Execution.lean#L121) |
| §2.2, ¶ Release/Acquire semantics; Fig. 1 | `ExecutionGraph.RAConsistent` | [Defs/Execution.lean:143](RAUndecidability/Defs/Execution.lean#L143) |
| §2.2, ¶ Release/Acquire program semantics | `ConcurrentProgram.RASemantics` | [Defs/Execution.lean:184](RAUndecidability/Defs/Execution.lean#L184) |
| §2.2, ¶ Release/Acquire reachability (see Termination, above) | `ConcurrentProgram.ReachesFinal` | [Defs/Execution.lean:207](RAUndecidability/Defs/Execution.lean#L207) |
| App. A, ¶ Syntax | `Command` | [ProgramSemantics/Syntax.lean:66](RAUndecidability/ProgramSemantics/Syntax.lean#L66) |
| App. A, ¶ Operational semantics | `Step` | [ProgramSemantics/Step.lean:53](RAUndecidability/ProgramSemantics/Step.lean#L53) |
| App. A, ¶ Derived forms (`while NDet(X)`) | `Command.whileNdet` | [ProgramSemantics/Sugar.lean:30](RAUndecidability/ProgramSemantics/Sugar.lean#L30) |
| App. A, ¶ Derived forms (`for`) | `Command.forLoop` | [ProgramSemantics/Sugar.lean:39](RAUndecidability/ProgramSemantics/Sugar.lean#L39) |
| App. A, ¶ Derived forms (`First()`) | `Command.firstIt` | [ProgramSemantics/Sugar.lean:51](RAUndecidability/ProgramSemantics/Sugar.lean#L51) |
| App. A, ¶ The induced LTS (see Termination, above) | `inducedLTS` | [ProgramSemantics/LTS.lean:85](RAUndecidability/ProgramSemantics/LTS.lean#L85) |
| §3, ¶ Event indexing (`w_i(t, x)`) | `ExecutionGraph.nthWrite` | [Reduction/Index.lean:88](RAUndecidability/Reduction/Index.lean#L88) |
| §3, ¶ Event indexing (`r_i(t, x)`) | `ExecutionGraph.nthRead` | [Reduction/Index.lean:95](RAUndecidability/Reduction/Index.lean#L95) |
| §3, ¶ Post's Correspondence Problem | `PCPInstance` | [Reduction/PCP.lean:17](RAUndecidability/Reduction/PCP.lean#L17) |
| §3.5, ¶ The execution graph G | `executionGraphOf` | [Reduction/Completeness/Graph.lean:5475](RAUndecidability/Reduction/Completeness/Graph.lean#L5475) |
| §3.5, ¶ Bridge events | `Event.IsBridge` | [Reduction/Completeness/Construction.lean:1209](RAUndecidability/Reduction/Completeness/Construction.lean#L1209) |
| §3.5, ¶ Alternating and minimal hb-paths (hb-paths) | `Path` | [Reduction/Completeness/Paths.lean:30](RAUndecidability/Reduction/Completeness/Paths.lean#L30) |
| §3.5, ¶ Alternating and minimal hb-paths (alternating) | `Path.IsAlternating` | [Reduction/Completeness/Paths.lean:95](RAUndecidability/Reduction/Completeness/Paths.lean#L95) |
| §3.5, ¶ Alternating and minimal hb-paths (minimal) | `Path.IsMinimal` | [Reduction/Completeness/Paths.lean:177](RAUndecidability/Reduction/Completeness/Paths.lean#L177) |
| §3.5, ¶ Thread sets ($\mathsf{Tid}_x$) | `ThreadDomX` | [Reduction/Completeness/Construction.lean:1217](RAUndecidability/Reduction/Completeness/Construction.lean#L1217) |
| §3.5, ¶ Thread sets ($\mathsf{Tid}_y$) | `ThreadDomY` | [Reduction/Completeness/Construction.lean:1224](RAUndecidability/Reduction/Completeness/Construction.lean#L1224) |

### The program of the construction

| Paper | Lean | Location |
|---|---|---|
| Fig. 7 | `ConcProg` | [Reduction/ConcProg.lean:101](RAUndecidability/Reduction/ConcProg.lean#L101) |
| Fig. 7, thread $g_α^x$ | `GuessAX.program` | [Reduction/Threads.lean:548](RAUndecidability/Reduction/Threads.lean#L548) |
| Fig. 7, thread $g_α^{x′}$ | `PrimeAX.program` | [Reduction/Threads.lean:216](RAUndecidability/Reduction/Threads.lean#L216) |
| Fig. 7, thread $g_α^y$ | `GuessAY.program` | [Reduction/Threads.lean:348](RAUndecidability/Reduction/Threads.lean#L348) |
| Fig. 7, thread $g_α^{y′}$ | `PrimeAY.program` | [Reduction/Threads.lean:854](RAUndecidability/Reduction/Threads.lean#L854) |
| Fig. 7, thread $g_β^x$ | `GuessBX.program` | [Reduction/Threads.lean:1169](RAUndecidability/Reduction/Threads.lean#L1169) |
| Fig. 7, thread $g_β^{x′}$ | `PrimeBX.program` | [Reduction/Threads.lean:923](RAUndecidability/Reduction/Threads.lean#L923) |
| Fig. 7, thread $g_β^y$ | `GuessBY.program` | [Reduction/Threads.lean:1282](RAUndecidability/Reduction/Threads.lean#L1282) |
| Fig. 7, thread $g_β^{y′}$ | `PrimeBY.program` | [Reduction/Threads.lean:992](RAUndecidability/Reduction/Threads.lean#L992) |
| Fig. 7, thread $c^x$ | `CheckX.program` | [Reduction/Threads.lean:684](RAUndecidability/Reduction/Threads.lean#L684) |
| Fig. 7, thread $c^{x′}$ | `PrimeCheckX.program` | [Reduction/Threads.lean:773](RAUndecidability/Reduction/Threads.lean#L773) |
| Fig. 7, thread $c^y$ | `CheckY.program` | [Reduction/Threads.lean:1404](RAUndecidability/Reduction/Threads.lean#L1404) |
| Fig. 7, thread $c^{y′}$ | `PrimeCheckY.program` | [Reduction/Threads.lean:1484](RAUndecidability/Reduction/Threads.lean#L1484) |

### Names and notation

The Lean names of the threads and locations of Fig. 7, and of the events of
Section 3:

| Paper | Lean | | Paper | Lean |
|---|---|---|---|---|
| $g_α^x$, $g_α^y$, $g_β^x$, $g_β^y$ | `Tid.guessAX`, `.guessAY`, `.guessBX`, `.guessBY` | | $x_α$, $x_β$, $y_α$, $y_β$ | `Loc.xA`, `.xB`, `.yA`, `.yB` |
| $g_α^{x′}$, $g_α^{y′}$, $g_β^{x′}$, $g_β^{y′}$ | `Tid.primeAX`, `.primeAY`, `.primeBX`, `.primeBY` | | $x′_α$, $x′_β$, $y′_α$, $y′_β$ | `Loc.xA'`, `.xB'`, `.yA'`, `.yB'` |
| $c^x$, $c^y$ | `Tid.checkX`, `.checkY` | | $z_α^{x,x′}$, $z_α^{y,y′}$, $z_β^{x,x′}$, $z_β^{y,y′}$ | `Loc.zAxx'`, `.zAyy'`, `.zBxx'`, `.zByy'` |
| $c^{x′}$, $c^{y′}$ | `Tid.primeCheckX`, `.primeCheckY` | | $z_α^{x′,x}$, $z_α^{y′,y}$, $z_β^{x′,x}$, $z_β^{y′,y}$ | `Loc.zAx'x`, `.zAy'y`, `.zBx'x`, `.zBy'y` |
| | | | $z_α^{x,y}$, $z_β^{x,y}$ (bridge) | `Loc.zAxy`, `.zBxy` |
| | | | $ℓ_α^{y,x}$, $ℓ_β^{y,x}$ (bridge) | `Loc.ellAyx`, `.ellByx` |

The paper's $\mathtt{w}_i(t, x)$ and $\mathtt{r}_i(t, x)$, the $i$-th write and
read of thread $t$ on $x$, are `G.nthWrite t x (i - 1)` and
`G.nthRead t x (i - 1)`: Lean indices start at 0. Docstrings use the paper's
notation in plain text (`w_i(g_α^x, x_α)`, `⟶rf`, `⟶hb`), and Lean names where
they refer to code.

### Lemmas

Lemmas 3.4-3.13 are about the execution graph `G` of Section 3.5
(`executionGraphOf I hsol` in Lean).

| Paper | Lean |
|---|---|
| Lemma 3.1: if `ConcProg` has an execution where all threads reach their final state, then the PCP instance has a solution | [`soundness`](RAUndecidability/Reduction/Soundness.lean#L2188) |
| Lemma 3.2: in every execution where all threads reach their final state, for each `(writer, reader, location)` of Eq. (15)-(17), the reader's `i`-th read (if it exists) reads from the writer's `i`-th write | [`no_skipping_pairs`](RAUndecidability/Reduction/Soundness/NoSkippingLemma.lean#L59) |
| Lemma 3.3: if the PCP instance has a solution, then `ConcProg` has an execution where all threads reach their final state | [`completeness`](RAUndecidability/Reduction/Completeness.lean#L23) |
| Lemma 3.4: a `po`-edge `e_i → w_j` into a non-bridge write has `i ≤ j`, and `i < j` if `e_i` is a read | [`executionGraphOf_po_monotone`](RAUndecidability/Reduction/Completeness/Graph.lean#L5525) |
| Lemma 3.5: a decreasing `po`-edge `r_i → r_j` between non-bridge reads has `j = i - 1` and is one of the listed pairs | [`executionGraphOf_po_reads_decreasing`](RAUndecidability/Reduction/Completeness/Graph.lean#L5689) |
| Lemma 3.6: `hb` is irreflexive | [`executionGraphOf_hb_irrefl`](RAUndecidability/Reduction/Completeness/Consistency.lean#L924) |
| Lemma 3.7: if `a →hb b`, there is a minimal `hb`-path from `a` to `b` | [`executionGraphOf_hb_minimal`](RAUndecidability/Reduction/Completeness/Consistency.lean#L1054) |
| Lemma 3.8: a minimal `hb`-path between non-bridge events of threads in the same `Tid_x` or `Tid_y` contains no bridge event | [`executionGraphOf_write_to_write_no_bridge`](RAUndecidability/Reduction/Completeness/Consistency.lean#L1730) |
| Lemma 3.9: a minimal bridge-free `hb`-path `w_i ⇝ w_j` has `i ≤ j`, and `i < j` if the two writes are on different threads | [`executionGraphOf_write_to_write_no_bridge_increasing`](RAUndecidability/Reduction/Completeness/Consistency.lean#L1861) |
| Lemma 3.10: an `hb`-edge `r_i → r_j` between same-location reads of the checker threads has `i < j` | [`executionGraphOf_hb_checker_reads`](RAUndecidability/Reduction/Completeness/Consistency.lean#L2095) |
| Lemma 3.11: an `hb`-edge `w_i → w_j` between the writes of one of the four listed pairs has `i < j - 1` | [`executionGraphOf_hb_primed_gap`](RAUndecidability/Reduction/Completeness/Consistency.lean#L2607) |
| Lemma 3.12: for every location, `hb` between writes is increasing | [`executionGraphOf_hb_writes_increasing`](RAUndecidability/Reduction/Completeness/Consistency.lean#L2700) |
| Lemma 3.13: for every location, `hb` from a write to a read is non-decreasing | [`executionGraphOf_hb_write_read`](RAUndecidability/Reduction/Completeness/Consistency.lean#L3208) |
| §3.5, ¶ Proof of Lemma 3.3: `G` is RA-consistent (`hb` irreflexive by Lemma 3.6, and write and read coherence) | [`executionGraphOf_consistent`](RAUndecidability/Reduction/Completeness/Consistency.lean#L3959) |

## Requirements

Building the Lean library needs only [`elan`](https://github.com/leanprover/elan),
Lean's toolchain manager. It reads `lean-toolchain` and installs the pinned Lean
version (`leanprover/lean4:v4.33.1`). Install it once with

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

which puts `lake` and `lean` on your `PATH`. Everything below runs from the
repository root.

## Building the Lean formalization

The project builds on [Mathlib](https://github.com/leanprover-community/mathlib4).
Download Mathlib's prebuilt cache first; compiling Mathlib from scratch takes
hours:

```sh
lake exe cache get   # download the prebuilt Mathlib cache (network required)
lake build           # build the library and Verify.lean
```

A `lake build` that finishes without errors is the full check: the Lean kernel
has checked every proof, and `Verify.lean` has checked that every declaration
of the library depends only on the three standard axioms (see below). The build
needs a lot of memory; on a small machine, limit it, e.g. `systemd-run --user --scope -p MemoryMax=9G lake build`.

## Verifying the results

To list the axioms the main results rely on, put the following in a file inside
the repository, e.g. `Axioms.lean`, and run `lake env lean Axioms.lean`:

```lean
import RAUndecidability

#print axioms RAUndecidability.reduction
#print axioms RAUndecidability.soundness
#print axioms RAUndecidability.completeness
#print axioms RAUndecidability.no_skipping_pairs
#print axioms RAUndecidability.executionGraphOf_consistent
```

Each reports only Lean's standard axioms:

```
'RAUndecidability.reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There are no other axioms in the project, and no `sorry`. `Verify.lean` runs this
check on every declaration of the library, including those Lean generates
automatically, as part of `lake build`:
the build fails if any of them is an `axiom` or depends on an axiom other than
these three, `sorryAx` included.

## Repository layout

- **`RAUndecidability/`**: the Lean sources, following the paper:
  - `Defs/`: Section 2 — LTSs, programs, events, execution graphs, the RA
    axioms, reachability.
  - `ProgramSemantics/`: Appendix A — the command language, its steps, the
    derived forms, the induced LTS, resolutions, and an executable interpreter.
  - `Reduction/`: Section 3 — PCP, the twelve threads and `ConcProg`, event
    indexing, soundness (Lemma 3.1), completeness (Lemma 3.3) and the main
    theorem.
  - `Reduction/Soundness/`: the run and word characterization of each
    thread, and Lemma 3.2.
  - `Reduction/Completeness/`: the ingredients of the execution graph `G`,
    its monotonicity lemmas, `G` itself, `hb`-paths and RA-consistency
    (Lemmas 3.4-3.13).
  - `Util/`: general list lemmas.
- **`RAUndecidability.lean`**: root module importing the whole library.
  **`Verify.lean`**: the axiom checks.
- **`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`**: build configuration.

## License

Apache License 2.0; see [`LICENSE`](LICENSE).
