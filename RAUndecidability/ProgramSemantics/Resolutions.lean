import RAUndecidability.ProgramSemantics.LTS
import Mathlib.Logic.Relation
import Mathlib.Data.List.Induction

/-!
# Resolutions

The paper does not state resolutions; they are this
development's tool for reading a thread's `NDet` choices off its word:

* resolutions: resolutions, and the run of a thread under one;
* `resolution_sound`: runs are words;
* `resolution_complete`: paths are runs, under *some* resolution.

`resolution_complete` is stated as existence of a resolution: uniqueness
fails for the language in general (`v ← NDet(X); v ← e` has `|X|`
resolutions producing the same run).
-/

namespace RAUndecidability

variable {D : Domains} {V : Vocabulary D}

/-! ## Resolutions -/

/-- One step of a run under a resolution (resolutions): `Step` with the
`term` rule dropped and a `List V.LVal` threaded through every constructor,
consumed only by `ndet`. The `k`-th application of `ndet` along a derivation
is the one that fires when exactly `k - 1` heads have already been consumed
by earlier `ndet`s on the path to it — identified by list position, exactly
as word-consumption identifies position in `LTS.Steps`.

`term` is dropped, not merely unused: its target under `Step` is `qfn`, not a
`Config`, and a run — living entirely in `Config`-space, per resolutions's
own phrasing — simply has nothing left to do at `⟨term, φ⟩`. -/
inductive Command.RunStep (t : D.Tid) :
    List V.LVal → Option (ThreadLabel D t) → Config D V → List V.LVal → Config D V → Prop
  | assign {s v e φ} :
      RunStep t s none ⟨.assign v e, φ⟩ s ⟨.skip, Function.update φ v (V.eval e φ)⟩
  | ndet {s v X hX c φ} (hc : c ∈ X) :
      RunStep t (c :: s) none ⟨.ndetAssign v X hX, φ⟩ s ⟨.skip, Function.update φ v c⟩
  | seqSkip {s C φ} : RunStep t s none ⟨.seq .skip C, φ⟩ s ⟨C, φ⟩
  | seqBreak {s C φ} : RunStep t s none ⟨.seq .brk C, φ⟩ s ⟨.brk, φ⟩
  | iteTrue {s b C1 C2 φ} (h : V.evalB b φ = true) :
      RunStep t s none ⟨.ite b C1 C2, φ⟩ s ⟨C1, φ⟩
  | iteFalse {s b C1 C2 φ} (h : V.evalB b φ = false) :
      RunStep t s none ⟨.ite b C1 C2, φ⟩ s ⟨C2, φ⟩
  | whileTrue {s b C φ} (h : V.evalB b φ = true) :
      RunStep t s none ⟨.whileLoop b C, φ⟩ s ⟨.loopSeq C (.whileLoop b C), φ⟩
  | whileFalse {s b C φ} (h : V.evalB b φ = false) :
      RunStep t s none ⟨.whileLoop b C, φ⟩ s ⟨.skip, φ⟩
  | loopSkip {s C φ} : RunStep t s none ⟨.loopSeq .skip C, φ⟩ s ⟨C, φ⟩
  | loopBreak {s C φ} : RunStep t s none ⟨.loopSeq .brk C, φ⟩ s ⟨.skip, φ⟩
  | write {s u e φ} :
      RunStep t s (some ⟨EventLabel.wt t u (V.evalV e φ), rfl⟩) ⟨.write u e, φ⟩ s ⟨.skip, φ⟩
  | read {s u e φ} :
      RunStep t s (some ⟨EventLabel.rd t u (V.evalV e φ), rfl⟩) ⟨.read u e, φ⟩ s ⟨.skip, φ⟩
  | seqCongr {s s' a C1 C1' C2 φ φ'} :
      RunStep t s a ⟨C1, φ⟩ s' ⟨C1', φ'⟩ → RunStep t s a ⟨.seq C1 C2, φ⟩ s' ⟨.seq C1' C2, φ'⟩
  | loopCongr {s s' a C1 C1' C2 φ φ'} :
      RunStep t s a ⟨C1, φ⟩ s' ⟨C1', φ'⟩ →
        RunStep t s a ⟨.loopSeq C1 C2, φ⟩ s' ⟨.loopSeq C1' C2, φ'⟩

/-- The run of thread `t` under resolution `s`, from `c₀` (resolutions):
`Run t s c₀ σ cLast s' cf` means the run emits `σ`, in order, and finishes —
possibly after further silent steps — at `(s', cf)`. `cLast` is the
configuration immediately following `σ`'s last labelled step, or `c₀` if
`σ = []`; it does not move under `silentSnoc`, since `Reaches`
(App. A, The induced LTS) absorbs silent steps *before* a label. -/
inductive Command.Run (t : D.Tid) :
    List V.LVal → Config D V → Word (ThreadLabel D t) → Config D V →
      List V.LVal → Config D V → Prop
  | nil {s c} : Run t s c [] c s c
  | silentSnoc {s c₀ σ cLast s' c' s'' c''} :
      Run t s c₀ σ cLast s' c' → Command.RunStep t s' none c' s'' c'' →
        Run t s c₀ σ cLast s'' c''
  | labelledSnoc {s c₀ σ cLast s' c' l s'' c''} :
      Run t s c₀ σ cLast s' c' → Command.RunStep t s' (some l) c' s'' c'' →
        Run t s c₀ (σ ++ [l]) c'' s'' c''

variable {t : D.Tid}

/-- A `RunStep` is a `Step` with the resolution bookkeeping erased: dropping
`RunStep`'s list arguments recovers exactly the corresponding `Step`
constructor, since `RunStep` mirrors `Step` one constructor at a time. -/
theorem Command.RunStep.toStep {s : List V.LVal} {a : Option (ThreadLabel D t)}
    {c : Config D V} {s' : List V.LVal} {c' : Config D V}
    (h : Command.RunStep t s a c s' c') : Step t (a.map some) c (some c') := by
  induction h with
  | assign => exact Step.assign
  | ndet hc => exact Step.ndet hc
  | seqSkip => exact Step.seqSkip
  | seqBreak => exact Step.seqBreak
  | iteTrue h => exact Step.iteTrue h
  | iteFalse h => exact Step.iteFalse h
  | whileTrue h => exact Step.whileTrue h
  | whileFalse h => exact Step.whileFalse h
  | loopSkip => exact Step.loopSkip
  | loopBreak => exact Step.loopBreak
  | write => exact Step.write
  | read => exact Step.read
  | seqCongr _ ih => exact Step.seqCongr ih
  | loopCongr _ ih => exact Step.loopCongr ih

/-- A run's `cLast` silently reaches its own full endpoint `cf`: the
trailing suffix after the last label (or the whole run, if it emits none) is
pure `silentSnoc`, and each `silentSnoc` is a `SilentTo` step by
`RunStep.toStep`. -/
theorem Command.Run.silentReaches {s : List V.LVal} {c₀ : Config D V}
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {s' : List V.LVal} {cf : Config D V}
    (h : Command.Run t s c₀ σ cLast s' cf) :
    Relation.ReflTransGen (SilentTo t) cLast cf := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | silentSnoc _ hstep ih => exact ih.tail (RunStep.toStep hstep)
  | labelledSnoc _ _ _ => exact Relation.ReflTransGen.refl

/-- A run's start `c₀` reaches its full endpoint `cf` via arbitrary
(silent-or-labelled) steps. -/
theorem Command.Run.reachable {s : List V.LVal} {c₀ : Config D V}
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {s' : List V.LVal} {cf : Config D V}
    (h : Command.Run t s c₀ σ cLast s' cf) :
    Reachable t c₀ cf := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | silentSnoc _ hstep ih => exact ih.tail (Or.inl (RunStep.toStep hstep))
  | labelledSnoc _ hstep ih => exact ih.tail (Or.inr ⟨_, RunStep.toStep hstep⟩)

variable {C_t : Command D V} {φ₀ : V.Store}

/-! ## `resolution_sound` -/

/-- Runs are words (`resolution_sound`): the labels a run emits form a
word of `Prog_t` reaching the configuration immediately following its last
labelled step (`cLast`, not the run's endpoint — see `Command.Run`).

By induction on the run. The `nil` and `silentSnoc` cases are immediate:
`nil` witnesses the empty word at `inducedLTS.init`, and `silentSnoc` changes
nothing this lemma's conclusion depends on (`cLast`, `σ`), since it moves the
run's endpoint, not its `cLast`. The content is in `labelledSnoc`: the
induction hypothesis gives a state reaching `cLast` on `σ`; `cLast`'s own
`silentReaches` fact bridges it to the pre-label configuration, so composing
with the new `RunStep` (via `RunStep.toStep`) gives exactly `⇒^a` (App. A, The induced LTS)'
`Reaches`, hence one more `inducedLTS` transition, appended by
`LTS.Steps.snoc`. -/
theorem resolution_sound (s s' : List V.LVal) (σ : Word (ThreadLabel D t))
    (cLast cf : Config D V) (hrun : Command.Run t s (C_t, φ₀) σ cLast s' cf) :
    ∃ q : InducedState D V t C_t φ₀, q.1 = some cLast ∧
      (inducedLTS (t := t) (C_t := C_t) (φ₀ := φ₀)).Reaches (σ.map some) q := by
  induction hrun with
  | nil => exact ⟨inducedInit, rfl, LTS.Steps.nil⟩
  | silentSnoc _ _ ih => exact ih
  | labelledSnoc hprem hstep ih =>
      rename_i σ₁ cLast₁ s'₁ c'₁ l s''₁ c''₁
      obtain ⟨q₀, hq₀1, hq₀2⟩ := ih
      have hreach := Command.Run.reachable (Command.Run.labelledSnoc hprem hstep)
      have hsilent := Command.Run.silentReaches hprem
      have hstepL := Command.RunStep.toStep hstep
      refine ⟨⟨some c''₁, Or.inr ⟨c''₁, rfl, hreach⟩⟩, rfl, ?_⟩
      have htrans : inducedLTS.trans q₀ (some l)
          (⟨some c''₁, Or.inr ⟨c''₁, rfl, hreach⟩⟩ : InducedState D V t C_t φ₀) := by
        change inducedTrans q₀ (some l) _
        unfold inducedTrans
        rw [hq₀1]
        exact ⟨c''₁, rfl, ⟨c'₁, hsilent, hstepL⟩⟩
      have hsnoc := LTS.Steps.snoc inducedLTS hq₀2 htrans
      have heq : (σ₁ ++ [l]).map some = σ₁.map some ++ [some l] := by simp
      rw [heq]
      exact hsnoc

/-- A strengthening of `resolution_sound` for a run that actually finishes:
if a run's endpoint `cf` is `⟨term, φf⟩`, its word reaches `inducedFinal`
(§2.2). `resolution_sound` gives a state `q` with `q.1 = some cLast`;
`cLast ⇒silent* ⟨term, φf⟩` (`Command.Run.silentReaches`) is exactly
`Halts t cLast`, which is exactly what `inducedTrans _ none inducedFinal`
needs, so one more `LTS.Steps.snoc` closes it. -/
theorem resolution_reaches_final (s s' : List V.LVal) (σ : Word (ThreadLabel D t))
    (cLast : Config D V) (φf : V.Store)
    (hrun : Command.Run t s (C_t, φ₀) σ cLast s' (Command.term, φf)) :
    (inducedLTS (t := t) (C_t := C_t) (φ₀ := φ₀)).Reaches (σ.map some ++ [none]) inducedFinal := by
  obtain ⟨q, hq1, hq2⟩ := resolution_sound s s' σ cLast (Command.term, φf) hrun
  have hhalts : Halts t cLast := ⟨φf, Command.Run.silentReaches hrun⟩
  have htrans : inducedTrans q none inducedFinal := by
    unfold inducedTrans
    rw [hq1]
    exact ⟨rfl, hhalts⟩
  exact LTS.Steps.snoc inducedLTS hq2 htrans

/-! ## `resolution_complete` -/

/-- Padding a `RunStep`'s resolution by an unused, untouched suffix on both
ends: no constructor examines anything past its own local pattern (at most
the head of the current list, for `ndet`), so appending `extra` to both
sides preserves every step. -/
theorem Command.RunStep.padTail {s : List V.LVal} {a : Option (ThreadLabel D t)}
    {c : Config D V} {s' : List V.LVal} {c' : Config D V}
    (h : Command.RunStep t s a c s' c') (extra : List V.LVal) :
    Command.RunStep t (s ++ extra) a c (s' ++ extra) c' := by
  induction h with
  | assign => exact Command.RunStep.assign
  | ndet hc => exact Command.RunStep.ndet hc
  | seqSkip => exact Command.RunStep.seqSkip
  | seqBreak => exact Command.RunStep.seqBreak
  | iteTrue h => exact Command.RunStep.iteTrue h
  | iteFalse h => exact Command.RunStep.iteFalse h
  | whileTrue h => exact Command.RunStep.whileTrue h
  | whileFalse h => exact Command.RunStep.whileFalse h
  | loopSkip => exact Command.RunStep.loopSkip
  | loopBreak => exact Command.RunStep.loopBreak
  | write => exact Command.RunStep.write
  | read => exact Command.RunStep.read
  | seqCongr _ ih => exact Command.RunStep.seqCongr ih
  | loopCongr _ ih => exact Command.RunStep.loopCongr ih

/-- The `Command.Run` analogue of `Command.RunStep.padTail`. -/
theorem Command.Run.padTail {s : List V.LVal} {c₀ : Config D V}
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {s' : List V.LVal} {cf : Config D V}
    (h : Command.Run t s c₀ σ cLast s' cf) (extra : List V.LVal) :
    Command.Run t (s ++ extra) c₀ σ cLast (s' ++ extra) cf := by
  induction h with
  | nil => exact Command.Run.nil
  | silentSnoc _ hstep ih => exact Command.Run.silentSnoc ih (Command.RunStep.padTail hstep extra)
  | labelledSnoc _ hstep ih =>
      exact Command.Run.labelledSnoc ih (Command.RunStep.padTail hstep extra)

/-- Composing two runs end to end: if the first reaches `(c1, s1)` and a
second run continues from there, their concatenation is a run too, from the
first run's start to the second's end.

By induction on the second run (`Run` is snoc-shaped). -/
theorem Command.Run.append {s : List V.LVal} {c0 : Config D V}
    {σ1 : Word (ThreadLabel D t)} {cLast1 : Config D V} {s1 : List V.LVal} {c1 : Config D V}
    (run1 : Command.Run t s c0 σ1 cLast1 s1 c1)
    {σ2 : Word (ThreadLabel D t)} {cLast2 : Config D V} {s2 : List V.LVal} {c2 : Config D V}
    (run2 : Command.Run t s1 c1 σ2 cLast2 s2 c2) :
    ∃ cLast, Command.Run t s c0 (σ1 ++ σ2) cLast s2 c2 := by
  induction run2 with
  | nil => exact ⟨cLast1, by simpa using run1⟩
  | silentSnoc _ hstep ih =>
      obtain ⟨cLast, ihrun⟩ := ih
      exact ⟨cLast, Command.Run.silentSnoc ihrun hstep⟩
  | labelledSnoc _ hstep ih =>
      obtain ⟨cLast, ihrun⟩ := ih
      exact ⟨_, by rw [← List.append_assoc]; exact Command.Run.labelledSnoc ihrun hstep⟩

/-- Lifting a self-contained run of `C1` into a `.seq C1 C2` context:
`C2` rides along unchanged at every step, since `Command.RunStep.seqCongr`
prepends it to the *same* underlying step one constructor at a time. -/
theorem Command.Run.seqCongr {s : List V.LVal} {c₀ : Config D V}
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {s' : List V.LVal} {cf : Config D V}
    (C2 : Command D V) (h : Command.Run t s c₀ σ cLast s' cf) :
    Command.Run t s (c₀.1.seq C2, c₀.2) σ (cLast.1.seq C2, cLast.2) s' (cf.1.seq C2, cf.2) := by
  induction h with
  | nil => exact Command.Run.nil
  | silentSnoc _ hstep ih => exact Command.Run.silentSnoc ih (Command.RunStep.seqCongr hstep)
  | labelledSnoc _ hstep ih => exact Command.Run.labelledSnoc ih (Command.RunStep.seqCongr hstep)

/-- `Command.Run.seqCongr`'s `loopSeq` counterpart: lifting a self-contained
run of `C1` into a `.loopSeq C1 C2` context, `C2` riding along unchanged at
every step via `Command.RunStep.loopCongr`. -/
theorem Command.Run.loopCongr {s : List V.LVal} {c₀ : Config D V}
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {s' : List V.LVal} {cf : Config D V}
    (C2 : Command D V) (h : Command.Run t s c₀ σ cLast s' cf) :
    Command.Run t s (c₀.1.loopSeq C2, c₀.2) σ (cLast.1.loopSeq C2, cLast.2) s'
      (cf.1.loopSeq C2, cf.2) := by
  induction h with
  | nil => exact Command.Run.nil
  | silentSnoc _ hstep ih => exact Command.Run.silentSnoc ih (Command.RunStep.loopCongr hstep)
  | labelledSnoc _ hstep ih => exact Command.Run.labelledSnoc ih (Command.RunStep.loopCongr hstep)

/-- Recovering a `RunStep` from a raw `Step` (excluding `term`, whose target
is `none`, not `some _`), for whatever resolution tail is wanted next. Stated
over a generic `oc2 : Option (Config D V)` plus an equation, so that
`induction` applies. -/
theorem Command.step_to_runStep :
    ∀ {a' : Option (Option (ThreadLabel D t))} {c1 : Config D V} {oc2 : Option (Config D V)},
      Step t a' c1 oc2 → ∀ c2, oc2 = some c2 → ∀ s_tail : List V.LVal,
        ∃ (a : Option (ThreadLabel D t)) (s_head : List V.LVal),
          a' = a.map some ∧ Command.RunStep t s_head a c1 s_tail c2 := by
  intro a' c1 oc2 h
  induction h with
  | assign => intro c2 heq s_tail; cases heq; exact ⟨none, s_tail, rfl, Command.RunStep.assign⟩
  | ndet hc =>
      intro c2 heq s_tail; cases heq
      exact ⟨none, _ :: s_tail, rfl, Command.RunStep.ndet hc⟩
  | seqSkip => intro c2 heq s_tail; cases heq; exact ⟨none, s_tail, rfl, Command.RunStep.seqSkip⟩
  | seqBreak => intro c2 heq s_tail; cases heq; exact ⟨none, s_tail, rfl, Command.RunStep.seqBreak⟩
  | iteTrue h =>
      intro c2 heq s_tail; cases heq
      exact ⟨none, s_tail, rfl, Command.RunStep.iteTrue h⟩
  | iteFalse h =>
      intro c2 heq s_tail; cases heq
      exact ⟨none, s_tail, rfl, Command.RunStep.iteFalse h⟩
  | whileTrue h =>
      intro c2 heq s_tail; cases heq
      exact ⟨none, s_tail, rfl, Command.RunStep.whileTrue h⟩
  | whileFalse h =>
      intro c2 heq s_tail; cases heq
      exact ⟨none, s_tail, rfl, Command.RunStep.whileFalse h⟩
  | loopSkip => intro c2 heq s_tail; cases heq; exact ⟨none, s_tail, rfl, Command.RunStep.loopSkip⟩
  | loopBreak =>
      intro c2 heq s_tail; cases heq
      exact ⟨none, s_tail, rfl, Command.RunStep.loopBreak⟩
  | write => intro c2 heq s_tail; cases heq; exact ⟨_, s_tail, rfl, Command.RunStep.write⟩
  | read => intro c2 heq s_tail; cases heq; exact ⟨_, s_tail, rfl, Command.RunStep.read⟩
  | termStep => intro c2 heq; cases heq
  | seqCongr _ ih =>
      intro c2 heq s_tail
      cases heq
      obtain ⟨a, s_head, ha, hrs⟩ := ih _ rfl s_tail
      exact ⟨a, s_head, ha, Command.RunStep.seqCongr hrs⟩
  | loopCongr _ ih =>
      intro c2 heq s_tail
      cases heq
      obtain ⟨a, s_head, ha, hrs⟩ := ih _ rfl s_tail
      exact ⟨a, s_head, ha, Command.RunStep.loopCongr hrs⟩

/-- Extending an already fully-consumed run through a chain of silent steps:
same `σ`/`cLast` (silent steps never touch either — see `Command.Run`'s own
docstring), a possibly larger resolution, still fully consumed. Induction on
the `ReflTransGen` derivation, which — like `Command.Run` itself — is
snoc-shaped (`refl`/`tail`), so it extends forward exactly as `Command.Run`
does: `step_to_runStep` recovers one more `RunStep`, `padTail` reconciles its
own fresh resolution with the one built so far, and `silentSnoc` appends it. -/
theorem Command.Run.extendSilent {c1 c2 : Config D V}
    (hchain : Relation.ReflTransGen (SilentTo t) c1 c2) :
    ∀ {c₀ : Config D V} {σ : Word (ThreadLabel D t)} {cLast : Config D V} {s : List V.LVal},
      Command.Run t s c₀ σ cLast [] c1 → ∃ s' : List V.LVal, Command.Run t s' c₀ σ cLast [] c2 := by
  induction hchain with
  | refl => intro c₀ σ cLast s hrun; exact ⟨s, hrun⟩
  | tail _ hstep ih =>
      intro c₀ σ cLast s hrun
      obtain ⟨s'', hrun''⟩ := ih hrun
      obtain ⟨a, s_head, ha, hrs⟩ := Command.step_to_runStep hstep _ rfl []
      cases a with
      | none =>
          exact ⟨s'' ++ s_head, Command.Run.silentSnoc (Command.Run.padTail hrun'' s_head) hrs⟩
      | some l => cases ha

/-- Paths are runs (`resolution_complete`): every path of `Prog_t` from
`InitState` is the run of `t` under *some* resolution (see the module docstring on
uniqueness).

By induction on `w` from the right (`List.reverseRecOn`), not on the path
derivation directly: `LTS.Steps` is built head-first (`cons`), the wrong
shape for extending a `Command.Run`, which is snoc-shaped. Each step splits
off the path's *last* transition via `LTS.Steps.snoc_inv`, recovers the
already-known resolution for the shorter prefix from the inductive
hypothesis, and extends it by one more transition: through `Reaches`'s
silent chain (`Command.Run.extendSilent`) then the final labelled step
(`Command.step_to_runStep`), for a real label; or, for the `term` action, no
extension is needed at all, since `inducedTrans`'s `term` case demands
exactly `Halts t cLast`, already in hand from the shorter prefix. The two
disjuncts mirror `inducedTrans`'s two cases. -/
theorem resolution_complete (w : Word (Option (ThreadLabel D t)))
    (q : InducedState D V t C_t φ₀)
    (hpath : (inducedLTS (t := t) (C_t := C_t) (φ₀ := φ₀)).Steps
      (inducedLTS (t := t) (C_t := C_t) (φ₀ := φ₀)).init w q) :
    (∃ (s : List V.LVal) (σ : Word (ThreadLabel D t)) (cLast : Config D V),
        Command.Run t s (C_t, φ₀) σ cLast [] cLast ∧ q.1 = some cLast ∧ w = σ.map some) ∨
    (∃ (s : List V.LVal) (σ : Word (ThreadLabel D t)) (cLast : Config D V),
        Command.Run t s (C_t, φ₀) σ cLast [] cLast ∧ q.1 = none ∧ Halts t cLast ∧
          w = σ.map some ++ [none]) := by
  suffices h :
      ∀ (w : Word (Option (ThreadLabel D t))) (q : InducedState D V t C_t φ₀),
        (inducedLTS (t := t) (C_t := C_t) (φ₀ := φ₀)).Steps
          (inducedLTS (t := t) (C_t := C_t) (φ₀ := φ₀)).init w q →
        (∃ (s : List V.LVal) (σ : Word (ThreadLabel D t)) (cLast : Config D V),
            Command.Run t s (C_t, φ₀) σ cLast [] cLast ∧ q.1 = some cLast ∧ w = σ.map some) ∨
        (∃ (s : List V.LVal) (σ : Word (ThreadLabel D t)) (cLast : Config D V),
            Command.Run t s (C_t, φ₀) σ cLast [] cLast ∧ q.1 = none ∧ Halts t cLast ∧
              w = σ.map some ++ [none]) from h w q hpath
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro q hpath
      cases hpath with
      | nil => exact Or.inl ⟨[], [], (C_t, φ₀), Command.Run.nil, rfl, rfl⟩
  | append_singleton w' a ih =>
      intro q hpath
      obtain ⟨q', hpath', htrans⟩ :=
        LTS.Steps.snoc_inv (inducedLTS (t := t) (C_t := C_t) (φ₀ := φ₀)) w' a hpath
      rcases ih q' hpath' with hleft | hright
      · obtain ⟨s, σ, cLast, hrun, hq'1, hweq⟩ := hleft
        change inducedTrans q' a q at htrans
        unfold inducedTrans at htrans
        rw [hq'1] at htrans
        cases a with
        | none =>
            obtain ⟨hqnone, hhalts⟩ := htrans
            exact Or.inr ⟨s, σ, cLast, hrun, hqnone, hhalts, by rw [hweq]⟩
        | some l =>
            obtain ⟨c', hqc', hreach⟩ := htrans
            obtain ⟨c'', hsilent, hlabel⟩ := hreach
            obtain ⟨s'', hrun''⟩ := Command.Run.extendSilent hsilent hrun
            obtain ⟨a2, s_head, ha2, hrs⟩ := Command.step_to_runStep hlabel _ rfl []
            cases a2 with
            | none => cases ha2
            | some l2 =>
                have hl2 : l2 = l := by
                  simp only [Option.map_some, Option.some.injEq] at ha2
                  exact ha2.symm
                subst hl2
                refine Or.inl ⟨s'' ++ s_head, σ ++ [l2], c', ?_, hqc', ?_⟩
                · exact Command.Run.labelledSnoc (Command.Run.padTail hrun'' s_head) hrs
                · rw [hweq]; simp
      · obtain ⟨s, σ, cLast, hrun, hq'1, hhalts, hweq⟩ := hright
        change inducedTrans q' a q at htrans
        unfold inducedTrans at htrans
        rw [hq'1] at htrans
        exact absurd htrans (by simp)

end RAUndecidability
