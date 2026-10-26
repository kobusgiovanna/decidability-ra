import RAUndecidability.ProgramSemantics.Resolutions

/-!
# A computable interpreter for `Command`, driven by a resolution

`Command.step` is a computable step function with the same content as
`Command.RunStep` (resolutions), proved sound and complete against it
(only `ndet` is non-deterministic, and it is driven by the resolution).
`Command.runFuel` is a fuel-bounded runner built on it, whose outcome
distinguishes termination (`stuck`) from running out of fuel.
-/

namespace RAUndecidability

variable {D : Domains} {V : Vocabulary D} {t : D.Tid}

/-! ## `Command.step` -/

/-- A computable step function for `Command`, mirroring `Command.RunStep` one
constructor at a time: `none` is stuck (no rule applies — `brk`, `term`,
`skip` on their own, or `ndetAssign` against an empty resolution), `some`
carries the label taken (if any), the successor command/store, and the
resolution with its head consumed (only by `ndetAssign`). -/
def Command.step (t : D.Tid) :
    Command D V → V.Store → List V.LVal →
      Option (Option (ThreadLabel D t) × Command D V × V.Store × List V.LVal)
  | .assign v e, φ, s => some (none, .skip, Function.update φ v (V.eval e φ), s)
  | .ndetAssign v X _, φ, c :: s =>
      if c ∈ X then some (none, .skip, Function.update φ v c, s) else none
  | .ndetAssign _ _ _, _, [] => none
  | .seq .skip C2, φ, s => some (none, C2, φ, s)
  | .seq .brk _, φ, s => some (none, .brk, φ, s)
  | .seq C1 C2, φ, s =>
      match Command.step t C1 φ s with
      | none => none
      | some (a, C1', φ', s') => some (a, .seq C1' C2, φ', s')
  | .ite b C1 C2, φ, s => if V.evalB b φ then some (none, C1, φ, s) else some (none, C2, φ, s)
  | .whileLoop b C, φ, s =>
      if V.evalB b φ then some (none, .loopSeq C (.whileLoop b C), φ, s)
      else some (none, .skip, φ, s)
  | .brk, _, _ => none
  | .term, _, _ => none
  | .loopSeq .skip C2, φ, s => some (none, C2, φ, s)
  | .loopSeq .brk _, φ, s => some (none, .skip, φ, s)
  | .loopSeq C1 C2, φ, s =>
      match Command.step t C1 φ s with
      | none => none
      | some (a, C1', φ', s') => some (a, .loopSeq C1' C2, φ', s')
  | .write u e, φ, s => some (some ⟨EventLabel.wt t u (V.evalV e φ), rfl⟩, .skip, φ, s)
  | .read u e, φ, s => some (some ⟨EventLabel.rd t u (V.evalV e φ), rfl⟩, .skip, φ, s)
  | .skip, _, _ => none

/-- `Command.step` is sound against `Command.RunStep`. Proved by the same
recursion as `Command.step` (its `.induct`), which supplies `C1 ≠ .skip`/`.brk`
in the `seq`/`loopSeq` congruence cases. The cases `case1`-`case21` are the
branches of `Command.step` in order, each congruence branch contributing two
(the subcommand stuck, or stepping); the comment before each names its command
and the rule it yields. -/
theorem Command.step_sound :
    ∀ (C : Command D V) (φ : V.Store) (s : List V.LVal) (a : Option (ThreadLabel D t))
      (C' : Command D V) (φ' : V.Store) (s' : List V.LVal),
      Command.step t C φ s = some (a, C', φ', s') →
        Command.RunStep t s a ⟨C, φ⟩ s' ⟨C', φ'⟩ := by
  intro C φ s
  induction C, φ, s using Command.step.induct (t := t) with
  -- `v ← e`: `assign`
  | case1 v e φ s =>
      intro a C' φ' s' h
      simp only [Command.step, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.assign
  -- `v ← NDet(X)`, next choice in `X`: `ndet`
  | case2 v X hX φ c s hc =>
      intro a C' φ' s' h
      simp only [Command.step, hc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.ndet hc
  -- `v ← NDet(X)`, next choice not in `X`: stuck
  | case3 v X hX φ c s hc =>
      intro a C' φ' s' h
      simp only [Command.step, hc] at h
      cases h
  -- `v ← NDet(X)`, no choices left: stuck
  | case4 v X hX φ =>
      intro a C' φ' s' h
      simp only [Command.step] at h
      cases h
  -- `skip ; C2`: `seq-skip`
  | case5 C2 φ s =>
      intro a C' φ' s' h
      simp only [Command.step, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.seqSkip
  -- `break ; C2`: `seq-break`
  | case6 C2 φ s =>
      intro a C' φ' s' h
      simp only [Command.step, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.seqBreak
  -- `C1 ; C2`, `C1` stuck: stuck
  | case7 C1 C2 φ s hne1 hne2 hstep ih =>
      intro a C' φ' s' h
      simp only [Command.step, hstep] at h
      cases h
  -- `C1 ; C2`, `C1` steps: `seq-step`
  | case8 C1 C2 φ s hne1 hne2 a1 C1' φ1' s1' hstep ih =>
      intro a C' φ' s' h
      simp only [Command.step, hstep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.seqCongr (ih a1 C1' φ1' s1' hstep)
  -- `if b …`, `b` true: `if-true`
  | case9 b C1 C2 φ s hb =>
      intro a C' φ' s' h
      simp only [Command.step, hb, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.iteTrue hb
  -- `if b …`, `b` false: `if-false`
  | case10 b C1 C2 φ s hb =>
      intro a C' φ' s' h
      simp only [Command.step, hb, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.iteFalse (by simpa using hb)
  -- `while b …`, `b` true: `while-true`
  | case11 b C φ s hb =>
      intro a C' φ' s' h
      simp only [Command.step, hb, if_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.whileTrue hb
  -- `while b …`, `b` false: `while-false`
  | case12 b C φ s hb =>
      intro a C' φ' s' h
      simp only [Command.step, hb, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.whileFalse (by simpa using hb)
  -- `break` alone: stuck
  | case13 φ s =>
      intro a C' φ' s' h
      simp only [Command.step] at h
      cases h
  -- `term`: stuck (its step leaves the configurations)
  | case14 φ s =>
      intro a C' φ' s' h
      simp only [Command.step] at h
      cases h
  -- `skip ▷ C2`: `loop-skip`
  | case15 C2 φ s =>
      intro a C' φ' s' h
      simp only [Command.step, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.loopSkip
  -- `break ▷ C2`: `loop-break`
  | case16 C2 φ s =>
      intro a C' φ' s' h
      simp only [Command.step, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.loopBreak
  -- `C1 ▷ C2`, `C1` stuck: stuck
  | case17 C1 C2 φ s hne1 hne2 hstep ih =>
      intro a C' φ' s' h
      simp only [Command.step, hstep] at h
      cases h
  -- `C1 ▷ C2`, `C1` steps: `loop-step`
  | case18 C1 C2 φ s hne1 hne2 a1 C1' φ1' s1' hstep ih =>
      intro a C' φ' s' h
      simp only [Command.step, hstep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.loopCongr (ih a1 C1' φ1' s1' hstep)
  -- `w(u, e)`: `write`
  | case19 u e φ s =>
      intro a C' φ' s' h
      simp only [Command.step, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.write
  -- `r(u, e)`: `read`
  | case20 u e φ s =>
      intro a C' φ' s' h
      simp only [Command.step, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact Command.RunStep.read
  -- `skip` alone: stuck
  | case21 φ s =>
      intro a C' φ' s' h
      simp only [Command.step] at h
      cases h

/-- `Command.step` is complete against `Command.RunStep`: every step `RunStep`
allows is the one `step` computes. By induction on the `RunStep` derivation. -/
theorem Command.step_complete {s : List V.LVal} {a : Option (ThreadLabel D t)}
    {c : Config D V} {s' : List V.LVal} {c' : Config D V}
    (h : Command.RunStep t s a c s' c') :
    Command.step t c.1 c.2 s = some (a, c'.1, c'.2, s') := by
  induction h with
  | assign => rfl
  | ndet hc => simp only [Command.step, hc, if_true]
  | seqSkip => rfl
  | seqBreak => rfl
  | iteTrue h => simp only [Command.step, h, if_true]
  | iteFalse h => simp only [Command.step, h]; rfl
  | whileTrue h => simp only [Command.step, h, if_true]
  | whileFalse h => simp only [Command.step, h]; rfl
  | loopSkip => rfl
  | loopBreak => rfl
  | write => rfl
  | read => rfl
  | seqCongr hstep ih =>
      rename_i s₁ s₁' a₁ C1 C1' C2 φ φ'
      have hskip : C1 ≠ Command.skip := by
        rintro rfl; simp only [Command.step] at ih; cases ih
      have hbrk : C1 ≠ Command.brk := by
        rintro rfl; simp only [Command.step] at ih; cases ih
      simp only [Command.step, hskip, hbrk, ih]
  | loopCongr hstep ih =>
      rename_i s₁ s₁' a₁ C1 C1' C2 φ φ'
      have hskip : C1 ≠ Command.skip := by
        rintro rfl; simp only [Command.step] at ih; cases ih
      have hbrk : C1 ≠ Command.brk := by
        rintro rfl; simp only [Command.step] at ih; cases ih
      simp only [Command.step, hskip, hbrk, ih]

/-! ## `Command.runFuel` -/

/-- The outcome of a fuel-bounded run: `stuck` means `Command.step` returned
`none` (no further step exists); `outOfFuel` means the fuel ran out with a
step still available. Only `stuck` has a soundness lemma
(`Command.runFuel_sound`). -/
inductive Command.RunOutcome
  | stuck
  | outOfFuel
  deriving DecidableEq, Repr

/-- A fuel-bounded run of thread `t` from `(c, s)`: the outcome, the word of
labels emitted along the way (in order), and the configuration/resolution
reached. -/
def Command.runFuel (t : D.Tid) :
    Config D V → List V.LVal → ℕ →
      Command.RunOutcome × Word (ThreadLabel D t) × Config D V × List V.LVal
  | c, s, 0 => (.outOfFuel, [], c, s)
  | c, s, n + 1 =>
      match Command.step t c.1 c.2 s with
      | none => (.stuck, [], c, s)
      | some (a, C', φ', s') =>
          match Command.runFuel t (C', φ') s' n with
          | (res, σ, cf, sf) => (res, (match a with | none => σ | some l => l :: σ), cf, sf)

/-- Prepending a silent `RunStep` to a `Command.Run` gives a `Command.Run`
starting one step earlier, with the same emitted word. -/
theorem Command.RunStep.consRunNone {s : List V.LVal}
    {c : Config D V} {s₁ : List V.LVal} {c₁ : Config D V}
    (hstep : Command.RunStep t s none c s₁ c₁)
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {sf : List V.LVal} {cf : Config D V}
    (hrun : Command.Run t s₁ c₁ σ cLast sf cf) :
    ∃ cLast', Command.Run t s c σ cLast' sf cf := by
  induction hrun with
  | nil => exact ⟨c, Command.Run.silentSnoc Command.Run.nil hstep⟩
  | silentSnoc _ hstep' ih =>
      obtain ⟨cLast', hRun'⟩ := ih
      exact ⟨cLast', Command.Run.silentSnoc hRun' hstep'⟩
  | labelledSnoc _ hstep' ih =>
      obtain ⟨cLast', hRun'⟩ := ih
      exact ⟨_, Command.Run.labelledSnoc hRun' hstep'⟩

/-- Prepending a labelled `RunStep` to a `Command.Run`, cons-ing its label
onto the front of the emitted word. See `Command.RunStep.consRunNone`. -/
theorem Command.RunStep.consRunSome {s : List V.LVal} {l : ThreadLabel D t}
    {c : Config D V} {s₁ : List V.LVal} {c₁ : Config D V}
    (hstep : Command.RunStep t s (some l) c s₁ c₁)
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {sf : List V.LVal} {cf : Config D V}
    (hrun : Command.Run t s₁ c₁ σ cLast sf cf) :
    ∃ cLast', Command.Run t s c (l :: σ) cLast' sf cf := by
  induction hrun with
  | nil => exact ⟨c₁, Command.Run.labelledSnoc Command.Run.nil hstep⟩
  | silentSnoc _ hstep' ih =>
      obtain ⟨cLast', hRun'⟩ := ih
      exact ⟨cLast', Command.Run.silentSnoc hRun' hstep'⟩
  | labelledSnoc _ hstep' ih =>
      obtain ⟨cLast', hRun'⟩ := ih
      exact ⟨_, Command.Run.labelledSnoc hRun' hstep'⟩

/-- `Command.runFuel`'s `stuck` outcome is sound against `Command.Run`. -/
theorem Command.runFuel_sound (t : D.Tid) :
    ∀ (n : ℕ) (c : Config D V) (s : List V.LVal) (σ : Word (ThreadLabel D t))
      (cf : Config D V) (sf : List V.LVal),
      Command.runFuel t c s n = (.stuck, σ, cf, sf) →
        ∃ cLast, Command.Run t s c σ cLast sf cf
  | 0, c, s, σ, cf, sf, h => by
      simp only [Command.runFuel, Prod.mk.injEq] at h
      obtain ⟨h1, -⟩ := h
      cases h1
  | n + 1, c, s, σ, cf, sf, h => by
      simp only [Command.runFuel] at h
      cases hstep : Command.step t c.1 c.2 s with
      | none =>
          rw [hstep] at h
          simp only [Prod.mk.injEq] at h
          obtain ⟨-, rfl, rfl, rfl⟩ := h
          exact ⟨c, Command.Run.nil⟩
      | some x =>
          obtain ⟨a, C', φ', s'⟩ := x
          rw [hstep] at h
          rcases hrec : Command.runFuel t (C', φ') s' n with ⟨res, σ0, cf0, sf0⟩
          simp only [hrec, Prod.mk.injEq] at h
          obtain ⟨hres, hσeq, hcf0, hsf0⟩ := h
          rw [hres, hcf0, hsf0] at hrec
          have hRunStep := Command.step_sound c.1 c.2 s a C' φ' s' hstep
          obtain ⟨cLast', hrun'⟩ := Command.runFuel_sound t n (C', φ') s' σ0 cf sf hrec
          rcases a with _ | l
          · obtain ⟨cLast'', hRun''⟩ := Command.RunStep.consRunNone hRunStep hrun'
            exact ⟨cLast'', by simpa using hσeq ▸ hRun''⟩
          · obtain ⟨cLast'', hRun''⟩ := Command.RunStep.consRunSome hRunStep hrun'
            exact ⟨cLast'', by simpa using hσeq ▸ hRun''⟩

/-! ## `Command.runFuel` under `seq`/`loopSeq` wrapping -/

/-- Wrapping a run of `C1` in `Command.seq C1 C2` preserves an `.outOfFuel`
outcome: every step taken is a `seqCongr` step, since `seqSkip`/`seqBreak`
would require the current sub-command to be `.skip`/`.brk`, on which
`Command.step` is `none`. By induction on the fuel. -/
theorem Command.runFuel_seqCongr_outOfFuel {t : D.Tid} :
    ∀ (N : ℕ) (C1 C2 : Command D V) (φ : V.Store) (s : List V.LVal)
      (C1' : Command D V) (φ' : V.Store) (σ : Word (ThreadLabel D t)) (sf : List V.LVal),
      Command.runFuel t (C1, φ) s N = (.outOfFuel, σ, (C1', φ'), sf) →
      Command.runFuel t (Command.seq C1 C2, φ) s N =
        (.outOfFuel, σ, (Command.seq C1' C2, φ'), sf)
  | 0, C1, C2, φ, s, C1', φ', σ, sf, h => by
      simp only [Command.runFuel, Prod.mk.injEq] at h
      obtain ⟨-, hσ, ⟨hC1', hφ'⟩, hsf⟩ := h
      subst hσ; subst hC1'; subst hφ'; subst hsf
      simp only [Command.runFuel]
  | N + 1, C1, C2, φ, s, C1', φ', σ, sf, h => by
      unfold Command.runFuel at h
      cases hstep : Command.step t C1 φ s with
      | none =>
          rw [hstep] at h
          simp only [Prod.mk.injEq] at h
          exact absurd h.1 (by decide)
      | some x =>
          obtain ⟨a, C1'', φ'', s''⟩ := x
          rw [hstep] at h
          rcases hrec : Command.runFuel t (C1'', φ'') s'' N with ⟨res, σ0, cf0, sf0⟩
          simp only [hrec, Prod.mk.injEq] at h
          obtain ⟨hres, hσeq, hcf, hsf'⟩ := h
          have hrec' : Command.runFuel t (C1'', φ'') s'' N = (.outOfFuel, σ0, (C1', φ'), sf) := by
            rw [hrec, hres, hcf, hsf']
          have hne_skip : C1 ≠ Command.skip := by
            rintro rfl; simp only [Command.step] at hstep
            cases hstep
          have hne_brk : C1 ≠ Command.brk := by
            rintro rfl; simp only [Command.step] at hstep
            cases hstep
          have ih :=
            Command.runFuel_seqCongr_outOfFuel N C1'' C2 φ'' s'' C1' φ' σ0 sf hrec'
          simp only [Command.runFuel, Command.step, hne_skip, hne_brk, hstep, ih, hσeq]

/-- The `Command.loopSeq` analogue of `Command.runFuel_seqCongr_outOfFuel`. -/
theorem Command.runFuel_loopSeqCongr_outOfFuel {t : D.Tid} :
    ∀ (N : ℕ) (C1 C2 : Command D V) (φ : V.Store) (s : List V.LVal)
      (C1' : Command D V) (φ' : V.Store) (σ : Word (ThreadLabel D t)) (sf : List V.LVal),
      Command.runFuel t (C1, φ) s N = (.outOfFuel, σ, (C1', φ'), sf) →
      Command.runFuel t (Command.loopSeq C1 C2, φ) s N =
        (.outOfFuel, σ, (Command.loopSeq C1' C2, φ'), sf)
  | 0, C1, C2, φ, s, C1', φ', σ, sf, h => by
      simp only [Command.runFuel, Prod.mk.injEq] at h
      obtain ⟨-, hσ, ⟨hC1', hφ'⟩, hsf⟩ := h
      subst hσ; subst hC1'; subst hφ'; subst hsf
      simp only [Command.runFuel]
  | N + 1, C1, C2, φ, s, C1', φ', σ, sf, h => by
      unfold Command.runFuel at h
      cases hstep : Command.step t C1 φ s with
      | none =>
          rw [hstep] at h
          simp only [Prod.mk.injEq] at h
          exact absurd h.1 (by decide)
      | some x =>
          obtain ⟨a, C1'', φ'', s''⟩ := x
          rw [hstep] at h
          rcases hrec : Command.runFuel t (C1'', φ'') s'' N with ⟨res, σ0, cf0, sf0⟩
          simp only [hrec, Prod.mk.injEq] at h
          obtain ⟨hres, hσeq, hcf, hsf'⟩ := h
          have hrec' : Command.runFuel t (C1'', φ'') s'' N = (.outOfFuel, σ0, (C1', φ'), sf) := by
            rw [hrec, hres, hcf, hsf']
          have hne_skip : C1 ≠ Command.skip := by
            rintro rfl; simp only [Command.step] at hstep
            cases hstep
          have hne_brk : C1 ≠ Command.brk := by
            rintro rfl; simp only [Command.step] at hstep
            cases hstep
          have ih :=
            Command.runFuel_loopSeqCongr_outOfFuel N C1'' C2 φ'' s'' C1' φ' σ0 sf hrec'
          simp only [Command.runFuel, Command.step, hne_skip, hne_brk, hstep, ih, hσeq]

/-- A run of `.seq C1 Command.term` that gets stuck at `Command.term` comes
from a run of `C1` that gets stuck at `.skip`: `.seq .skip C2` steps to `C2`,
while `.seq .brk _` steps to `.brk`, which can never reach `Command.term`. -/
theorem Command.runFuel_seqTerm_stuck_unwrap {t : D.Tid} :
    ∀ (N : ℕ) (C1 : Command D V) (φ : V.Store) (s : List V.LVal)
      (σ : Word (ThreadLabel D t)) (φ' : V.Store),
      Command.runFuel t (Command.seq C1 Command.term, φ) s N =
        (.stuck, σ, (Command.term, φ'), []) →
      ∃ N', N = N' + 1 ∧
        Command.runFuel t (C1, φ) s N' = (.stuck, σ, (Command.skip, φ'), [])
  | 0, C1, φ, s, σ, φ', h => by
      simp only [Command.runFuel, Prod.mk.injEq] at h
      exact absurd h.1 (by rintro ⟨⟩)
  | N + 1, C1, φ, s, σ, φ', h => by
      rcases eq_or_ne C1 Command.skip with rfl | hns
      · refine ⟨N, rfl, ?_⟩
        have hstep : Command.step t (Command.seq Command.skip Command.term) φ s =
            some (none, Command.term, φ, s) := rfl
        unfold Command.runFuel at h
        rw [hstep] at h
        simp only at h
        cases N with
        | zero =>
            exfalso
            simp only [Command.runFuel, Prod.mk.injEq] at h
            exact absurd h.1 (by rintro ⟨⟩)
        | succ M =>
            have hstepT : Command.step t Command.term φ s = none := rfl
            simp only [Command.runFuel, hstepT, Prod.mk.injEq] at h
            obtain ⟨-, hσ, ⟨-, hφeq⟩, hseq⟩ := h
            subst hσ; subst hφeq; subst hseq
            have hstepS : Command.step t Command.skip φ [] = none := rfl
            simp only [Command.runFuel, hstepS]
      · rcases eq_or_ne C1 Command.brk with rfl | hnb
        · exfalso
          have hstep : Command.step t (Command.seq Command.brk Command.term) φ s =
              some (none, Command.brk, φ, s) := rfl
          unfold Command.runFuel at h
          rw [hstep] at h
          simp only at h
          cases N with
          | zero =>
              simp only [Command.runFuel, Prod.mk.injEq] at h
              exact absurd h.1 (by rintro ⟨⟩)
          | succ M =>
              have hstepB : Command.step t Command.brk φ s = none := rfl
              simp only [Command.runFuel, hstepB, Prod.mk.injEq] at h
              exact absurd h.2.2.1.1 (by rintro ⟨⟩)
        · unfold Command.runFuel at h
          cases hstep1 : Command.step t C1 φ s with
          | none =>
              have hstepw : Command.step t (Command.seq C1 Command.term) φ s = none := by
                simp only [Command.step, hns, hnb, hstep1]
              rw [hstepw] at h
              simp only [Prod.mk.injEq] at h
              exact absurd h.2.2.1.1 (by rintro ⟨⟩)
          | some x =>
              obtain ⟨a, C1', φ1', s1'⟩ := x
              have hstepw : Command.step t (Command.seq C1 Command.term) φ s =
                  some (a, Command.seq C1' Command.term, φ1', s1') := by
                simp only [Command.step, hns, hnb, hstep1]
              rw [hstepw] at h
              rcases hrec : Command.runFuel t (Command.seq C1' Command.term, φ1') s1' N with
                ⟨res, σ0, cf0, sf0⟩
              simp only [hrec, Prod.mk.injEq] at h
              obtain ⟨hres, hσeq, hcf, hsf⟩ := h
              have hrec' : Command.runFuel t (Command.seq C1' Command.term, φ1') s1' N =
                  (.stuck, σ0, (Command.term, φ'), []) := by
                rw [hres, hcf, hsf] at hrec; exact hrec
              obtain ⟨N', hNeq, hcase⟩ :=
                Command.runFuel_seqTerm_stuck_unwrap N C1' φ1' s1' σ0 φ' hrec'
              refine ⟨N' + 1, by omega, ?_⟩
              simp only [Command.runFuel, hstep1, hcase, hσeq]

end RAUndecidability
