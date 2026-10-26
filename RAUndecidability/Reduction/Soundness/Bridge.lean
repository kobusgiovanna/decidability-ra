import RAUndecidability.ProgramSemantics.Resolutions
import RAUndecidability.ProgramSemantics.Interpreter
import RAUndecidability.Reduction.Index
import RAUndecidability.Util.List

/-!
# Soundness bridge: from an arbitrary execution to a `Command.Run`

Thread-independent infrastructure connecting an arbitrary RA-consistent
execution to a concrete `Command.Run` per thread (the thread word of an execution (§2.2),
the RA semantics (§2.2), reachability (§2.2)): determinism of `Command.Run`, the
passage from `inducedLTS` reachability to a term-reaching run, and the
correspondence between a thread's closed-form word and `G.nthWrite`/
`G.nthRead`/`G.po`.
-/

namespace RAUndecidability

variable {D : Domains} {V : Vocabulary D} {t : D.Tid}

/-! ## Which `(Loc, VExpr)` pairs a write-labelled `RunStep` can produce

`Command.HasWrite u e C` holds when `Command.write u e` occurs syntactically
in `C`, in a position `Command.RunStep` can reach (either side of
`seq`/`loopSeq`, either branch of `ite`, the body of `whileLoop`). It is
closed backward under `RunStep` (`Command.RunStep.hasWrite_backward`), so every
write emitted by a run of `C_t` comes from a `write u e` node of `C_t` itself
(`Command.Run.write_hasWrite`). -/
def Command.HasWrite (u : D.Loc) (e : V.VExpr) : Command D V → Prop
  | .write u' e' => u = u' ∧ e = e'
  | .seq C1 C2 => Command.HasWrite u e C1 ∨ Command.HasWrite u e C2
  | .ite _ C1 C2 => Command.HasWrite u e C1 ∨ Command.HasWrite u e C2
  | .whileLoop _ C => Command.HasWrite u e C
  | .loopSeq C1 C2 => Command.HasWrite u e C1 ∨ Command.HasWrite u e C2
  | _ => False

/-- `Command.HasWrite` is closed backward under a single `RunStep`: `RunStep`
only unfolds or selects among the source's syntax. By induction on the
`RunStep` derivation. -/
theorem Command.RunStep.hasWrite_backward {s a c s' c'} (h : Command.RunStep t s a c s' c')
    {u : D.Loc} {e : V.VExpr} (hc' : Command.HasWrite u e c'.1) :
    Command.HasWrite u e c.1 := by
  induction h with
  | assign => simp [Command.HasWrite] at hc'
  | ndet => simp [Command.HasWrite] at hc'
  | seqSkip => exact Or.inr hc'
  | seqBreak => simp [Command.HasWrite] at hc'
  | iteTrue => exact Or.inl hc'
  | iteFalse => exact Or.inr hc'
  | whileTrue => rcases hc' with h | h <;> exact h
  | whileFalse => simp [Command.HasWrite] at hc'
  | loopSkip => exact Or.inr hc'
  | loopBreak => simp [Command.HasWrite] at hc'
  | write => simp [Command.HasWrite] at hc'
  | read => simp [Command.HasWrite] at hc'
  | seqCongr _ ih => rcases hc' with h | h; exacts [Or.inl (ih h), Or.inr h]
  | loopCongr _ ih => rcases hc' with h | h; exacts [Or.inl (ih h), Or.inr h]

/-- A write-labelled `RunStep`'s source command `HasWrite`s the `(u, e)` pair
backing its label, whose value is `V.evalV e` at that step's store. By
induction on the `RunStep` derivation. -/
theorem Command.RunStep.write_hasWrite {s a c s' c'} (h : Command.RunStep t s a c s' c')
    {l : ThreadLabel D t} (hl : a = some l) (hwt : l.1.op = .wt) :
    ∃ e : V.VExpr, Command.HasWrite l.1.loc e c.1 ∧ l.1.val = V.evalV e c.2 := by
  induction h with
  | assign => cases hl
  | ndet => cases hl
  | seqSkip => cases hl
  | seqBreak => cases hl
  | iteTrue => cases hl
  | iteFalse => cases hl
  | whileTrue => cases hl
  | whileFalse => cases hl
  | loopSkip => cases hl
  | loopBreak => cases hl
  | write =>
      injection hl with hl
      subst hl
      exact ⟨_, ⟨rfl, rfl⟩, rfl⟩
  | read =>
      injection hl with hl
      subst hl
      simp [EventLabel.op] at hwt
  | seqCongr _ ih =>
      obtain ⟨e, hhw, hval⟩ := ih hl
      exact ⟨e, Or.inl hhw, hval⟩
  | loopCongr _ ih =>
      obtain ⟨e, hhw, hval⟩ := ih hl
      exact ⟨e, Or.inl hhw, hval⟩

variable {C_t' : Command D V} {φ₀' : V.Store}

/-- `Command.HasWrite` transports from any configuration of a `Command.Run`
starting at `(C_t, φ₀)` back to `C_t`. -/
theorem Command.Run.hasWrite_endpoint {s σ cLast s' cf}
    (hrun : Command.Run t s (C_t', φ₀') σ cLast s' cf) {u : D.Loc} {e : V.VExpr}
    (h : Command.HasWrite u e cf.1) : Command.HasWrite u e C_t' := by
  induction hrun with
  | nil => exact h
  | silentSnoc _ hstep ih => exact ih (hstep.hasWrite_backward h)
  | labelledSnoc _ hstep ih => exact ih (hstep.hasWrite_backward h)

/-- Every write-labelled entry of a `Command.Run`'s emitted word comes from a
`write u e` node of the starting command `C_t`, with value `V.evalV e` at the
store of that step. By induction on `Command.Run`. -/
theorem Command.Run.write_hasWrite {s σ cLast s' cf}
    (hrun : Command.Run t s (C_t', φ₀') σ cLast s' cf) :
    ∀ l ∈ σ, l.1.op = .wt → ∃ e : V.VExpr, Command.HasWrite l.1.loc e C_t' ∧
      ∃ φ, l.1.val = V.evalV e φ := by
  induction hrun with
  | nil => intro l hl; cases hl
  | silentSnoc _ _ ih => exact ih
  | labelledSnoc hprev hstep ih =>
      intro l hl hwt
      rcases List.mem_append.mp hl with hl' | hl'
      · exact ih l hl' hwt
      · have hl'' : l = _ := (List.mem_singleton.mp hl')
        subst hl''
        obtain ⟨e, hhw, hval⟩ := hstep.write_hasWrite rfl hwt
        exact ⟨e, hprev.hasWrite_endpoint hhw, _, hval⟩

/-- `Command.step` on `.ndetAssign` against the empty resolution is `none`. -/
theorem Command.step_ndetAssign_nil (v : V.LVar) (X : Finset V.LVal) (hX : X.Nonempty)
    (φ : V.Store) : Command.step t (Command.ndetAssign v X hX) φ [] = none := rfl

/-- `Command.step` on `.ndetAssign` against a resolution whose head lies in `X`
assigns that head to `v`. -/
theorem Command.step_ndetAssign_cons_pos (v : V.LVar) (X : Finset V.LVal) (hX : X.Nonempty)
    (φ : V.Store) (c : V.LVal) (rest : List V.LVal) (hc : c ∈ X) :
    Command.step t (Command.ndetAssign v X hX) φ (c :: rest) =
      some (none, Command.skip, Function.update φ v c, rest) := by
  simp only [Command.step, hc, if_true]
  rfl


/-- `Command.step_ndetAssign_nil` under a `.loopSeq`/`.seq` wrapping. -/
theorem Command.step_seq_loopSeq_ndetAssign_nil (v : V.LVar) (X : Finset V.LVal)
    (hX : X.Nonempty) (φ : V.Store) (C2 C3 : Command D V) :
    Command.step t (Command.seq (Command.loopSeq (Command.ndetAssign v X hX) C2) C3) φ [] =
      none := rfl

/-- `Command.step` on a wrapped `.ndetAssign` against a resolution whose head
lies outside `X` is `none`. -/
theorem Command.step_seq_loopSeq_ndetAssign_cons_neg (v : V.LVar) (X : Finset V.LVal)
    (hX : X.Nonempty) (φ : V.Store) (C2 C3 : Command D V) (c : V.LVal) (rest : List V.LVal)
    (hc : c ∉ X) :
    Command.step t (Command.seq (Command.loopSeq (Command.ndetAssign v X hX) C2) C3) φ
      (c :: rest) = none := by
  simp only [Command.step, hc, if_false]

/-! ## Which `(Loc, VExpr)` pairs a read-labelled run step can produce

The read counterpart of `Command.HasWrite`. -/

section HasRead

variable {D : Domains} {V : Vocabulary D} {t : D.Tid}

/-- `Command.HasRead u e C`: `Command.read u e` occurs in `C` in a position a
`RunStep` can reach. -/
def Command.HasRead (u : D.Loc) (e : V.VExpr) : Command D V → Prop
  | .read u' e' => u = u' ∧ e = e'
  | .seq C1 C2 => Command.HasRead u e C1 ∨ Command.HasRead u e C2
  | .ite _ C1 C2 => Command.HasRead u e C1 ∨ Command.HasRead u e C2
  | .whileLoop _ C => Command.HasRead u e C
  | .loopSeq C1 C2 => Command.HasRead u e C1 ∨ Command.HasRead u e C2
  | _ => False

/-- `Command.HasRead` is closed backward under a single `RunStep`. -/
theorem Command.RunStep.hasRead_backward {s a c s' c'} (h : Command.RunStep t s a c s' c')
    {u : D.Loc} {e : V.VExpr} (hc' : Command.HasRead u e c'.1) :
    Command.HasRead u e c.1 := by
  induction h with
  | assign => simp [Command.HasRead] at hc'
  | ndet => simp [Command.HasRead] at hc'
  | seqSkip => exact Or.inr hc'
  | seqBreak => simp [Command.HasRead] at hc'
  | iteTrue => exact Or.inl hc'
  | iteFalse => exact Or.inr hc'
  | whileTrue => rcases hc' with h | h <;> exact h
  | whileFalse => simp [Command.HasRead] at hc'
  | loopSkip => exact Or.inr hc'
  | loopBreak => simp [Command.HasRead] at hc'
  | write => simp [Command.HasRead] at hc'
  | read => simp [Command.HasRead] at hc'
  | seqCongr _ ih => rcases hc' with h | h; exacts [Or.inl (ih h), Or.inr h]
  | loopCongr _ ih => rcases hc' with h | h; exacts [Or.inl (ih h), Or.inr h]

/-- A read-labelled `RunStep`'s source command `HasRead`s the `(u, e)` pair
backing its label, whose value is `V.evalV e` at that step's store. -/
theorem Command.RunStep.read_hasRead {s a c s' c'} (h : Command.RunStep t s a c s' c')
    {l : ThreadLabel D t} (hl : a = some l) (hrd : l.1.op = .rd) :
    ∃ e : V.VExpr, Command.HasRead l.1.loc e c.1 ∧ l.1.val = V.evalV e c.2 := by
  induction h with
  | assign => cases hl
  | ndet => cases hl
  | seqSkip => cases hl
  | seqBreak => cases hl
  | iteTrue => cases hl
  | iteFalse => cases hl
  | whileTrue => cases hl
  | whileFalse => cases hl
  | loopSkip => cases hl
  | loopBreak => cases hl
  | write =>
      injection hl with hl
      subst hl
      simp [EventLabel.op] at hrd
  | read =>
      injection hl with hl
      subst hl
      exact ⟨_, ⟨rfl, rfl⟩, rfl⟩
  | seqCongr _ ih =>
      obtain ⟨e, hhr, hval⟩ := ih hl
      exact ⟨e, Or.inl hhr, hval⟩
  | loopCongr _ ih =>
      obtain ⟨e, hhr, hval⟩ := ih hl
      exact ⟨e, Or.inl hhr, hval⟩

variable {C_t' : Command D V} {φ₀' : V.Store}

/-- `Command.HasRead` transports from any configuration of a `Command.Run`
starting at `(C_t, φ₀)` back to `C_t`. -/
theorem Command.Run.hasRead_endpoint {s σ cLast s' cf}
    (hrun : Command.Run t s (C_t', φ₀') σ cLast s' cf) {u : D.Loc} {e : V.VExpr}
    (h : Command.HasRead u e cf.1) : Command.HasRead u e C_t' := by
  induction hrun with
  | nil => exact h
  | silentSnoc _ hstep ih => exact ih (hstep.hasRead_backward h)
  | labelledSnoc _ hstep ih => exact ih (hstep.hasRead_backward h)

/-- Every read-labelled entry of a `Command.Run`'s emitted word comes from a
`read u e` node of the starting command `C_t`, with value `V.evalV e` at the
store of that step. -/
theorem Command.Run.read_hasRead {s σ cLast s' cf}
    (hrun : Command.Run t s (C_t', φ₀') σ cLast s' cf) :
    ∀ l ∈ σ, l.1.op = .rd → ∃ e : V.VExpr, Command.HasRead l.1.loc e C_t' ∧
      ∃ φ, l.1.val = V.evalV e φ := by
  induction hrun with
  | nil => intro l hl; cases hl
  | silentSnoc _ _ ih => exact ih
  | labelledSnoc hprev hstep ih =>
      intro l hl hrd
      rcases List.mem_append.mp hl with hl' | hl'
      · exact ih l hl' hrd
      · have hl'' : l = _ := (List.mem_singleton.mp hl')
        subst hl''
        obtain ⟨e, hhr, hval⟩ := hstep.read_hasRead rfl hrd
        exact ⟨e, hprev.hasRead_endpoint hhr, _, hval⟩

end HasRead

/-! ## `Command.Run` determinism, via `Command.runFuel` -/

/-! `Command.runFuelCLast` runs alongside `Command.runFuel`, tracking `cLast`:
the configuration right after the most recent labelled step (or the start, if
there has been none). -/

/-- `Command.runFuelCLast t c s n acc`: run `n` more steps from `(c, s)`,
threading `acc` as the accumulator described above. -/
def Command.runFuelCLast (t : D.Tid) : Config D V → List V.LVal → ℕ → Config D V → Config D V
  | _, _, 0, cLast => cLast
  | c, s, n + 1, cLast =>
      match Command.step t c.1 c.2 s with
      | none => cLast
      | some (a, C', φ', s') =>
          Command.runFuelCLast t (C', φ') s' n (match a with | none => cLast | some _ => (C', φ'))

/-- Transporting a `Command.Run` across `Command.runFuel`: if the run's
endpoint `(s', cf)` continues, under `n2` more fuel, to `(res2, σ2, c2, s2)`,
then some fuel `n1` takes the whole run there from `(s, c₀)`, emitting the
run's word first. By induction on the run, using `Command.step_complete`. -/
theorem Command.Run.exists_runFuel_combined_append {s : List V.LVal} {c₀ : Config D V}
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {s' : List V.LVal} {cf : Config D V}
    (hrun : Command.Run t s c₀ σ cLast s' cf) :
    ∀ (n2 : ℕ) (res2 : Command.RunOutcome) (σ2 : Word (ThreadLabel D t)) (c2 : Config D V)
      (s2 : List V.LVal) (rcl : Config D V),
      Command.runFuel t cf s' n2 = (res2, σ2, c2, s2) →
      Command.runFuelCLast t cf s' n2 cLast = rcl →
      ∃ n1, Command.runFuel t c₀ s n1 = (res2, σ ++ σ2, c2, s2) ∧
        Command.runFuelCLast t c₀ s n1 c₀ = rcl := by
  induction hrun with
  | nil => intro n2 res2 σ2 c2 s2 rcl h2 h2'; exact ⟨n2, by simpa using h2, h2'⟩
  | silentSnoc _ hstep ih =>
      intro n2 res2 σ2 c2 s2 rcl h2 h2'
      have hcstep := Command.step_complete hstep
      refine ih (n2 + 1) res2 σ2 c2 s2 rcl ?_ ?_
      · simp only [Command.runFuel, hcstep]; simpa using h2
      · rw [Command.runFuelCLast, hcstep]; dsimp only; exact h2'
  | @labelledSnoc _ cLastP s' c' l _ _ hprem hstep ih =>
      intro n2 res2 σ2 c2 s2 rcl h2 h2'
      have hcstep := Command.step_complete hstep
      have hfuel : Command.runFuel t c' s' (n2 + 1) = (res2, l :: σ2, c2, s2) := by
        rw [Command.runFuel, hcstep]
        dsimp only
        rw [h2]
      have hfuelCL : Command.runFuelCLast t c' s' (n2 + 1) cLastP = rcl := by
        rw [Command.runFuelCLast, hcstep]
        dsimp only
        exact h2'
      obtain ⟨n1, hn1, hn1'⟩ := ih (n2 + 1) res2 (l :: σ2) c2 s2 rcl hfuel hfuelCL
      exact ⟨n1, by simpa using hn1, hn1'⟩

/-- A run that reaches `term` matches `Command.runFuel` (with outcome
`.stuck`) and `Command.runFuelCLast` (with value the run's `cLast`) at one
common fuel value. -/
theorem Command.Run.exists_runFuel_combined_of_term {s : List V.LVal} {c₀ : Config D V}
    {σ : Word (ThreadLabel D t)} {cLast : Config D V} {s' : List V.LVal} {φ : V.Store}
    (hrun : Command.Run t s c₀ σ cLast s' (Command.term, φ)) :
    ∃ n, Command.runFuel t c₀ s n = (.stuck, σ, (Command.term, φ), s') ∧
      Command.runFuelCLast t c₀ s n c₀ = cLast := by
  obtain ⟨n, hn, hn'⟩ :=
    Command.Run.exists_runFuel_combined_append hrun 1 .stuck [] (Command.term, φ) s' cLast
      (by simp [Command.runFuel, Command.step]) (by rw [Command.runFuelCLast]; simp [Command.step])
  exact ⟨n, by simpa using hn, hn'⟩

/-- One more unit of fuel past a `.stuck` result changes nothing. By
induction on `n`. -/
theorem Command.runFuel_stuck_succ {σ : Word (ThreadLabel D t)} {cf : Config D V}
    {sf : List V.LVal} :
    ∀ (n : ℕ) (c : Config D V) (s : List V.LVal),
      Command.runFuel t c s n = (.stuck, σ, cf, sf) →
      Command.runFuel t c s (n + 1) = (.stuck, σ, cf, sf)
  | 0, c, s, h => by simp [Command.runFuel] at h
  | n + 1, c, s, h => by
      unfold Command.runFuel at h ⊢
      cases hs : Command.step t c.1 c.2 s with
      | none => simp only [hs] at h ⊢; exact h
      | some x =>
          obtain ⟨a, C', φ', s'⟩ := x
          simp only [hs] at h ⊢
          rcases hrec : Command.runFuel t (C', φ') s' n with ⟨res, σr, cr, sr⟩
          simp only [hrec, Prod.mk.injEq] at h
          obtain ⟨hres, hσ, hcf, hsf⟩ := h
          have hrec' : Command.runFuel t (C', φ') s' n = (.stuck, σr, cf, sf) := by
            rw [hrec, hres, hcf, hsf]
          simp only [Command.runFuel_stuck_succ n (C', φ') s' hrec', hσ]

/-- Once `Command.runFuel` reports `.stuck`, more fuel changes nothing. -/
theorem Command.runFuel_stuck_stable {c : Config D V} {s : List V.LVal}
    {σ : Word (ThreadLabel D t)} {cf : Config D V} {sf : List V.LVal} {n : ℕ}
    (h : Command.runFuel t c s n = (.stuck, σ, cf, sf)) :
    ∀ k, Command.runFuel t c s (n + k) = (.stuck, σ, cf, sf) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have := Command.runFuel_stuck_succ (n + k) c s ih
      rwa [Nat.add_assoc] at this


/-! ## From `inducedLTS` reachability to a term-reaching `Command.Run` -/

variable {C_t : Command D V} {φ₀ : V.Store}

/-- An `inducedLTS` word ending in `term` (what `ExecutionGraph.Reaches`
unfolds to at the final state, by the term-appended branch of reachability (§2.2))
comes from a `Command.Run` that reaches `Command.term`: by
`resolution_complete` (second disjunct) and `Command.Run.extendSilent`. -/
theorem exists_run_of_induced_reaches {w : Word (ThreadLabel D t)}
    (hreaches : (inducedLTS (t := t) (C_t := C_t) (φ₀ := φ₀)).Reaches (w.map some ++ [none])
      (inducedFinal (t := t) (C_t := C_t) (φ₀ := φ₀))) :
    ∃ (s : List V.LVal) (cLast : Config D V) (φ : V.Store),
      Command.Run t s (C_t, φ₀) w cLast [] (Command.term, φ) := by
  rcases resolution_complete (w.map some ++ [none]) inducedFinal hreaches with
    ⟨s, σ, cLast, hrun, hq, hweq⟩ | ⟨s, σ, cLast, hrun, hq, hhalts, hweq⟩
  · cases hq
  · have hweq' : w.map some = σ.map some := List.append_left_injective [none] hweq
    have hσw : w = σ :=
      List.map_injective_iff.mpr (fun _ _ h => Option.some.injEq _ _ ▸ h) hweq'
    subst hσw
    obtain ⟨φ, hchain⟩ := hhalts
    obtain ⟨s', hrun'⟩ := Command.Run.extendSilent hchain hrun
    exact ⟨s', cLast, φ, hrun'⟩

/-! ## Splitting a `Command.runFuel` evaluation at an `.outOfFuel` point -/

/-- If `k` fuel from `(c, s)` runs out (`.outOfFuel`) at `(cf, sf)` after
emitting `σ0`, then `k + m` fuel from `(c, s)` agrees with `m` more fuel from
`(cf, sf)`, with `σ0` prepended. By induction on `k`. -/
theorem Command.runFuel_outOfFuel_split {t : D.Tid} :
    ∀ (k : ℕ) (c : Config D V) (s : List V.LVal) (σ0 : Word (ThreadLabel D t))
      (cf : Config D V) (sf : List V.LVal),
      Command.runFuel t c s k = (.outOfFuel, σ0, cf, sf) →
      ∀ (m : ℕ) (res : Command.RunOutcome) (σ' : Word (ThreadLabel D t)) (c' : Config D V)
        (s' : List V.LVal),
        Command.runFuel t c s (k + m) = (res, σ', c', s') →
        ∃ σ1, Command.runFuel t cf sf m = (res, σ1, c', s') ∧ σ' = σ0 ++ σ1
  | 0, c, s, σ0, cf, sf, h, m, res, σ', c', s', h2 => by
      simp only [Command.runFuel, Prod.mk.injEq] at h
      obtain ⟨-, hσ0, hcf, hsf⟩ := h
      subst hσ0; subst hcf; subst hsf
      simp only [Nat.zero_add] at h2
      exact ⟨σ', h2, rfl⟩
  | k + 1, c, s, σ0, cf, sf, h, m, res, σ', c', s', h2 => by
      unfold Command.runFuel at h
      cases hs : Command.step t c.1 c.2 s with
      | none =>
          simp only [hs, Prod.mk.injEq] at h
          exact absurd h.1 (by decide)
      | some x =>
          obtain ⟨a, C', φ'', s''⟩ := x
          simp only [hs] at h
          rcases hrec : Command.runFuel t (C', φ'') s'' k with ⟨resk, σk, cfk, sfk⟩
          simp only [hrec, Prod.mk.injEq] at h
          obtain ⟨hresk, hσ0, hcfk, hsfk⟩ := h
          have hk : Command.runFuel t (C', φ'') s'' k = (.outOfFuel, σk, cf, sf) := by
            rw [hrec, hresk, hcfk, hsfk]
          have h2' : Command.runFuel t c s (k + m + 1) = (res, σ', c', s') := by
            rw [show k + m + 1 = k + 1 + m from by omega]; exact h2
          unfold Command.runFuel at h2'
          simp only [hs] at h2'
          rcases hrec2 : Command.runFuel t (C', φ'') s'' (k + m) with ⟨res2, σ2, cf2, sf2⟩
          simp only [hrec2, Prod.mk.injEq] at h2'
          obtain ⟨hres2, hσ2, hcf2, hsf2⟩ := h2'
          obtain ⟨σ1, ihres, ihσ⟩ :=
            Command.runFuel_outOfFuel_split k (C', φ'') s'' σk cf sf hk m res2 σ2 cf2 sf2 hrec2
          refine ⟨σ1, ?_, ?_⟩
          · rw [← hres2, ← hcf2, ← hsf2]; exact ihres
          · rw [← hσ2, ← hσ0, ihσ]
            cases a with
            | none => rfl
            | some l => rfl

/-- The converse of `Command.runFuel_outOfFuel_split`: an `.outOfFuel`
checkpoint at `k` fuel followed by any outcome after `m` more fuel gives that
outcome after `k + m` fuel, with the two emitted words concatenated. -/
theorem Command.runFuel_outOfFuel_append {t : D.Tid} :
    ∀ (k : ℕ) (c : Config D V) (s : List V.LVal) (σ0 : Word (ThreadLabel D t))
      (cf : Config D V) (sf : List V.LVal),
      Command.runFuel t c s k = (.outOfFuel, σ0, cf, sf) →
      ∀ (m : ℕ) (res : Command.RunOutcome) (σ1 : Word (ThreadLabel D t)) (c' : Config D V)
        (s' : List V.LVal),
        Command.runFuel t cf sf m = (res, σ1, c', s') →
        Command.runFuel t c s (k + m) = (res, σ0 ++ σ1, c', s')
  | 0, c, s, σ0, cf, sf, h, m, res, σ1, c', s', h2 => by
      simp only [Command.runFuel, Prod.mk.injEq] at h
      obtain ⟨-, hσ0, hcf, hsf⟩ := h
      subst hσ0; subst hcf; subst hsf
      simpa using h2
  | k + 1, c, s, σ0, cf, sf, h, m, res, σ1, c', s', h2 => by
      unfold Command.runFuel at h
      cases hstep : Command.step t c.1 c.2 s with
      | none =>
          rw [hstep] at h
          simp only [Prod.mk.injEq] at h
          exact absurd h.1 (by decide)
      | some x =>
          obtain ⟨a, C', φ', s''⟩ := x
          rw [hstep] at h
          rcases hrec : Command.runFuel t (C', φ') s'' k with ⟨res0, σk, cfk, sfk⟩
          simp only [hrec, Prod.mk.injEq] at h
          obtain ⟨hres0, hσ0eq, hcfk, hsfk⟩ := h
          have hrec' : Command.runFuel t (C', φ') s'' k = (.outOfFuel, σk, cf, sf) := by
            rw [hrec, hres0, hcfk, hsfk]
          have ihApplied :=
            Command.runFuel_outOfFuel_append k (C', φ') s'' σk cf sf hrec' m res σ1 c' s' h2
          have hfuel : k + 1 + m = k + m + 1 := by omega
          rw [hfuel]
          simp only [Command.runFuel, hstep, ihApplied]
          rw [← hσ0eq]
          cases a with
          | none => rfl
          | some l => rfl

/-! ## From `threadWord` to `nthWrite`/`nthRead`

Once a thread's word `G.threadWord t` is known in closed form, its indexed
events `G.nthWrite`/`G.nthRead` (`Reduction/Index.lean`) are read off from the
closed form. -/

variable {G : ExecutionGraph D}

/-- `threadWord` without the `some`-wrap: the labels of `G.threadEvents t`, as
`ThreadLabel`s. -/
noncomputable def ExecutionGraph.threadLabels (G : ExecutionGraph D) (t : D.Tid) :
    Word (ThreadLabel D t) :=
  (G.threadEvents t).map
    fun (e : {x // x ∈ G.Events.filter (fun e => e.tid = t)}) =>
      let he : e.1.tid = t := (Finset.mem_filter.mp e.2).2
      (⟨e.1.lab, he⟩ : ThreadLabel D t)

/-- An event of `G` on thread `t` has its label among `G.threadLabels t`. -/
theorem ExecutionGraph.mem_threadLabels_of_mem_Events {e : Event D} {t : D.Tid}
    (he : e ∈ G.Events) (htid : e.tid = t) :
    (⟨e.lab, htid⟩ : ThreadLabel D t) ∈ G.threadLabels t := by
  have hmem : (⟨e, Finset.mem_filter.mpr ⟨he, htid⟩⟩ :
      {x // x ∈ G.Events.filter (fun e' => e'.tid = t)}) ∈ G.threadEvents t := by
    rw [ExecutionGraph.threadEvents, Finset.mem_sort]
    exact Finset.mem_univ _
  unfold ExecutionGraph.threadLabels
  exact List.mem_map.mpr ⟨_, hmem, rfl⟩

/-- `threadWord` is `threadLabels`, `some`-wrapped. -/
theorem ExecutionGraph.threadWord_eq_map_threadLabels (t : D.Tid) :
    G.threadWord t = (G.threadLabels t).map some := by
  unfold ExecutionGraph.threadWord ExecutionGraph.threadLabels
  rw [List.map_map]
  rfl

/-- `G.threadWord t = w.map some` forces `G.threadLabels t = w`. -/
theorem ExecutionGraph.threadLabels_eq_of_threadWord {t : D.Tid}
    {w : Word (ThreadLabel D t)} (hw : G.threadWord t = w.map some) :
    G.threadLabels t = w :=
  List.map_injective_iff.mpr (fun _ _ h => Option.some.injEq _ _ ▸ h)
    ((G.threadWord_eq_map_threadLabels t).symm.trans hw)

/-- The labels of `G.opEvents t x op` are the `(x, op)`-filtered sublist of
`G.threadLabels t`. -/
theorem ExecutionGraph.opEvents_map_lab_eq_filter_threadLabels (t : D.Tid) (x : D.Loc)
    (op : OpType) :
    (G.opEvents t x op).map Event.lab =
      ((G.threadLabels t).filter (fun l => l.1.loc = x ∧ l.1.op = op)).map Subtype.val := by
  unfold ExecutionGraph.threadLabels ExecutionGraph.opEvents
  rw [List.filter_map, List.map_map, List.map_map]
  rfl

/-- Once `G.threadWord t = w.map some`, `G.nthEvent t x op i` exists exactly
when the `i`-th `(x, op)`-matching position of `w` does, and carries its
label. -/
theorem ExecutionGraph.nthEvent_lab_of_threadWord {t : D.Tid} {w : Word (ThreadLabel D t)}
    (hw : G.threadWord t = w.map some) (x : D.Loc) (op : OpType) (i : ℕ) :
    (G.nthEvent t x op i).map Event.lab =
      (w.filter (fun l => l.1.loc = x ∧ l.1.op = op))[i]?.map Subtype.val := by
  have hlabels := ExecutionGraph.threadLabels_eq_of_threadWord hw
  have hopmap := ExecutionGraph.opEvents_map_lab_eq_filter_threadLabels (G := G) t x op
  rw [hlabels] at hopmap
  unfold ExecutionGraph.nthEvent
  rw [← List.getElem?_map, hopmap, List.getElem?_map]

/-- `nthEvent_lab_of_threadWord`, specialized: if the closed-form word's
`i`-th matching label is known, so is the label of `G`'s `i`-th matching
event. -/
theorem ExecutionGraph.nthEvent_lab_eq_of_threadWord {t : D.Tid} {w : Word (ThreadLabel D t)}
    (hw : G.threadWord t = w.map some) {x : D.Loc} {op : OpType} {i : ℕ} {lab : ThreadLabel D t}
    (hlab : (w.filter (fun l => l.1.loc = x ∧ l.1.op = op))[i]? = some lab) :
    ∃ e, G.nthEvent t x op i = some e ∧ e.lab = lab.1 := by
  have h := ExecutionGraph.nthEvent_lab_of_threadWord hw x op i
  rw [hlab] at h
  simp only [Option.map_some, Option.map_eq_some_iff] at h
  obtain ⟨e, he1, he2⟩ := h
  exact ⟨e, he1, he2⟩

/-- The converse of `nthEvent_lab_eq_of_threadWord`: if `G`'s `i`-th matching
event exists, so does the closed-form word's `i`-th matching label, and the
two agree. -/
theorem ExecutionGraph.exists_filter_of_nthEvent {t : D.Tid} {w : Word (ThreadLabel D t)}
    (hw : G.threadWord t = w.map some) {x : D.Loc} {op : OpType} {i : ℕ} {e : Event D}
    (he : G.nthEvent t x op i = some e) :
    ∃ lab : ThreadLabel D t,
      (w.filter (fun l => l.1.loc = x ∧ l.1.op = op))[i]? = some lab ∧ e.lab = lab.1 := by
  have h := ExecutionGraph.nthEvent_lab_of_threadWord hw x op i
  rw [he] at h
  rcases hf : (w.filter (fun l => l.1.loc = x ∧ l.1.op = op))[i]? with _ | lab
  · rw [hf] at h; simp at h
  · rw [hf] at h
    exact ⟨lab, hf, Option.some.inj h⟩

/-- `nthEvent_lab_eq_of_threadWord`, specialized to a write. -/
theorem ExecutionGraph.nthWrite_lab_eq_of_threadWord {t : D.Tid} {w : Word (ThreadLabel D t)}
    (hw : G.threadWord t = w.map some) {x : D.Loc} {i : ℕ} {lab : ThreadLabel D t}
    (hlab : (w.filter (fun l => l.1.loc = x ∧ l.1.op = OpType.wt))[i]? = some lab) :
    ∃ e, G.nthWrite t x i = some e ∧ e.lab = lab.1 :=
  ExecutionGraph.nthEvent_lab_eq_of_threadWord hw hlab

/-- `nthEvent_lab_eq_of_threadWord`, specialized to a read. -/
theorem ExecutionGraph.nthRead_lab_eq_of_threadWord {t : D.Tid} {w : Word (ThreadLabel D t)}
    (hw : G.threadWord t = w.map some) {x : D.Loc} {i : ℕ} {lab : ThreadLabel D t}
    (hlab : (w.filter (fun l => l.1.loc = x ∧ l.1.op = OpType.rd))[i]? = some lab) :
    ∃ e, G.nthRead t x i = some e ∧ e.lab = lab.1 :=
  ExecutionGraph.nthEvent_lab_eq_of_threadWord hw hlab

/-! ## `po` agrees with position order in a closed-form word

`G.threadEvents t` is sorted by `G.po`, so the overall position of an event in
a thread's closed-form word determines its `po`-order against other events of
the same thread. -/

/-- `G.threadEvents t` is `G.po`-sorted (`Finset.pairwise_sort` under the
`LinearOrder` induced by `po_total`). -/
theorem ExecutionGraph.threadEvents_pairwise_po (G : ExecutionGraph D) (t : D.Tid) :
    (G.threadEvents t).Pairwise (fun a b => G.po a.1 b.1) := by
  have hl_unfold :
      haveI := G.po_total t
      haveI : DecidableRel
          (fun a b : {e : Event D // e ∈ G.Events.filter (fun e => e.tid = t)} => G.po a.1 b.1) :=
        Classical.decRel _
      haveI : LinearOrder {e : Event D // e ∈ G.Events.filter (fun e => e.tid = t)} :=
        linearOrderOfSTO fun a b => G.po a.1 b.1
      G.threadEvents t = Finset.univ.sort (· ≤ ·) := by
    unfold ExecutionGraph.threadEvents
    rfl
  have hnodup : (G.threadEvents t).Nodup := by
    unfold ExecutionGraph.threadEvents
    exact Finset.sort_nodup _ _
  have hpwLE :
      haveI := G.po_total t
      haveI : DecidableRel
          (fun a b : {e : Event D // e ∈ G.Events.filter (fun e => e.tid = t)} => G.po a.1 b.1) :=
        Classical.decRel _
      haveI : LinearOrder {e : Event D // e ∈ G.Events.filter (fun e => e.tid = t)} :=
        linearOrderOfSTO fun a b => G.po a.1 b.1
      (G.threadEvents t).Pairwise (· ≤ ·) := by
    rw [hl_unfold]
    exact Finset.pairwise_sort _ _
  rw [List.pairwise_iff_getElem] at hpwLE ⊢
  intro i j hi hj hij
  rcases hpwLE i j hi hj hij with heq | hlt
  · exact absurd ((List.getElem_inj hnodup).mp heq) (by omega)
  · exact hlt

/-- A closed-form word's value at position `p` identifies the
`G.threadEvents t` entry at `p` and its label. -/
theorem ExecutionGraph.threadEvents_getElem_lab_of_threadWord {t : D.Tid}
    {w : Word (ThreadLabel D t)} (hw : G.threadWord t = w.map some) (p : ℕ) (l : ThreadLabel D t)
    (hl : w[p]? = some l) :
    ∃ (e : {x // x ∈ G.Events.filter (fun e => e.tid = t)})
      (hlt : p < (G.threadEvents t).length),
      (G.threadEvents t)[p]'hlt = e ∧ e.1.lab = l.1 := by
  have hlabels := G.threadLabels_eq_of_threadWord hw
  have hl' : (G.threadLabels t)[p]? = some l := by rw [hlabels]; exact hl
  unfold ExecutionGraph.threadLabels at hl'
  rw [List.getElem?_map] at hl'
  obtain ⟨e, heq, hval⟩ := Option.map_eq_some_iff.mp hl'
  obtain ⟨hlt, heq2⟩ := List.getElem?_eq_some_iff.mp heq
  exact ⟨e, hlt, heq2, congrArg Subtype.val hval⟩


/-- Identifies the event `G.nthEvent t x op i` with the entry at a known
overall position `P` of `G.threadEvents t`, given that `w[P]` is an
`(x, op)`-label and exactly `i` of the first `P` entries of `w` are
(`hcount`). Needed where labels recur (e.g. `CheckX`'s `xA`-write value has
period 4), so that the label alone does not identify the event. -/
theorem ExecutionGraph.nthEvent_eq_of_threadWord_pos {t : D.Tid} {w : Word (ThreadLabel D t)}
    (hw : G.threadWord t = w.map some) {x : D.Loc} {op : OpType} {i P : ℕ}
    (hP : P < (G.threadEvents t).length) {lab : ThreadLabel D t} (hlabP : w[P]? = some lab)
    (hloc : lab.1.loc = x) (hop : lab.1.op = op)
    (hcount : ((w.take P).filter (fun l => l.1.loc = x ∧ l.1.op = op)).length = i) :
    G.nthEvent t x op i = some ((G.threadEvents t)[P]'hP).1 := by
  have hgetP : (G.threadEvents t)[P]? = some ((G.threadEvents t)[P]'hP) :=
    List.getElem?_eq_getElem hP
  have hlabeq : ((G.threadEvents t)[P]'hP).1.lab = lab.1 := by
    obtain ⟨e, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw P lab hlabP
    rw [show (G.threadEvents t)[P]'hP = (G.threadEvents t)[P]'hlt from rfl, heq]
    exact hlab
  have hpredP : (fun e : {x // x ∈ G.Events.filter (fun e => e.tid = t)} =>
      e.1.loc = x ∧ e.1.op = op) ((G.threadEvents t)[P]'hP) := by
    refine ⟨?_, ?_⟩
    · change ((G.threadEvents t)[P]'hP).1.lab.loc = x
      rw [hlabeq]; exact hloc
    · change ((G.threadEvents t)[P]'hP).1.lab.op = op
      rw [hlabeq]; exact hop
  have hlen : (G.threadEvents t).length = w.length := by
    have := congrArg List.length (G.threadLabels_eq_of_threadWord hw)
    unfold ExecutionGraph.threadLabels at this
    rwa [List.length_map] at this
  have hrel : ∀ q (h1 : q < (G.threadEvents t).length) (h2 : q < w.length),
      decide (((G.threadEvents t)[q]'h1).1.loc = x ∧ ((G.threadEvents t)[q]'h1).1.op = op) =
        decide ((w[q]'h2).1.loc = x ∧ (w[q]'h2).1.op = op) := by
    intro q h1 h2
    obtain ⟨e, hlt, heq, hlab⟩ :=
      G.threadEvents_getElem_lab_of_threadWord hw q (w[q]'h2) (List.getElem?_eq_getElem h2)
    change decide (((G.threadEvents t)[q]'h1).1.lab.loc = x ∧
        ((G.threadEvents t)[q]'h1).1.lab.op = op) = decide ((w[q]'h2).1.loc = x ∧
        (w[q]'h2).1.op = op)
    rw [show (G.threadEvents t)[q]'h1 = (G.threadEvents t)[q]'hlt from rfl, heq, hlab]
  have hcount' : (((G.threadEvents t).take P).filter
      (fun e : {x // x ∈ G.Events.filter (fun e => e.tid = t)} =>
        e.1.loc = x ∧ e.1.op = op)).length = i := by
    have hthis := List.filter_take_length_eq_of_forall_getElem hlen
      (fun e : {x // x ∈ G.Events.filter (fun e => e.tid = t)} =>
        decide (e.1.loc = x ∧ e.1.op = op))
      (fun l : ThreadLabel D t => decide (l.1.loc = x ∧ l.1.op = op)) hrel P
    rw [hthis]
    simpa using hcount
  have hkey := List.getElem?_filter_of_take_filter_length (G.threadEvents t)
    (fun e : {x // x ∈ G.Events.filter (fun e => e.tid = t)} => decide (e.1.loc = x ∧ e.1.op = op))
    P i ((G.threadEvents t)[P]'hP) hgetP (by simpa using hpredP)
    (by simpa using hcount')
  have hkey' : (G.opEvents t x op)[i]? = some ((G.threadEvents t)[P]'hP).1 := by
    unfold ExecutionGraph.opEvents
    rw [List.getElem?_map]
    simp only [(by simpa using hkey : (List.filter
      (fun e : {x // x ∈ G.Events.filter (fun e => e.tid = t)} => e.1.loc = x ∧ e.1.op = op)
      (G.threadEvents t))[i]? = some ((G.threadEvents t)[P]'hP))]
    rfl
  exact hkey'

/-! ## Indexed events at known positions

For a thread whose closed-form word is known, the event `G.nthEvent t x op i`
is identified with an entry of `G.threadEvents t` at a computed position, and
`po` between two events of the thread is read off their positions. -/

/-- The indexed `(x, op)`-events of a thread whose closed-form word is a
prefix `pre` followed by blocks `L.flatMap B` of length `n`, each with exactly
one `(x, op)`-label, at offset `p0` (`hmap`): if `pre` holds `c` of them, then
`G`'s `(j + c)`-th one exists only for `j < L.length`, and for `L[j]? = some a`
it is the event at position `pre.length + j * n + p0`. -/
theorem ExecutionGraph.nthEvent_of_uniform {α : Type} {t : D.Tid} {x : D.Loc} {op : OpType}
    {pre : List (ThreadLabel D t)} {L : List α} {B : α → List (ThreadLabel D t)}
    (hw : G.threadWord t = (pre ++ L.flatMap B).map some) {n p0 c : ℕ} (hp0 : p0 < n)
    (hmap : ∀ a, (B a).map (fun l => decide (l.1.loc = x ∧ l.1.op = op)) =
      List.ofFn (fun q : Fin n => decide (q.val = p0)))
    (hpre : (pre.filter (fun l => l.1.loc = x ∧ l.1.op = op)).length = c) :
    (∀ {j : ℕ} {e : Event D}, G.nthEvent t x op (j + c) = some e → j < L.length) ∧
    (∀ {j : ℕ} {a : α}, L[j]? = some a →
      ∃ hP : pre.length + (j * n + p0) < (G.threadEvents t).length,
        G.nthEvent t x op (j + c) = some ((G.threadEvents t)[pre.length + (j * n + p0)]'hP).1) := by
  have hB : ∀ a, (B a).length = n := fun a => by
    simpa using congrArg List.length (hmap a)
  have hpos : ∀ a q l, (B a)[q]? = some l → (l.1.loc = x ∧ l.1.op = op ↔ q = p0) := by
    intro a q l h
    have hq : q < n := hB a ▸ (List.getElem?_eq_some_iff.mp h).1
    have h2 := congrArg (·[q]?) (hmap a)
    simp only [List.getElem?_map, h, Option.map_some, List.getElem?_ofFn, hq, dite_true,
      Option.some.injEq] at h2
    exact decide_eq_decide.mp h2
  let g : α → ThreadLabel D t := fun a => (B a)[p0]'(by rw [hB]; exact hp0)
  have h0 : ∀ a, (B a)[p0]? = some (g a) := fun a => List.getElem?_eq_getElem _
  have htrue : ∀ a, (g a).1.loc = x ∧ (g a).1.op = op := fun a => (hpos a p0 _ (h0 a)).2 rfl
  have hfalse : ∀ a q l, q ≠ p0 → (B a)[q]? = some l → ¬ (l.1.loc = x ∧ l.1.op = op) :=
    fun a q l hq hl h => hq ((hpos a q l hl).1 h)
  have hone : ∀ a, (B a).filter (fun l => l.1.loc = x ∧ l.1.op = op) = [g a] := fun a =>
    list_filter_singleton_of_unique' (B a) _ p0 (g a) (h0 a) (by simpa using htrue a)
      (fun q l hq hl => by simpa using hfalse a q l hq hl)
  refine ⟨fun {j e} he => ?_, fun {j a} ha => ?_⟩
  · obtain ⟨lab, hf, -⟩ := G.exists_filter_of_nthEvent hw he
    have hlt := (List.getElem?_eq_some_iff.mp hf).1
    rw [List.filter_append, List.length_append, hpre, list_filter_flatMap_distrib] at hlt
    simp only [hone] at hlt
    rw [list_flatMap_singleton_eq_map, List.length_map] at hlt
    omega
  · have hget : (pre ++ L.flatMap B)[pre.length + (j * n + p0)]? = some (g a) := by
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        flatMap_uniform_getElem_fwd B n hB L j p0 a ha hp0, h0]
    have hlenw : (G.threadEvents t).length = (pre ++ L.flatMap B).length := by
      have := congrArg List.length (G.threadLabels_eq_of_threadWord hw)
      unfold ExecutionGraph.threadLabels at this
      rwa [List.length_map] at this
    have hP : pre.length + (j * n + p0) < (G.threadEvents t).length := by
      rw [hlenw]; exact (List.getElem?_eq_some_iff.mp hget).1
    refine ⟨hP, G.nthEvent_eq_of_threadWord_pos hw hP hget (htrue a).1 (htrue a).2 ?_⟩
    rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.filter_append, List.length_append, hpre,
      flatMap_uniform_take_count B n hB _ p0 hp0 g h0 (fun a => by simpa using htrue a)
        (fun a q l hq hl => by simpa using hfalse a q l hq hl) L j a ha p0 hp0.le]
    simp only [lt_self_iff_false, if_false, Nat.add_zero]
    omega


/-- `nthEvent_eq_of_threadWord_pos`, with the position bound derived. -/
theorem ExecutionGraph.nthEvent_of_threadWord_pos {t : D.Tid} {w : Word (ThreadLabel D t)}
    (hw : G.threadWord t = w.map some) {x : D.Loc} {op : OpType} {i P : ℕ}
    {lab : ThreadLabel D t} (hlabP : w[P]? = some lab)
    (hloc : lab.1.loc = x) (hop : lab.1.op = op)
    (hcount : ((w.take P).filter (fun l => l.1.loc = x ∧ l.1.op = op)).length = i) :
    ∃ hP : P < (G.threadEvents t).length,
      G.nthEvent t x op i = some ((G.threadEvents t)[P]'hP).1 := by
  have hP : P < (G.threadEvents t).length := by
    have := congrArg List.length (G.threadLabels_eq_of_threadWord hw)
    unfold ExecutionGraph.threadLabels at this
    rw [List.length_map] at this
    rw [this]; exact (List.getElem?_eq_some_iff.mp hlabP).1
  exact ⟨hP, G.nthEvent_eq_of_threadWord_pos hw hP hlabP hloc hop hcount⟩

/-- An indexed event known to sit at position `P` of its thread. -/
theorem ExecutionGraph.eq_of_nthEvent_pos {t : D.Tid} {x : D.Loc} {op : OpType} {i P : ℕ}
    {e : Event D} (he : G.nthEvent t x op i = some e)
    (hpos : ∃ hP : P < (G.threadEvents t).length,
      G.nthEvent t x op i = some ((G.threadEvents t)[P]'hP).1) :
    ∃ hP : P < (G.threadEvents t).length, e = ((G.threadEvents t)[P]'hP).1 := by
  obtain ⟨hP, h⟩ := hpos
  exact ⟨hP, Option.some.inj (he.symm.trans h)⟩

/-- Two events of thread `t` at positions `P1 < P2` of `G.threadEvents t` are
`po`-ordered. -/
theorem ExecutionGraph.po_of_pos {t : D.Tid} {P1 P2 : ℕ} {e1 e2 : Event D}
    (h1 : ∃ hP : P1 < (G.threadEvents t).length, e1 = ((G.threadEvents t)[P1]'hP).1)
    (h2 : ∃ hP : P2 < (G.threadEvents t).length, e2 = ((G.threadEvents t)[P2]'hP).1)
    (hlt : P1 < P2) : G.po e1 e2 := by
  obtain ⟨hP1, rfl⟩ := h1
  obtain ⟨hP2, rfl⟩ := h2
  exact (List.pairwise_iff_getElem.mp (G.threadEvents_pairwise_po t)) P1 P2 hP1 hP2 hlt

end RAUndecidability
