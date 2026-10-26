import RAUndecidability.Reduction.Soundness.Bridge
import RAUndecidability.Reduction.Completeness.Construction
import RAUndecidability.Reduction.ConcProg

/-!
# Per-thread word characterizations (the word characterization of the threads)

For each of the twelve threads: a term-reaching `Command.Run` of the thread
(as obtained from an arbitrary execution by `exists_run_of_induced_reaches`)
emits a word of the closed form given by that thread's `*_shape`/
`*_general_run` theorem (`Completeness/Construction.lean`), for some
resolution of the shape described there. These are the converses of those
theorems.

The proofs go through `Command.runFuel` (`ProgramSemantics/Interpreter.lean`),
which is computable and front-recursive: deterministic steps unfold
mechanically, and only the `NDet` draws (the head of the resolution) need a
case split. Each step is stated as a separate `Command.step` fact and
transported into the running hypothesis with `▸`. Since a `.stuck` result
does not change with more fuel (`Command.runFuel_stuck_stable`), the fuel
can be padded to whatever each step lemma requires.
-/

namespace RAUndecidability

/-! ## `PrimeCheckX` -/

/-- The converse of `primeCheckX_iter_step`: a run that takes one more full
iteration of `primeCheckXLoop` (within a continuation `.seq _ C2`) consumes a
`Bool` `v` as the head of `s`, emits the six-event block, and returns to
`primeCheckXLoop` with `cnt` advanced and `b` set to `v`. -/
theorem primeCheckX_iter_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (PrimeCheckX.Vocab I))
    (s : List PrimeCheckX.Vals) (φ : (PrimeCheckX.Vocab I).Store)
    (hb : φ PrimeCheckX.Vars.b = Sum.inr true) (cnt0 : Fin 4)
    (hcnt0 : φ PrimeCheckX.Vars.cnt = Sum.inl cnt0) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeCheckX)) (φ' : (PrimeCheckX.Vocab I).Store)
    (h : Command.runFuel Tid.primeCheckX ((primeCheckXLoop I).seq C2, φ) s (N + 17) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v : Bool) (rest : List PrimeCheckX.Vals)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.primeCheckX)),
      s = Sum.inr v :: rest ∧
      σ = [ ⟨EventLabel.wt Tid.primeCheckX Loc.xA' (Val.primeTag Tid.primeCheckX (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.wt Tid.primeCheckX Loc.xB' (Val.primeTag Tid.primeCheckX (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.primeCheckX Loc.xA' (Val.primeTag Tid.primeAX 0), rfl⟩
          , ⟨EventLabel.rd Tid.primeCheckX Loc.xB' (Val.primeTag Tid.primeBX 0), rfl⟩
          , ⟨EventLabel.rd Tid.primeCheckX Loc.xA
              (Val.primeTag Tid.checkX (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.primeCheckX Loc.xB
              (Val.primeTag Tid.checkX (cnt0 + 1)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.primeCheckX
        ((primeCheckXLoop I).seq C2,
          Function.update (Function.update φ PrimeCheckX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeCheckX.Vars.b (Sum.inr v)) rest N =
        (.stuck, σ1, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeCheckXLoop, PrimeCheckX.Vocab,
    PrimeCheckX.evalB, hb, if_true, PrimeCheckX.evalV, primeCheckXLoopBody, PrimeCheckX.body,
    hcnt0, PrimeCheckX.cntOf, PrimeCheckX.eval, Prod.mk.injEq] at h
  cases s with
  | nil =>
      simp only [Command.step] at h
      exact absurd h.2.2.1 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.step, PrimeCheckX.X, Finset.mem_insert, Finset.mem_singleton] at h
      split_ifs at h with hc
      · obtain ⟨v, rfl⟩ : ∃ v : Bool, c = Sum.inr v := by
          rcases hc with rfl | rfl
          · exact ⟨false, rfl⟩
          · exact ⟨true, rfl⟩
        simp only [Command.step] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨v, rest, _, rfl, h2.symm, ?_⟩
        change Command.runFuel Tid.primeCheckX
            ((Command.whileLoop PrimeCheckX.BExpr.isB
                (((Command.assign PrimeCheckX.Vars.cnt PrimeCheckX.Expr.nextCnt).seq
                      ((Command.write Loc.xA' PrimeCheckX.VExpr.cntTagVal).seq
                        ((Command.write Loc.xB' PrimeCheckX.VExpr.cntTagVal).seq
                          ((Command.read Loc.xA' PrimeCheckX.VExpr.xApExpect).seq
                            ((Command.read Loc.xB' PrimeCheckX.VExpr.xBpExpect).seq
                              ((Command.read Loc.xA PrimeCheckX.VExpr.checkExpect).seq
                                (Command.read Loc.xB PrimeCheckX.VExpr.checkExpect))))))).seq
                  (Command.ndetAssign PrimeCheckX.Vars.b PrimeCheckX.X
                    PrimeCheckX.X_nonempty))).seq C2,
              Function.update (Function.update φ PrimeCheckX.Vars.cnt (Sum.inl (cnt0 + 1)))
                PrimeCheckX.Vars.b (Sum.inr v)) rest N = _
        exact Prod.ext h1 (Prod.ext rfl (Prod.ext h3 h4))
      · exact absurd h.2.2.1 (by rintro ⟨⟩)

/-- One `Command.step` of `PrimeCheckX.program`'s leading `NDet({⊥,⊤})` draw,
against the empty resolution (by `rfl`). -/
theorem primeCheckX_lead_hstep_nil (I : PCPInstance) :
    Command.step Tid.primeCheckX (PrimeCheckX.program I)
      ((PrimeCheckX.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      ([] : List PrimeCheckX.Vals) = none := rfl

/-- One `Command.step` of `PrimeCheckX.program`'s leading draw, against a
resolution whose head `Sum.inl k` is not in `PrimeCheckX.X`. -/
theorem primeCheckX_lead_hstep_inl (I : PCPInstance) (k : Fin 4)
    (rest : List PrimeCheckX.Vals) :
    Command.step Tid.primeCheckX (PrimeCheckX.program I)
      ((PrimeCheckX.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      (Sum.inl k :: rest) = none := rfl

/-- The converse of `PrimeCheckX.program`'s leading `NDet({⊥,⊤})` draw: a run
consuming at least one more step draws a `Bool` `b0` as the head of `s` and
reaches `(primeCheckXLoop I).seq Command.term` with `b` set to `b0`. -/
theorem primeCheckX_lead_step_inv (I : PCPInstance) (s : List PrimeCheckX.Vals) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeCheckX)) (φ' : (PrimeCheckX.Vocab I).Store)
    (h : Command.runFuel Tid.primeCheckX (PrimeCheckX.program I, (PrimeCheckX.Vocab I).mkStore
      (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0)) s
      (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (b0 : Bool) (rest : List PrimeCheckX.Vals),
      s = Sum.inr b0 :: rest ∧
      Command.runFuel Tid.primeCheckX
        ((primeCheckXLoop I).seq Command.term,
          Function.update ((PrimeCheckX.Vocab I).mkStore
            (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
            PrimeCheckX.Vars.b (Sum.inr b0)) rest N = (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel] at h
      have h2 := primeCheckX_lead_hstep_nil I ▸ h
      dsimp only at h2
      have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
      exact absurd h3 (by rintro ⟨⟩)
  | cons c rest =>
      rcases c with k | b0
      · simp only [Command.runFuel] at h
        have h2 := primeCheckX_lead_hstep_inl I k rest ▸ h
        dsimp only at h2
        have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
        exact absurd h3 (by rintro ⟨⟩)
      · rcases b0 with rfl | rfl
        · simp only [Command.runFuel] at h
          exact ⟨false, rest, rfl, h⟩
        · simp only [Command.runFuel] at h
          exact ⟨true, rest, rfl, h⟩

/-- The converse of `primeCheckX_stop_step`: with the guard false
(`φ.b = ⊥`), the next two steps are silent and reach `(C2, φ)`. -/
theorem primeCheckX_stop_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (PrimeCheckX.Vocab I)) (s : List PrimeCheckX.Vals)
    (φ : (PrimeCheckX.Vocab I).Store) (hb : φ PrimeCheckX.Vars.b = Sum.inr false) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeCheckX)) (φ' : (PrimeCheckX.Vocab I).Store)
    (h : Command.runFuel Tid.primeCheckX ((primeCheckXLoop I).seq C2, φ) s (N + 2) =
      (.stuck, σ, (Command.term, φ'), [])) :
    Command.runFuel Tid.primeCheckX (C2, φ) s N = (.stuck, σ, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeCheckXLoop, PrimeCheckX.Vocab,
    PrimeCheckX.evalB, hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))

/-- The converse of `primeCheckX_shape`: a run entering `primeCheckXLoop`
(`φ.b = ⊤`, `φ.cnt = cnt0`) and reaching `(Command.term, φ')` draws `M'`
continues and then one stop, and emits `M' + 1` six-event blocks. By strong
induction on `s.length`. -/
theorem primeCheckX_loop_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List PrimeCheckX.Vals), s.length = n →
      ∀ (φ : (PrimeCheckX.Vocab I).Store) (cnt0 : Fin 4)
        (_hb : φ PrimeCheckX.Vars.b = Sum.inr true)
        (_hcnt0 : φ PrimeCheckX.Vars.cnt = Sum.inl cnt0)
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.primeCheckX))
        (φ' : (PrimeCheckX.Vocab I).Store),
        Command.runFuel Tid.primeCheckX ((primeCheckXLoop I).seq Command.term, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (M' : ℕ) (cnts : List (Fin 4)),
          s = List.replicate M' (Sum.inr true) ++ [Sum.inr false] ∧
          cnts.length = M' + 1 ∧
          (∀ i, i < cnts.length →
            cnts[i]? = some (⟨(cnt0.val + i + 1) % 4, by omega⟩ : Fin 4)) ∧
          σ = primeCheckXBlockWord I cnts := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen φ cnt0 hb hcnt0 N σ φ' h
    have h17 := Command.runFuel_stuck_stable h 17
    obtain ⟨v, rest, σ1, hseq, hσeq, h2⟩ :=
      primeCheckX_iter_step_inv I Command.term s φ hb cnt0 hcnt0 N σ φ' h17
    subst hseq
    cases v with
    | false =>
        have h2' := Command.runFuel_stuck_stable h2 2
        have hbf : Function.update (Function.update φ PrimeCheckX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeCheckX.Vars.b (Sum.inr false) PrimeCheckX.Vars.b = Sum.inr false :=
          Function.update_self _ _ _
        have h3 := primeCheckX_stop_step_inv I Command.term rest _ hbf N σ1 φ' h2'
        have hrest : rest = [] ∧ σ1 = ([] : Word (ThreadLabel (domainOf I) Tid.primeCheckX)) := by
          rcases N with _ | N'
          · simp only [Command.runFuel] at h3
            exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
          · simp only [Command.runFuel, Command.step] at h3
            refine ⟨?_, ?_⟩
            · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
            · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
        obtain ⟨hrest0, hσ10⟩ := hrest
        subst hrest0
        refine ⟨0, [cnt0 + 1], rfl, rfl, ?_, ?_⟩
        · intro i hi
          have hi0 : i = 0 := by simpa using hi
          subst hi0
          simp only [List.getElem?_cons_zero, Option.some.injEq]
          apply Fin.ext
          simp [Fin.add_def]
        · simp only [hσeq, hσ10, List.append_nil, primeCheckXBlockWord, List.flatMap_cons,
            List.flatMap_nil, List.append_nil]
    | true =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inr true :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        have hbnew : Function.update (Function.update φ PrimeCheckX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeCheckX.Vars.b (Sum.inr true) PrimeCheckX.Vars.b = Sum.inr true :=
          Function.update_self _ _ _
        have hne_cntb : PrimeCheckX.Vars.cnt ≠ PrimeCheckX.Vars.b := by decide
        have hcntnew :
            Function.update (Function.update φ PrimeCheckX.Vars.cnt (Sum.inl (cnt0 + 1)))
              PrimeCheckX.Vars.b (Sum.inr true) PrimeCheckX.Vars.cnt = Sum.inl (cnt0 + 1) :=
          (Function.update_of_ne hne_cntb (Sum.inr true) _).trans (Function.update_self _ _ _)
        obtain ⟨M'', cnts'', hrest_eq, hcnts_len, hcnts_val, hσ1⟩ :=
          ih rest.length hrest_len rest rfl
            (Function.update (Function.update φ PrimeCheckX.Vars.cnt (Sum.inl (cnt0 + 1)))
              PrimeCheckX.Vars.b (Sum.inr true))
            (cnt0 + 1) hbnew hcntnew N σ1 φ' h2
        refine ⟨M'' + 1, (cnt0 + 1) :: cnts'', ?_, ?_, ?_, ?_⟩
        · rw [hrest_eq, List.replicate_succ, List.cons_append]
        · simp [hcnts_len]
        · intro i hi
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq]
              apply Fin.ext
              simp [Fin.add_def]
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < cnts''.length := by omega
              have hval' := hcnts_val i hi'
              simp only [List.getElem?_cons_succ]
              rw [hval']
              congr 1
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · rw [hσeq, hσ1]
          simp only [primeCheckXBlockWord, List.flatMap_cons]

/-- **The word characterization of the threads, `PrimeCheckX`.** The converse of
`primeCheckX_general_run`: a term-reaching run of `PrimeCheckX.program` from
its initial store draws `M` times `⊤` and then `⊥`, and its word is
`primeCheckXBlockWord` of the `M` iteration counters. -/
theorem primeCheckX_shape_inv (I : PCPInstance) {s : List PrimeCheckX.Vals}
    {φ' : (PrimeCheckX.Vocab I).Store} {cLast : Config (domainOf I) (PrimeCheckX.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.primeCheckX)}
    (hrun : Command.Run Tid.primeCheckX s
      (PrimeCheckX.program I, (PrimeCheckX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      σ cLast [] (Command.term, φ')) :
    ∃ (M : ℕ) (cnts : List (Fin 4)),
      s = List.replicate M (Sum.inr true) ++ [Sum.inr false] ∧
      cnts.length = M ∧
      (∀ i, i < cnts.length → cnts[i]? = some (⟨(i + 1) % 4, by omega⟩ : Fin 4)) ∧
      σ = primeCheckXBlockWord I cnts := by
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨b0, rest, hs, h2⟩ := primeCheckX_lead_step_inv I s n σ φ' hn2
  cases b0 with
  | false =>
      have hbf : Function.update ((PrimeCheckX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeCheckX.Vars.b (Sum.inr false) PrimeCheckX.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h2' := Command.runFuel_stuck_stable h2 2
      have h3 := primeCheckX_stop_step_inv I Command.term rest _ hbf n σ φ' h2'
      have hrest : rest = [] ∧ σ = ([] : Word (ThreadLabel (domainOf I) Tid.primeCheckX)) := by
        rcases n with _ | n'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ0⟩ := hrest
      refine ⟨0, [], ?_, rfl, ?_, ?_⟩
      · simp [hs, hrest0]
      · intro i hi; simp at hi
      · simp [hσ0, primeCheckXBlockWord]
  | true =>
      have hb2 : Function.update ((PrimeCheckX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeCheckX.Vars.b (Sum.inr true) PrimeCheckX.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hcnt2 : Function.update ((PrimeCheckX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeCheckX.Vars.b (Sum.inr true) PrimeCheckX.Vars.cnt = Sum.inl (0 : Fin 4) := by
        have hne : PrimeCheckX.Vars.cnt ≠ PrimeCheckX.Vars.b := by decide
        exact Function.update_of_ne hne _ _
      obtain ⟨M', cnts, hrest_eq, hcnts_len, hcnts_val, hσeq⟩ :=
        primeCheckX_loop_shape_inv I rest.length rest rfl _ 0 hb2 hcnt2 n σ φ' h2
      refine ⟨M' + 1, cnts, ?_, ?_, ?_, hσeq⟩
      · rw [hs, hrest_eq, List.replicate_succ, List.cons_append]
      · omega
      · intro i hi
        have := hcnts_val i hi
        simpa using this

/-! ## `CheckX` -/

/-- `c ∈ CheckX.auxSet I` iff `c = Sum.inl (some v)` for some `v`. -/
theorem CheckX.mem_auxSet_iff {I : PCPInstance} (c : CheckX.Vals I) :
    c ∈ CheckX.auxSet I ↔ ∃ v, c = Sum.inl (some v) := by
  unfold CheckX.auxSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv.symm⟩, fun ⟨v, hv⟩ => ⟨v, hv.symm⟩⟩

/-- The converse of `CheckX.program`'s leading `NDet(Γ)` draw: a run consuming
at least two more steps draws some `v0 : I.Γ` as the head of `s`. -/
theorem checkX_lead_step_inv (I : PCPInstance) (s : List (CheckX.Vals I)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.checkX)) (φ' : (CheckX.Vocab I).Store)
    (h : Command.runFuel Tid.checkX (CheckX.program I,
      (CheckX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none)) s (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v0 : I.Γ) (rest : List (CheckX.Vals I)),
      s = Sum.inl (some v0) :: rest ∧
      Command.runFuel Tid.checkX
        ((checkXLoop I).seq Command.term,
          Function.update ((CheckX.Vocab I).mkStore (fun v => match v with
            | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
            | .fst => some (Sum.inr (Sum.inr true))
            | _ => none) (Sum.inl none)) CheckX.Vars.aux (Sum.inl (some v0))) rest N =
        (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel, Command.step, CheckX.program] at h
      have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
      exact absurd h2 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.runFuel, Command.step, CheckX.program] at h
      split_ifs at h with hc
      · obtain ⟨v0, rfl⟩ := (CheckX.mem_auxSet_iff c).mp hc
        simp only [Command.step, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨v0, rest, rfl, ?_⟩
        change Command.runFuel Tid.checkX
            ((Command.whileLoop CheckX.BExpr.tt (CheckX.body I)).seq Command.term,
              Function.update ((CheckX.Vocab I).mkStore (fun v => match v with
                | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
                | .fst => some (Sum.inr (Sum.inr true))
                | _ => none) (Sum.inl none)) CheckX.Vars.aux (Sum.inl (some v0))) rest N = _
        exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
      · have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
        exact absurd h2 (by rintro ⟨⟩)

/-- `c ∈ CheckX.auxSetBot I` iff `c = Sum.inl w` for some
`w : Option I.Γ`. -/
theorem CheckX.mem_auxSetBot_iff {I : PCPInstance} (c : CheckX.Vals I) :
    c ∈ CheckX.auxSetBot I ↔ ∃ w : Option I.Γ, c = Sum.inl w := by
  unfold CheckX.auxSetBot
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, hw.symm⟩, fun ⟨w, hw⟩ => ⟨w, hw.symm⟩⟩

/-- The converse of `checkX_block0_step`: a run taking at least 20 more steps
from a store with `fst = true`, `cnt = 0`, `aux = some v0` emits
`checkXBlock0Elems I v0`, consumes some `Sum.inl w` as the head of `s`, and
returns to `checkXLoop` with `fst = false`, `cnt = 1`, `aux = Sum.inl w`.
Each of the 20 steps is a separate `Command.step` fact (`hs1`–`hs20`). -/
theorem checkX_block0_step_inv (I : PCPInstance) (C2 : Command (domainOf I) (CheckX.Vocab I))
    (s : List (CheckX.Vals I)) (φ : (CheckX.Vocab I).Store)
    (hfst : φ CheckX.Vars.fst = Sum.inr (Sum.inr true))
    (hcnt0 : φ CheckX.Vars.cnt = Sum.inr (Sum.inl 0))
    (v0 : I.Γ) (haux0 : φ CheckX.Vars.aux = Sum.inl (some v0)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.checkX)) (φ' : (CheckX.Vocab I).Store)
    (h : Command.runFuel Tid.checkX ((checkXLoop I).seq C2, φ) s (N + 20) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (w : Option I.Γ) (rest : List (CheckX.Vals I))
      (σ1 : Word (ThreadLabel (domainOf I) Tid.checkX)),
      s = Sum.inl w :: rest ∧
      σ = checkXBlock0Elems I v0 ++ σ1 ∧
      ∃ (φ3 : (CheckX.Vocab I).Store),
        φ3 CheckX.Vars.fst = Sum.inr (Sum.inr false) ∧
        φ3 CheckX.Vars.cnt = Sum.inr (Sum.inl 1) ∧
        φ3 CheckX.Vars.aux = Sum.inl w ∧
        Command.runFuel Tid.checkX ((checkXLoop I).seq C2, φ3) rest N =
          (.stuck, σ1, (Command.term, φ'), []) := by
  set φ1 : (CheckX.Vocab I).Store :=
    Function.update φ CheckX.Vars.prev (CheckX.eval I CheckX.Expr.readCnt φ) with hφ1
  set φ2 : (CheckX.Vocab I).Store :=
    Function.update φ1 CheckX.Vars.cnt (CheckX.eval I CheckX.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 CheckX.Vars.cnt = φ CheckX.Vars.cnt := rfl
  have hcnt2eq : φ2 CheckX.Vars.cnt = CheckX.eval I CheckX.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2 : CheckX.cntOf I φ2 = 1 := by
    simp only [CheckX.cntOf, hcnt2eq, CheckX.eval, hcnt_φ1, hcnt0]
    decide
  have hne_aux_cnt : CheckX.Vars.aux ≠ CheckX.Vars.cnt := by decide
  have haux_φ1 : φ1 CheckX.Vars.aux = φ CheckX.Vars.aux := rfl
  have haux2 : φ2 CheckX.Vars.aux = Sum.inl (some v0) := by
    have h1' : φ2 CheckX.Vars.aux = φ1 CheckX.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    rw [h1', haux_φ1, haux0]
  have hcnt1val : (CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2
      = Val.primeTag Tid.checkX 1 := by
    simp only [CheckX.Vocab, CheckX.evalV, hcnt2]
    rfl
  have hne_fst_cnt : CheckX.Vars.fst ≠ CheckX.Vars.cnt := by decide
  have hfst_φ1 : φ1 CheckX.Vars.fst = φ CheckX.Vars.fst := rfl
  have hfst2 : φ2 CheckX.Vars.fst = Sum.inr (Sum.inr true) := by
    have h1' : φ2 CheckX.Vars.fst = φ1 CheckX.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1', hfst_φ1, hfst]
  set φ3 : (CheckX.Vocab I).Store :=
    Function.update φ2 CheckX.Vars.fst (CheckX.eval I CheckX.Expr.fstFalse φ2) with hφ3
  have hne_aux_fst : CheckX.Vars.aux ≠ CheckX.Vars.fst := by decide
  have haux3 : φ3 CheckX.Vars.aux = Sum.inl (some v0) := by
    have h1' : φ3 CheckX.Vars.aux = φ2 CheckX.Vars.aux := Function.update_of_ne hne_aux_fst _ _
    rw [h1', haux2]
  have hxAFirst : (CheckX.Vocab I).evalV CheckX.VExpr.xAFirst φ3
      = Val.xTag (Tid.guessAX, true) (some v0) := by
    simp only [CheckX.Vocab, CheckX.evalV, CheckX.auxOf, haux3]
    rfl
  have hxBFirst : (CheckX.Vocab I).evalV CheckX.VExpr.xBFirst φ3
      = Val.xTag (Tid.guessBX, true) (some v0) := by
    simp only [CheckX.Vocab, CheckX.evalV, CheckX.auxOf, haux3]
    rfl
  have hisBot3 : CheckX.evalB I CheckX.BExpr.isBot φ3 = false := by
    simp only [CheckX.evalB]
    cases hφ : φ3 CheckX.Vars.aux with
    | inl w => cases w with
        | none => rw [haux3] at hφ; injection hφ with hφ2; injection hφ2
        | some _ => simp
    | inr w => simp
  have hcnt2raw : φ2 CheckX.Vars.cnt = Sum.inr (Sum.inl 1) := by
    simp only [hcnt2eq, CheckX.eval, CheckX.cntOf, hcnt_φ1, hcnt0]
    rfl
  have hcnt3 : φ3 CheckX.Vars.cnt = Sum.inr (Sum.inl 1) :=
    (Function.update_of_ne hne_fst_cnt.symm _ _).trans hcnt2raw
  have hfst3 : φ3 CheckX.Vars.fst = Sum.inr (Sum.inr false) := Function.update_self _ _ _
  -- Step 1: unwrap the loop guard (constant `tt`).
  have hs1 : Command.step Tid.checkX (checkXLoop I) φ s =
      some (none, Command.loopSeq (CheckX.body I) (checkXLoop I), φ, s) := by
    simp only [checkXLoop, Command.step, CheckX.Vocab, CheckX.evalB, if_true]
  -- Step 2: `prev ← readCnt`.
  have hs2 : Command.step Tid.checkX (Command.loopSeq (CheckX.body I) (checkXLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I))))))
        (checkXLoop I), φ1, s) := by
    change Command.step Tid.checkX (Command.loopSeq (CheckX.body I) (checkXLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I))))))
        (checkXLoop I),
        Function.update φ CheckX.Vars.prev (CheckX.eval I CheckX.Expr.readCnt φ), s)
    simp only [CheckX.body, Command.step, CheckX.Vocab]
    rfl
  -- Step 3: `.seq Command.skip _` elimination.
  have hs3 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 4: `cnt ← nextCnt`.
  have hs4 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ2, s) := by
    change Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I),
        Function.update φ1 CheckX.Vars.cnt (CheckX.eval I CheckX.Expr.nextCnt φ1), s)
    simp only [Command.step, CheckX.Vocab]
    rfl
  -- Step 5: `.seq Command.skip _` elimination (before writing `xA`).
  have hs5 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 6: `w(xA, cntTagVal)`.
  have hs6 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I))))
      (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkX Loc.xA
        ((CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab]
  -- Step 7: `.seq Command.skip _` elimination (before writing `xB`).
  have hs7 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
        (Command.seq (checkXIteFirst I) (checkXTail I))))
      (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 8: `w(xB, cntTagVal)`.
  have hs8 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
        (Command.seq (checkXIteFirst I) (checkXTail I)))
      (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkX Loc.xB
        ((CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab]
  -- Step 9: `.seq Command.skip _` elimination (before `Command.firstIt`'s guard).
  have hs9 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkXIteFirst I) (checkXTail I)) (checkXLoop I),
        φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 10: `Command.firstIt`'s guard, resolved true via `hfst2`.
  have hs10 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (checkXIteFirst I) (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkXFirstBranch I) (checkXTail I))
        (checkXLoop I), φ2, s) := by
    simp only [checkXIteFirst, Command.step, CheckX.Vocab, CheckX.evalB, hfst2, if_true]
  -- Step 11: `fst ← False`, entering `checkXFirstBranch`.
  have hs11 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (checkXFirstBranch I) (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst))) (checkXTail I)) (checkXLoop I),
        φ3, s) := by
    change Command.step Tid.checkX
      (Command.loopSeq (Command.seq (checkXFirstBranch I) (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst))) (checkXTail I)) (checkXLoop I),
        Function.update φ2 CheckX.Vars.fst (CheckX.eval I CheckX.Expr.fstFalse φ2), s)
    simp only [checkXFirstBranch, Command.step, CheckX.Vocab]
    rfl
  -- Step 12: `.seq Command.skip _` elimination (before reading `xA`).
  have hs12 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst))) (checkXTail I)) (checkXLoop I)) φ3 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst)) (checkXTail I)) (checkXLoop I),
        φ3, s) := by
    simp only [Command.step]
    rfl
  -- Step 13: `r(xA, xAFirst)`.
  have hs13 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst)) (checkXTail I)) (checkXLoop I)) φ3 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xA
        ((CheckX.Vocab I).evalV CheckX.VExpr.xAFirst φ3), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.read Loc.xB CheckX.VExpr.xBFirst)) (checkXTail I)) (checkXLoop I),
        φ3, s) := by
    simp only [Command.step, CheckX.Vocab]
  -- Step 14: `.seq Command.skip _` elimination (before reading `xB`).
  have hs14 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.xB CheckX.VExpr.xBFirst)) (checkXTail I)) (checkXLoop I)) φ3 s =
      some (none, Command.loopSeq (Command.seq (Command.read Loc.xB CheckX.VExpr.xBFirst)
        (checkXTail I)) (checkXLoop I), φ3, s) := by
    simp only [Command.step]
    rfl
  -- Step 15: `r(xB, xBFirst)`.
  have hs15 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.read Loc.xB CheckX.VExpr.xBFirst) (checkXTail I))
        (checkXLoop I)) φ3 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xB
        ((CheckX.Vocab I).evalV CheckX.VExpr.xBFirst φ3), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (checkXTail I)) (checkXLoop I), φ3, s) := by
    simp only [Command.step, CheckX.Vocab]
  -- Step 16: `.seq Command.skip _` elimination (before `checkXTail`).
  have hs16 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq Command.skip (checkXTail I)) (checkXLoop I)) φ3 s =
      some (none, Command.loopSeq (checkXTail I) (checkXLoop I), φ3, s) := by
    simp only [Command.step]
    rfl
  -- Step 17: `if aux = ⊥ then break endif` resolves false, via `hisBot3`.
  have hs17 : Command.step Tid.checkX (Command.loopSeq (checkXTail I) (checkXLoop I)) φ3 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I)))
        (checkXLoop I), φ3, s) := by
    simp only [checkXTail, Command.step, CheckX.Vocab, hisBot3, Bool.false_eq_true, if_false]
  -- Step 18: `.seq Command.skip _` elimination (before the trailing `NDet` draw).
  have hs18 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I)))
      (checkXLoop I)) φ3 s =
      some (none, Command.loopSeq
        (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I))
        (checkXLoop I), φ3, s) := by
    simp only [Command.step]
    rfl
  -- Transport steps 1-18 (which do not depend on the resolution) into `h`,
  -- one at a time.
  have hrs1 : Command.RunStep Tid.checkX s none (checkXLoop I, φ) s
      (Command.loopSeq (CheckX.body I) (checkXLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (CheckX.body I) (checkXLoop I), φ) s
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I))))))
        (checkXLoop I), φ1) := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I))))))
        (checkXLoop I), φ1) s
      (Command.loopSeq
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ1) := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 : Command.RunStep Tid.checkX s none
      (Command.loopSeq
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ1) s
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ2) s
      (Command.loopSeq
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 : Command.RunStep Tid.checkX s
      (some ⟨EventLabel.wt Tid.checkX Loc.xA
        ((CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2) s
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2) s
      (Command.loopSeq
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 : Command.RunStep Tid.checkX s
      (some ⟨EventLabel.wt Tid.checkX Loc.xB
        ((CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2) s
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2) s
      (Command.loopSeq (Command.seq (checkXIteFirst I) (checkXTail I)) (checkXLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq (checkXIteFirst I) (checkXTail I)) (checkXLoop I), φ2) s
      (Command.loopSeq (Command.seq (checkXFirstBranch I) (checkXTail I)) (checkXLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq (checkXFirstBranch I) (checkXTail I)) (checkXLoop I), φ2) s
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst))) (checkXTail I)) (checkXLoop I),
        φ3) := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst))) (checkXTail I)) (checkXLoop I), φ3) s
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst)) (checkXTail I)) (checkXLoop I),
        φ3) := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 : Command.RunStep Tid.checkX s
      (some ⟨EventLabel.rd Tid.checkX Loc.xA
        ((CheckX.Vocab I).evalV CheckX.VExpr.xAFirst φ3), rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xA CheckX.VExpr.xAFirst)
          (Command.read Loc.xB CheckX.VExpr.xBFirst)) (checkXTail I)) (checkXLoop I), φ3) s
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.xB CheckX.VExpr.xBFirst)) (checkXTail I)) (checkXLoop I),
        φ3) := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.xB CheckX.VExpr.xBFirst)) (checkXTail I)) (checkXLoop I), φ3) s
      (Command.loopSeq (Command.seq (Command.read Loc.xB CheckX.VExpr.xBFirst)
        (checkXTail I)) (checkXLoop I), φ3) := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 : Command.RunStep Tid.checkX s
      (some ⟨EventLabel.rd Tid.checkX Loc.xB
        ((CheckX.Vocab I).evalV CheckX.VExpr.xBFirst φ3), rfl⟩)
      (Command.loopSeq (Command.seq (Command.read Loc.xB CheckX.VExpr.xBFirst) (checkXTail I))
        (checkXLoop I), φ3) s
      (Command.loopSeq (Command.seq Command.skip (checkXTail I)) (checkXLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq Command.skip (checkXTail I)) (checkXLoop I), φ3) s
      (Command.loopSeq (checkXTail I) (checkXLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (checkXTail I) (checkXLoop I), φ3) s
      (Command.loopSeq (Command.seq Command.skip
        (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I)))
        (checkXLoop I), φ3) := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 : Command.RunStep Tid.checkX s none
      (Command.loopSeq (Command.seq Command.skip
        (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I)))
        (checkXLoop I), φ3) s
      (Command.loopSeq
        (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I))
        (checkXLoop I), φ3) := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  cases s with
  | nil =>
      have hnone : Command.step Tid.checkX
          ((Command.loopSeq (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I)
            (CheckX.auxSetBot_nonempty I)) (checkXLoop I)).seq C2) φ3 [] = none :=
        Command.step_seq_loopSeq_ndetAssign_nil _ _ _ _ _ _
      have h' := hnone ▸ h
      injection h' with _ h2
      injection h2 with _ h4
      injection h4 with h5 _
      exact absurd h5 (by rintro ⟨⟩)
  | cons c rest =>
      rcases Classical.em (c ∈ CheckX.auxSetBot I) with hc | hc
      · obtain ⟨w, rfl⟩ := (CheckX.mem_auxSetBot_iff c).mp hc
        have hcpos := Command.step_ndetAssign_cons_pos (t := Tid.checkX) CheckX.Vars.aux
          (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I) φ3 (Sum.inl w) rest hc
        have hrs19a : Command.RunStep Tid.checkX (Sum.inl w :: rest) none
            (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I)
              (CheckX.auxSetBot_nonempty I), φ3) rest
            (Command.skip, Function.update φ3 CheckX.Vars.aux (Sum.inl w)) :=
          Command.step_sound _ _ _ _ _ _ _ hcpos
        have hrs19 := Command.RunStep.loopCongr (C2 := checkXLoop I) hrs19a
        have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
        have h := hw19 ▸ h
        dsimp only at h
        have hrs20 : Command.RunStep Tid.checkX rest none
            (Command.loopSeq Command.skip (checkXLoop I),
              Function.update φ3 CheckX.Vars.aux (Sum.inl w)) rest
            (checkXLoop I, Function.update φ3 CheckX.Vars.aux (Sum.inl w)) :=
          Command.RunStep.loopSkip
        have hw20 : Command.step Tid.checkX
            ((Command.loopSeq Command.skip (checkXLoop I)).seq C2)
            (Function.update φ3 CheckX.Vars.aux (Sum.inl w)) rest =
            some (none, (checkXLoop I).seq C2,
              Function.update φ3 CheckX.Vars.aux (Sum.inl w), rest) :=
          Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs20)
        have h := hw20 ▸ h
        have hne_fst_aux2 : CheckX.Vars.fst ≠ CheckX.Vars.aux := by decide
        have hne_cnt_aux2 : CheckX.Vars.cnt ≠ CheckX.Vars.aux := by decide
        rw [hcnt1val, hxAFirst, hxBFirst] at h
        injection h with hh1 hrest1
        injection hrest1 with hh2 hrest2
        injection hrest2 with hh3 hh4
        refine ⟨w, rest,
          (Command.runFuel Tid.checkX ((checkXLoop I).seq C2,
            Function.update φ3 CheckX.Vars.aux (Sum.inl w)) rest N).2.1,
          rfl, hh2.symm, Function.update φ3 CheckX.Vars.aux (Sum.inl w),
          (Function.update_of_ne hne_fst_aux2 (Sum.inl w) φ3).trans hfst3,
          (Function.update_of_ne hne_cnt_aux2 (Sum.inl w) φ3).trans hcnt3,
          Function.update_self _ _ _, Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩
      · exfalso
        have hs19' : Command.step Tid.checkX
            ((Command.loopSeq
              (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I)
                (CheckX.auxSetBot_nonempty I)) (checkXLoop I)).seq C2) φ3 (c :: rest) = none :=
          Command.step_seq_loopSeq_ndetAssign_cons_neg (t := Tid.checkX) CheckX.Vars.aux
            (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I) φ3 (checkXLoop I) C2 c rest hc
        have h' := hs19' ▸ h
        injection h' with _ h2
        injection h2 with _ h4
        injection h4 with h5 _
        exact absurd h5 (by rintro ⟨⟩)

/-- The converse of `checkX_blockRest_continue_step`: a run taking at least
22 more steps from a store with `fst = false`, `cnt = k`, `aux = some w` emits
`checkXBlockRestElems I (k, some w)`, consumes some `Sum.inl w'` as the head
of `s`, and returns to `checkXLoop` with `cnt = k + 1`, `aux = Sum.inl w'`. -/
theorem checkX_blockRest_continue_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (CheckX.Vocab I))
    (s : List (CheckX.Vals I)) (φ : (CheckX.Vocab I).Store)
    (hfst : φ CheckX.Vars.fst = Sum.inr (Sum.inr false)) (k : Fin 4)
    (hcnt0 : φ CheckX.Vars.cnt = Sum.inr (Sum.inl k))
    (w : I.Γ) (haux0 : φ CheckX.Vars.aux = Sum.inl (some w)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.checkX)) (φ' : (CheckX.Vocab I).Store)
    (h : Command.runFuel Tid.checkX ((checkXLoop I).seq C2, φ) s (N + 22) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (w' : Option I.Γ) (rest : List (CheckX.Vals I))
      (σ1 : Word (ThreadLabel (domainOf I) Tid.checkX)),
      s = Sum.inl w' :: rest ∧
      σ = checkXBlockRestElems I (k, some w) ++ σ1 ∧
      ∃ (φ2u : (CheckX.Vocab I).Store),
        φ2u CheckX.Vars.fst = Sum.inr (Sum.inr false) ∧
        φ2u CheckX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
        φ2u CheckX.Vars.aux = Sum.inl w' ∧
        Command.runFuel Tid.checkX ((checkXLoop I).seq C2, φ2u) rest N =
          (.stuck, σ1, (Command.term, φ'), []) := by
  set φ1 : (CheckX.Vocab I).Store :=
    Function.update φ CheckX.Vars.prev (CheckX.eval I CheckX.Expr.readCnt φ) with hφ1
  set φ2 : (CheckX.Vocab I).Store :=
    Function.update φ1 CheckX.Vars.cnt (CheckX.eval I CheckX.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 CheckX.Vars.cnt = φ CheckX.Vars.cnt := rfl
  have hcnt2eq : φ2 CheckX.Vars.cnt = CheckX.eval I CheckX.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2raw : φ2 CheckX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt2eq, CheckX.eval, CheckX.cntOf, hcnt_φ1, hcnt0]
    rfl
  have hcnt2 : CheckX.cntOf I φ2 = k + 1 := by simp only [CheckX.cntOf, hcnt2raw]
  have hne_aux_cnt : CheckX.Vars.aux ≠ CheckX.Vars.cnt := by decide
  have haux_φ1 : φ1 CheckX.Vars.aux = φ CheckX.Vars.aux := rfl
  have haux2 : φ2 CheckX.Vars.aux = Sum.inl (some w) := by
    have h1' : φ2 CheckX.Vars.aux = φ1 CheckX.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    rw [h1', haux_φ1, haux0]
  have hcnt1val : (CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2
      = Val.primeTag Tid.checkX (k + 1) := by
    simp only [CheckX.Vocab, CheckX.evalV, hcnt2]
    rfl
  have hprev_φ1 : CheckX.prevOf I φ1 = k := by
    simp only [hφ1, CheckX.prevOf, CheckX.eval, hcnt0]
    rfl
  have hne_fst_cnt : CheckX.Vars.fst ≠ CheckX.Vars.cnt := by decide
  have hfst_φ1 : φ1 CheckX.Vars.fst = φ CheckX.Vars.fst := rfl
  have hfst2 : φ2 CheckX.Vars.fst = Sum.inr (Sum.inr false) := by
    have h1' : φ2 CheckX.Vars.fst = φ1 CheckX.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1', hfst_φ1, hfst]
  have hne_prev_cnt : CheckX.Vars.prev ≠ CheckX.Vars.cnt := by decide
  have hprev_φ2 : CheckX.prevOf I φ2 = k := by
    have h1' : φ2 CheckX.Vars.prev = φ1 CheckX.Vars.prev :=
      Function.update_of_ne hne_prev_cnt _ _
    simp only [CheckX.prevOf, h1']
    exact hprev_φ1
  have hxARest : (CheckX.Vocab I).evalV CheckX.VExpr.xARest φ2
      = Val.xTag (Tid.guessAX, false) (some w) := by
    simp only [CheckX.Vocab, CheckX.evalV, CheckX.auxOf, haux2]
    rfl
  have hxBRest : (CheckX.Vocab I).evalV CheckX.VExpr.xBRest φ2
      = Val.xTag (Tid.guessBX, false) (some w) := by
    simp only [CheckX.Vocab, CheckX.evalV, CheckX.auxOf, haux2]
    rfl
  have hprimeCheck : (CheckX.Vocab I).evalV CheckX.VExpr.primeCheckVal φ2
      = Val.primeTag Tid.primeCheckX k := by
    simp only [CheckX.Vocab, CheckX.evalV, hprev_φ2]
    rfl
  have hisBot2 : CheckX.evalB I CheckX.BExpr.isBot φ2 = false := by
    simp only [CheckX.evalB]
    cases hφ : φ2 CheckX.Vars.aux with
    | inl w' => cases w' with
        | none => rw [haux2] at hφ; injection hφ with hφ2; injection hφ2
        | some _ => simp
    | inr w' => simp
  have hs1 : Command.step Tid.checkX (checkXLoop I) φ s =
      some (none, Command.loopSeq (CheckX.body I) (checkXLoop I), φ, s) := by
    simp only [checkXLoop, Command.step, CheckX.Vocab, CheckX.evalB, if_true]
  have hs2 : Command.step Tid.checkX (Command.loopSeq (CheckX.body I) (checkXLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I))))))
        (checkXLoop I), φ1, s) := by
    change Command.step Tid.checkX (Command.loopSeq (CheckX.body I) (checkXLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I))))))
        (checkXLoop I),
        Function.update φ CheckX.Vars.prev (CheckX.eval I CheckX.Expr.readCnt φ), s)
    simp only [CheckX.body, Command.step, CheckX.Vocab]
    rfl
  have hs3 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  have hs4 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ2, s) := by
    change Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I),
        Function.update φ1 CheckX.Vars.cnt (CheckX.eval I CheckX.Expr.nextCnt φ1), s)
    simp only [Command.step, CheckX.Vocab]
    rfl
  have hs5 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs6 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I))))
      (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkX Loc.xA
        ((CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab]
  have hs7 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
        (Command.seq (checkXIteFirst I) (checkXTail I))))
      (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs8 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
        (Command.seq (checkXIteFirst I) (checkXTail I)))
      (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkX Loc.xB
        ((CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab]
  have hs9 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkXIteFirst I) (checkXTail I)) (checkXLoop I),
        φ2, s) := by
    simp only [Command.step]
    rfl
  have hs10 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (checkXIteFirst I) (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkXElseBranch I) (checkXTail I))
        (checkXLoop I), φ2, s) := by
    simp only [checkXIteFirst, Command.step, CheckX.Vocab, CheckX.evalB, hfst2]
    rfl
  have hs11 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (checkXElseBranch I) (checkXTail I)) (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xA
        ((CheckX.Vocab I).evalV CheckX.VExpr.xARest φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.seq (Command.read Loc.xB CheckX.VExpr.xBRest)
            (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
              (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))))
          (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [checkXElseBranch, Command.step, CheckX.Vocab, CheckX.evalV]
  have hs12 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xB CheckX.VExpr.xBRest)
          (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
            (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xB CheckX.VExpr.xBRest)
          (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
            (Command.read Loc.xB' CheckX.VExpr.primeCheckVal)))
        (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs13 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xB CheckX.VExpr.xBRest)
          (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
            (Command.read Loc.xB' CheckX.VExpr.primeCheckVal)))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xB
        ((CheckX.Vocab I).evalV CheckX.VExpr.xBRest φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
            (Command.read Loc.xB' CheckX.VExpr.primeCheckVal)))
          (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab, CheckX.evalV]
  have hs14 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
          (Command.read Loc.xB' CheckX.VExpr.primeCheckVal)))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
          (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))
        (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs15 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
          (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xA'
        ((CheckX.Vocab I).evalV CheckX.VExpr.primeCheckVal φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))
          (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab, CheckX.evalV]
  have hs16 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.read Loc.xB' CheckX.VExpr.primeCheckVal) (checkXTail I))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs17 : Command.step Tid.checkX
      (Command.loopSeq
        (Command.seq (Command.read Loc.xB' CheckX.VExpr.primeCheckVal) (checkXTail I))
        (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xB'
        ((CheckX.Vocab I).evalV CheckX.VExpr.primeCheckVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab, CheckX.evalV]
  have hs18 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq Command.skip (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (checkXTail I) (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs19 : Command.step Tid.checkX
      (Command.loopSeq (checkXTail I) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I)))
        (checkXLoop I), φ2, s) := by
    simp only [checkXTail, Command.step, CheckX.Vocab, hisBot2, Bool.false_eq_true, if_false]
  have hs20 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I)))
      (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hrs1 : Command.RunStep Tid.checkX s none (checkXLoop I, φ) s
      (Command.loopSeq (CheckX.body I) (checkXLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  have hrs19 := Command.step_sound _ _ _ _ _ _ _ hs19
  have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
  simp only [hw19] at h
  have hrs20 := Command.step_sound _ _ _ _ _ _ _ hs20
  have hw20 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs20)
  simp only [hw20] at h
  cases s with
  | nil =>
      have hnone : Command.step Tid.checkX
          ((Command.loopSeq (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I)
            (CheckX.auxSetBot_nonempty I)) (checkXLoop I)).seq C2) φ2 [] = none :=
        Command.step_seq_loopSeq_ndetAssign_nil _ _ _ _ _ _
      have h' := hnone ▸ h
      injection h' with _ h2
      injection h2 with _ h4
      injection h4 with h5 _
      exact absurd h5 (by rintro ⟨⟩)
  | cons c rest =>
      rcases Classical.em (c ∈ CheckX.auxSetBot I) with hc | hc
      · obtain ⟨w', rfl⟩ := (CheckX.mem_auxSetBot_iff c).mp hc
        have hcpos := Command.step_ndetAssign_cons_pos (t := Tid.checkX) CheckX.Vars.aux
          (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I) φ2 (Sum.inl w') rest hc
        have hrs21a : Command.RunStep Tid.checkX (Sum.inl w' :: rest) none
            (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I)
              (CheckX.auxSetBot_nonempty I), φ2) rest
            (Command.skip, Function.update φ2 CheckX.Vars.aux (Sum.inl w')) :=
          Command.step_sound _ _ _ _ _ _ _ hcpos
        have hrs21 := Command.RunStep.loopCongr (C2 := checkXLoop I) hrs21a
        have hw21 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs21)
        have h := hw21 ▸ h
        dsimp only at h
        have hrs22 : Command.RunStep Tid.checkX rest none
            (Command.loopSeq Command.skip (checkXLoop I),
              Function.update φ2 CheckX.Vars.aux (Sum.inl w')) rest
            (checkXLoop I, Function.update φ2 CheckX.Vars.aux (Sum.inl w')) :=
          Command.RunStep.loopSkip
        have hw22 : Command.step Tid.checkX
            ((Command.loopSeq Command.skip (checkXLoop I)).seq C2)
            (Function.update φ2 CheckX.Vars.aux (Sum.inl w')) rest =
            some (none, (checkXLoop I).seq C2,
              Function.update φ2 CheckX.Vars.aux (Sum.inl w'), rest) :=
          Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs22)
        have h := hw22 ▸ h
        rw [hcnt1val, hxARest, hxBRest, hprimeCheck] at h
        injection h with hh1 hrest1
        injection hrest1 with hh2 hrest2
        injection hrest2 with hh3 hh4
        have hne_fst_aux2 : CheckX.Vars.fst ≠ CheckX.Vars.aux := by decide
        have hne_cnt_aux2 : CheckX.Vars.cnt ≠ CheckX.Vars.aux := by decide
        refine ⟨w', rest,
          (Command.runFuel Tid.checkX ((checkXLoop I).seq C2,
            Function.update φ2 CheckX.Vars.aux (Sum.inl w')) rest N).2.1,
          rfl, hh2.symm, Function.update φ2 CheckX.Vars.aux (Sum.inl w'),
          (Function.update_of_ne hne_fst_aux2 (Sum.inl w') φ2).trans hfst2,
          (Function.update_of_ne hne_cnt_aux2 (Sum.inl w') φ2).trans hcnt2raw,
          Function.update_self _ _ _, Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩
      · exfalso
        have hs21' : Command.step Tid.checkX
            ((Command.loopSeq
              (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I)
                (CheckX.auxSetBot_nonempty I)) (checkXLoop I)).seq C2) φ2 (c :: rest) = none :=
          Command.step_seq_loopSeq_ndetAssign_cons_neg (t := Tid.checkX) CheckX.Vars.aux
            (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I) φ2 (checkXLoop I) C2 c rest hc
        have h' := hs21' ▸ h
        injection h' with _ h2
        injection h2 with _ h4
        injection h4 with h5 _
        exact absurd h5 (by rintro ⟨⟩)

/-- The converse of `checkX_blockRest_break_step`: a run taking at least 22
more steps from a store with `fst = false`, `cnt = k`, `aux = Sum.inl none`
emits `checkXBlockRestElems I (k, none)`, consumes nothing (the `break` skips
the trailing draw), and reaches `(C2, φ2)`. -/
theorem checkX_blockRest_break_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (CheckX.Vocab I))
    (s : List (CheckX.Vals I)) (φ : (CheckX.Vocab I).Store)
    (hfst : φ CheckX.Vars.fst = Sum.inr (Sum.inr false)) (k : Fin 4)
    (hcnt0 : φ CheckX.Vars.cnt = Sum.inr (Sum.inl k))
    (haux0 : φ CheckX.Vars.aux = Sum.inl none) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.checkX)) (φ' : (CheckX.Vocab I).Store)
    (h : Command.runFuel Tid.checkX ((checkXLoop I).seq C2, φ) s (N + 22) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (σ1 : Word (ThreadLabel (domainOf I) Tid.checkX)) (φ2u : (CheckX.Vocab I).Store),
      φ2u CheckX.Vars.fst = Sum.inr (Sum.inr false) ∧
      φ2u CheckX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
      φ2u CheckX.Vars.aux = Sum.inl none ∧
      σ = checkXBlockRestElems I (k, none) ++ σ1 ∧
      Command.runFuel Tid.checkX (C2, φ2u) s N = (.stuck, σ1, (Command.term, φ'), []) := by
  set φ1 : (CheckX.Vocab I).Store :=
    Function.update φ CheckX.Vars.prev (CheckX.eval I CheckX.Expr.readCnt φ) with hφ1
  set φ2 : (CheckX.Vocab I).Store :=
    Function.update φ1 CheckX.Vars.cnt (CheckX.eval I CheckX.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 CheckX.Vars.cnt = φ CheckX.Vars.cnt := rfl
  have hcnt2eq : φ2 CheckX.Vars.cnt = CheckX.eval I CheckX.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2raw : φ2 CheckX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt2eq, CheckX.eval, CheckX.cntOf, hcnt_φ1, hcnt0]
    rfl
  have hcnt2 : CheckX.cntOf I φ2 = k + 1 := by simp only [CheckX.cntOf, hcnt2raw]
  have hne_aux_cnt : CheckX.Vars.aux ≠ CheckX.Vars.cnt := by decide
  have haux_φ1 : φ1 CheckX.Vars.aux = φ CheckX.Vars.aux := rfl
  have haux2 : φ2 CheckX.Vars.aux = Sum.inl none := by
    have h1' : φ2 CheckX.Vars.aux = φ1 CheckX.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    rw [h1', haux_φ1, haux0]
  have hcnt1val : (CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2
      = Val.primeTag Tid.checkX (k + 1) := by
    simp only [CheckX.Vocab, CheckX.evalV, hcnt2]
    rfl
  have hprev_φ1 : CheckX.prevOf I φ1 = k := by
    simp only [hφ1, CheckX.prevOf, CheckX.eval, hcnt0]
    rfl
  have hne_fst_cnt : CheckX.Vars.fst ≠ CheckX.Vars.cnt := by decide
  have hfst_φ1 : φ1 CheckX.Vars.fst = φ CheckX.Vars.fst := rfl
  have hfst2 : φ2 CheckX.Vars.fst = Sum.inr (Sum.inr false) := by
    have h1' : φ2 CheckX.Vars.fst = φ1 CheckX.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1', hfst_φ1, hfst]
  have hne_prev_cnt : CheckX.Vars.prev ≠ CheckX.Vars.cnt := by decide
  have hprev_φ2 : CheckX.prevOf I φ2 = k := by
    have h1' : φ2 CheckX.Vars.prev = φ1 CheckX.Vars.prev :=
      Function.update_of_ne hne_prev_cnt _ _
    simp only [CheckX.prevOf, h1']
    exact hprev_φ1
  have hxARest : (CheckX.Vocab I).evalV CheckX.VExpr.xARest φ2
      = Val.xTag (Tid.guessAX, false) none := by
    simp only [CheckX.Vocab, CheckX.evalV, CheckX.auxOf, haux2]
    rfl
  have hxBRest : (CheckX.Vocab I).evalV CheckX.VExpr.xBRest φ2
      = Val.xTag (Tid.guessBX, false) none := by
    simp only [CheckX.Vocab, CheckX.evalV, CheckX.auxOf, haux2]
    rfl
  have hprimeCheck : (CheckX.Vocab I).evalV CheckX.VExpr.primeCheckVal φ2
      = Val.primeTag Tid.primeCheckX k := by
    simp only [CheckX.Vocab, CheckX.evalV, hprev_φ2]
    rfl
  have hisBot2 : CheckX.evalB I CheckX.BExpr.isBot φ2 = true := by
    simp only [CheckX.evalB, haux2]
  have hs1 : Command.step Tid.checkX (checkXLoop I) φ s =
      some (none, Command.loopSeq (CheckX.body I) (checkXLoop I), φ, s) := by
    simp only [checkXLoop, Command.step, CheckX.Vocab, CheckX.evalB, if_true]
  have hs2 : Command.step Tid.checkX (Command.loopSeq (CheckX.body I) (checkXLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I))))))
        (checkXLoop I), φ1, s) := by
    change Command.step Tid.checkX (Command.loopSeq (CheckX.body I) (checkXLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I))))))
        (checkXLoop I),
        Function.update φ CheckX.Vars.prev (CheckX.eval I CheckX.Expr.readCnt φ), s)
    simp only [CheckX.body, Command.step, CheckX.Vocab]
    rfl
  have hs3 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
          (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
              (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  have hs4 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I), φ2, s) := by
    change Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.assign CheckX.Vars.cnt CheckX.Expr.nextCnt)
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I)))))
        (checkXLoop I),
        Function.update φ1 CheckX.Vars.cnt (CheckX.eval I CheckX.Expr.nextCnt φ1), s)
    simp only [Command.step, CheckX.Vocab]
    rfl
  have hs5 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I)))))
      (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs6 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.write Loc.xA CheckX.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I))))
      (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkX Loc.xA
        ((CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip
          (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
            (Command.seq (checkXIteFirst I) (checkXTail I))))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab]
  have hs7 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
        (Command.seq (checkXIteFirst I) (checkXTail I))))
      (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
          (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs8 : Command.step Tid.checkX (Command.loopSeq
      (Command.seq (Command.write Loc.xB CheckX.VExpr.cntTagVal)
        (Command.seq (checkXIteFirst I) (checkXTail I)))
      (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkX Loc.xB
        ((CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab]
  have hs9 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkXIteFirst I) (checkXTail I)))
        (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkXIteFirst I) (checkXTail I)) (checkXLoop I),
        φ2, s) := by
    simp only [Command.step]
    rfl
  have hs10 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (checkXIteFirst I) (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkXElseBranch I) (checkXTail I))
        (checkXLoop I), φ2, s) := by
    simp only [checkXIteFirst, Command.step, CheckX.Vocab, CheckX.evalB, hfst2]
    rfl
  have hs11 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (checkXElseBranch I) (checkXTail I)) (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xA
        ((CheckX.Vocab I).evalV CheckX.VExpr.xARest φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.seq (Command.read Loc.xB CheckX.VExpr.xBRest)
            (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
              (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))))
          (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [checkXElseBranch, Command.step, CheckX.Vocab, CheckX.evalV]
  have hs12 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xB CheckX.VExpr.xBRest)
          (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
            (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xB CheckX.VExpr.xBRest)
          (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
            (Command.read Loc.xB' CheckX.VExpr.primeCheckVal)))
        (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs13 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xB CheckX.VExpr.xBRest)
          (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
            (Command.read Loc.xB' CheckX.VExpr.primeCheckVal)))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xB
        ((CheckX.Vocab I).evalV CheckX.VExpr.xBRest φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
            (Command.read Loc.xB' CheckX.VExpr.primeCheckVal)))
          (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab, CheckX.evalV]
  have hs14 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
          (Command.read Loc.xB' CheckX.VExpr.primeCheckVal)))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
          (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))
        (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs15 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.xA' CheckX.VExpr.primeCheckVal)
          (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xA'
        ((CheckX.Vocab I).evalV CheckX.VExpr.primeCheckVal φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))
          (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab, CheckX.evalV]
  have hs16 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.xB' CheckX.VExpr.primeCheckVal))
        (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.read Loc.xB' CheckX.VExpr.primeCheckVal) (checkXTail I))
        (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs17 : Command.step Tid.checkX
      (Command.loopSeq
        (Command.seq (Command.read Loc.xB' CheckX.VExpr.primeCheckVal) (checkXTail I))
        (checkXLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkX Loc.xB'
        ((CheckX.Vocab I).evalV CheckX.VExpr.primeCheckVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (checkXTail I)) (checkXLoop I), φ2, s) := by
    simp only [Command.step, CheckX.Vocab, CheckX.evalV]
  have hs18 : Command.step Tid.checkX
      (Command.loopSeq (Command.seq Command.skip (checkXTail I)) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (checkXTail I) (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs19 : Command.step Tid.checkX
      (Command.loopSeq (checkXTail I) (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq Command.brk
        (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I)))
        (checkXLoop I), φ2, s) := by
    simp only [checkXTail, Command.step, CheckX.Vocab, hisBot2, if_true]
  have hs20 : Command.step Tid.checkX (Command.loopSeq (Command.seq Command.brk
      (Command.ndetAssign CheckX.Vars.aux (CheckX.auxSetBot I) (CheckX.auxSetBot_nonempty I)))
      (checkXLoop I)) φ2 s =
      some (none, Command.loopSeq Command.brk (checkXLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs21 : Command.step Tid.checkX
      (Command.loopSeq Command.brk (checkXLoop I)) φ2 s =
      some (none, Command.skip, φ2, s) := by
    simp only [Command.step]
    rfl
  have hs22 : Command.step Tid.checkX (Command.seq Command.skip C2) φ2 s =
      some (none, C2, φ2, s) := by
    simp only [Command.step]
    rfl
  have hrs1 : Command.RunStep Tid.checkX s none (checkXLoop I, φ) s
      (Command.loopSeq (CheckX.body I) (checkXLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  have hrs19 := Command.step_sound _ _ _ _ _ _ _ hs19
  have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
  simp only [hw19] at h
  have hrs20 := Command.step_sound _ _ _ _ _ _ _ hs20
  have hw20 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs20)
  simp only [hw20] at h
  have hrs21 := Command.step_sound _ _ _ _ _ _ _ hs21
  have hw21 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs21)
  simp only [hw21] at h
  simp only [hs22] at h
  rw [hcnt1val, hxARest, hxBRest, hprimeCheck] at h
  injection h with hh1 hrest1
  injection hrest1 with hh2 hrest2
  injection hrest2 with hh3 hh4
  refine ⟨(Command.runFuel Tid.checkX (C2, φ2) s N).2.1, φ2, hfst2, hcnt2raw, haux2, hh2.symm,
    Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩

/-- The converse of `checkXChain_shape_val`. By strong induction on `s.length`:
after `checkX_blockRest_continue_step_inv`, the drawn `w'` is either `none`
(`checkX_blockRest_break_step_inv` ends the chain) or `some w1` (recursion). -/
theorem checkX_chain_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (CheckX.Vals I)), s.length = n →
      ∀ (C2 : Command (domainOf I) (CheckX.Vocab I)) (φ : (CheckX.Vocab I).Store)
        (_hfst : φ CheckX.Vars.fst = Sum.inr (Sum.inr false))
        (k0 : Fin 4) (_hcnt0 : φ CheckX.Vars.cnt = Sum.inr (Sum.inl k0))
        (w0 : I.Γ) (_haux0 : φ CheckX.Vars.aux = Sum.inl (some w0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.checkX))
        (φ' : (CheckX.Vocab I).Store),
        Command.runFuel Tid.checkX ((checkXLoop I).seq C2, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (ws : List I.Γ) (rest0 : List (CheckX.Vals I))
          (kws : List (Fin 4 × Option I.Γ)) (φ2u : (CheckX.Vocab I).Store)
          (σ1 : Word (ThreadLabel (domainOf I) Tid.checkX)),
          s = ws.map (fun w => (Sum.inl (some w) : CheckX.Vals I)) ++
            Sum.inl none :: rest0 ∧
          kws.length = ws.length + 2 ∧
          (∀ i, i < kws.length →
            ∃ w, kws[i]? = some (⟨(k0.val + i) % 4, by omega⟩, w)) ∧
          σ = kws.flatMap (checkXBlockRestElems I) ++ σ1 ∧
          Command.runFuel Tid.checkX (C2, φ2u) rest0 N =
            (.stuck, σ1, (Command.term, φ'), []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen C2 φ hfst k0 hcnt0 w0 haux0 N σ φ' h
    have h22 := Command.runFuel_stuck_stable h 22
    obtain ⟨w', rest, σ1, hseq, hσeq, φ2u, hfst2, hcnt2, haux2, h2⟩ :=
      checkX_blockRest_continue_step_inv I C2 s φ hfst k0 hcnt0 w0 haux0 N σ φ' h22
    subst hseq
    cases w' with
    | none =>
        have h2' := Command.runFuel_stuck_stable h2 22
        obtain ⟨σ1', φ3u, hfst3, hcnt3, haux3, hσ1eq, h3⟩ :=
          checkX_blockRest_break_step_inv I C2 rest φ2u hfst2 (k0 + 1) hcnt2 haux2 N σ1 φ' h2'
        refine ⟨[], rest, [(k0, some w0), (k0 + 1, none)], φ3u, σ1', rfl, rfl, ?_, ?_, h3⟩
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · refine ⟨some w0, ?_⟩
            simp only [List.getElem?_cons_zero]
            congr 2
            apply Fin.ext
            have hk0 := k0.isLt
            simp only [Nat.add_zero]
            omega
          · refine ⟨none, ?_⟩
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
            congr 2
        · rw [hσeq, hσ1eq]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | some w1 =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inl (some w1) :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        obtain ⟨ws', rest0, kws', φ2u', σ1', hseq', hlen', hval', hσeq', h3⟩ :=
          ih rest.length hrest_len rest rfl C2 φ2u hfst2 (k0 + 1) hcnt2 w1 haux2 N σ1 φ' h2
        refine ⟨w1 :: ws', rest0, (k0, some w0) :: kws', φ2u', σ1',
          by simp [hseq'], by simp [hlen'], ?_, ?_, h3⟩
        · intro i hi
          cases i with
          | zero =>
              refine ⟨some w0, ?_⟩
              simp only [List.getElem?_cons_zero]
              congr 2
              apply Fin.ext
              have hk0 := k0.isLt
              simp only [Nat.add_zero]
              omega
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              obtain ⟨w, hw⟩ := hval' i hi'
              refine ⟨w, ?_⟩
              simp only [List.getElem?_cons_succ]
              rw [hw]
              congr 2
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · rw [hσeq, hσeq']
          simp only [List.flatMap_cons, List.append_assoc]

/-- **The word characterization of the threads, `CheckX`.** The converse of
`checkX_general_run_val`: a term-reaching run of `CheckX.program` from its initial
store draws some `v0 : I.Γ` (`checkX_lead_step_inv`), then runs block 0
(`checkX_block0_step_inv`), then either stops (`w = none`) or continues the
chain (`checkX_chain_shape_inv`). -/
theorem checkX_shape_inv (I : PCPInstance) {s : List (CheckX.Vals I)}
    {φ' : (CheckX.Vocab I).Store} {cLast : Config (domainOf I) (CheckX.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.checkX)}
    (hrun : Command.Run Tid.checkX s
      (CheckX.program I, (CheckX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : I.Γ) (js : List I.Γ) (kws : List (Fin 4 × Option I.Γ)),
      s = Sum.inl (some v0) ::
        (js.map (fun w => (Sum.inl (some w) : CheckX.Vals I)) ++ [Sum.inl none]) ∧
      kws.length = js.length + 1 ∧
      (∀ i, i < kws.length → ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w)) ∧
      σ = checkXBlockWord I v0 kws := by
  have hterm_stuck : ∀ (φt : (CheckX.Vocab I).Store) (r : List (CheckX.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.checkX)) (φt' : (CheckX.Vocab I).Store),
      Command.runFuel Tid.checkX (Command.term, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      r = [] ∧ σt = [] ∧ φt' = φt := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        exact absurd (congrArg Prod.fst hm) (by rintro ⟨⟩)
    | succ m =>
        simp only [Command.runFuel, Command.step] at hm
        injection hm with hh1 hrest
        injection hrest with hh2 hrest2
        injection hrest2 with hh3 hh4
        exact ⟨hh4, hh2.symm, (congrArg Prod.snd hh3).symm⟩
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := checkX_lead_step_inv I s n σ φ' hn2
  have hfst1 : Function.update ((CheckX.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) CheckX.Vars.aux (Sum.inl (some v0))
      CheckX.Vars.fst = Sum.inr (Sum.inr true) := by
    have hne : CheckX.Vars.fst ≠ CheckX.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have hcnt1 : Function.update ((CheckX.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) CheckX.Vars.aux (Sum.inl (some v0))
      CheckX.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne : CheckX.Vars.cnt ≠ CheckX.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have h20 := Command.runFuel_stuck_stable h2 20
  obtain ⟨w, rest2, σ1, hs2, hσ2, φ3, hfst3, hcnt3, haux3, h3⟩ :=
    checkX_block0_step_inv I Command.term rest _ hfst1 hcnt1 v0 (Function.update_self _ _ _)
      n σ φ' h20
  cases w with
  | none =>
      have h22 := Command.runFuel_stuck_stable h3 22
      obtain ⟨σ1', φ4, hfst4, hcnt4, haux4, hσ1eq, h4⟩ :=
        checkX_blockRest_break_step_inv I Command.term rest2 φ3 hfst3 1 hcnt3 haux3 n σ1 φ' h22
      obtain ⟨hrest2nil, hσ1'nil, hφ4eq⟩ := hterm_stuck φ4 rest2 n σ1' φ' h4
      refine ⟨v0, [], [(1, none)], ?_, rfl, ?_, ?_⟩
      · simp [hs, hs2, hrest2nil]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨none, rfl⟩
      · simp [hσ2, hσ1eq, hσ1'nil, checkXBlockWord, List.flatMap_cons, List.flatMap_nil]
  | some w1 =>
      obtain ⟨ws, rest0, kws, φ2u, σ1', hseq', hlen', hval', hσeq', h4⟩ :=
        checkX_chain_shape_inv I rest2.length rest2 rfl Command.term φ3 hfst3 1 hcnt3 w1 haux3
          n σ1 φ' h3
      obtain ⟨hrest0nil, hσ1'nil, hφ2ueq⟩ := hterm_stuck φ2u rest0 n σ1' φ' h4
      refine ⟨v0, w1 :: ws, kws, ?_, by omega, ?_, ?_⟩
      · rw [hs, hs2, hseq', hrest0nil]
        simp
      · intro i hi
        have := hval' i hi
        simpa using this
      · rw [hσ2, hσeq', hσ1'nil, List.append_nil]
        rfl

/-- `checkX_chain_shape_inv`, with the second components of `kws` determined:
`kws[i]?.map Prod.snd = some ((w0 :: ws)[i]?)` for every `i < kws.length`
(the last entry being the terminating `none`). -/
theorem checkX_chain_shape_inv_vals (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (CheckX.Vals I)), s.length = n →
      ∀ (C2 : Command (domainOf I) (CheckX.Vocab I)) (φ : (CheckX.Vocab I).Store)
        (_hfst : φ CheckX.Vars.fst = Sum.inr (Sum.inr false))
        (k0 : Fin 4) (_hcnt0 : φ CheckX.Vars.cnt = Sum.inr (Sum.inl k0))
        (w0 : I.Γ) (_haux0 : φ CheckX.Vars.aux = Sum.inl (some w0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.checkX))
        (φ' : (CheckX.Vocab I).Store),
        Command.runFuel Tid.checkX ((checkXLoop I).seq C2, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (ws : List I.Γ) (rest0 : List (CheckX.Vals I))
          (kws : List (Fin 4 × Option I.Γ)) (φ2u : (CheckX.Vocab I).Store)
          (σ1 : Word (ThreadLabel (domainOf I) Tid.checkX)),
          s = ws.map (fun w => (Sum.inl (some w) : CheckX.Vals I)) ++
            Sum.inl none :: rest0 ∧
          kws.length = ws.length + 2 ∧
          (∀ i, i < kws.length →
            ∃ w, kws[i]? = some (⟨(k0.val + i) % 4, by omega⟩, w)) ∧
          (∀ i, i < kws.length → kws[i]?.map Prod.snd = some ((w0 :: ws)[i]?)) ∧
          σ = kws.flatMap (checkXBlockRestElems I) ++ σ1 ∧
          Command.runFuel Tid.checkX (C2, φ2u) rest0 N =
            (.stuck, σ1, (Command.term, φ'), []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen C2 φ hfst k0 hcnt0 w0 haux0 N σ φ' h
    have h22 := Command.runFuel_stuck_stable h 22
    obtain ⟨w', rest, σ1, hseq, hσeq, φ2u, hfst2, hcnt2, haux2, h2⟩ :=
      checkX_blockRest_continue_step_inv I C2 s φ hfst k0 hcnt0 w0 haux0 N σ φ' h22
    subst hseq
    cases w' with
    | none =>
        have h2' := Command.runFuel_stuck_stable h2 22
        obtain ⟨σ1', φ3u, hfst3, hcnt3, haux3, hσ1eq, h3⟩ :=
          checkX_blockRest_break_step_inv I C2 rest φ2u hfst2 (k0 + 1) hcnt2 haux2 N σ1 φ' h2'
        refine ⟨[], rest, [(k0, some w0), (k0 + 1, none)], φ3u, σ1', rfl, rfl, ?_, ?_, ?_, h3⟩
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · refine ⟨some w0, ?_⟩
            simp only [List.getElem?_cons_zero]
            congr 2
            apply Fin.ext
            have hk0 := k0.isLt
            simp only [Nat.add_zero]
            omega
          · refine ⟨none, ?_⟩
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
            congr 2
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · simp
          · simp
        · rw [hσeq, hσ1eq]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | some w1 =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inl (some w1) :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        obtain ⟨ws', rest0, kws', φ2u', σ1', hseq', hlen', hval', hval2', hσeq', h4⟩ :=
          ih rest.length hrest_len rest rfl C2 φ2u hfst2 (k0 + 1) hcnt2 w1 haux2 N σ1 φ' h2
        refine ⟨w1 :: ws', rest0, (k0, some w0) :: kws', φ2u', σ1',
          by simp [hseq'], by simp [hlen'], ?_, ?_, ?_, h4⟩
        · intro i hi
          cases i with
          | zero =>
              refine ⟨some w0, ?_⟩
              simp only [List.getElem?_cons_zero]
              congr 2
              apply Fin.ext
              have hk0 := k0.isLt
              simp only [Nat.add_zero]
              omega
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              obtain ⟨w, hw⟩ := hval' i hi'
              refine ⟨w, ?_⟩
              simp only [List.getElem?_cons_succ]
              rw [hw]
              congr 2
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · intro i hi
          cases i with
          | zero => simp
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              have := hval2' i hi'
              simpa using this
        · rw [hσeq, hσeq']
          simp only [List.flatMap_cons, List.append_assoc]

/-- `checkX_shape_inv`, with the second components of `kws` determined:
`kws[i]?.map Prod.snd = some (js[i]?)` for every `i < kws.length`. -/
theorem checkX_shape_inv_vals (I : PCPInstance) {s : List (CheckX.Vals I)}
    {φ' : (CheckX.Vocab I).Store} {cLast : Config (domainOf I) (CheckX.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.checkX)}
    (hrun : Command.Run Tid.checkX s
      (CheckX.program I, (CheckX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : I.Γ) (js : List I.Γ) (kws : List (Fin 4 × Option I.Γ)),
      s = Sum.inl (some v0) ::
        (js.map (fun w => (Sum.inl (some w) : CheckX.Vals I)) ++ [Sum.inl none]) ∧
      kws.length = js.length + 1 ∧
      (∀ i, i < kws.length → ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w)) ∧
      (∀ i, i < kws.length → kws[i]?.map Prod.snd = some (js[i]?)) ∧
      σ = checkXBlockWord I v0 kws := by
  have hterm_stuck : ∀ (φt : (CheckX.Vocab I).Store) (r : List (CheckX.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.checkX)) (φt' : (CheckX.Vocab I).Store),
      Command.runFuel Tid.checkX (Command.term, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      r = [] ∧ σt = [] ∧ φt' = φt := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        exact absurd (congrArg Prod.fst hm) (by rintro ⟨⟩)
    | succ m =>
        simp only [Command.runFuel, Command.step] at hm
        injection hm with hh1 hrest
        injection hrest with hh2 hrest2
        injection hrest2 with hh3 hh4
        exact ⟨hh4, hh2.symm, (congrArg Prod.snd hh3).symm⟩
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := checkX_lead_step_inv I s n σ φ' hn2
  have hfst1 : Function.update ((CheckX.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) CheckX.Vars.aux (Sum.inl (some v0))
      CheckX.Vars.fst = Sum.inr (Sum.inr true) := by
    have hne : CheckX.Vars.fst ≠ CheckX.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have hcnt1 : Function.update ((CheckX.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) CheckX.Vars.aux (Sum.inl (some v0))
      CheckX.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne : CheckX.Vars.cnt ≠ CheckX.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have h20 := Command.runFuel_stuck_stable h2 20
  obtain ⟨w, rest2, σ1, hs2, hσ2, φ3, hfst3, hcnt3, haux3, h3⟩ :=
    checkX_block0_step_inv I Command.term rest _ hfst1 hcnt1 v0 (Function.update_self _ _ _)
      n σ φ' h20
  cases w with
  | none =>
      have h22 := Command.runFuel_stuck_stable h3 22
      obtain ⟨σ1', φ4, hfst4, hcnt4, haux4, hσ1eq, h4⟩ :=
        checkX_blockRest_break_step_inv I Command.term rest2 φ3 hfst3 1 hcnt3 haux3 n σ1 φ' h22
      obtain ⟨hrest2nil, hσ1'nil, hφ4eq⟩ := hterm_stuck φ4 rest2 n σ1' φ' h4
      refine ⟨v0, [], [(1, none)], ?_, rfl, ?_, ?_, ?_⟩
      · simp [hs, hs2, hrest2nil]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨none, rfl⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp
      · simp [hσ2, hσ1eq, hσ1'nil, checkXBlockWord, List.flatMap_cons, List.flatMap_nil]
  | some w1 =>
      obtain ⟨ws, rest0, kws, φ2u, σ1', hseq', hlen', hval', hval2', hσeq', h4⟩ :=
        checkX_chain_shape_inv_vals I rest2.length rest2 rfl Command.term φ3 hfst3 1 hcnt3 w1 haux3
          n σ1 φ' h3
      obtain ⟨hrest0nil, hσ1'nil, hφ2ueq⟩ := hterm_stuck φ2u rest0 n σ1' φ' h4
      refine ⟨v0, w1 :: ws, kws, ?_, by omega, ?_, ?_, ?_⟩
      · rw [hs, hs2, hseq', hrest0nil]
        simp
      · intro i hi
        have := hval' i hi
        simpa using this
      · intro i hi
        have := hval2' i hi
        simpa using this
      · rw [hσ2, hσeq', hσ1'nil, List.append_nil]
        rfl

/-! ## `PrimeAX`

As for `PrimeCheckX`: `PrimeAX`'s iterations are uniform. -/

/-- The converse of `primeAX_iter_step`: a run that takes one more full
iteration of `primeAXLoop` (within `.seq _ C2`) consumes some `v ∈ PrimeAX.X`
as the head of `s`, emits the three-event block, and returns to
`primeAXLoop` with `cnt` advanced and `b` set to `v`. -/
theorem primeAX_iter_step_inv (I : PCPInstance) (C2 : Command (domainOf I) (PrimeAX.Vocab I))
    (s : List PrimeAX.Vals) (φ : (PrimeAX.Vocab I).Store)
    (hb : φ PrimeAX.Vars.b = Sum.inr true) (cnt0 : Fin 4)
    (hcnt0 : φ PrimeAX.Vars.cnt = Sum.inl cnt0) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeAX)) (φ' : (PrimeAX.Vocab I).Store)
    (h : Command.runFuel Tid.primeAX ((primeAXLoop I).seq C2, φ) s (N + 11) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v : PrimeAX.Vals) (rest : List PrimeAX.Vals)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.primeAX)),
      v ∈ PrimeAX.X ∧
      s = v :: rest ∧
      σ = [ ⟨EventLabel.wt Tid.primeAX Loc.xA' (Val.primeTag Tid.primeAX 0), rfl⟩
          , ⟨EventLabel.wt Tid.primeAX Loc.zAxx' (Val.cnt (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.primeAX Loc.zAx'x (Val.cnt (cnt0 + 1)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.primeAX
        ((primeAXLoop I).seq C2,
          Function.update (Function.update φ PrimeAX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeAX.Vars.b v) rest N = (.stuck, σ1, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeAXLoop, PrimeAX.Vocab,
    PrimeAX.evalB, hb, if_true, PrimeAX.evalV, primeAXLoopBody, PrimeAX.body,
    hcnt0, PrimeAX.eval, Prod.mk.injEq] at h
  cases s with
  | nil =>
      simp only [Command.step] at h
      exact absurd h.2.2.1 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.step, PrimeAX.X, Finset.mem_insert,
        Finset.mem_singleton] at h
      split_ifs at h with hc
      · simp only [Command.step] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨c, rest, _, ?_, rfl, h2.symm, ?_⟩
        · simp only [PrimeAX.X, Finset.mem_insert, Finset.mem_singleton]; exact hc
        · change Command.runFuel Tid.primeAX
              ((Command.whileLoop PrimeAX.BExpr.isB
                  (Command.seq (Command.seq (Command.assign PrimeAX.Vars.cnt PrimeAX.Expr.nextCnt)
                      (Command.seq (Command.write Loc.xA' PrimeAX.VExpr.xPrimeTag)
                        (Command.seq (Command.write Loc.zAxx' PrimeAX.VExpr.cntVal)
                          (Command.read Loc.zAx'x PrimeAX.VExpr.cntVal))))
                    (Command.ndetAssign PrimeAX.Vars.b PrimeAX.X PrimeAX.X_nonempty))).seq C2,
                Function.update (Function.update φ PrimeAX.Vars.cnt (Sum.inl (cnt0 + 1)))
                  PrimeAX.Vars.b c) rest N = _
          exact Prod.ext h1 (Prod.ext rfl (Prod.ext h3 h4))
      · exact absurd h.2.2.1 (by rintro ⟨⟩)

/-- One `Command.step` of `PrimeAX.program`'s leading `NDet({⊥,⊤})` draw,
against the empty resolution (by `rfl`). -/
theorem primeAX_lead_hstep_nil (I : PCPInstance) :
    Command.step Tid.primeAX (PrimeAX.program I)
      ((PrimeAX.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      ([] : List PrimeAX.Vals) = none := rfl

/-- One `Command.step` of `PrimeAX.program`'s leading draw, against a
resolution with a head not in `PrimeAX.X`. -/
theorem primeAX_lead_hstep_inl (I : PCPInstance) (k : Fin 4)
    (rest : List PrimeAX.Vals) :
    Command.step Tid.primeAX (PrimeAX.program I)
      ((PrimeAX.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      (Sum.inl k :: rest) = none := rfl

/-- The converse of `PrimeAX.program`'s leading `NDet({⊥,⊤})` draw: a run
consuming at least one more step draws a `Bool` `b0` as the head of `s` and
reaches `(primeAXLoop I).seq Command.term` with `b` set to `b0`. -/
theorem primeAX_lead_step_inv (I : PCPInstance) (s : List PrimeAX.Vals) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeAX)) (φ' : (PrimeAX.Vocab I).Store)
    (h : Command.runFuel Tid.primeAX (PrimeAX.program I, (PrimeAX.Vocab I).mkStore
      (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0)) s
      (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (b0 : Bool) (rest : List PrimeAX.Vals),
      s = Sum.inr b0 :: rest ∧
      Command.runFuel Tid.primeAX
        ((primeAXLoop I).seq Command.term,
          Function.update ((PrimeAX.Vocab I).mkStore
            (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
            PrimeAX.Vars.b (Sum.inr b0)) rest N = (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel] at h
      have h2 := primeAX_lead_hstep_nil I ▸ h
      dsimp only at h2
      have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
      exact absurd h3 (by rintro ⟨⟩)
  | cons c rest =>
      rcases c with k | b0
      · simp only [Command.runFuel] at h
        have h2 := primeAX_lead_hstep_inl I k rest ▸ h
        dsimp only at h2
        have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
        exact absurd h3 (by rintro ⟨⟩)
      · rcases b0 with rfl | rfl
        · simp only [Command.runFuel] at h
          exact ⟨false, rest, rfl, h⟩
        · simp only [Command.runFuel] at h
          exact ⟨true, rest, rfl, h⟩

/-- The converse of `primeAX_stop_step`: with the guard false, the next two
steps are silent and reach `(C2, φ)`. -/
theorem primeAX_stop_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (PrimeAX.Vocab I)) (s : List PrimeAX.Vals)
    (φ : (PrimeAX.Vocab I).Store) (hb : φ PrimeAX.Vars.b = Sum.inr false) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeAX)) (φ' : (PrimeAX.Vocab I).Store)
    (h : Command.runFuel Tid.primeAX ((primeAXLoop I).seq C2, φ) s (N + 2) =
      (.stuck, σ, (Command.term, φ'), [])) :
    Command.runFuel Tid.primeAX (C2, φ) s N = (.stuck, σ, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeAXLoop, PrimeAX.Vocab,
    PrimeAX.evalB, hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))

/-- The converse of `primeAX_shape`: a run entering `primeAXLoop` and reaching
`(Command.term, φ')` emits `M' + 1` three-event blocks. By strong induction
on `s.length`. -/
theorem primeAX_loop_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List PrimeAX.Vals), s.length = n →
      ∀ (φ : (PrimeAX.Vocab I).Store) (cnt0 : Fin 4)
        (_hb : φ PrimeAX.Vars.b = Sum.inr true)
        (_hcnt0 : φ PrimeAX.Vars.cnt = Sum.inl cnt0)
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.primeAX))
        (φ' : (PrimeAX.Vocab I).Store),
        Command.runFuel Tid.primeAX ((primeAXLoop I).seq Command.term, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (M' : ℕ) (vals : List (Val I)),
          s = List.replicate M' (Sum.inr true) ++ [Sum.inr false] ∧
          vals.length = M' + 1 ∧
          (∀ i, i < vals.length →
            vals[i]? = some (Val.cnt (⟨(cnt0.val + i + 1) % 4, by omega⟩ : Fin 4))) ∧
          σ = primeAXBlockWord I vals := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen φ cnt0 hb hcnt0 N σ φ' h
    have h11 := Command.runFuel_stuck_stable h 11
    obtain ⟨v, rest, σ1, hvmem, hseq, hσeq, h2⟩ :=
      primeAX_iter_step_inv I Command.term s φ hb cnt0 hcnt0 N σ φ' h11
    subst hseq
    simp only [PrimeAX.X, Finset.mem_insert, Finset.mem_singleton] at hvmem
    rcases hvmem with rfl | rfl
    · have h2' := Command.runFuel_stuck_stable h2 2
      have hbf : Function.update (Function.update φ PrimeAX.Vars.cnt (Sum.inl (cnt0 + 1)))
          PrimeAX.Vars.b (Sum.inr false) PrimeAX.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h3 := primeAX_stop_step_inv I Command.term rest _ hbf N σ1 φ' h2'
      have hrest : rest = [] ∧ σ1 = ([] : Word (ThreadLabel (domainOf I) Tid.primeAX)) := by
        rcases N with _ | N'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ10⟩ := hrest
      subst hrest0
      refine ⟨0, [Val.cnt (cnt0 + 1)], rfl, rfl, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        congr 1
      · simp only [hσeq, hσ10, List.append_nil, primeAXBlockWord]
        rfl
    · have hrest_len : rest.length < n := by
        have heq : (Sum.inr true :: rest).length = n := hslen
        simp only [List.length_cons] at heq
        omega
      have hbnew : Function.update (Function.update φ PrimeAX.Vars.cnt (Sum.inl (cnt0 + 1)))
          PrimeAX.Vars.b (Sum.inr true) PrimeAX.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hne_cntb : PrimeAX.Vars.cnt ≠ PrimeAX.Vars.b := by decide
      have hcntnew :
          Function.update (Function.update φ PrimeAX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeAX.Vars.b (Sum.inr true) PrimeAX.Vars.cnt = Sum.inl (cnt0 + 1) :=
        (Function.update_of_ne hne_cntb (Sum.inr true) _).trans (Function.update_self _ _ _)
      obtain ⟨M'', vals'', hrest_eq, hvals_len, hvals_val, hσ1⟩ :=
        ih rest.length hrest_len rest rfl
          (Function.update (Function.update φ PrimeAX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeAX.Vars.b (Sum.inr true))
          (cnt0 + 1) hbnew hcntnew N σ1 φ' h2
      refine ⟨M'' + 1, Val.cnt (cnt0 + 1) :: vals'', ?_, ?_, ?_, ?_⟩
      · rw [hrest_eq, List.replicate_succ, List.cons_append]
      · simp [hvals_len]
      · intro i hi
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq]
            congr 1
        | succ i =>
            simp only [List.length_cons] at hi
            have hi' : i < vals''.length := by omega
            have hval' := hvals_val i hi'
            simp only [List.getElem?_cons_succ]
            rw [hval']
            congr 2
            apply Fin.ext
            simp [Fin.add_def]
            omega
      · rw [hσeq, hσ1]
        simp only [primeAXBlockWord]
        rfl

/-- **The word characterization of the threads, `PrimeAX`.** The converse of
`primeAX_general_run`: a term-reaching run of `PrimeAX.program` from its
initial store draws `M` times `⊤` and then `⊥`, and its word is
`primeAXBlockWord` of the `M` values written to `zAxx'`. In particular every
`xA'`-write of `PrimeAX` carries `Val.primeTag Tid.primeAX 0`
(`primeAXBlockWord_xA'_val`). -/
theorem primeAX_shape_inv (I : PCPInstance) {s : List PrimeAX.Vals}
    {φ' : (PrimeAX.Vocab I).Store} {cLast : Config (domainOf I) (PrimeAX.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.primeAX)}
    (hrun : Command.Run Tid.primeAX s
      (PrimeAX.program I, (PrimeAX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      σ cLast [] (Command.term, φ')) :
    ∃ (M : ℕ) (vals : List (Val I)),
      s = List.replicate M (Sum.inr true) ++ [Sum.inr false] ∧
      vals.length = M ∧
      (∀ i, i < vals.length → vals[i]? = some (Val.cnt (⟨(i + 1) % 4, by omega⟩ : Fin 4))) ∧
      σ = primeAXBlockWord I vals := by
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨b0, rest, hs, h2⟩ := primeAX_lead_step_inv I s n σ φ' hn2
  cases b0 with
  | false =>
      have hbf : Function.update ((PrimeAX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeAX.Vars.b (Sum.inr false) PrimeAX.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h2' := Command.runFuel_stuck_stable h2 2
      have h3 := primeAX_stop_step_inv I Command.term rest _ hbf n σ φ' h2'
      have hrest : rest = [] ∧ σ = ([] : Word (ThreadLabel (domainOf I) Tid.primeAX)) := by
        rcases n with _ | n'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ0⟩ := hrest
      refine ⟨0, [], ?_, rfl, ?_, ?_⟩
      · simp [hs, hrest0]
      · intro i hi; simp at hi
      · simp only [hσ0, primeAXBlockWord]; rfl
  | true =>
      have hb2 : Function.update ((PrimeAX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeAX.Vars.b (Sum.inr true) PrimeAX.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hcnt2 : Function.update ((PrimeAX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeAX.Vars.b (Sum.inr true) PrimeAX.Vars.cnt = Sum.inl (0 : Fin 4) := by
        have hne : PrimeAX.Vars.cnt ≠ PrimeAX.Vars.b := by decide
        exact Function.update_of_ne hne _ _
      obtain ⟨M', vals, hrest_eq, hvals_len, hvals_val, hσeq⟩ :=
        primeAX_loop_shape_inv I rest.length rest rfl _ 0 hb2 hcnt2 n σ φ' h2
      refine ⟨M' + 1, vals, ?_, ?_, ?_, hσeq⟩
      · rw [hs, hrest_eq, List.replicate_succ, List.cons_append]
      · omega
      · intro i hi
        have := hvals_val i hi
        simpa using this


/-! ## `PrimeBY`

As for `PrimeAX`. -/

/-- The converse of `primeBY_iter_step`. -/
theorem primeBY_iter_step_inv (I : PCPInstance) (C2 : Command (domainOf I) (PrimeBY.Vocab I))
    (s : List PrimeBY.Vals) (φ : (PrimeBY.Vocab I).Store)
    (hb : φ PrimeBY.Vars.b = Sum.inr true) (cnt0 : Fin 4)
    (hcnt0 : φ PrimeBY.Vars.cnt = Sum.inl cnt0) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeBY)) (φ' : (PrimeBY.Vocab I).Store)
    (h : Command.runFuel Tid.primeBY ((primeBYLoop I).seq C2, φ) s (N + 11) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v : PrimeBY.Vals) (rest : List PrimeBY.Vals)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.primeBY)),
      v ∈ PrimeBY.X ∧
      s = v :: rest ∧
      σ = [ ⟨EventLabel.wt Tid.primeBY Loc.yB' (Val.primeTag Tid.primeBY 0), rfl⟩
          , ⟨EventLabel.wt Tid.primeBY Loc.zByy' (Val.cnt (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.primeBY Loc.zBy'y (Val.cnt (cnt0 + 1)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.primeBY
        ((primeBYLoop I).seq C2,
          Function.update (Function.update φ PrimeBY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeBY.Vars.b v) rest N = (.stuck, σ1, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeBYLoop, PrimeBY.Vocab,
    PrimeBY.evalB, hb, if_true, PrimeBY.evalV, primeBYLoopBody, PrimeBY.body,
    hcnt0, PrimeBY.eval, Prod.mk.injEq] at h
  cases s with
  | nil =>
      simp only [Command.step] at h
      exact absurd h.2.2.1 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.step, PrimeBY.X, Finset.mem_insert,
        Finset.mem_singleton] at h
      split_ifs at h with hc
      · simp only [Command.step] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨c, rest, _, ?_, rfl, h2.symm, ?_⟩
        · simp only [PrimeBY.X, Finset.mem_insert, Finset.mem_singleton]; exact hc
        · change Command.runFuel Tid.primeBY
              ((Command.whileLoop PrimeBY.BExpr.isB
                  (Command.seq (Command.seq (Command.assign PrimeBY.Vars.cnt PrimeBY.Expr.nextCnt)
                      (Command.seq (Command.write Loc.yB' PrimeBY.VExpr.yPrimeTag)
                        (Command.seq (Command.write Loc.zByy' PrimeBY.VExpr.cntVal)
                          (Command.read Loc.zBy'y PrimeBY.VExpr.cntVal))))
                    (Command.ndetAssign PrimeBY.Vars.b PrimeBY.X PrimeBY.X_nonempty))).seq C2,
                Function.update (Function.update φ PrimeBY.Vars.cnt (Sum.inl (cnt0 + 1)))
                  PrimeBY.Vars.b c) rest N = _
          exact Prod.ext h1 (Prod.ext rfl (Prod.ext h3 h4))
      · exact absurd h.2.2.1 (by rintro ⟨⟩)

/-- One `Command.step` of `PrimeBY.program`'s leading `NDet({⊥,⊤})` draw,
against the empty resolution (by `rfl`). -/
theorem primeBY_lead_hstep_nil (I : PCPInstance) :
    Command.step Tid.primeBY (PrimeBY.program I)
      ((PrimeBY.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      ([] : List PrimeBY.Vals) = none := rfl

/-- One `Command.step` of `PrimeBY.program`'s leading draw, against a
resolution with a head not in `PrimeBY.X`. -/
theorem primeBY_lead_hstep_inl (I : PCPInstance) (k : Fin 4)
    (rest : List PrimeBY.Vals) :
    Command.step Tid.primeBY (PrimeBY.program I)
      ((PrimeBY.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      (Sum.inl k :: rest) = none := rfl

/-- The converse of `PrimeBY.program`'s leading `NDet({⊥,⊤})` draw. -/
theorem primeBY_lead_step_inv (I : PCPInstance) (s : List PrimeBY.Vals) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeBY)) (φ' : (PrimeBY.Vocab I).Store)
    (h : Command.runFuel Tid.primeBY (PrimeBY.program I, (PrimeBY.Vocab I).mkStore
      (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0)) s
      (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (b0 : Bool) (rest : List PrimeBY.Vals),
      s = Sum.inr b0 :: rest ∧
      Command.runFuel Tid.primeBY
        ((primeBYLoop I).seq Command.term,
          Function.update ((PrimeBY.Vocab I).mkStore
            (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
            PrimeBY.Vars.b (Sum.inr b0)) rest N = (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel] at h
      have h2 := primeBY_lead_hstep_nil I ▸ h
      dsimp only at h2
      have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
      exact absurd h3 (by rintro ⟨⟩)
  | cons c rest =>
      rcases c with k | b0
      · simp only [Command.runFuel] at h
        have h2 := primeBY_lead_hstep_inl I k rest ▸ h
        dsimp only at h2
        have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
        exact absurd h3 (by rintro ⟨⟩)
      · rcases b0 with rfl | rfl
        · simp only [Command.runFuel] at h
          exact ⟨false, rest, rfl, h⟩
        · simp only [Command.runFuel] at h
          exact ⟨true, rest, rfl, h⟩

/-- The converse of `primeBY_stop_step`. -/
theorem primeBY_stop_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (PrimeBY.Vocab I)) (s : List PrimeBY.Vals)
    (φ : (PrimeBY.Vocab I).Store) (hb : φ PrimeBY.Vars.b = Sum.inr false) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeBY)) (φ' : (PrimeBY.Vocab I).Store)
    (h : Command.runFuel Tid.primeBY ((primeBYLoop I).seq C2, φ) s (N + 2) =
      (.stuck, σ, (Command.term, φ'), [])) :
    Command.runFuel Tid.primeBY (C2, φ) s N = (.stuck, σ, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeBYLoop, PrimeBY.Vocab,
    PrimeBY.evalB, hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))

/-- The converse of `primeBY_shape`. By strong induction on `s.length`. -/
theorem primeBY_loop_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List PrimeBY.Vals), s.length = n →
      ∀ (φ : (PrimeBY.Vocab I).Store) (cnt0 : Fin 4)
        (_hb : φ PrimeBY.Vars.b = Sum.inr true)
        (_hcnt0 : φ PrimeBY.Vars.cnt = Sum.inl cnt0)
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.primeBY))
        (φ' : (PrimeBY.Vocab I).Store),
        Command.runFuel Tid.primeBY ((primeBYLoop I).seq Command.term, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (M' : ℕ) (vals : List (Val I)),
          s = List.replicate M' (Sum.inr true) ++ [Sum.inr false] ∧
          vals.length = M' + 1 ∧
          (∀ i, i < vals.length →
            vals[i]? = some (Val.cnt (⟨(cnt0.val + i + 1) % 4, by omega⟩ : Fin 4))) ∧
          σ = primeBYBlockWord I vals := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen φ cnt0 hb hcnt0 N σ φ' h
    have h11 := Command.runFuel_stuck_stable h 11
    obtain ⟨v, rest, σ1, hvmem, hseq, hσeq, h2⟩ :=
      primeBY_iter_step_inv I Command.term s φ hb cnt0 hcnt0 N σ φ' h11
    subst hseq
    simp only [PrimeBY.X, Finset.mem_insert, Finset.mem_singleton] at hvmem
    rcases hvmem with rfl | rfl
    · have h2' := Command.runFuel_stuck_stable h2 2
      have hbf : Function.update (Function.update φ PrimeBY.Vars.cnt (Sum.inl (cnt0 + 1)))
          PrimeBY.Vars.b (Sum.inr false) PrimeBY.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h3 := primeBY_stop_step_inv I Command.term rest _ hbf N σ1 φ' h2'
      have hrest : rest = [] ∧ σ1 = ([] : Word (ThreadLabel (domainOf I) Tid.primeBY)) := by
        rcases N with _ | N'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ10⟩ := hrest
      subst hrest0
      refine ⟨0, [Val.cnt (cnt0 + 1)], rfl, rfl, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        congr 1
      · simp only [hσeq, hσ10, List.append_nil, primeBYBlockWord]
        rfl
    · have hrest_len : rest.length < n := by
        have heq : (Sum.inr true :: rest).length = n := hslen
        simp only [List.length_cons] at heq
        omega
      have hbnew : Function.update (Function.update φ PrimeBY.Vars.cnt (Sum.inl (cnt0 + 1)))
          PrimeBY.Vars.b (Sum.inr true) PrimeBY.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hne_cntb : PrimeBY.Vars.cnt ≠ PrimeBY.Vars.b := by decide
      have hcntnew :
          Function.update (Function.update φ PrimeBY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeBY.Vars.b (Sum.inr true) PrimeBY.Vars.cnt = Sum.inl (cnt0 + 1) :=
        (Function.update_of_ne hne_cntb (Sum.inr true) _).trans (Function.update_self _ _ _)
      obtain ⟨M'', vals'', hrest_eq, hvals_len, hvals_val, hσ1⟩ :=
        ih rest.length hrest_len rest rfl
          (Function.update (Function.update φ PrimeBY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeBY.Vars.b (Sum.inr true))
          (cnt0 + 1) hbnew hcntnew N σ1 φ' h2
      refine ⟨M'' + 1, Val.cnt (cnt0 + 1) :: vals'', ?_, ?_, ?_, ?_⟩
      · rw [hrest_eq, List.replicate_succ, List.cons_append]
      · simp [hvals_len]
      · intro i hi
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq]
            congr 1
        | succ i =>
            simp only [List.length_cons] at hi
            have hi' : i < vals''.length := by omega
            have hval' := hvals_val i hi'
            simp only [List.getElem?_cons_succ]
            rw [hval']
            congr 2
            apply Fin.ext
            simp [Fin.add_def]
            omega
      · rw [hσeq, hσ1]
        simp only [primeBYBlockWord]
        rfl

/-- **The word characterization of the threads, `PrimeBY`.** The converse of
`primeBY_general_run`: the word of a term-reaching run of `PrimeBY.program`
is `primeBYBlockWord` of the values written to `zByy'`. -/
theorem primeBY_shape_inv (I : PCPInstance) {s : List PrimeBY.Vals}
    {φ' : (PrimeBY.Vocab I).Store} {cLast : Config (domainOf I) (PrimeBY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.primeBY)}
    (hrun : Command.Run Tid.primeBY s
      (PrimeBY.program I, (PrimeBY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      σ cLast [] (Command.term, φ')) :
    ∃ (M : ℕ) (vals : List (Val I)),
      s = List.replicate M (Sum.inr true) ++ [Sum.inr false] ∧
      vals.length = M ∧
      (∀ i, i < vals.length → vals[i]? = some (Val.cnt (⟨(i + 1) % 4, by omega⟩ : Fin 4))) ∧
      σ = primeBYBlockWord I vals := by
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨b0, rest, hs, h2⟩ := primeBY_lead_step_inv I s n σ φ' hn2
  cases b0 with
  | false =>
      have hbf : Function.update ((PrimeBY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeBY.Vars.b (Sum.inr false) PrimeBY.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h2' := Command.runFuel_stuck_stable h2 2
      have h3 := primeBY_stop_step_inv I Command.term rest _ hbf n σ φ' h2'
      have hrest : rest = [] ∧ σ = ([] : Word (ThreadLabel (domainOf I) Tid.primeBY)) := by
        rcases n with _ | n'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ0⟩ := hrest
      refine ⟨0, [], ?_, rfl, ?_, ?_⟩
      · simp [hs, hrest0]
      · intro i hi; simp at hi
      · simp only [hσ0, primeBYBlockWord]; rfl
  | true =>
      have hb2 : Function.update ((PrimeBY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeBY.Vars.b (Sum.inr true) PrimeBY.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hcnt2 : Function.update ((PrimeBY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeBY.Vars.b (Sum.inr true) PrimeBY.Vars.cnt = Sum.inl (0 : Fin 4) := by
        have hne : PrimeBY.Vars.cnt ≠ PrimeBY.Vars.b := by decide
        exact Function.update_of_ne hne _ _
      obtain ⟨M', vals, hrest_eq, hvals_len, hvals_val, hσeq⟩ :=
        primeBY_loop_shape_inv I rest.length rest rfl _ 0 hb2 hcnt2 n σ φ' h2
      refine ⟨M' + 1, vals, ?_, ?_, ?_, hσeq⟩
      · rw [hs, hrest_eq, List.replicate_succ, List.cons_append]
      · omega
      · intro i hi
        have := hvals_val i hi
        simpa using this


/-! ## `PrimeAY`

As for `PrimeAX`. -/

/-- The converse of `primeAY_iter_step`. -/
theorem primeAY_iter_step_inv (I : PCPInstance) (C2 : Command (domainOf I) (PrimeAY.Vocab I))
    (s : List PrimeAY.Vals) (φ : (PrimeAY.Vocab I).Store)
    (hb : φ PrimeAY.Vars.b = Sum.inr true) (cnt0 : Fin 4)
    (hcnt0 : φ PrimeAY.Vars.cnt = Sum.inl cnt0) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeAY)) (φ' : (PrimeAY.Vocab I).Store)
    (h : Command.runFuel Tid.primeAY ((primeAYLoop I).seq C2, φ) s (N + 11) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v : PrimeAY.Vals) (rest : List PrimeAY.Vals)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.primeAY)),
      v ∈ PrimeAY.X ∧
      s = v :: rest ∧
      σ = [ ⟨EventLabel.wt Tid.primeAY Loc.yA' (Val.primeTag Tid.primeAY 0), rfl⟩
          , ⟨EventLabel.wt Tid.primeAY Loc.zAyy' (Val.cnt (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.primeAY Loc.zAy'y (Val.cnt (cnt0 + 1)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.primeAY
        ((primeAYLoop I).seq C2,
          Function.update (Function.update φ PrimeAY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeAY.Vars.b v) rest N = (.stuck, σ1, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeAYLoop, PrimeAY.Vocab,
    PrimeAY.evalB, hb, if_true, PrimeAY.evalV, primeAYLoopBody, PrimeAY.body,
    hcnt0, PrimeAY.eval, Prod.mk.injEq] at h
  cases s with
  | nil =>
      simp only [Command.step] at h
      exact absurd h.2.2.1 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.step, PrimeAY.X, Finset.mem_insert,
        Finset.mem_singleton] at h
      split_ifs at h with hc
      · simp only [Command.step] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨c, rest, _, ?_, rfl, h2.symm, ?_⟩
        · simp only [PrimeAY.X, Finset.mem_insert, Finset.mem_singleton]; exact hc
        · change Command.runFuel Tid.primeAY
              ((Command.whileLoop PrimeAY.BExpr.isB
                  (Command.seq (Command.seq (Command.assign PrimeAY.Vars.cnt PrimeAY.Expr.nextCnt)
                      (Command.seq (Command.write Loc.yA' PrimeAY.VExpr.yPrimeTag)
                        (Command.seq (Command.write Loc.zAyy' PrimeAY.VExpr.cntVal)
                          (Command.read Loc.zAy'y PrimeAY.VExpr.cntVal))))
                    (Command.ndetAssign PrimeAY.Vars.b PrimeAY.X PrimeAY.X_nonempty))).seq C2,
                Function.update (Function.update φ PrimeAY.Vars.cnt (Sum.inl (cnt0 + 1)))
                  PrimeAY.Vars.b c) rest N = _
          exact Prod.ext h1 (Prod.ext rfl (Prod.ext h3 h4))
      · exact absurd h.2.2.1 (by rintro ⟨⟩)

/-- See `primeAX_lead_hstep_nil`. -/
theorem primeAY_lead_hstep_nil (I : PCPInstance) :
    Command.step Tid.primeAY (PrimeAY.program I)
      ((PrimeAY.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      ([] : List PrimeAY.Vals) = none := rfl

/-- See `primeAX_lead_hstep_inl`. -/
theorem primeAY_lead_hstep_inl (I : PCPInstance) (k : Fin 4)
    (rest : List PrimeAY.Vals) :
    Command.step Tid.primeAY (PrimeAY.program I)
      ((PrimeAY.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      (Sum.inl k :: rest) = none := rfl

/-- The converse of `PrimeAY.program`'s leading `NDet({⊥,⊤})` draw. -/
theorem primeAY_lead_step_inv (I : PCPInstance) (s : List PrimeAY.Vals) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeAY)) (φ' : (PrimeAY.Vocab I).Store)
    (h : Command.runFuel Tid.primeAY (PrimeAY.program I, (PrimeAY.Vocab I).mkStore
      (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0)) s
      (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (b0 : Bool) (rest : List PrimeAY.Vals),
      s = Sum.inr b0 :: rest ∧
      Command.runFuel Tid.primeAY
        ((primeAYLoop I).seq Command.term,
          Function.update ((PrimeAY.Vocab I).mkStore
            (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
            PrimeAY.Vars.b (Sum.inr b0)) rest N = (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel] at h
      have h2 := primeAY_lead_hstep_nil I ▸ h
      dsimp only at h2
      have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
      exact absurd h3 (by rintro ⟨⟩)
  | cons c rest =>
      rcases c with k | b0
      · simp only [Command.runFuel] at h
        have h2 := primeAY_lead_hstep_inl I k rest ▸ h
        dsimp only at h2
        have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
        exact absurd h3 (by rintro ⟨⟩)
      · rcases b0 with rfl | rfl
        · simp only [Command.runFuel] at h
          exact ⟨false, rest, rfl, h⟩
        · simp only [Command.runFuel] at h
          exact ⟨true, rest, rfl, h⟩

/-- The converse of `primeAY_stop_step`. -/
theorem primeAY_stop_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (PrimeAY.Vocab I)) (s : List PrimeAY.Vals)
    (φ : (PrimeAY.Vocab I).Store) (hb : φ PrimeAY.Vars.b = Sum.inr false) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeAY)) (φ' : (PrimeAY.Vocab I).Store)
    (h : Command.runFuel Tid.primeAY ((primeAYLoop I).seq C2, φ) s (N + 2) =
      (.stuck, σ, (Command.term, φ'), [])) :
    Command.runFuel Tid.primeAY (C2, φ) s N = (.stuck, σ, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeAYLoop, PrimeAY.Vocab,
    PrimeAY.evalB, hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))

/-- The converse of `primeAY_shape`. -/
theorem primeAY_loop_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List PrimeAY.Vals), s.length = n →
      ∀ (φ : (PrimeAY.Vocab I).Store) (cnt0 : Fin 4)
        (_hb : φ PrimeAY.Vars.b = Sum.inr true)
        (_hcnt0 : φ PrimeAY.Vars.cnt = Sum.inl cnt0)
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.primeAY))
        (φ' : (PrimeAY.Vocab I).Store),
        Command.runFuel Tid.primeAY ((primeAYLoop I).seq Command.term, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (M' : ℕ) (vals : List (Val I)),
          s = List.replicate M' (Sum.inr true) ++ [Sum.inr false] ∧
          vals.length = M' + 1 ∧
          (∀ i, i < vals.length →
            vals[i]? = some (Val.cnt (⟨(cnt0.val + i + 1) % 4, by omega⟩ : Fin 4))) ∧
          σ = primeAYBlockWord I vals := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen φ cnt0 hb hcnt0 N σ φ' h
    have h11 := Command.runFuel_stuck_stable h 11
    obtain ⟨v, rest, σ1, hvmem, hseq, hσeq, h2⟩ :=
      primeAY_iter_step_inv I Command.term s φ hb cnt0 hcnt0 N σ φ' h11
    subst hseq
    simp only [PrimeAY.X, Finset.mem_insert, Finset.mem_singleton] at hvmem
    rcases hvmem with rfl | rfl
    · have h2' := Command.runFuel_stuck_stable h2 2
      have hbf : Function.update (Function.update φ PrimeAY.Vars.cnt (Sum.inl (cnt0 + 1)))
          PrimeAY.Vars.b (Sum.inr false) PrimeAY.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h3 := primeAY_stop_step_inv I Command.term rest _ hbf N σ1 φ' h2'
      have hrest : rest = [] ∧ σ1 = ([] : Word (ThreadLabel (domainOf I) Tid.primeAY)) := by
        rcases N with _ | N'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ10⟩ := hrest
      subst hrest0
      refine ⟨0, [Val.cnt (cnt0 + 1)], rfl, rfl, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        congr 1
      · simp only [hσeq, hσ10, List.append_nil, primeAYBlockWord]
        rfl
    · have hrest_len : rest.length < n := by
        have heq : (Sum.inr true :: rest).length = n := hslen
        simp only [List.length_cons] at heq
        omega
      have hbnew : Function.update (Function.update φ PrimeAY.Vars.cnt (Sum.inl (cnt0 + 1)))
          PrimeAY.Vars.b (Sum.inr true) PrimeAY.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hne_cntb : PrimeAY.Vars.cnt ≠ PrimeAY.Vars.b := by decide
      have hcntnew :
          Function.update (Function.update φ PrimeAY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeAY.Vars.b (Sum.inr true) PrimeAY.Vars.cnt = Sum.inl (cnt0 + 1) :=
        (Function.update_of_ne hne_cntb (Sum.inr true) _).trans (Function.update_self _ _ _)
      obtain ⟨M'', vals'', hrest_eq, hvals_len, hvals_val, hσ1⟩ :=
        ih rest.length hrest_len rest rfl
          (Function.update (Function.update φ PrimeAY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeAY.Vars.b (Sum.inr true))
          (cnt0 + 1) hbnew hcntnew N σ1 φ' h2
      refine ⟨M'' + 1, Val.cnt (cnt0 + 1) :: vals'', ?_, ?_, ?_, ?_⟩
      · rw [hrest_eq, List.replicate_succ, List.cons_append]
      · simp [hvals_len]
      · intro i hi
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq]
            congr 1
        | succ i =>
            simp only [List.length_cons] at hi
            have hi' : i < vals''.length := by omega
            have hval' := hvals_val i hi'
            simp only [List.getElem?_cons_succ]
            rw [hval']
            congr 2
            apply Fin.ext
            simp [Fin.add_def]
            omega
      · rw [hσeq, hσ1]
        simp only [primeAYBlockWord]
        rfl

/-- **The word characterization of the threads, `PrimeAY`.** The converse of
`primeAY_general_run`: the word of a term-reaching run of `PrimeAY.program`
is `primeAYBlockWord` of the values written to `zAyy'`. -/
theorem primeAY_shape_inv (I : PCPInstance) {s : List PrimeAY.Vals}
    {φ' : (PrimeAY.Vocab I).Store} {cLast : Config (domainOf I) (PrimeAY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.primeAY)}
    (hrun : Command.Run Tid.primeAY s
      (PrimeAY.program I, (PrimeAY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      σ cLast [] (Command.term, φ')) :
    ∃ (M : ℕ) (vals : List (Val I)),
      s = List.replicate M (Sum.inr true) ++ [Sum.inr false] ∧
      vals.length = M ∧
      (∀ i, i < vals.length → vals[i]? = some (Val.cnt (⟨(i + 1) % 4, by omega⟩ : Fin 4))) ∧
      σ = primeAYBlockWord I vals := by
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨b0, rest, hs, h2⟩ := primeAY_lead_step_inv I s n σ φ' hn2
  cases b0 with
  | false =>
      have hbf : Function.update ((PrimeAY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeAY.Vars.b (Sum.inr false) PrimeAY.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h2' := Command.runFuel_stuck_stable h2 2
      have h3 := primeAY_stop_step_inv I Command.term rest _ hbf n σ φ' h2'
      have hrest : rest = [] ∧ σ = ([] : Word (ThreadLabel (domainOf I) Tid.primeAY)) := by
        rcases n with _ | n'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ0⟩ := hrest
      refine ⟨0, [], ?_, rfl, ?_, ?_⟩
      · simp [hs, hrest0]
      · intro i hi; simp at hi
      · simp only [hσ0, primeAYBlockWord]; rfl
  | true =>
      have hb2 : Function.update ((PrimeAY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeAY.Vars.b (Sum.inr true) PrimeAY.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hcnt2 : Function.update ((PrimeAY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeAY.Vars.b (Sum.inr true) PrimeAY.Vars.cnt = Sum.inl (0 : Fin 4) := by
        have hne : PrimeAY.Vars.cnt ≠ PrimeAY.Vars.b := by decide
        exact Function.update_of_ne hne _ _
      obtain ⟨M', vals, hrest_eq, hvals_len, hvals_val, hσeq⟩ :=
        primeAY_loop_shape_inv I rest.length rest rfl _ 0 hb2 hcnt2 n σ φ' h2
      refine ⟨M' + 1, vals, ?_, ?_, ?_, hσeq⟩
      · rw [hs, hrest_eq, List.replicate_succ, List.cons_append]
      · omega
      · intro i hi
        have := hvals_val i hi
        simpa using this

/-! ## `PrimeBX`

As for `PrimeAX`, inverting `primeBX_iter_step_val`, which tracks the value
written. -/

/-- The converse of `primeBX_iter_step_val`. -/
theorem primeBX_iter_step_inv (I : PCPInstance) (C2 : Command (domainOf I) (PrimeBX.Vocab I))
    (s : List PrimeBX.Vals) (φ : (PrimeBX.Vocab I).Store)
    (hb : φ PrimeBX.Vars.b = Sum.inr true) (cnt0 : Fin 4)
    (hcnt0 : φ PrimeBX.Vars.cnt = Sum.inl cnt0) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeBX)) (φ' : (PrimeBX.Vocab I).Store)
    (h : Command.runFuel Tid.primeBX ((primeBXLoop I).seq C2, φ) s (N + 11) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v : PrimeBX.Vals) (rest : List PrimeBX.Vals)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.primeBX)),
      v ∈ PrimeBX.X ∧
      s = v :: rest ∧
      σ = [ ⟨EventLabel.wt Tid.primeBX Loc.xB' (Val.primeTag Tid.primeBX 0), rfl⟩
          , ⟨EventLabel.wt Tid.primeBX Loc.zBxx' (Val.cnt (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.primeBX Loc.zBx'x (Val.cnt (cnt0 + 1)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.primeBX
        ((primeBXLoop I).seq C2,
          Function.update (Function.update φ PrimeBX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeBX.Vars.b v) rest N = (.stuck, σ1, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeBXLoop, PrimeBX.Vocab,
    PrimeBX.evalB, hb, if_true, PrimeBX.evalV, primeBXLoopBody, PrimeBX.body,
    hcnt0, PrimeBX.eval, Prod.mk.injEq] at h
  cases s with
  | nil =>
      simp only [Command.step] at h
      exact absurd h.2.2.1 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.step, PrimeBX.X, Finset.mem_insert,
        Finset.mem_singleton] at h
      split_ifs at h with hc
      · simp only [Command.step] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨c, rest, _, ?_, rfl, h2.symm, ?_⟩
        · simp only [PrimeBX.X, Finset.mem_insert, Finset.mem_singleton]; exact hc
        · change Command.runFuel Tid.primeBX
              ((Command.whileLoop PrimeBX.BExpr.isB
                  (Command.seq (Command.seq (Command.assign PrimeBX.Vars.cnt PrimeBX.Expr.nextCnt)
                      (Command.seq (Command.write Loc.xB' PrimeBX.VExpr.xPrimeTag)
                        (Command.seq (Command.write Loc.zBxx' PrimeBX.VExpr.cntVal)
                          (Command.read Loc.zBx'x PrimeBX.VExpr.cntVal))))
                    (Command.ndetAssign PrimeBX.Vars.b PrimeBX.X PrimeBX.X_nonempty))).seq C2,
                Function.update (Function.update φ PrimeBX.Vars.cnt (Sum.inl (cnt0 + 1)))
                  PrimeBX.Vars.b c) rest N = _
          exact Prod.ext h1 (Prod.ext rfl (Prod.ext h3 h4))
      · exact absurd h.2.2.1 (by rintro ⟨⟩)

/-- See `primeAX_lead_hstep_nil`. -/
theorem primeBX_lead_hstep_nil (I : PCPInstance) :
    Command.step Tid.primeBX (PrimeBX.program I)
      ((PrimeBX.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      ([] : List PrimeBX.Vals) = none := rfl

/-- See `primeAX_lead_hstep_inl`. -/
theorem primeBX_lead_hstep_inl (I : PCPInstance) (k : Fin 4)
    (rest : List PrimeBX.Vals) :
    Command.step Tid.primeBX (PrimeBX.program I)
      ((PrimeBX.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      (Sum.inl k :: rest) = none := rfl

/-- The reverse direction of `PrimeBX.program`'s leading `NDet({⊥,⊤})`
draw. Mirrors `primeAX_lead_step_inv` exactly. -/
theorem primeBX_lead_step_inv (I : PCPInstance) (s : List PrimeBX.Vals) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeBX)) (φ' : (PrimeBX.Vocab I).Store)
    (h : Command.runFuel Tid.primeBX (PrimeBX.program I, (PrimeBX.Vocab I).mkStore
      (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0)) s
      (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (b0 : Bool) (rest : List PrimeBX.Vals),
      s = Sum.inr b0 :: rest ∧
      Command.runFuel Tid.primeBX
        ((primeBXLoop I).seq Command.term,
          Function.update ((PrimeBX.Vocab I).mkStore
            (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
            PrimeBX.Vars.b (Sum.inr b0)) rest N = (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel] at h
      have h2 := primeBX_lead_hstep_nil I ▸ h
      dsimp only at h2
      have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
      exact absurd h3 (by rintro ⟨⟩)
  | cons c rest =>
      rcases c with k | b0
      · simp only [Command.runFuel] at h
        have h2 := primeBX_lead_hstep_inl I k rest ▸ h
        dsimp only at h2
        have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
        exact absurd h3 (by rintro ⟨⟩)
      · rcases b0 with rfl | rfl
        · simp only [Command.runFuel] at h
          exact ⟨false, rest, rfl, h⟩
        · simp only [Command.runFuel] at h
          exact ⟨true, rest, rfl, h⟩

/-- See `primeAX_stop_step_inv`. -/
theorem primeBX_stop_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (PrimeBX.Vocab I)) (s : List PrimeBX.Vals)
    (φ : (PrimeBX.Vocab I).Store) (hb : φ PrimeBX.Vars.b = Sum.inr false) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeBX)) (φ' : (PrimeBX.Vocab I).Store)
    (h : Command.runFuel Tid.primeBX ((primeBXLoop I).seq C2, φ) s (N + 2) =
      (.stuck, σ, (Command.term, φ'), [])) :
    Command.runFuel Tid.primeBX (C2, φ) s N = (.stuck, σ, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeBXLoop, PrimeBX.Vocab,
    PrimeBX.evalB, hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))

/-- The converse of `primeBX_shape_val`, tracking the values written. By strong
induction on `s.length`. -/
theorem primeBX_loop_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List PrimeBX.Vals), s.length = n →
      ∀ (φ : (PrimeBX.Vocab I).Store) (cnt0 : Fin 4)
        (_hb : φ PrimeBX.Vars.b = Sum.inr true)
        (_hcnt0 : φ PrimeBX.Vars.cnt = Sum.inl cnt0)
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.primeBX))
        (φ' : (PrimeBX.Vocab I).Store),
        Command.runFuel Tid.primeBX ((primeBXLoop I).seq Command.term, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (M' : ℕ) (vals : List (Val I)),
          s = List.replicate M' (Sum.inr true) ++ [Sum.inr false] ∧
          vals.length = M' + 1 ∧
          (∀ i, i < vals.length →
            vals[i]? = some (Val.cnt (⟨(cnt0.val + i + 1) % 4, by omega⟩ : Fin 4))) ∧
          σ = primeBXBlockWord I vals := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen φ cnt0 hb hcnt0 N σ φ' h
    have h11 := Command.runFuel_stuck_stable h 11
    obtain ⟨v, rest, σ1, hvmem, hseq, hσeq, h2⟩ :=
      primeBX_iter_step_inv I Command.term s φ hb cnt0 hcnt0 N σ φ' h11
    subst hseq
    simp only [PrimeBX.X, Finset.mem_insert, Finset.mem_singleton] at hvmem
    rcases hvmem with rfl | rfl
    · have h2' := Command.runFuel_stuck_stable h2 2
      have hbf : Function.update (Function.update φ PrimeBX.Vars.cnt (Sum.inl (cnt0 + 1)))
          PrimeBX.Vars.b (Sum.inr false) PrimeBX.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h3 := primeBX_stop_step_inv I Command.term rest _ hbf N σ1 φ' h2'
      have hrest : rest = [] ∧ σ1 = ([] : Word (ThreadLabel (domainOf I) Tid.primeBX)) := by
        rcases N with _ | N'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ10⟩ := hrest
      subst hrest0
      refine ⟨0, [Val.cnt (cnt0 + 1)], rfl, rfl, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp only [List.getElem?_cons_zero, Option.some.injEq]
        congr 1
      · simp only [hσeq, hσ10, List.append_nil, primeBXBlockWord]
        rfl
    · have hrest_len : rest.length < n := by
        have heq : (Sum.inr true :: rest).length = n := hslen
        simp only [List.length_cons] at heq
        omega
      have hbnew : Function.update (Function.update φ PrimeBX.Vars.cnt (Sum.inl (cnt0 + 1)))
          PrimeBX.Vars.b (Sum.inr true) PrimeBX.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hne_cntb : PrimeBX.Vars.cnt ≠ PrimeBX.Vars.b := by decide
      have hcntnew :
          Function.update (Function.update φ PrimeBX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeBX.Vars.b (Sum.inr true) PrimeBX.Vars.cnt = Sum.inl (cnt0 + 1) :=
        (Function.update_of_ne hne_cntb (Sum.inr true) _).trans (Function.update_self _ _ _)
      obtain ⟨M'', vals'', hrest_eq, hvals_len, hvals_val, hσ1⟩ :=
        ih rest.length hrest_len rest rfl
          (Function.update (Function.update φ PrimeBX.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeBX.Vars.b (Sum.inr true))
          (cnt0 + 1) hbnew hcntnew N σ1 φ' h2
      refine ⟨M'' + 1, Val.cnt (cnt0 + 1) :: vals'', ?_, ?_, ?_, ?_⟩
      · rw [hrest_eq, List.replicate_succ, List.cons_append]
      · simp [hvals_len]
      · intro i hi
        cases i with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq]
            congr 1
        | succ i =>
            simp only [List.length_cons] at hi
            have hi' : i < vals''.length := by omega
            have hval' := hvals_val i hi'
            simp only [List.getElem?_cons_succ]
            rw [hval']
            congr 2
            apply Fin.ext
            simp [Fin.add_def]
            omega
      · rw [hσeq, hσ1]
        simp only [primeBXBlockWord]
        rfl

/-- **The word characterization of the threads, `PrimeBX`.** The converse of
`primeBX_general_run_val`. -/
theorem primeBX_shape_inv (I : PCPInstance) {s : List PrimeBX.Vals}
    {φ' : (PrimeBX.Vocab I).Store} {cLast : Config (domainOf I) (PrimeBX.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.primeBX)}
    (hrun : Command.Run Tid.primeBX s
      (PrimeBX.program I, (PrimeBX.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      σ cLast [] (Command.term, φ')) :
    ∃ (M : ℕ) (vals : List (Val I)),
      s = List.replicate M (Sum.inr true) ++ [Sum.inr false] ∧
      vals.length = M ∧
      (∀ i, i < vals.length → vals[i]? = some (Val.cnt (⟨(i + 1) % 4, by omega⟩ : Fin 4))) ∧
      σ = primeBXBlockWord I vals := by
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨b0, rest, hs, h2⟩ := primeBX_lead_step_inv I s n σ φ' hn2
  cases b0 with
  | false =>
      have hbf : Function.update ((PrimeBX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeBX.Vars.b (Sum.inr false) PrimeBX.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h2' := Command.runFuel_stuck_stable h2 2
      have h3 := primeBX_stop_step_inv I Command.term rest _ hbf n σ φ' h2'
      have hrest : rest = [] ∧ σ = ([] : Word (ThreadLabel (domainOf I) Tid.primeBX)) := by
        rcases n with _ | n'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ0⟩ := hrest
      refine ⟨0, [], ?_, rfl, ?_, ?_⟩
      · simp [hs, hrest0]
      · intro i hi; simp at hi
      · simp only [hσ0, primeBXBlockWord]; rfl
  | true =>
      have hb2 : Function.update ((PrimeBX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeBX.Vars.b (Sum.inr true) PrimeBX.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hcnt2 : Function.update ((PrimeBX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeBX.Vars.b (Sum.inr true) PrimeBX.Vars.cnt = Sum.inl (0 : Fin 4) := by
        have hne : PrimeBX.Vars.cnt ≠ PrimeBX.Vars.b := by decide
        exact Function.update_of_ne hne _ _
      obtain ⟨M', vals, hrest_eq, hvals_len, hvals_val, hσeq⟩ :=
        primeBX_loop_shape_inv I rest.length rest rfl _ 0 hb2 hcnt2 n σ φ' h2
      refine ⟨M' + 1, vals, ?_, ?_, ?_, hσeq⟩
      · rw [hs, hrest_eq, List.replicate_succ, List.cons_append]
      · omega
      · intro i hi
        have := hvals_val i hi
        simpa using this

/-- One iteration of `guessAXInnerLoop` after the first call, as an
`.outOfFuel` result after exactly 14 steps (with no assumption on the
continuation). -/
theorem guessAX_innerLoop_rest_step_outOfFuel (I : PCPInstance) (rest : List (GuessAX.Vals I))
    (φ : (GuessAX.Vocab I).Store)
    (hguard : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ = true)
    (hfst : φ GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)))
    (k : Fin 4) (hcnt0 : φ GuessAX.Vars.cnt = Sum.inr (Sum.inl k)) :
    ∃ (φ' : (GuessAX.Vocab I).Store),
      φ' GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
      φ' GuessAX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
      φ' GuessAX.Vars.j = GuessAX.eval I GuessAX.Expr.jIncr φ ∧
      φ' GuessAX.Vars.aux = φ GuessAX.Vars.aux ∧
      φ' GuessAX.Vars.cntY = φ GuessAX.Vars.cntY ∧
      φ' GuessAX.Vars.N = φ GuessAX.Vars.N ∧
      Command.runFuel Tid.guessAX (guessAXInnerLoop I, φ) rest 14 =
        (.outOfFuel,
          [ ⟨EventLabel.wt Tid.guessAX Loc.xA
              (Val.xTag (Tid.guessAX, false)
                (GuessAX.jthLetter I (GuessAX.auxOf I φ) (GuessAX.jOf I φ))), rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt (k + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.guessAX Loc.zAxx' (Val.cnt k), rfl⟩ ],
          (guessAXInnerLoop I, φ'), rest) := by
  set φ1 : (GuessAX.Vocab I).Store :=
    Function.update φ GuessAX.Vars.prev (GuessAX.eval I GuessAX.Expr.readCnt φ) with hφ1
  set φ2 : (GuessAX.Vocab I).Store :=
    Function.update φ1 GuessAX.Vars.cnt (GuessAX.eval I GuessAX.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 GuessAX.Vars.cnt = φ GuessAX.Vars.cnt := rfl
  have hcntOf_φ1 : GuessAX.cntOf I φ1 = k := by
    simp only [GuessAX.cntOf, hcnt_φ1, hcnt0]
  have hcnt2eq : φ2 GuessAX.Vars.cnt = GuessAX.eval I GuessAX.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2raw : φ2 GuessAX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt2eq, GuessAX.eval, hcntOf_φ1]; rfl
  have hguard' : GuessAX.evalB I GuessAX.BExpr.jLeN φ = true := hguard
  have hne_prev_cnt : GuessAX.Vars.prev ≠ GuessAX.Vars.cnt := by decide
  have hprev_φ1 : GuessAX.prevOf I φ1 = k := by
    simp only [hφ1, GuessAX.prevOf, GuessAX.eval, hcnt0]; rfl
  have hprev_φ2 : GuessAX.prevOf I φ2 = k := by
    have h1x : φ2 GuessAX.Vars.prev = φ1 GuessAX.Vars.prev := Function.update_of_ne hne_prev_cnt _ _
    simp only [GuessAX.prevOf, h1x]
    exact hprev_φ1
  have hne_fst_cnt : GuessAX.Vars.fst ≠ GuessAX.Vars.cnt := by decide
  have hne_fst_prev : GuessAX.Vars.fst ≠ GuessAX.Vars.prev := by decide
  have hfst_φ1 : φ1 GuessAX.Vars.fst = φ GuessAX.Vars.fst := rfl
  have hfst2 : φ2 GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    have h1x : φ2 GuessAX.Vars.fst = φ1 GuessAX.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1x, hfst_φ1, hfst]
  have hisFirst2 : (GuessAX.Vocab I).evalB GuessAX.BExpr.isFirst φ2 = false := by
    simp [GuessAX.Vocab, GuessAX.evalB, hfst2]
  have hisFirst2' : GuessAX.evalB I GuessAX.BExpr.isFirst φ2 = false := hisFirst2
  have hne_aux_cnt : GuessAX.Vars.aux ≠ GuessAX.Vars.cnt := by decide
  have hne_aux_prev : GuessAX.Vars.aux ≠ GuessAX.Vars.prev := by decide
  have haux_φ2 : φ2 GuessAX.Vars.aux = φ GuessAX.Vars.aux := by
    have h1x : φ2 GuessAX.Vars.aux = φ1 GuessAX.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    have h2x : φ1 GuessAX.Vars.aux = φ GuessAX.Vars.aux := Function.update_of_ne hne_aux_prev _ _
    rw [h1x, h2x]
  have hj_φ2 : GuessAX.jOf I φ2 = GuessAX.jOf I φ := by
    have hne1 : GuessAX.Vars.j ≠ GuessAX.Vars.cnt := by decide
    have hne2 : GuessAX.Vars.j ≠ GuessAX.Vars.prev := by decide
    have h1x : φ2 GuessAX.Vars.j = φ1 GuessAX.Vars.j := Function.update_of_ne hne1 _ _
    have h2x : φ1 GuessAX.Vars.j = φ GuessAX.Vars.j := Function.update_of_ne hne2 _ _
    simp only [GuessAX.jOf, h1x, h2x]
  have hxTagRest2 : (GuessAX.Vocab I).evalV GuessAX.VExpr.xTagRest φ2 =
      Val.xTag (Tid.guessAX, false)
        (GuessAX.jthLetter I (GuessAX.auxOf I φ) (GuessAX.jOf I φ)) := by
    simp only [GuessAX.Vocab, GuessAX.evalV, GuessAX.auxOf, haux_φ2, hj_φ2]; rfl
  have hcntVal2 : (GuessAX.Vocab I).evalV GuessAX.VExpr.cntVal φ2 = Val.cnt (k + 1) := by
    have hcnt2 : GuessAX.cntOf I φ2 = k + 1 := by simp only [GuessAX.cntOf, hcnt2raw]
    simp only [GuessAX.Vocab, GuessAX.evalV, hcnt2]; rfl
  have hprevVal2 : (GuessAX.Vocab I).evalV GuessAX.VExpr.prevVal φ2 = Val.cnt k := by
    simp only [GuessAX.Vocab, GuessAX.evalV, hprev_φ2]; rfl
  have h1 : Command.RunStep Tid.guessAX rest none (guessAXInnerLoop I, φ) rest
      (Command.loopSeq (Command.seq (GuessAX.innerBody I)
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [guessAXInnerLoop, Command.step, GuessAX.Vocab, hguard', if_true])
  have h2 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq (GuessAX.innerBody I)
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.assign GuessAX.Vars.cnt GuessAX.Expr.nextCnt)
          (Command.ite GuessAX.BExpr.isFirst
            (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
                (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
                (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ1) := by
    rw [hφ1]
    exact Command.step_sound _ _ _ _ _ _ _ (by
      simp only [GuessAX.innerBody, Command.firstIt, Command.step, GuessAX.Vocab]; rfl)
  have h3 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.assign GuessAX.Vars.cnt GuessAX.Expr.nextCnt)
          (Command.ite GuessAX.BExpr.isFirst
            (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
                (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
                (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ1) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessAX.Vars.cnt GuessAX.Expr.nextCnt)
          (Command.ite GuessAX.BExpr.isFirst
            (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
                (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
                (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ1) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h4 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessAX.Vars.cnt GuessAX.Expr.nextCnt)
          (Command.ite GuessAX.BExpr.isFirst
            (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
                (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
                (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ1) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.ite GuessAX.BExpr.isFirst
          (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
              (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
              (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) := by
    rw [hφ2]
    exact Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessAX.Vocab])
  have h5 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.ite GuessAX.BExpr.isFirst
          (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
              (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
              (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.ite GuessAX.BExpr.isFirst
          (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
              (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
              (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h6 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        (Command.ite GuessAX.BExpr.isFirst
          (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
              (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
              (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
          (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
            (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [Command.step, GuessAX.Vocab, hisFirst2']; rfl)
  have h7 : Command.RunStep Tid.guessAX rest
      (some ⟨EventLabel.wt Tid.guessAX Loc.xA ((GuessAX.Vocab I).evalV GuessAX.VExpr.xTagRest φ2),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
          (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
            (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
            (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h8 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
            (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
          (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h9 : Command.RunStep Tid.guessAX rest
      (some ⟨EventLabel.wt Tid.guessAX Loc.zAx'x ((GuessAX.Vocab I).evalV GuessAX.VExpr.cntVal φ2),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
          (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h10 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h11 : Command.RunStep Tid.guessAX rest
      (some ⟨EventLabel.rd Tid.guessAX Loc.zAxx' ((GuessAX.Vocab I).evalV GuessAX.VExpr.prevVal φ2),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        Command.skip (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I),
        φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h12 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        Command.skip (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I),
        φ2) rest
      (Command.loopSeq (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr) (guessAXInnerLoop I),
        φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h13 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr) (guessAXInnerLoop I),
        φ2) rest
      (Command.loopSeq Command.skip (guessAXInnerLoop I),
        Function.update φ2 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ2)) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessAX.Vocab])
  have h14 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq Command.skip (guessAXInnerLoop I),
        Function.update φ2 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ2)) rest
      (guessAXInnerLoop I,
        Function.update φ2 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ2)) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  have w2 := Command.step_complete h2
  have w3 := Command.step_complete h3
  have w4 := Command.step_complete h4
  have w5 := Command.step_complete h5
  have w6 := Command.step_complete h6
  have w7 := Command.step_complete h7
  have w8 := Command.step_complete h8
  have w9 := Command.step_complete h9
  have w10 := Command.step_complete h10
  have w11 := Command.step_complete h11
  have w12 := Command.step_complete h12
  have w13 := Command.step_complete h13
  have w14 := Command.step_complete h14
  set φ3 : (GuessAX.Vocab I).Store :=
    Function.update φ2 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ2) with hφ3
  have hfst3 : φ3 GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    have hne : GuessAX.Vars.fst ≠ GuessAX.Vars.j := by decide
    simp only [hφ3, Function.update_of_ne hne]; exact hfst2
  have hcnt3 : φ3 GuessAX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    have hne : GuessAX.Vars.cnt ≠ GuessAX.Vars.j := by decide
    simp only [hφ3, Function.update_of_ne hne]; exact hcnt2raw
  have hj3 : φ3 GuessAX.Vars.j = GuessAX.eval I GuessAX.Expr.jIncr φ2 := by
    rw [hφ3]; exact Function.update_self _ _ _
  have hj3' : φ3 GuessAX.Vars.j = GuessAX.eval I GuessAX.Expr.jIncr φ := by
    rw [hj3]; simp only [GuessAX.eval, hj_φ2]; rfl
  have haux3 : φ3 GuessAX.Vars.aux = φ GuessAX.Vars.aux := by
    have hne : GuessAX.Vars.aux ≠ GuessAX.Vars.j := by decide
    simp only [hφ3, Function.update_of_ne hne]; exact haux_φ2
  have hcntY_φ2 : φ2 GuessAX.Vars.cntY = φ GuessAX.Vars.cntY := by
    have hne_cnt : GuessAX.Vars.cntY ≠ GuessAX.Vars.cnt := by decide
    have hne_prev : GuessAX.Vars.cntY ≠ GuessAX.Vars.prev := by decide
    have hh1 : φ2 GuessAX.Vars.cntY = φ1 GuessAX.Vars.cntY := Function.update_of_ne hne_cnt _ _
    have hh2 : φ1 GuessAX.Vars.cntY = φ GuessAX.Vars.cntY := Function.update_of_ne hne_prev _ _
    rw [hh1, hh2]
  have hN_φ2 : φ2 GuessAX.Vars.N = φ GuessAX.Vars.N := by
    have hne_cnt : GuessAX.Vars.N ≠ GuessAX.Vars.cnt := by decide
    have hne_prev : GuessAX.Vars.N ≠ GuessAX.Vars.prev := by decide
    have hh1 : φ2 GuessAX.Vars.N = φ1 GuessAX.Vars.N := Function.update_of_ne hne_cnt _ _
    have hh2 : φ1 GuessAX.Vars.N = φ GuessAX.Vars.N := Function.update_of_ne hne_prev _ _
    rw [hh1, hh2]
  have hne_cntY_j : GuessAX.Vars.cntY ≠ GuessAX.Vars.j := by decide
  have hne_N_j : GuessAX.Vars.N ≠ GuessAX.Vars.j := by decide
  have hcntY3 : φ3 GuessAX.Vars.cntY = φ GuessAX.Vars.cntY := by
    have hh : φ3 GuessAX.Vars.cntY = φ2 GuessAX.Vars.cntY := Function.update_of_ne hne_cntY_j _ _
    rw [hh, hcntY_φ2]
  have hN3 : φ3 GuessAX.Vars.N = φ GuessAX.Vars.N := by
    have hh : φ3 GuessAX.Vars.N = φ2 GuessAX.Vars.N := Function.update_of_ne hne_N_j _ _
    rw [hh, hN_φ2]
  refine ⟨φ3, hfst3, hcnt3, hj3', haux3, hcntY3, hN3, ?_⟩
  simp only [Command.runFuel, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    hxTagRest2, hcntVal2, hprevVal2]
  rfl

/-! ## Runs from `G.Reaches`

`exists_run_of_induced_reaches` (`Soundness/Bridge.lean`) at each thread's
program and initial store (`Reduction/ConcProg.lean`): an execution `G`
reaching `ConcProg`'s final state yields, for each thread, a term-reaching
`Command.Run` emitting `G.threadLabels t`. -/

theorem checkX_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List (CheckX.Vals I)) (cLast : Config (domainOf I) (CheckX.Vocab I))
      (φ : (CheckX.Vocab I).Store),
      Command.Run Tid.checkX s
        (CheckX.program I, (CheckX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr true))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.checkX) cLast [] (Command.term, φ) := by
  have hvx := (hG.2 Tid.checkX).2 rfl
  have hw : G.threadWord Tid.checkX = (G.threadLabels Tid.checkX).map some :=
    G.threadWord_eq_map_threadLabels Tid.checkX
  rw [hw] at hvx
  exact exists_run_of_induced_reaches hvx

theorem primeCheckX_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List PrimeCheckX.Vals) (cLast : Config (domainOf I) (PrimeCheckX.Vocab I))
      (φ : (PrimeCheckX.Vocab I).Store),
      Command.Run Tid.primeCheckX s
        (PrimeCheckX.program I, (PrimeCheckX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeCheckX) cLast [] (Command.term, φ) := by
  have hpvx := (hG.2 Tid.primeCheckX).2 rfl
  have hw : G.threadWord Tid.primeCheckX = (G.threadLabels Tid.primeCheckX).map some :=
    G.threadWord_eq_map_threadLabels Tid.primeCheckX
  rw [hw] at hpvx
  exact exists_run_of_induced_reaches hpvx

theorem primeAX_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List PrimeAX.Vals) (cLast : Config (domainOf I) (PrimeAX.Vocab I))
      (φ : (PrimeAX.Vocab I).Store),
      Command.Run Tid.primeAX s
        (PrimeAX.program I, (PrimeAX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeAX) cLast [] (Command.term, φ) := by
  have hpax := (hG.2 Tid.primeAX).2 rfl
  have hw : G.threadWord Tid.primeAX = (G.threadLabels Tid.primeAX).map some :=
    G.threadWord_eq_map_threadLabels Tid.primeAX
  rw [hw] at hpax
  exact exists_run_of_induced_reaches hpax

/-- `checkX_run_of_reaches` for `CheckY`. -/
theorem checkY_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List (CheckY.Vals I)) (cLast : Config (domainOf I) (CheckY.Vocab I))
      (φ : (CheckY.Vocab I).Store),
      Command.Run Tid.checkY s
        (CheckY.program I, (CheckY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr true))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.checkY) cLast [] (Command.term, φ) := by
  have hvy := (hG.2 Tid.checkY).2 rfl
  have hw : G.threadWord Tid.checkY = (G.threadLabels Tid.checkY).map some :=
    G.threadWord_eq_map_threadLabels Tid.checkY
  rw [hw] at hvy
  exact exists_run_of_induced_reaches hvy

/-- `primeCheckX_run_of_reaches` for `PrimeCheckY`. -/
theorem primeCheckY_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List PrimeCheckY.Vals) (cLast : Config (domainOf I) (PrimeCheckY.Vocab I))
      (φ : (PrimeCheckY.Vocab I).Store),
      Command.Run Tid.primeCheckY s
        (PrimeCheckY.program I, (PrimeCheckY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeCheckY) cLast [] (Command.term, φ) := by
  have hpvy := (hG.2 Tid.primeCheckY).2 rfl
  have hw : G.threadWord Tid.primeCheckY = (G.threadLabels Tid.primeCheckY).map some :=
    G.threadWord_eq_map_threadLabels Tid.primeCheckY
  rw [hw] at hpvy
  exact exists_run_of_induced_reaches hpvy

/-- `checkX_run_of_reaches` for `GuessAX` (initial store: `cntY`, `cnt` both
`0`, `fst` true). -/
theorem guessAX_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List (GuessAX.Vals I)) (cLast : Config (domainOf I) (GuessAX.Vocab I))
      (φ : (GuessAX.Vocab I).Store),
      Command.Run Tid.guessAX s
        (GuessAX.program I, (GuessAX.Vocab I).mkStore (fun v => match v with
          | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.guessAX) cLast [] (Command.term, φ) := by
  have hgax := (hG.2 Tid.guessAX).2 rfl
  have hw : G.threadWord Tid.guessAX = (G.threadLabels Tid.guessAX).map some :=
    G.threadWord_eq_map_threadLabels Tid.guessAX
  rw [hw] at hgax
  exact exists_run_of_induced_reaches hgax

/-- The `β`-mirror of `guessAX_run_of_reaches`. -/
theorem guessBX_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List (GuessBX.Vals I)) (cLast : Config (domainOf I) (GuessBX.Vocab I))
      (φ : (GuessBX.Vocab I).Store),
      Command.Run Tid.guessBX s
        (GuessBX.program I, (GuessBX.Vocab I).mkStore (fun v => match v with
          | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.guessBX) cLast [] (Command.term, φ) := by
  have hgbx := (hG.2 Tid.guessBX).2 rfl
  have hw : G.threadWord Tid.guessBX = (G.threadLabels Tid.guessBX).map some :=
    G.threadWord_eq_map_threadLabels Tid.guessBX
  rw [hw] at hgbx
  exact exists_run_of_induced_reaches hgbx

/-- The `y`-mirror of `guessAX_run_of_reaches`. -/
theorem guessAY_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List (GuessAY.Vals I)) (cLast : Config (domainOf I) (GuessAY.Vocab I))
      (φ : (GuessAY.Vocab I).Store),
      Command.Run Tid.guessAY s
        (GuessAY.program I, (GuessAY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr true))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.guessAY) cLast [] (Command.term, φ) := by
  have hgay := (hG.2 Tid.guessAY).2 rfl
  have hw : G.threadWord Tid.guessAY = (G.threadLabels Tid.guessAY).map some :=
    G.threadWord_eq_map_threadLabels Tid.guessAY
  rw [hw] at hgay
  exact exists_run_of_induced_reaches hgay

/-- The `xy`-mirror of `guessAY_run_of_reaches`. -/
theorem guessBY_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List (GuessBY.Vals I)) (cLast : Config (domainOf I) (GuessBY.Vocab I))
      (φ : (GuessBY.Vocab I).Store),
      Command.Run Tid.guessBY s
        (GuessBY.program I, (GuessBY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr true))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.guessBY) cLast [] (Command.term, φ) := by
  have hgby := (hG.2 Tid.guessBY).2 rfl
  have hw : G.threadWord Tid.guessBY = (G.threadLabels Tid.guessBY).map some :=
    G.threadWord_eq_map_threadLabels Tid.guessBY
  rw [hw] at hgby
  exact exists_run_of_induced_reaches hgby

/-- The `y`-mirror of `primeAX_run_of_reaches`. -/
theorem primeAY_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List PrimeAY.Vals) (cLast : Config (domainOf I) (PrimeAY.Vocab I))
      (φ : (PrimeAY.Vocab I).Store),
      Command.Run Tid.primeAY s
        (PrimeAY.program I, (PrimeAY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeAY) cLast [] (Command.term, φ) := by
  have hpay := (hG.2 Tid.primeAY).2 rfl
  have hw : G.threadWord Tid.primeAY = (G.threadLabels Tid.primeAY).map some :=
    G.threadWord_eq_map_threadLabels Tid.primeAY
  rw [hw] at hpay
  exact exists_run_of_induced_reaches hpay

/-- The `β`-mirror of `primeAX_run_of_reaches`. -/
theorem primeBX_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List PrimeBX.Vals) (cLast : Config (domainOf I) (PrimeBX.Vocab I))
      (φ : (PrimeBX.Vocab I).Store),
      Command.Run Tid.primeBX s
        (PrimeBX.program I, (PrimeBX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeBX) cLast [] (Command.term, φ) := by
  have hpbx := (hG.2 Tid.primeBX).2 rfl
  have hw : G.threadWord Tid.primeBX = (G.threadLabels Tid.primeBX).map some :=
    G.threadWord_eq_map_threadLabels Tid.primeBX
  rw [hw] at hpbx
  exact exists_run_of_induced_reaches hpbx

/-- The `xy`-mirror of `primeAY_run_of_reaches`. -/
theorem primeBY_run_of_reaches (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    ∃ (s : List PrimeBY.Vals) (cLast : Config (domainOf I) (PrimeBY.Vocab I))
      (φ : (PrimeBY.Vocab I).Store),
      Command.Run Tid.primeBY s
        (PrimeBY.program I, (PrimeBY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeBY) cLast [] (Command.term, φ) := by
  have hpby := (hG.2 Tid.primeBY).2 rfl
  have hw : G.threadWord Tid.primeBY = (G.threadLabels Tid.primeBY).map some :=
    G.threadWord_eq_map_threadLabels Tid.primeBY
  rw [hw] at hpby
  exact exists_run_of_induced_reaches hpby

/-! ## `GuessAX`'s outer loop

The converse of `guessAX_outer0_step` (`Completeness/Construction.lean`), the
first outer iteration of `GuessAX`'s `while True do … done` loop, and of its
five constituent steps, each with explicit fuel. Pieces that occur under a
`.seq`/`.loopSeq` wrapping are stated as `.outOfFuel` facts, which transport
through the wrapping (`Command.runFuel_seqCongr_outOfFuel`/
`_loopSeqCongr_outOfFuel`), and are chained with
`Command.runFuel_outOfFuel_append`/`_split`. -/

/-- `rem` iterations of `guessAXInnerLoop` after the first call, as an
`.outOfFuel` result (chaining `guessAX_innerLoop_rest_step_outOfFuel`). -/
theorem guessAXInnerLoop_chain_outOfFuel (I : PCPInstance) :
    ∀ (rem : ℕ) (rest : List (GuessAX.Vals I)) (φ : (GuessAX.Vocab I).Store),
      (GuessAX.jOf I φ).val + rem = (GuessAX.NOf I φ).val + 1 →
      (k0 : Fin 4) → φ GuessAX.Vars.cnt = Sum.inr (Sum.inl k0) →
      φ GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) →
      (GuessAX.NOf I φ).val ≤ GuessAX.maxLen I →
      ∃ (vs : List (Val I × Val I × Val I)) (φf : (GuessAX.Vocab I).Store),
        vs.length = rem ∧
        φf GuessAX.Vars.cnt = Sum.inr (Sum.inl (⟨(k0.val + rem) % 4, by omega⟩ : Fin 4)) ∧
        φf GuessAX.Vars.aux = φ GuessAX.Vars.aux ∧
        φf GuessAX.Vars.cntY = φ GuessAX.Vars.cntY ∧
        φf GuessAX.Vars.N = φ GuessAX.Vars.N ∧
        φf GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
        (GuessAX.jOf I φf).val = (GuessAX.jOf I φ).val + rem ∧
        (∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
          e.2.2 = Val.cnt (⟨(k0.val + n) % 4, by omega⟩ : Fin 4) ∧
          e.2.1 = Val.cnt (⟨(k0.val + n + 1) % 4, by omega⟩ : Fin 4)) ∧
        (∀ n, n < rem → ∃ e j, vs[n]? = some e ∧ j.val = (GuessAX.jOf I φ).val + n ∧
          e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (GuessAX.auxOf I φ) j)) ∧
        Command.runFuel Tid.guessAX (guessAXInnerLoop I, φ) rest (14 * rem) =
          (.outOfFuel, vs.flatMap (guessAXInnerBlockElems I), (guessAXInnerLoop I, φf), rest) := by
  intro rem
  induction rem with
  | zero =>
      intro rest φ hrem k0 hcnt0 hfst hNbound
      refine ⟨[], φ, rfl, ?_, rfl, rfl, rfl, hfst, by omega, ?_, ?_, ?_⟩
      · have heq0 : (⟨(k0.val + 0) % 4, by omega⟩ : Fin 4) = k0 := by
          apply Fin.ext; show (k0.val + 0) % 4 = k0.val; omega
        rw [heq0]; exact hcnt0
      · intro n hn; simp at hn
      · intro n hn; omega
      · simp only [Command.runFuel, List.flatMap_nil]; rfl
  | succ rem ih =>
      intro rest φ hrem k0 hcnt0 hfst hNbound
      have hguardT' : GuessAX.evalB I GuessAX.BExpr.jLeN φ = true := by
        simp only [GuessAX.evalB, decide_eq_true_eq, Fin.le_def]
        omega
      have hguardT : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ = true := hguardT'
      obtain ⟨φ', hfst', hcnt', hj', haux', hcntY', hN', hstep14⟩ :=
        guessAX_innerLoop_rest_step_outOfFuel I rest φ hguardT hfst k0 hcnt0
      have hjleN : (GuessAX.jOf I φ).val ≤ (GuessAX.NOf I φ).val := by
        have hb := hguardT'
        simp only [GuessAX.evalB, decide_eq_true_eq, Fin.le_def] at hb
        exact hb
      have hjbound : (GuessAX.jOf I φ).val ≤ GuessAX.maxLen I := by omega
      have h1val : (1 : Fin (GuessAX.maxLen I + 2)).val = 1 := by
        simp [Fin.val_one']
      have hjOf' : (GuessAX.jOf I φ').val = (GuessAX.jOf I φ).val + 1 := by
        have heval : GuessAX.jOf I φ' = GuessAX.jOf I φ + 1 := by
          simp only [GuessAX.jOf, hj', GuessAX.eval]
        rw [heval, Fin.val_add_eq_of_add_lt (by rw [h1val]; omega), h1val]
      have hNOf' : (GuessAX.NOf I φ').val = (GuessAX.NOf I φ).val := by
        simp only [GuessAX.NOf, hN']
      have hrem' : (GuessAX.jOf I φ').val + rem = (GuessAX.NOf I φ').val + 1 := by
        rw [hjOf', hNOf']; omega
      have hNbound' : (GuessAX.NOf I φ').val ≤ GuessAX.maxLen I := by rw [hNOf']; exact hNbound
      obtain ⟨vs, φf, hvslen, hcntf, hauxf, hcntYf, hNf, hfstf, hjf, hval, hvalx, hstepRem⟩ :=
        ih rest φ' hrem' (k0 + 1) hcnt' hfst' hNbound'
      have hfuel : 14 * (rem + 1) = 14 + 14 * rem := by omega
      refine ⟨(Val.xTag (Tid.guessAX, false)
          (GuessAX.jthLetter I (GuessAX.auxOf I φ) (GuessAX.jOf I φ)),
          Val.cnt (k0 + 1), Val.cnt k0) :: vs, φf, by simp [hvslen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩
      · rw [hcntf]; congr 2; apply Fin.ext; show ((k0.val + 1) % 4 + rem) % 4 = (k0.val + (rem + 1)) % 4
        omega
      · rw [hauxf, haux']
      · rw [hcntYf, hcntY']
      · rw [hNf, hN']
      · exact hfstf
      · rw [hjf, hjOf']; omega
      · intro n hn
        cases n with
        | zero =>
            refine ⟨_, rfl, ?_, ?_⟩
            · show Val.cnt k0 = Val.cnt (⟨(k0.val + 0) % 4, by omega⟩ : Fin 4)
              congr 1; apply Fin.ext; show k0.val = (k0.val + 0) % 4; omega
            · show Val.cnt (k0 + 1) = Val.cnt (⟨(k0.val + 0 + 1) % 4, by omega⟩ : Fin 4)
              congr 1
        | succ n =>
            simp only [List.length_cons] at hn
            have hn' : n < vs.length := by omega
            obtain ⟨e, hevs, he1, he2⟩ := hval n hn'
            refine ⟨e, ?_, ?_, ?_⟩
            · simpa using hevs
            · rw [he1]; congr 1; apply Fin.ext
              simp only [Fin.val_add]
              omega
            · rw [he2]; congr 1; apply Fin.ext
              simp only [Fin.val_add]
              omega
      · intro n hn
        cases n with
        | zero =>
            refine ⟨_, GuessAX.jOf I φ, rfl, by simp, rfl⟩
        | succ n =>
            simp only [Nat.add_lt_add_iff_right] at hn
            obtain ⟨e, j, hevs, hjval, he1⟩ := hvalx n hn
            refine ⟨e, j, ?_, ?_, ?_⟩
            · simpa using hevs
            · rw [hjval, hjOf']; omega
            · rw [he1]; simp only [GuessAX.auxOf, haux']
      · rw [hfuel]
        have hcomb := Command.runFuel_outOfFuel_append 14 (guessAXInnerLoop I, φ) rest _ _ _
          hstep14 (14 * rem) _ _ _ _ hstepRem
        rw [show
          ((Val.xTag (Tid.guessAX, false)
              (GuessAX.jthLetter I (GuessAX.auxOf I φ) (GuessAX.jOf I φ)),
              Val.cnt (k0 + 1), Val.cnt k0) :: vs).flatMap (guessAXInnerBlockElems I) =
            [ ⟨EventLabel.wt Tid.guessAX Loc.xA
                (Val.xTag (Tid.guessAX, false)
                  (GuessAX.jthLetter I (GuessAX.auxOf I φ) (GuessAX.jOf I φ))), rfl⟩
            , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt (k0 + 1)), rfl⟩
            , ⟨EventLabel.rd Tid.guessAX Loc.zAxx' (Val.cnt k0), rfl⟩ ] ++
              vs.flatMap (guessAXInnerBlockElems I) from by
            simp only [List.flatMap_cons]; congr 1]
        exact hcomb

/-- The exit of `guessAXInnerLoop`, as an
`.outOfFuel` result. -/
theorem guessAXOuterExit_step_outOfFuel (I : PCPInstance) (rest : List (GuessAX.Vals I))
    (φ : (GuessAX.Vocab I).Store) (C2 : Command (domainOf I) (GuessAX.Vocab I))
    (hguard : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ = false) :
    Command.runFuel Tid.guessAX (Command.seq (guessAXInnerLoop I) C2, φ) rest 2 =
      (.outOfFuel, [], (C2, φ), rest) := by
  have hguard' : GuessAX.evalB I GuessAX.BExpr.jLeN φ = false := hguard
  have h1 : Command.RunStep Tid.guessAX rest none
      (Command.seq (guessAXInnerLoop I) C2, φ) rest
      (Command.seq Command.skip C2, φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [guessAXInnerLoop, Command.step, GuessAX.Vocab, hguard']; rfl)
  have h2 : Command.RunStep Tid.guessAX rest none
      (Command.seq Command.skip C2, φ) rest (C2, φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  have w2 := Command.step_complete h2
  simp only [Command.runFuel, w1, w2]
  rfl

/-- The first four steps of `guessAXOuterTail_continue_step_inv` (the
`r(ℓ_α^{y,x})`, the `ite isBot`, and `seqSkip`, up to the `ndetAssign`
draw), as an `.outOfFuel` result for an arbitrary resolution `s`. Used to
determine the drawn value from `s` itself. -/
theorem guessAXOuterTail_continue_pre_step_outOfFuel (I : PCPInstance)
    (s : List (GuessAX.Vals I)) (φ : (GuessAX.Vocab I).Store)
    (cntY0 : Fin 4) (hcntY0 : φ GuessAX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (v : Fin I.n) (haux : φ GuessAX.Vars.aux = Sum.inl (some v)) :
    Command.runFuel Tid.guessAX
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ) s 4 =
      (.outOfFuel,
        [⟨EventLabel.rd Tid.guessAX Loc.ellAyx (Val.cntAux cntY0 (some v)), rfl⟩],
        (Command.loopSeq
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I))
          (guessAXLoop I), φ), s) := by
  have hellVal :
      (GuessAX.Vocab I).evalV GuessAX.VExpr.cntYAuxVal φ = Val.cntAux cntY0 (some v) := by
    have hcntYOfφ : GuessAX.cntYOf I φ = cntY0 := by simp only [GuessAX.cntYOf, hcntY0]
    have hauxOfφ : GuessAX.auxOf I φ = some v := by simp only [GuessAX.auxOf, haux]
    simp only [GuessAX.Vocab, GuessAX.evalV, hcntYOfφ, hauxOfφ]; rfl
  have h1 : Command.RunStep Tid.guessAX s
      (some ⟨EventLabel.rd Tid.guessAX Loc.ellAyx
        ((GuessAX.Vocab I).evalV GuessAX.VExpr.cntYAuxVal φ), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ)
      s
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  have h2 : Command.RunStep Tid.guessAX s none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ)
      s
      (Command.loopSeq
        (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w2 := Command.step_complete h2
  have haux' : (GuessAX.Vocab I).evalB GuessAX.BExpr.isBot φ = false := by
    simp [GuessAX.Vocab, GuessAX.evalB, haux]
  have h3 : Command.RunStep Tid.guessAX s none
      (Command.loopSeq
        (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ)
      s
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp [Command.step, haux'])
  have w3 := Command.step_complete h3
  have h4 : Command.RunStep Tid.guessAX s none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ)
      s
      (Command.loopSeq
        (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
          (GuessAX.auxSetBot_nonempty I))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w4 := Command.step_complete h4
  simp only [Command.runFuel, w1, w2, w3, w4, hellVal]
  rfl

/-- The converse of `guessAXOuterTail_continue_step`, for a given drawn value
`v0'` and remaining resolution `rest`. -/
theorem guessAXOuterTail_continue_step_inv (I : PCPInstance) (v0' : Option (Fin I.n))
    (rest : List (GuessAX.Vals I))
    (φ : (GuessAX.Vocab I).Store)
    (cntY0 : Fin 4) (hcntY0 : φ GuessAX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (v : Fin I.n) (haux : φ GuessAX.Vars.aux = Sum.inl (some v))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAX))
    (cf : Config (domainOf I) (GuessAX.Vocab I)) (sf : List (GuessAX.Vals I))
    (h : Command.runFuel Tid.guessAX
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ) (Sum.inl v0' :: rest) (N + 6) = (.stuck, σ, cf, sf)) :
    ∃ σ1, σ = [⟨EventLabel.rd Tid.guessAX Loc.ellAyx (Val.cntAux cntY0 (some v)), rfl⟩] ++ σ1 ∧
      Command.runFuel Tid.guessAX (guessAXLoop I,
        Function.update φ GuessAX.Vars.aux (Sum.inl v0')) rest N = (.stuck, σ1, cf, sf) := by
  have hellVal :
      (GuessAX.Vocab I).evalV GuessAX.VExpr.cntYAuxVal φ = Val.cntAux cntY0 (some v) := by
    have hcntYOfφ : GuessAX.cntYOf I φ = cntY0 := by simp only [GuessAX.cntYOf, hcntY0]
    have hauxOfφ : GuessAX.auxOf I φ = some v := by simp only [GuessAX.auxOf, haux]
    simp only [GuessAX.Vocab, GuessAX.evalV, hcntYOfφ, hauxOfφ]; rfl
  have h1 : Command.RunStep Tid.guessAX (Sum.inl v0' :: rest)
      (some ⟨EventLabel.rd Tid.guessAX Loc.ellAyx
        ((GuessAX.Vocab I).evalV GuessAX.VExpr.cntYAuxVal φ), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ)
      (Sum.inl v0' :: rest)
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  simp only [Command.runFuel, w1] at h
  have h2 : Command.RunStep Tid.guessAX (Sum.inl v0' :: rest) none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ)
      (Sum.inl v0' :: rest)
      (Command.loopSeq
        (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w2 := Command.step_complete h2
  simp only [w2] at h
  have haux' : (GuessAX.Vocab I).evalB GuessAX.BExpr.isBot φ = false := by
    simp [GuessAX.Vocab, GuessAX.evalB, haux]
  have h3 : Command.RunStep Tid.guessAX (Sum.inl v0' :: rest) none
      (Command.loopSeq
        (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ)
      (Sum.inl v0' :: rest)
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp [Command.step, haux'])
  have w3 := Command.step_complete h3
  simp only [w3] at h
  have h4 : Command.RunStep Tid.guessAX (Sum.inl v0' :: rest) none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ)
      (Sum.inl v0' :: rest)
      (Command.loopSeq
        (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
          (GuessAX.auxSetBot_nonempty I))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w4 := Command.step_complete h4
  simp only [w4] at h
  have hmem : (Sum.inl v0' : GuessAX.Vals I) ∈ GuessAX.auxSetBot I := by
    simp only [GuessAX.auxSetBot, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨v0', rfl⟩
  have h5 : Command.RunStep Tid.guessAX (Sum.inl v0' :: rest) none
      (Command.loopSeq
        (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
          (GuessAX.auxSetBot_nonempty I))
        (guessAXLoop I), φ)
      rest
      (Command.loopSeq Command.skip (guessAXLoop I),
        Function.update φ GuessAX.Vars.aux (Sum.inl v0')) := by
    apply Command.step_sound
    simp only [Command.step]
    split_ifs with hif
    · rfl
    · exact absurd hmem hif
  have w5 := Command.step_complete h5
  simp only [w5] at h
  have h6 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq Command.skip (guessAXLoop I),
        Function.update φ GuessAX.Vars.aux (Sum.inl v0'))
      rest
      (guessAXLoop I, Function.update φ GuessAX.Vars.aux (Sum.inl v0')) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w6 := Command.step_complete h6
  simp only [w6] at h
  injection h with hres h'
  injection h' with hwd h''
  injection h'' with hcf hsf
  rw [hellVal] at hwd
  exact ⟨(Command.runFuel Tid.guessAX (guessAXLoop I,
    Function.update φ GuessAX.Vars.aux (Sum.inl v0')) rest N).2.1, hwd.symm,
    by rw [← hres, ← hcf, ← hsf]; rfl⟩

/-- The converse of `guessAXOuterTail_break_step`: with `aux = ⊥`, the `ite`
takes the `break` branch, skipping the trailing draw; five steps reach
`(Command.skip, φ)`, consuming nothing. -/
theorem guessAXOuterTail_break_step_inv (I : PCPInstance) (rest : List (GuessAX.Vals I))
    (φ : (GuessAX.Vocab I).Store)
    (cntY0 : Fin 4) (hcntY0 : φ GuessAX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (haux : φ GuessAX.Vars.aux = Sum.inl none)
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAX))
    (cf : Config (domainOf I) (GuessAX.Vocab I)) (sf : List (GuessAX.Vals I))
    (h : Command.runFuel Tid.guessAX
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ) rest (N + 5) = (.stuck, σ, cf, sf)) :
    ∃ σ1, σ = [⟨EventLabel.rd Tid.guessAX Loc.ellAyx (Val.cntAux cntY0 none), rfl⟩] ++ σ1 ∧
      Command.runFuel Tid.guessAX (Command.skip, φ) rest N = (.stuck, σ1, cf, sf) := by
  have hellVal :
      (GuessAX.Vocab I).evalV GuessAX.VExpr.cntYAuxVal φ = Val.cntAux cntY0 none := by
    have hcntYOfφ : GuessAX.cntYOf I φ = cntY0 := by simp only [GuessAX.cntYOf, hcntY0]
    have hauxOfφ : GuessAX.auxOf I φ = none := by simp only [GuessAX.auxOf, haux]
    simp only [GuessAX.Vocab, GuessAX.evalV, hcntYOfφ, hauxOfφ]; rfl
  have h1 : Command.RunStep Tid.guessAX rest
      (some ⟨EventLabel.rd Tid.guessAX Loc.ellAyx
        ((GuessAX.Vocab I).evalV GuessAX.VExpr.cntYAuxVal φ), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ)
      rest
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  simp only [Command.runFuel, w1] at h
  have h2 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I))))
        (guessAXLoop I), φ)
      rest
      (Command.loopSeq
        (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w2 := Command.step_complete h2
  simp only [w2] at h
  have haux' : (GuessAX.Vocab I).evalB GuessAX.BExpr.isBot φ = true := by
    simp [GuessAX.Vocab, GuessAX.evalB, haux]
  have h3 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq
        (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ)
      rest
      (Command.loopSeq
        (Command.seq Command.brk
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp [Command.step, haux'])
  have w3 := Command.step_complete h3
  simp only [w3] at h
  have h4 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq
        (Command.seq Command.brk
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I)))
        (guessAXLoop I), φ)
      rest
      (Command.loopSeq Command.brk (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w4 := Command.step_complete h4
  simp only [w4] at h
  have h5 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq Command.brk (guessAXLoop I), φ)
      rest
      (Command.skip, φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w5 := Command.step_complete h5
  simp only [w5] at h
  injection h with hres h'
  injection h' with hwd h''
  injection h'' with hcf hsf
  rw [hellVal] at hwd
  exact ⟨(Command.runFuel Tid.guessAX (Command.skip, φ) rest N).2.1, hwd.symm,
    by rw [← hres, ← hcf, ← hsf]; rfl⟩

/-- The converse of `guessAXOuterHead_step`: nine steps (one labelled,
`w(zAxy, cntY0+1)`), updating `cntY`, `j`, `N`. -/
theorem guessAXOuterHead_step_inv (I : PCPInstance) (rest : List (GuessAX.Vals I))
    (φ : (GuessAX.Vocab I).Store)
    (aux0 : Option (Fin I.n)) (haux0 : φ GuessAX.Vars.aux = Sum.inl aux0)
    (cntY0 : Fin 4) (hcntY0 : φ GuessAX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAX))
    (cf : Config (domainOf I) (GuessAX.Vocab I)) (sf : List (GuessAX.Vals I))
    (h : Command.runFuel Tid.guessAX (guessAXLoop I, φ) rest (N + 9) = (.stuck, σ, cf, sf)) :
    ∃ (φ' : (GuessAX.Vocab I).Store) (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAX)),
      σ = [⟨EventLabel.wt Tid.guessAX Loc.zAxy (Val.cnt (cntY0 + 1)), rfl⟩] ++ σ1 ∧
      φ' GuessAX.Vars.cnt = φ GuessAX.Vars.cnt ∧
      φ' GuessAX.Vars.fst = φ GuessAX.Vars.fst ∧
      φ' GuessAX.Vars.aux = φ GuessAX.Vars.aux ∧
      φ' GuessAX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) ∧
      (GuessAX.jOf I φ').val = 1 ∧
      (GuessAX.NOf I φ').val = (GuessAX.extAlpha I aux0).length ∧
      Command.runFuel Tid.guessAX
        (Command.loopSeq (Command.seq (guessAXInnerLoop I)
          (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
            (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                (GuessAX.auxSetBot_nonempty I)))))
          (guessAXLoop I), φ') rest N = (.stuck, σ1, cf, sf) := by
  set φ0 : (GuessAX.Vocab I).Store :=
    Function.update φ GuessAX.Vars.cntY (GuessAX.eval I GuessAX.Expr.nextCntY φ) with hφ0
  set φ0j : (GuessAX.Vocab I).Store :=
    Function.update φ0 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.one φ0) with hφ0j
  set φ0jN : (GuessAX.Vocab I).Store :=
    Function.update φ0j GuessAX.Vars.N (GuessAX.eval I GuessAX.Expr.alphaLen φ0j) with hφ0jN
  have hcntYOfφ : GuessAX.cntYOf I φ = cntY0 := by simp only [GuessAX.cntYOf, hcntY0]
  have hcntY0eq : φ0 GuessAX.Vars.cntY = GuessAX.eval I GuessAX.Expr.nextCntY φ :=
    Function.update_self _ _ _
  have hcntY0raw : φ0 GuessAX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
    simp only [hcntY0eq, GuessAX.eval, hcntYOfφ]; rfl
  have hne_cnt_cntY : GuessAX.Vars.cnt ≠ GuessAX.Vars.cntY := by decide
  have hne_fst_cntY : GuessAX.Vars.fst ≠ GuessAX.Vars.cntY := by decide
  have hne_aux_cntY : GuessAX.Vars.aux ≠ GuessAX.Vars.cntY := by decide
  have hcnt0' : φ0 GuessAX.Vars.cnt = φ GuessAX.Vars.cnt := Function.update_of_ne hne_cnt_cntY _ _
  have hfst0' : φ0 GuessAX.Vars.fst = φ GuessAX.Vars.fst := Function.update_of_ne hne_fst_cntY _ _
  have haux0' : φ0 GuessAX.Vars.aux = φ GuessAX.Vars.aux := Function.update_of_ne hne_aux_cntY _ _
  have hcntYVal0 : (GuessAX.Vocab I).evalV GuessAX.VExpr.cntYVal φ0 = Val.cnt (cntY0 + 1) := by
    have hh : GuessAX.cntYOf I φ0 = cntY0 + 1 := by simp only [GuessAX.cntYOf, hcntY0raw]
    simp only [GuessAX.Vocab, GuessAX.evalV, hh]; rfl
  have hj0eq : φ0j GuessAX.Vars.j = GuessAX.eval I GuessAX.Expr.one φ0 := Function.update_self _ _ _
  have hjOf0jVal : (GuessAX.jOf I φ0j).val = 1 := by
    simp only [hj0eq, GuessAX.jOf, GuessAX.eval]
  have hne_cnt_j : GuessAX.Vars.cnt ≠ GuessAX.Vars.j := by decide
  have hne_fst_j : GuessAX.Vars.fst ≠ GuessAX.Vars.j := by decide
  have hne_aux_j : GuessAX.Vars.aux ≠ GuessAX.Vars.j := by decide
  have hne_cntY_j : GuessAX.Vars.cntY ≠ GuessAX.Vars.j := by decide
  have hcnt0j : φ0j GuessAX.Vars.cnt = φ0 GuessAX.Vars.cnt := Function.update_of_ne hne_cnt_j _ _
  have hfst0j : φ0j GuessAX.Vars.fst = φ0 GuessAX.Vars.fst := Function.update_of_ne hne_fst_j _ _
  have haux0j : φ0j GuessAX.Vars.aux = φ0 GuessAX.Vars.aux := Function.update_of_ne hne_aux_j _ _
  have hcntY0j : φ0j GuessAX.Vars.cntY = φ0 GuessAX.Vars.cntY :=
    Function.update_of_ne hne_cntY_j _ _
  have haux0j' : φ0j GuessAX.Vars.aux = Sum.inl aux0 := by rw [haux0j, haux0', haux0]
  have hauxOf0j : GuessAX.auxOf I φ0j = aux0 := by simp only [GuessAX.auxOf, haux0j']
  have hN0jeq : φ0jN GuessAX.Vars.N = GuessAX.eval I GuessAX.Expr.alphaLen φ0j :=
    Function.update_self _ _ _
  have hNOf0jNVal : (GuessAX.NOf I φ0jN).val = (GuessAX.extAlpha I aux0).length := by
    simp only [hN0jeq, GuessAX.NOf, GuessAX.eval, hauxOf0j]
  have hne_cnt_N : GuessAX.Vars.cnt ≠ GuessAX.Vars.N := by decide
  have hne_fst_N : GuessAX.Vars.fst ≠ GuessAX.Vars.N := by decide
  have hne_aux_N : GuessAX.Vars.aux ≠ GuessAX.Vars.N := by decide
  have hne_j_N : GuessAX.Vars.j ≠ GuessAX.Vars.N := by decide
  have hne_cntY_N : GuessAX.Vars.cntY ≠ GuessAX.Vars.N := by decide
  have hcnt0jN : φ0jN GuessAX.Vars.cnt = φ0j GuessAX.Vars.cnt := Function.update_of_ne hne_cnt_N _ _
  have hfst0jN : φ0jN GuessAX.Vars.fst = φ0j GuessAX.Vars.fst := Function.update_of_ne hne_fst_N _ _
  have haux0jN : φ0jN GuessAX.Vars.aux = φ0j GuessAX.Vars.aux := Function.update_of_ne hne_aux_N _ _
  have hj0jN : φ0jN GuessAX.Vars.j = φ0j GuessAX.Vars.j := Function.update_of_ne hne_j_N _ _
  have hcntY0jN : φ0jN GuessAX.Vars.cntY = φ0j GuessAX.Vars.cntY :=
    Function.update_of_ne hne_cntY_N _ _
  have hjOf0jNVal : (GuessAX.jOf I φ0jN).val = 1 := by
    have heq : GuessAX.jOf I φ0jN = GuessAX.jOf I φ0j := by simp only [GuessAX.jOf, hj0jN]
    rw [heq]; exact hjOf0jVal
  have h1 : Command.RunStep Tid.guessAX rest none (guessAXLoop I, φ) rest
      (Command.loopSeq (GuessAX.outerBody I) (guessAXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [guessAXLoop, Command.step, GuessAX.Vocab, GuessAX.evalB, if_true])
  have w1 := Command.step_complete h1
  simp only [Command.runFuel, w1] at h
  have h2 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (GuessAX.outerBody I) (guessAXLoop I), φ) rest
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.zAxy GuessAX.VExpr.cntYVal)
          (Command.seq (Command.forLoop GuessAX.Vars.j GuessAX.Vars.N GuessAX.Expr.alphaLen
              GuessAX.Expr.one GuessAX.BExpr.jLeN GuessAX.Expr.jIncr (GuessAX.innerBody I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))))
        (guessAXLoop I), φ0) := by
    rw [hφ0]
    exact Command.step_sound _ _ _ _ _ _ _ (by
      simp only [GuessAX.outerBody, Command.step, GuessAX.Vocab]; rfl)
  have w2 := Command.step_complete h2
  simp only [w2] at h
  have h3 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.zAxy GuessAX.VExpr.cntYVal)
          (Command.seq (Command.forLoop GuessAX.Vars.j GuessAX.Vars.N GuessAX.Expr.alphaLen
              GuessAX.Expr.one GuessAX.BExpr.jLeN GuessAX.Expr.jIncr (GuessAX.innerBody I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))))
        (guessAXLoop I), φ0) rest
      (Command.loopSeq
        (Command.seq (Command.write Loc.zAxy GuessAX.VExpr.cntYVal)
          (Command.seq (Command.forLoop GuessAX.Vars.j GuessAX.Vars.N GuessAX.Expr.alphaLen
              GuessAX.Expr.one GuessAX.BExpr.jLeN GuessAX.Expr.jIncr (GuessAX.innerBody I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I))))))
        (guessAXLoop I), φ0) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w3 := Command.step_complete h3
  simp only [w3] at h
  have h4 : Command.RunStep Tid.guessAX rest
      (some ⟨EventLabel.wt Tid.guessAX Loc.zAxy ((GuessAX.Vocab I).evalV GuessAX.VExpr.cntYVal φ0),
        rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.write Loc.zAxy GuessAX.VExpr.cntYVal)
          (Command.seq (Command.forLoop GuessAX.Vars.j GuessAX.Vars.N GuessAX.Expr.alphaLen
              GuessAX.Expr.one GuessAX.BExpr.jLeN GuessAX.Expr.jIncr (GuessAX.innerBody I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I))))))
        (guessAXLoop I), φ0) rest
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.forLoop GuessAX.Vars.j GuessAX.Vars.N GuessAX.Expr.alphaLen
              GuessAX.Expr.one GuessAX.BExpr.jLeN GuessAX.Expr.jIncr (GuessAX.innerBody I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I))))))
        (guessAXLoop I), φ0) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w4 := Command.step_complete h4
  simp only [Command.runFuel, w4] at h
  have h5 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.forLoop GuessAX.Vars.j GuessAX.Vars.N GuessAX.Expr.alphaLen
              GuessAX.Expr.one GuessAX.BExpr.jLeN GuessAX.Expr.jIncr (GuessAX.innerBody I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I))))))
        (guessAXLoop I), φ0) rest
      (Command.loopSeq
        (Command.seq (Command.forLoop GuessAX.Vars.j GuessAX.Vars.N GuessAX.Expr.alphaLen
              GuessAX.Expr.one GuessAX.BExpr.jLeN GuessAX.Expr.jIncr (GuessAX.innerBody I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w5 := Command.step_complete h5
  simp only [w5] at h
  have h6 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq
        (Command.seq (Command.forLoop GuessAX.Vars.j GuessAX.Vars.N GuessAX.Expr.alphaLen
              GuessAX.Expr.one GuessAX.BExpr.jLeN GuessAX.Expr.jIncr (GuessAX.innerBody I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0) rest
      (Command.loopSeq
        (Command.seq (Command.seq Command.skip
            (Command.seq (Command.assign GuessAX.Vars.N GuessAX.Expr.alphaLen)
              (guessAXInnerLoop I)))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0j) := by
    rw [hφ0j]
    exact Command.step_sound _ _ _ _ _ _ _ (by
      simp only [Command.forLoop, guessAXInnerLoop, Command.step, GuessAX.Vocab]; rfl)
  have w6 := Command.step_complete h6
  simp only [w6] at h
  have h7 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq
        (Command.seq (Command.seq Command.skip
            (Command.seq (Command.assign GuessAX.Vars.N GuessAX.Expr.alphaLen)
              (guessAXInnerLoop I)))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0j) rest
      (Command.loopSeq
        (Command.seq
            (Command.seq (Command.assign GuessAX.Vars.N GuessAX.Expr.alphaLen)
              (guessAXInnerLoop I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0j) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w7 := Command.step_complete h7
  simp only [w7] at h
  have h8 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq
        (Command.seq
            (Command.seq (Command.assign GuessAX.Vars.N GuessAX.Expr.alphaLen)
              (guessAXInnerLoop I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0j) rest
      (Command.loopSeq
        (Command.seq
            (Command.seq Command.skip (guessAXInnerLoop I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0jN) := by
    rw [hφ0jN]
    exact Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessAX.Vocab])
  have w8 := Command.step_complete h8
  simp only [w8] at h
  have h9 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq
        (Command.seq
            (Command.seq Command.skip (guessAXInnerLoop I))
            (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0jN) rest
      (Command.loopSeq (Command.seq (guessAXInnerLoop I)
          (Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
            (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                (GuessAX.auxSetBot_nonempty I)))))
        (guessAXLoop I), φ0jN) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w9 := Command.step_complete h9
  simp only [w9] at h
  injection h with h1' h2'
  injection h2' with hwd h3'
  injection h3' with hcf hsf
  rw [hcntYVal0] at hwd
  refine ⟨φ0jN, _, hwd.symm, ?_, ?_, ?_, ?_, hjOf0jNVal, hNOf0jNVal,
    by rw [← h1', ← hcf, ← hsf]; rfl⟩
  · rw [hcnt0jN, hcnt0j, hcnt0']
  · rw [hfst0jN, hfst0j, hfst0']
  · rw [haux0jN, haux0j, haux0']
  · rw [hcntY0jN, hcntY0j, hcntY0raw]

/-- The first call of `guessAXInnerLoop`, as an `.outOfFuel` result after
exactly 14 steps. -/
theorem guessAX_innerLoop_first_step_outOfFuel (I : PCPInstance) (rest : List (GuessAX.Vals I))
    (φ : (GuessAX.Vocab I).Store)
    (hguard : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ = true)
    (hfst : φ GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)))
    (k : Fin 4) (hcnt0 : φ GuessAX.Vars.cnt = Sum.inr (Sum.inl k)) :
    ∃ (φ' : (GuessAX.Vocab I).Store),
      φ' GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
      φ' GuessAX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
      φ' GuessAX.Vars.j = GuessAX.eval I GuessAX.Expr.jIncr φ ∧
      φ' GuessAX.Vars.aux = φ GuessAX.Vars.aux ∧
      φ' GuessAX.Vars.cntY = φ GuessAX.Vars.cntY ∧
      φ' GuessAX.Vars.N = φ GuessAX.Vars.N ∧
      Command.runFuel Tid.guessAX (guessAXInnerLoop I, φ) rest 14 =
        (.outOfFuel,
          [ ⟨EventLabel.wt Tid.guessAX Loc.xA
              (Val.xTag (Tid.guessAX, true)
                (GuessAX.jthLetter I (GuessAX.auxOf I φ) (GuessAX.jOf I φ))), rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt (k + 1)), rfl⟩ ],
          (guessAXInnerLoop I, φ'), rest) := by
  set φ1 : (GuessAX.Vocab I).Store :=
    Function.update φ GuessAX.Vars.prev (GuessAX.eval I GuessAX.Expr.readCnt φ) with hφ1
  set φ2 : (GuessAX.Vocab I).Store :=
    Function.update φ1 GuessAX.Vars.cnt (GuessAX.eval I GuessAX.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 GuessAX.Vars.cnt = φ GuessAX.Vars.cnt := rfl
  have hcntOf_φ1 : GuessAX.cntOf I φ1 = k := by simp only [GuessAX.cntOf, hcnt_φ1, hcnt0]
  have hcnt2eq : φ2 GuessAX.Vars.cnt = GuessAX.eval I GuessAX.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2raw : φ2 GuessAX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt2eq, GuessAX.eval, hcntOf_φ1]; rfl
  have hguard' : GuessAX.evalB I GuessAX.BExpr.jLeN φ = true := hguard
  have hne_fst_cnt : GuessAX.Vars.fst ≠ GuessAX.Vars.cnt := by decide
  have hne_fst_prev : GuessAX.Vars.fst ≠ GuessAX.Vars.prev := by decide
  have hfst_φ1 : φ1 GuessAX.Vars.fst = φ GuessAX.Vars.fst := rfl
  have hfst2 : φ2 GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)) := by
    have h1x : φ2 GuessAX.Vars.fst = φ1 GuessAX.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1x, hfst_φ1, hfst]
  have hisFirst2 : (GuessAX.Vocab I).evalB GuessAX.BExpr.isFirst φ2 = true := by
    simp [GuessAX.Vocab, GuessAX.evalB, hfst2]
  have hisFirst2' : GuessAX.evalB I GuessAX.BExpr.isFirst φ2 = true := hisFirst2
  set φ3 : (GuessAX.Vocab I).Store :=
    Function.update φ2 GuessAX.Vars.fst (GuessAX.eval I GuessAX.Expr.fstFalse φ2) with hφ3
  have hfst3 : φ3 GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    have h1x : φ3 GuessAX.Vars.fst = GuessAX.eval I GuessAX.Expr.fstFalse φ2 :=
      Function.update_self _ _ _
    simp only [h1x, GuessAX.eval]; rfl
  have hne_cnt_fst : GuessAX.Vars.cnt ≠ GuessAX.Vars.fst := by decide
  have hcnt3raw : φ3 GuessAX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    have h1x : φ3 GuessAX.Vars.cnt = φ2 GuessAX.Vars.cnt := Function.update_of_ne hne_cnt_fst _ _
    rw [h1x, hcnt2raw]
  have hne_aux_cnt : GuessAX.Vars.aux ≠ GuessAX.Vars.cnt := by decide
  have hne_aux_prev : GuessAX.Vars.aux ≠ GuessAX.Vars.prev := by decide
  have hne_aux_fst : GuessAX.Vars.aux ≠ GuessAX.Vars.fst := by decide
  have haux_φ2 : φ2 GuessAX.Vars.aux = φ GuessAX.Vars.aux := by
    have h1x : φ2 GuessAX.Vars.aux = φ1 GuessAX.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    have h2x : φ1 GuessAX.Vars.aux = φ GuessAX.Vars.aux := Function.update_of_ne hne_aux_prev _ _
    rw [h1x, h2x]
  have haux_φ3 : φ3 GuessAX.Vars.aux = φ GuessAX.Vars.aux := by
    have h1x : φ3 GuessAX.Vars.aux = φ2 GuessAX.Vars.aux := Function.update_of_ne hne_aux_fst _ _
    rw [h1x, haux_φ2]
  have hne_j_cnt : GuessAX.Vars.j ≠ GuessAX.Vars.cnt := by decide
  have hne_j_prev : GuessAX.Vars.j ≠ GuessAX.Vars.prev := by decide
  have hne_j_fst : GuessAX.Vars.j ≠ GuessAX.Vars.fst := by decide
  have hj_φ2 : GuessAX.jOf I φ2 = GuessAX.jOf I φ := by
    have h1x : φ2 GuessAX.Vars.j = φ1 GuessAX.Vars.j := Function.update_of_ne hne_j_cnt _ _
    have h2x : φ1 GuessAX.Vars.j = φ GuessAX.Vars.j := Function.update_of_ne hne_j_prev _ _
    simp only [GuessAX.jOf, h1x, h2x]
  have hj_φ3 : GuessAX.jOf I φ3 = GuessAX.jOf I φ := by
    have h1x : φ3 GuessAX.Vars.j = φ2 GuessAX.Vars.j := Function.update_of_ne hne_j_fst _ _
    simp only [GuessAX.jOf, h1x]; exact hj_φ2
  have hxTagFirst3 : (GuessAX.Vocab I).evalV GuessAX.VExpr.xTagFirst φ3 =
      Val.xTag (Tid.guessAX, true) (GuessAX.jthLetter I (GuessAX.auxOf I φ) (GuessAX.jOf I φ)) := by
    simp only [GuessAX.Vocab, GuessAX.evalV, GuessAX.auxOf, haux_φ3, hj_φ3]; rfl
  have hcntVal3 : (GuessAX.Vocab I).evalV GuessAX.VExpr.cntVal φ3 = Val.cnt (k + 1) := by
    have hcnt3 : GuessAX.cntOf I φ3 = k + 1 := by simp only [GuessAX.cntOf, hcnt3raw]
    simp only [GuessAX.Vocab, GuessAX.evalV, hcnt3]; rfl
  have h1 : Command.RunStep Tid.guessAX rest none (guessAXInnerLoop I, φ) rest
      (Command.loopSeq (Command.seq (GuessAX.innerBody I)
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [guessAXInnerLoop, Command.step, GuessAX.Vocab, hguard', if_true])
  have w1 := Command.step_complete h1
  have h2 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq (GuessAX.innerBody I)
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.assign GuessAX.Vars.cnt GuessAX.Expr.nextCnt)
          (Command.ite GuessAX.BExpr.isFirst
            (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
                (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
                (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ1) := by
    rw [hφ1]
    exact Command.step_sound _ _ _ _ _ _ _ (by
      simp only [GuessAX.innerBody, Command.firstIt, Command.step, GuessAX.Vocab]; rfl)
  have w2 := Command.step_complete h2
  have h3 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.assign GuessAX.Vars.cnt GuessAX.Expr.nextCnt)
          (Command.ite GuessAX.BExpr.isFirst
            (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
                (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
                (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ1) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessAX.Vars.cnt GuessAX.Expr.nextCnt)
          (Command.ite GuessAX.BExpr.isFirst
            (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
                (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
                (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ1) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w3 := Command.step_complete h3
  have h4 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessAX.Vars.cnt GuessAX.Expr.nextCnt)
          (Command.ite GuessAX.BExpr.isFirst
            (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
                (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
                (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ1) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.ite GuessAX.BExpr.isFirst
          (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
              (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
              (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) := by
    rw [hφ2]
    exact Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessAX.Vocab])
  have w4 := Command.step_complete h4
  have h5 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.ite GuessAX.BExpr.isFirst
          (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
              (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
              (Command.read Loc.zAxx' GuessAX.VExpr.prevVal)))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.ite GuessAX.BExpr.isFirst
          (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
              (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
              (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w5 := Command.step_complete h5
  have h6 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        (Command.ite GuessAX.BExpr.isFirst
          (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
              (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
              (Command.read Loc.zAxx' GuessAX.VExpr.prevVal))))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
            (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [Command.step, GuessAX.Vocab, hisFirst2']; rfl)
  have w6 := Command.step_complete h6
  have h7 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessAX.Vars.fst GuessAX.Expr.fstFalse)
          (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
            (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
          (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ3) := by
    rw [hφ3]
    exact Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessAX.Vocab])
  have w7 := Command.step_complete h7
  have h8 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
          (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ3) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
          (Command.write Loc.zAx'x GuessAX.VExpr.cntVal))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w8 := Command.step_complete h8
  have h9 : Command.RunStep Tid.guessAX rest
      (some ⟨EventLabel.wt Tid.guessAX Loc.xA ((GuessAX.Vocab I).evalV GuessAX.VExpr.xTagFirst φ3),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.xA GuessAX.VExpr.xTagFirst)
          (Command.write Loc.zAx'x GuessAX.VExpr.cntVal))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ3) rest
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip
          (Command.write Loc.zAx'x GuessAX.VExpr.cntVal))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w9 := Command.step_complete h9
  have h10 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip
          (Command.write Loc.zAx'x GuessAX.VExpr.cntVal))
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ3) rest
      (Command.loopSeq (Command.seq
        (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w10 := Command.step_complete h10
  have h11 : Command.RunStep Tid.guessAX rest
      (some ⟨EventLabel.wt Tid.guessAX Loc.zAx'x ((GuessAX.Vocab I).evalV GuessAX.VExpr.cntVal φ3),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.write Loc.zAx'x GuessAX.VExpr.cntVal)
        (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I), φ3) rest
      (Command.loopSeq (Command.seq
        Command.skip (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I),
        φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w11 := Command.step_complete h11
  have h12 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.seq
        Command.skip (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr)) (guessAXInnerLoop I),
        φ3) rest
      (Command.loopSeq (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr) (guessAXInnerLoop I),
        φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w12 := Command.step_complete h12
  have h13 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq (Command.assign GuessAX.Vars.j GuessAX.Expr.jIncr) (guessAXInnerLoop I),
        φ3) rest
      (Command.loopSeq Command.skip (guessAXInnerLoop I),
        Function.update φ3 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ3)) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessAX.Vocab])
  have w13 := Command.step_complete h13
  have h14 : Command.RunStep Tid.guessAX rest none
      (Command.loopSeq Command.skip (guessAXInnerLoop I),
        Function.update φ3 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ3)) rest
      (guessAXInnerLoop I,
        Function.update φ3 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ3)) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w14 := Command.step_complete h14
  have hj_final : Function.update φ3 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ3)
      GuessAX.Vars.j = GuessAX.eval I GuessAX.Expr.jIncr φ := by
    have hself : Function.update φ3 GuessAX.Vars.j (GuessAX.eval I GuessAX.Expr.jIncr φ3)
        GuessAX.Vars.j = GuessAX.eval I GuessAX.Expr.jIncr φ3 := Function.update_self _ _ _
    rw [hself]
    have hjeq : GuessAX.eval I GuessAX.Expr.jIncr φ3 = GuessAX.eval I GuessAX.Expr.jIncr φ := by
      simp only [GuessAX.eval, hj_φ3]
    rw [hjeq]
  have hne_j_aux : GuessAX.Vars.j ≠ GuessAX.Vars.aux := by decide
  have hne_j_cntY : GuessAX.Vars.j ≠ GuessAX.Vars.cntY := by decide
  have hne_j_N : GuessAX.Vars.j ≠ GuessAX.Vars.N := by decide
  have hne_cntY_cnt : GuessAX.Vars.cntY ≠ GuessAX.Vars.cnt := by decide
  have hne_cntY_prev : GuessAX.Vars.cntY ≠ GuessAX.Vars.prev := by decide
  have hne_cntY_fst : GuessAX.Vars.cntY ≠ GuessAX.Vars.fst := by decide
  have hcntY_φ2 : φ2 GuessAX.Vars.cntY = φ GuessAX.Vars.cntY := by
    have h1x : φ2 GuessAX.Vars.cntY = φ1 GuessAX.Vars.cntY := Function.update_of_ne hne_cntY_cnt _ _
    have h2x : φ1 GuessAX.Vars.cntY = φ GuessAX.Vars.cntY := Function.update_of_ne hne_cntY_prev _ _
    rw [h1x, h2x]
  have hcntY_φ3 : φ3 GuessAX.Vars.cntY = φ GuessAX.Vars.cntY := by
    have h1x : φ3 GuessAX.Vars.cntY = φ2 GuessAX.Vars.cntY := Function.update_of_ne hne_cntY_fst _ _
    rw [h1x, hcntY_φ2]
  have hne_N_cnt : GuessAX.Vars.N ≠ GuessAX.Vars.cnt := by decide
  have hne_N_prev : GuessAX.Vars.N ≠ GuessAX.Vars.prev := by decide
  have hne_N_fst : GuessAX.Vars.N ≠ GuessAX.Vars.fst := by decide
  have hN_φ2 : φ2 GuessAX.Vars.N = φ GuessAX.Vars.N := by
    have h1x : φ2 GuessAX.Vars.N = φ1 GuessAX.Vars.N := Function.update_of_ne hne_N_cnt _ _
    have h2x : φ1 GuessAX.Vars.N = φ GuessAX.Vars.N := Function.update_of_ne hne_N_prev _ _
    rw [h1x, h2x]
  have hN_φ3 : φ3 GuessAX.Vars.N = φ GuessAX.Vars.N := by
    have h1x : φ3 GuessAX.Vars.N = φ2 GuessAX.Vars.N := Function.update_of_ne hne_N_fst _ _
    rw [h1x, hN_φ2]
  refine ⟨_,
    (Function.update_of_ne hne_j_fst.symm _ _).trans hfst3,
    (Function.update_of_ne hne_j_cnt.symm _ _).trans hcnt3raw,
    hj_final,
    (Function.update_of_ne hne_j_aux.symm _ _).trans haux_φ3,
    (Function.update_of_ne hne_j_cntY.symm _ _).trans hcntY_φ3,
    (Function.update_of_ne hne_j_N.symm _ _).trans hN_φ3, ?_⟩
  simp only [Command.runFuel, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    hxTagFirst3, hcntVal3]
  rfl

/-- The converse of `guessAX_outer0_step` (`Completeness/Construction.lean`):
the first outer iteration of `GuessAX`, composed from
`guessAXOuterHead_step_inv`, the first inner call, the inner chain,
`guessAXOuterExit_step`, and `guessAXOuterTail_continue_step_inv`. Fuel
`N + 31 + 14 * K` (`9` head + `14` first call + `14 * K` chain + `2` exit +
`6` tail). -/
theorem guessAX_outer0_step_inv (I : PCPInstance) (K : ℕ) (v0 : Fin I.n)
    (hlen : (I.α v0).length = K + 1)
    (rest : List (GuessAX.Vals I)) (φ : (GuessAX.Vocab I).Store)
    (hfst0 : φ GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)))
    (cnt0 : Fin 4) (hcnt0 : φ GuessAX.Vars.cnt = Sum.inr (Sum.inl cnt0))
    (haux0 : φ GuessAX.Vars.aux = Sum.inl (some v0))
    (cntY0 : Fin 4) (hcntY0 : φ GuessAX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (v0' : Option (Fin I.n))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAX))
    (cf : Config (domainOf I) (GuessAX.Vocab I)) (sf : List (GuessAX.Vals I))
    (h : Command.runFuel Tid.guessAX (guessAXLoop I, φ) (Sum.inl v0' :: rest) (N + 31 + 14 * K) =
      (.stuck, σ, cf, sf)) :
    ∃ (v1 v2 : Val I) (vs : List (Val I × Val I × Val I)) (φ' : (GuessAX.Vocab I).Store)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAX)),
      vs.length = K ∧
      v2 = Val.cnt (cnt0 + 1) ∧
      (∃ j : Fin (GuessAX.maxLen I + 2), j.val = 1 ∧
        v1 = Val.xTag (Tid.guessAX, true) (GuessAX.jthLetter I (some v0) j)) ∧
      (∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨((cnt0 + 1).val + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨((cnt0 + 1).val + n + 1) % 4, by omega⟩ : Fin 4)) ∧
      (∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 2 ∧
        e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some v0) j)) ∧
      φ' GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
      φ' GuessAX.Vars.aux = Sum.inl v0' ∧
      (∃ cntF : Fin 4, φ' GuessAX.Vars.cnt = Sum.inr (Sum.inl cntF) ∧
        cntF = (⟨((cnt0 + 1).val + K) % 4, by omega⟩ : Fin 4)) ∧
      φ' GuessAX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) ∧
      σ = [ ⟨EventLabel.wt Tid.guessAX Loc.zAxy (Val.cnt (cntY0 + 1)), rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
          vs.flatMap (guessAXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx (Val.cntAux (cntY0 + 1) (some v0)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.guessAX (guessAXLoop I, φ') rest N = (.stuck, σ1, cf, sf) := by
  have hfuel0 : N + 31 + 14 * K = (N + 14 + 14 * K + 2 + 6) + 9 := by omega
  rw [hfuel0] at h
  obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
    guessAXOuterHead_step_inv I (Sum.inl v0' :: rest) φ (some v0) haux0 cntY0 hcntY0
      (N + 14 + 14 * K + 2 + 6) σ cf sf h
  have hNOf_h' : (GuessAX.NOf I φh).val = (I.α v0).length := by
    rw [hNOf_h]; simp [GuessAX.extAlpha, List.length_map]
  have hNOf_hK : (GuessAX.NOf I φh).val = K + 1 := by rw [hNOf_h', hlen]
  have hfst_head : φh GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)) := by
    rw [hfst_h, hfst0]
  have hcnt_head : φh GuessAX.Vars.cnt = Sum.inr (Sum.inl cnt0) := by rw [hcnt_h, hcnt0]
  have hmaxpos := GuessAX.maxLen_pos I
  have hguard_first : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φh = true := by
    simp only [GuessAX.Vocab, GuessAX.evalB, decide_eq_true_eq, Fin.le_def]
    omega
  obtain ⟨φ1, hfst1, hcnt1, hj1, haux1, hcntY1, hN1, hstep14⟩ :=
    guessAX_innerLoop_first_step_outOfFuel I (Sum.inl v0' :: rest) φh hguard_first hfst_head
      cnt0 hcnt_head
  set C2 : Command (domainOf I) (GuessAX.Vocab I) :=
    Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
      (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
          (GuessAX.auxSetBot_nonempty I))) with hC2
  have hstep14_seq :=
    Command.runFuel_seqCongr_outOfFuel 14 (guessAXInnerLoop I) C2 φh (Sum.inl v0' :: rest)
      (guessAXInnerLoop I) φ1 _ (Sum.inl v0' :: rest) hstep14
  have hstep14_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 14 (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φh (Sum.inl v0' :: rest) (Command.seq (guessAXInnerLoop I) C2) φ1 _
      (Sum.inl v0' :: rest) hstep14_seq
  have hjOf1val : (GuessAX.jOf I φ1).val = (GuessAX.jOf I φh).val + 1 := by
    have heval : GuessAX.jOf I φ1 = GuessAX.jOf I φh + 1 := by
      simp only [GuessAX.jOf, hj1, GuessAX.eval]
    have h1val : (1 : Fin (GuessAX.maxLen I + 2)).val = 1 := by simp [Fin.val_one']
    rw [heval, Fin.val_add_eq_of_add_lt (by rw [h1val]; omega), h1val]
  have hNOf1 : (GuessAX.NOf I φ1).val = (GuessAX.NOf I φh).val := by
    simp only [GuessAX.NOf, hN1]
  have hNbound1 : (GuessAX.NOf I φ1).val ≤ GuessAX.maxLen I := by
    rw [hNOf1, hNOf_hK]
    have hextle := GuessAX.extAlpha_length_le I (some v0)
    simp only [GuessAX.extAlpha, List.length_map] at hextle
    omega
  have hK1 : (GuessAX.jOf I φ1).val + K = (GuessAX.NOf I φ1).val + 1 := by
    rw [hjOf1val, hjOf_h, hNOf1, hNOf_hK]; omega
  obtain ⟨vs, φ2, hvslen, hcntf, hauxf, hcntYf, hNf, hfstf, hjf, hval, hvalx, hstepChain⟩ :=
    guessAXInnerLoop_chain_outOfFuel I K (Sum.inl v0' :: rest) φ1 hK1 (cnt0 + 1) hcnt1 hfst1
      hNbound1
  have hstepChain_seq :=
    Command.runFuel_seqCongr_outOfFuel (14 * K) (guessAXInnerLoop I) C2 φ1
      (Sum.inl v0' :: rest) (guessAXInnerLoop I) φ2 _ (Sum.inl v0' :: rest) hstepChain
  have hstepChain_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel (14 * K) (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φ1 (Sum.inl v0' :: rest) (Command.seq (guessAXInnerLoop I) C2) φ2 _
      (Sum.inl v0' :: rest) hstepChain_seq
  have hcomb14K :=
    Command.runFuel_outOfFuel_append 14
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hstep14_loop (14 * K) _ _ _ _ hstepChain_loop
  have hNOf2 : (GuessAX.NOf I φ2).val = (GuessAX.NOf I φ1).val := by
    simp only [GuessAX.NOf, hNf]
  have hguardFalse2 : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ2 = false := by
    simp only [GuessAX.Vocab, GuessAX.evalB, decide_eq_false_iff_not, Fin.le_def]
    omega
  have hexit := guessAXOuterExit_step_outOfFuel I (Sum.inl v0' :: rest) φ2 C2 hguardFalse2
  have hexit_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φ2 (Sum.inl v0' :: rest) C2 φ2 [] (Sum.inl v0' :: rest) hexit
  have hcombAll :=
    Command.runFuel_outOfFuel_append (14 + 14 * K)
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hcomb14K 2 _ _ _ _ hexit_loop
  have hfuel1 : N + 14 + 14 * K + 2 + 6 = (14 + 14 * K + 2) + (N + 6) := by omega
  rw [hfuel1] at runH
  obtain ⟨σ1b, runTailPre, hσ1eq⟩ :=
    Command.runFuel_outOfFuel_split (14 + 14 * K + 2)
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hcombAll (N + 6) _ σ1a cf sf runH
  have hauxOf_φ2 : φ2 GuessAX.Vars.aux = Sum.inl (some v0) := by
    rw [hauxf, haux1, haux_h, haux0]
  have hcntY_φ2 : φ2 GuessAX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
    rw [hcntYf, hcntY1, hcntY_h]
  obtain ⟨σ1c, hσ1beq, runFinal⟩ :=
    guessAXOuterTail_continue_step_inv I v0' rest φ2 (cntY0 + 1) hcntY_φ2 v0 hauxOf_φ2
      (N + 6 - 6) σ1b cf sf (by rw [show N + 6 - 6 = N from by omega]; exact runTailPre)
  refine ⟨Val.xTag (Tid.guessAX, true)
      (GuessAX.jthLetter I (GuessAX.auxOf I φh) (GuessAX.jOf I φh)),
    Val.cnt (cnt0 + 1), vs, Function.update φ2 GuessAX.Vars.aux (Sum.inl v0'), σ1c,
    hvslen, rfl, ⟨GuessAX.jOf I φh, hjOf_h, ?_⟩, hval, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · rw [show GuessAX.auxOf I φh = some v0 from by simp only [GuessAX.auxOf, haux_h, haux0]]
  · intro n hn
    have hn' : n < K := by rw [← hvslen]; exact hn
    obtain ⟨e, j, he, hjval, he1⟩ := hvalx n hn'
    refine ⟨e, j, he, ?_, ?_⟩
    · rw [hjval, hjOf1val, hjOf_h]; omega
    · rw [he1]
      congr 1
      simp only [GuessAX.auxOf, haux1, haux_h, haux0]
  · have hne_aux_fst : GuessAX.Vars.aux ≠ GuessAX.Vars.fst := by decide
    exact (Function.update_of_ne hne_aux_fst.symm _ _).trans hfstf
  · exact ⟨(⟨((cnt0 + 1).val + K) % 4, by omega⟩ : Fin 4),
      by
        have hne_aux_cnt : GuessAX.Vars.aux ≠ GuessAX.Vars.cnt := by decide
        exact (Function.update_of_ne hne_aux_cnt.symm _ _).trans hcntf,
      rfl⟩
  · have hne_aux_cntY : GuessAX.Vars.aux ≠ GuessAX.Vars.cntY := by decide
    exact (Function.update_of_ne hne_aux_cntY.symm _ _).trans hcntY_φ2
  · rw [hσeq, hσ1eq, hσ1beq]
    simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]
  · exact runFinal

/-- The converse of `guessAX_outerRest_continue_step`
(`Completeness/Construction.lean`): a continuing later outer iteration
(`fst = false`), whose `K + 1` inner calls form one chain. Fuel
`N + 31 + 14 * K`. -/
theorem guessAX_outerRest_continue_step_inv (I : PCPInstance) (K : ℕ) (w : Fin I.n)
    (hlen : (I.α w).length = K + 1)
    (rest : List (GuessAX.Vals I)) (φ : (GuessAX.Vocab I).Store)
    (hfst : φ GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)))
    (cnt0 : Fin 4) (hcnt0 : φ GuessAX.Vars.cnt = Sum.inr (Sum.inl cnt0))
    (haux : φ GuessAX.Vars.aux = Sum.inl (some w))
    (cntY0 : Fin 4) (hcntY0 : φ GuessAX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (v0' : Option (Fin I.n))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAX))
    (cf : Config (domainOf I) (GuessAX.Vocab I)) (sf : List (GuessAX.Vals I))
    (h : Command.runFuel Tid.guessAX (guessAXLoop I, φ) (Sum.inl v0' :: rest) (N + 31 + 14 * K) =
      (.stuck, σ, cf, sf)) :
    ∃ (vs : List (Val I × Val I × Val I)) (φ' : (GuessAX.Vocab I).Store)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAX)),
      vs.length = K + 1 ∧
      φ' GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
      φ' GuessAX.Vars.aux = Sum.inl v0' ∧
      (∃ cntF : Fin 4, φ' GuessAX.Vars.cnt = Sum.inr (Sum.inl cntF) ∧
        cntF = (⟨(cnt0.val + (K + 1)) % 4, by omega⟩ : Fin 4)) ∧
      φ' GuessAX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) ∧
      (∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(cnt0.val + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(cnt0.val + n + 1) % 4, by omega⟩ : Fin 4)) ∧
      (∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some w) j)) ∧
      σ = [ ⟨EventLabel.wt Tid.guessAX Loc.zAxy (Val.cnt (cntY0 + 1)), rfl⟩ ] ++
          vs.flatMap (guessAXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx (Val.cntAux (cntY0 + 1) (some w)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.guessAX (guessAXLoop I, φ') rest N = (.stuck, σ1, cf, sf) := by
  have hfuel0 : N + 31 + 14 * K = (N + 14 * (K + 1) + 2 + 6) + 9 := by omega
  rw [hfuel0] at h
  obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
    guessAXOuterHead_step_inv I (Sum.inl v0' :: rest) φ (some w) haux cntY0 hcntY0
      (N + 14 * (K + 1) + 2 + 6) σ cf sf h
  have hNOf_h' : (GuessAX.NOf I φh).val = (I.α w).length := by
    rw [hNOf_h]; simp [GuessAX.extAlpha, List.length_map]
  have hNOf_hK : (GuessAX.NOf I φh).val = K + 1 := by rw [hNOf_h', hlen]
  have hfst_head : φh GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    rw [hfst_h, hfst]
  have hcnt_head : φh GuessAX.Vars.cnt = Sum.inr (Sum.inl cnt0) := by rw [hcnt_h, hcnt0]
  have hmaxpos := GuessAX.maxLen_pos I
  have hNbound_head : (GuessAX.NOf I φh).val ≤ GuessAX.maxLen I := by
    rw [hNOf_hK]
    have hextle := GuessAX.extAlpha_length_le I (some w)
    simp only [GuessAX.extAlpha, List.length_map] at hextle
    omega
  have hK_head : (GuessAX.jOf I φh).val + (K + 1) = (GuessAX.NOf I φh).val + 1 := by
    rw [hjOf_h, hNOf_hK]; omega
  set C2 : Command (domainOf I) (GuessAX.Vocab I) :=
    Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
      (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
          (GuessAX.auxSetBot_nonempty I))) with hC2
  obtain ⟨vs, φ2, hvslen, hcntf, hauxf, hcntYf, hNf, hfstf, hjf, hval, hvalx, hstepChain⟩ :=
    guessAXInnerLoop_chain_outOfFuel I (K + 1) (Sum.inl v0' :: rest) φh hK_head cnt0 hcnt_head
      hfst_head hNbound_head
  have hstepChain_seq :=
    Command.runFuel_seqCongr_outOfFuel (14 * (K + 1)) (guessAXInnerLoop I) C2 φh
      (Sum.inl v0' :: rest) (guessAXInnerLoop I) φ2 _ (Sum.inl v0' :: rest) hstepChain
  have hstepChain_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel (14 * (K + 1)) (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φh (Sum.inl v0' :: rest) (Command.seq (guessAXInnerLoop I) C2) φ2 _
      (Sum.inl v0' :: rest) hstepChain_seq
  have hNOf2 : (GuessAX.NOf I φ2).val = (GuessAX.NOf I φh).val := by
    simp only [GuessAX.NOf, hNf]
  have hguardFalse2 : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ2 = false := by
    simp only [GuessAX.Vocab, GuessAX.evalB, decide_eq_false_iff_not, Fin.le_def]
    omega
  have hexit := guessAXOuterExit_step_outOfFuel I (Sum.inl v0' :: rest) φ2 C2 hguardFalse2
  have hexit_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φ2 (Sum.inl v0' :: rest) C2 φ2 [] (Sum.inl v0' :: rest) hexit
  have hcombAll :=
    Command.runFuel_outOfFuel_append (14 * (K + 1))
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hstepChain_loop 2 _ _ _ _ hexit_loop
  have hfuel1 : N + 14 * (K + 1) + 2 + 6 = (14 * (K + 1) + 2) + (N + 6) := by omega
  rw [hfuel1] at runH
  obtain ⟨σ1b, runTailPre, hσ1eq⟩ :=
    Command.runFuel_outOfFuel_split (14 * (K + 1) + 2)
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hcombAll (N + 6) _ σ1a cf sf runH
  have hauxOf_φ2 : φ2 GuessAX.Vars.aux = Sum.inl (some w) := by
    rw [hauxf, haux_h, haux]
  have hcntY_φ2 : φ2 GuessAX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
    rw [hcntYf, hcntY_h]
  obtain ⟨σ1c, hσ1beq, runFinal⟩ :=
    guessAXOuterTail_continue_step_inv I v0' rest φ2 (cntY0 + 1) hcntY_φ2 w hauxOf_φ2
      N σ1b cf sf runTailPre
  refine ⟨vs, Function.update φ2 GuessAX.Vars.aux (Sum.inl v0'), σ1c, hvslen, ?_, rfl,
    ⟨(⟨(cnt0.val + (K + 1)) % 4, by omega⟩ : Fin 4), ?_, rfl⟩, ?_, hval, ?_, ?_, runFinal⟩
  · have hne_aux_fst : GuessAX.Vars.aux ≠ GuessAX.Vars.fst := by decide
    exact (Function.update_of_ne hne_aux_fst.symm _ _).trans hfstf
  · have hne_aux_cnt : GuessAX.Vars.aux ≠ GuessAX.Vars.cnt := by decide
    exact (Function.update_of_ne hne_aux_cnt.symm _ _).trans hcntf
  · have hne_aux_cntY : GuessAX.Vars.aux ≠ GuessAX.Vars.cntY := by decide
    exact (Function.update_of_ne hne_aux_cntY.symm _ _).trans hcntY_φ2
  · intro n hn
    have hn' : n < K + 1 := by rw [← hvslen]; exact hn
    obtain ⟨e, j, he, hjval, he1⟩ := hvalx n hn'
    refine ⟨e, j, he, ?_, ?_⟩
    · rw [hjval, hjOf_h]; omega
    · rw [he1]; congr 1; simp only [GuessAX.auxOf, haux_h, haux]
  · rw [hσeq, hσ1eq, hσ1beq]
    simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]

/-- The converse of `guessAX_outerRest_break_step`
(`Completeness/Construction.lean`): the terminating outer iteration
(`aux = ⊥`), with one inner call (`extAlpha I none = [none]`), reaching
`(Command.skip, φ2)` without consuming the resolution. Fuel `N + 30`. -/
theorem guessAX_outerRest_break_step_inv (I : PCPInstance)
    (rest : List (GuessAX.Vals I)) (φ : (GuessAX.Vocab I).Store)
    (hfst : φ GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)))
    (cnt0 : Fin 4) (hcnt0 : φ GuessAX.Vars.cnt = Sum.inr (Sum.inl cnt0))
    (haux : φ GuessAX.Vars.aux = Sum.inl none)
    (cntY0 : Fin 4) (hcntY0 : φ GuessAX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAX))
    (cf : Config (domainOf I) (GuessAX.Vocab I)) (sf : List (GuessAX.Vals I))
    (h : Command.runFuel Tid.guessAX (guessAXLoop I, φ) rest (N + 30) = (.stuck, σ, cf, sf)) :
    ∃ (vs : List (Val I × Val I × Val I)) (φ' : (GuessAX.Vocab I).Store)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAX)),
      vs.length = 1 ∧
      (∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(cnt0.val + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(cnt0.val + n + 1) % 4, by omega⟩ : Fin 4)) ∧
      (∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I none j)) ∧
      σ = [ ⟨EventLabel.wt Tid.guessAX Loc.zAxy (Val.cnt (cntY0 + 1)), rfl⟩ ] ++
          vs.flatMap (guessAXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx (Val.cntAux (cntY0 + 1) none), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.guessAX (Command.skip, φ') rest N = (.stuck, σ1, cf, sf) := by
  have hfuel0 : N + 30 = (N + 14 + 2 + 5) + 9 := by omega
  rw [hfuel0] at h
  obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
    guessAXOuterHead_step_inv I rest φ none haux cntY0 hcntY0 (N + 14 + 2 + 5) σ cf sf h
  have hNOf_hK : (GuessAX.NOf I φh).val = 1 := by
    rw [hNOf_h]; simp [GuessAX.extAlpha]
  have hfst_head : φh GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    rw [hfst_h, hfst]
  have hcnt_head : φh GuessAX.Vars.cnt = Sum.inr (Sum.inl cnt0) := by rw [hcnt_h, hcnt0]
  have hmaxpos := GuessAX.maxLen_pos I
  have hNbound_head : (GuessAX.NOf I φh).val ≤ GuessAX.maxLen I := by rw [hNOf_hK]; omega
  have hK_head : (GuessAX.jOf I φh).val + 1 = (GuessAX.NOf I φh).val + 1 := by
    rw [hjOf_h, hNOf_hK]
  set C2 : Command (domainOf I) (GuessAX.Vocab I) :=
    Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
      (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
          (GuessAX.auxSetBot_nonempty I))) with hC2
  obtain ⟨vs, φ2, hvslen, hcntf, hauxf, hcntYf, hNf, hfstf, hjf, hval, hvalx, hstepChain⟩ :=
    guessAXInnerLoop_chain_outOfFuel I 1 rest φh hK_head cnt0 hcnt_head hfst_head hNbound_head
  have hstepChain_seq :=
    Command.runFuel_seqCongr_outOfFuel 14 (guessAXInnerLoop I) C2 φh rest
      (guessAXInnerLoop I) φ2 _ rest hstepChain
  have hstepChain_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 14 (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φh rest (Command.seq (guessAXInnerLoop I) C2) φ2 _ rest hstepChain_seq
  have hNOf2 : (GuessAX.NOf I φ2).val = (GuessAX.NOf I φh).val := by
    simp only [GuessAX.NOf, hNf]
  have hguardFalse2 : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ2 = false := by
    simp only [GuessAX.Vocab, GuessAX.evalB, decide_eq_false_iff_not, Fin.le_def]
    omega
  have hexit := guessAXOuterExit_step_outOfFuel I rest φ2 C2 hguardFalse2
  have hexit_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φ2 rest C2 φ2 [] rest hexit
  have hcombAll :=
    Command.runFuel_outOfFuel_append 14
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh)
      rest _ _ _ hstepChain_loop 2 _ _ _ _ hexit_loop
  have hfuel1 : N + 14 + 2 + 5 = (14 + 2) + (N + 5) := by omega
  rw [hfuel1] at runH
  obtain ⟨σ1b, runTailPre, hσ1eq⟩ :=
    Command.runFuel_outOfFuel_split (14 + 2)
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh)
      rest _ _ _ hcombAll (N + 5) _ σ1a cf sf runH
  have hauxOf_φ2 : φ2 GuessAX.Vars.aux = Sum.inl none := by
    rw [hauxf, haux_h, haux]
  have hcntY_φ2 : φ2 GuessAX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
    rw [hcntYf, hcntY_h]
  obtain ⟨σ1c, hσ1beq, runFinal⟩ :=
    guessAXOuterTail_break_step_inv I rest φ2 (cntY0 + 1) hcntY_φ2 hauxOf_φ2 N σ1b cf sf runTailPre
  refine ⟨vs, φ2, σ1c, hvslen, hval, ?_, ?_, runFinal⟩
  · intro n hn
    have hn' : n < 1 := by rw [← hvslen]; exact hn
    obtain ⟨e, j, he, hjval, he1⟩ := hvalx n hn'
    refine ⟨e, j, he, ?_, ?_⟩
    · rw [hjval, hjOf_h]; omega
    · rw [he1]; congr 1; simp only [GuessAX.auxOf, haux_h, haux]
  · rw [hσeq, hσ1eq, hσ1beq]
    simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]

/-- The converse of `guessAXChain_shape` (`Completeness/Construction.lean`):
the outer iterations after the first, from a store with `fst = false`,
`aux = some w0`. By strong induction on the length of the resolution: the
head of the resolution at each draw is determined by running up to the draw
(`guessAXOuterTail_continue_pre_step_outOfFuel`), where an empty or ill-typed
head would leave the run stuck at the draw, not at `(Command.skip, φ')`. -/
theorem guessAX_chain_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (GuessAX.Vals I)), s.length = n →
      ∀ (K0 : ℕ) (w0 : Fin I.n) (hlen0 : (I.α w0).length = K0 + 1)
        (φ : (GuessAX.Vocab I).Store)
        (hfst : φ GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)))
        (cnt0 : Fin 4) (hcnt0 : φ GuessAX.Vars.cnt = Sum.inr (Sum.inl cnt0))
        (haux0 : φ GuessAX.Vars.aux = Sum.inl (some w0))
        (cntY0 : Fin 4) (hcntY0 : φ GuessAX.Vars.cntY = Sum.inr (Sum.inl cntY0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAX))
        (φ' : (GuessAX.Vocab I).Store),
        Command.runFuel Tid.guessAX (guessAXLoop I, φ) s N =
          (.stuck, σ, (Command.skip, φ'), []) →
        ∃ (js : List (Fin I.n))
          (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))),
          s = js.map (fun idx => (Sum.inl (some idx) : GuessAX.Vals I)) ++ [Sum.inl none] ∧
          outerRest.length = js.length + 2 ∧
          (∀ m, m < js.length + 1 → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
            (K0 :: guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1) ∧
          (∃ b vs, outerRest[js.length + 1]? = some (b, vs) ∧ vs.length = 1) ∧
          (∀ m, m < js.length + 2 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
            ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
              e.2.2 = Val.cnt (⟨(cnt0.val + ksPrefix (K0 :: guessAXJsToKs I js) m + n) % 4,
                by omega⟩ : Fin 4) ∧
              e.2.1 = Val.cnt (⟨(cnt0.val + ksPrefix (K0 :: guessAXJsToKs I js) m + n + 1) % 4,
                by omega⟩ : Fin 4)) ∧
          (∀ m, m < js.length + 2 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
            b.1 = Val.cnt (⟨(cntY0.val + 1 + m) % 4, by omega⟩ : Fin 4) ∧
            (m = 0 → b.2 = Val.cntAux (⟨(cntY0.val + 1 + m) % 4, by omega⟩ : Fin 4) (some w0)) ∧
            (1 ≤ m → m ≤ js.length → ∃ w, js[m - 1]? = some w ∧
              b.2 = Val.cntAux (⟨(cntY0.val + 1 + m) % 4, by omega⟩ : Fin 4) (some w)) ∧
            (m = js.length + 1 →
              b.2 = Val.cntAux (⟨(cntY0.val + 1 + m) % 4, by omega⟩ : Fin 4) none)) ∧
          (∀ m, m < js.length + 2 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
            (m = 0 → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
              e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some w0) j)) ∧
            (1 ≤ m → m ≤ js.length → ∃ w, js[m - 1]? = some w ∧
              ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
                e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some w) j)) ∧
            (m = js.length + 1 → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
              e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I none j))) ∧
          σ = outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen K0 w0 hlen0 φ hfst cnt0 hcnt0 haux0 cntY0 hcntY0 N σ φ' h
    -- Run up to the `ndetAssign` draw, with `s` untouched, to determine the
    -- head of `s`.
    have hpre : Command.runFuel Tid.guessAX (guessAXLoop I, φ) s
        (N + (9 + 14 * (K0 + 1) + 2 + 4)) = (.stuck, σ, (Command.skip, φ'), []) :=
      Command.runFuel_stuck_stable h (9 + 14 * (K0 + 1) + 2 + 4)
    have hpad : N + (9 + 14 * (K0 + 1) + 2 + 4) = (N + 14 * (K0 + 1) + 2 + 4) + 9 := by omega
    rw [hpad] at hpre
    obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
      guessAXOuterHead_step_inv I s φ (some w0) haux0 cntY0 hcntY0
        (N + 14 * (K0 + 1) + 2 + 4) σ (Command.skip, φ') [] hpre
    have hNOf_h' : (GuessAX.NOf I φh).val = (I.α w0).length := by
      rw [hNOf_h]; simp [GuessAX.extAlpha, List.length_map]
    have hNOf_hK : (GuessAX.NOf I φh).val = K0 + 1 := by rw [hNOf_h', hlen0]
    have hfst_head : φh GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
      rw [hfst_h, hfst]
    have hcnt_head : φh GuessAX.Vars.cnt = Sum.inr (Sum.inl cnt0) := by rw [hcnt_h, hcnt0]
    have hmaxpos := GuessAX.maxLen_pos I
    have hNbound_head : (GuessAX.NOf I φh).val ≤ GuessAX.maxLen I := by
      rw [hNOf_hK]
      have hextle := GuessAX.extAlpha_length_le I (some w0)
      simp only [GuessAX.extAlpha, List.length_map] at hextle
      omega
    have hK_head : (GuessAX.jOf I φh).val + (K0 + 1) = (GuessAX.NOf I φh).val + 1 := by
      rw [hjOf_h, hNOf_hK]; omega
    set C2 : Command (domainOf I) (GuessAX.Vocab I) :=
      Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
        (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
            (GuessAX.auxSetBot_nonempty I))) with hC2
    obtain ⟨vsc, φ2, hvslenc, hcntfc, hauxfc, hcntYfc, hNfc, hfstfc, hjfc, hvalc, hvalxc,
      hstepChain⟩ :=
      guessAXInnerLoop_chain_outOfFuel I (K0 + 1) s φh hK_head cnt0 hcnt_head hfst_head
        hNbound_head
    have hstepChain_seq :=
      Command.runFuel_seqCongr_outOfFuel (14 * (K0 + 1)) (guessAXInnerLoop I) C2 φh s
        (guessAXInnerLoop I) φ2 _ s hstepChain
    have hstepChain_loop :=
      Command.runFuel_loopSeqCongr_outOfFuel (14 * (K0 + 1)) (Command.seq (guessAXInnerLoop I) C2)
        (guessAXLoop I) φh s (Command.seq (guessAXInnerLoop I) C2) φ2 _ s hstepChain_seq
    have hNOf2 : (GuessAX.NOf I φ2).val = (GuessAX.NOf I φh).val := by
      simp only [GuessAX.NOf, hNfc]
    have hguardFalse2 : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ2 = false := by
      simp only [GuessAX.Vocab, GuessAX.evalB, decide_eq_false_iff_not, Fin.le_def]
      omega
    have hexit := guessAXOuterExit_step_outOfFuel I s φ2 C2 hguardFalse2
    have hexit_loop :=
      Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessAXInnerLoop I) C2)
        (guessAXLoop I) φ2 s C2 φ2 [] s hexit
    have hcomb1 :=
      Command.runFuel_outOfFuel_append (14 * (K0 + 1))
        (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh) s _ _ _
        hstepChain_loop 2 _ _ _ _ hexit_loop
    have hauxOf_φ2 : φ2 GuessAX.Vars.aux = Sum.inl (some w0) := by
      rw [hauxfc, haux_h, haux0]
    have hcntY_φ2 : φ2 GuessAX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
      rw [hcntYfc, hcntY_h]
    have hpref := guessAXOuterTail_continue_pre_step_outOfFuel I s φ2 (cntY0 + 1) hcntY_φ2 w0
      hauxOf_φ2
    have hcombAll :=
      Command.runFuel_outOfFuel_append (14 * (K0 + 1) + 2)
        (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh) s _ _ _
        hcomb1 4 _ _ _ _ hpref
    have hfuel1 : N + 14 * (K0 + 1) + 2 + 4 = (14 * (K0 + 1) + 2 + 4) + N := by omega
    rw [hfuel1] at runH
    obtain ⟨σ1b, hpost, hσ1eq⟩ :=
      Command.runFuel_outOfFuel_split (14 * (K0 + 1) + 2 + 4)
        (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh) s _ _ _
        hcombAll N _ σ1a (Command.skip, φ') [] runH
    -- The head of `s`: empty or ill-typed is impossible, since the run would
    -- be stuck at the draw rather than at `(Command.skip, φ')`.
    rcases s with _ | ⟨c0, rest0⟩
    · exfalso
      cases N with
      | zero =>
          simp only [Command.runFuel] at hpost
          injection hpost with h1'
          injection h1'
      | succ N' =>
          have hstep : Command.step Tid.guessAX
              (Command.loopSeq (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                (GuessAX.auxSetBot_nonempty I)) (guessAXLoop I)) φ2 [] = none := by
            simp only [Command.step, Command.step_ndetAssign_nil]
          simp only [Command.runFuel, hstep] at hpost
          injection hpost with h1' h2'
          injection h2' with h3' h4'
          injection h4' with h5' h6'
          simp only [Prod.mk.injEq] at h5'
          exact absurd h5'.1 (by rintro ⟨⟩)
    · rcases c0 with v0' | c0'
      · -- Sum.inl v0': proceed via the padded original hypothesis.
        have h2 : Command.runFuel Tid.guessAX (guessAXLoop I, φ) (Sum.inl v0' :: rest0)
            (N + 31 + 14 * K0) = (.stuck, σ, (Command.skip, φ'), []) := by
          have h2' := Command.runFuel_stuck_stable h (31 + 14 * K0)
          have hpad2 : N + (31 + 14 * K0) = N + 31 + 14 * K0 := by omega
          rwa [hpad2] at h2'
        obtain ⟨vs1, φ1, σ1x, hlen1, hfst1, haux1, ⟨cntF, hcnt1, hcntFeq1⟩, hcntY1, hval1,
          hvalxA1, hσeq1, hrun1⟩ :=
          guessAX_outerRest_continue_step_inv I K0 w0 hlen0 rest0 φ hfst cnt0 hcnt0 haux0 cntY0
            hcntY0 v0' N σ (Command.skip, φ') [] h2
        cases v0' with
        | none =>
            have hrun1' := Command.runFuel_stuck_stable hrun1 30
            obtain ⟨vs2, φ3, σ2, hlen2, hval2, hvalxA2, hσ2eq, hrun2⟩ :=
              guessAX_outerRest_break_step_inv I rest0 φ1 hfst1 cntF hcnt1 haux1 (cntY0 + 1)
                hcntY1 N σ1x (Command.skip, φ') [] hrun1'
            have hrest0nil : rest0 = [] ∧ σ2 = [] ∧ φ3 = φ' := by
              cases N with
              | zero =>
                  exfalso
                  simp only [Command.runFuel] at hrun2
                  injection hrun2 with hz1
                  injection hz1
              | succ N'' =>
                  have hskipstep : Command.step Tid.guessAX Command.skip φ3 rest0 = none := rfl
                  simp only [Command.runFuel, hskipstep] at hrun2
                  injection hrun2 with e1 e2
                  injection e2 with e3 e4
                  injection e4 with e5 e6
                  injection e5 with e7 e8
                  exact ⟨e6, e3.symm, e8⟩
            obtain ⟨hrest0nil', hσ2nil, hφ3eq⟩ := hrest0nil
            subst hrest0nil'
            refine ⟨[], [((Val.cnt (cntY0 + 1), Val.cntAux (cntY0 + 1) (some w0)), vs1),
                ((Val.cnt (cntY0 + 1 + 1), Val.cntAux (cntY0 + 1 + 1) none), vs2)],
              rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro m hm
              simp only [List.length_nil] at hm
              have hm0 : m = 0 := by omega
              subst hm0
              exact ⟨_, vs1, K0, rfl, rfl, hlen1⟩
            · exact ⟨_, vs2, rfl, hlen2⟩
            · have hcntFeq1' : cntF.val = (cnt0.val + (K0 + 1)) % 4 := by rw [hcntFeq1]
              have hks0 : ksPrefix (K0 :: guessAXJsToKs I ([] : List (Fin I.n))) 0 = 0 := rfl
              have hks1 : ksPrefix (K0 :: guessAXJsToKs I ([] : List (Fin I.n))) 1 = K0 + 1 := by
                rw [show (1 : ℕ) = 0 + 1 from rfl, ksPrefix_cons]
                simp [ksPrefix]
              intro m hm
              have hm2 : m = 0 ∨ m = 1 := by simp only [List.length_nil] at hm; omega
              rcases hm2 with rfl | rfl
              · refine ⟨_, vs1, rfl, ?_⟩
                intro n hn
                obtain ⟨e, he, he22, he21⟩ := hval1 n hn
                refine ⟨e, he, ?_, ?_⟩
                · rw [he22]; simp only [Val.cnt.injEq, Fin.ext_iff]; omega
                · rw [he21]; simp only [Val.cnt.injEq, Fin.ext_iff]; omega
              · refine ⟨_, vs2, rfl, ?_⟩
                intro n hn
                obtain ⟨e, he, he22, he21⟩ := hval2 n hn
                refine ⟨e, he, ?_, ?_⟩
                · rw [he22]; simp only [Val.cnt.injEq, Fin.ext_iff]; omega
                · rw [he21]; simp only [Val.cnt.injEq, Fin.ext_iff]; omega
            · intro m hm
              simp only [List.length_nil] at hm
              have hm2 : m = 0 ∨ m = 1 := by omega
              rcases hm2 with rfl | rfl
              · refine ⟨_, vs1, rfl, ?_, ?_, ?_, ?_⟩
                · rfl
                · intro _; rfl
                · omega
                · omega
              · refine ⟨_, vs2, rfl, ?_, ?_, ?_, ?_⟩
                · dsimp only; first | rfl | (congr 1; apply Fin.ext; simp [Fin.add_def])
                · omega
                · intro _ hmle; simp only [List.length_nil] at hmle; omega
                · intro _; dsimp only; first | rfl | (congr 1; apply Fin.ext; simp [Fin.add_def])
            · intro m hm
              simp only [List.length_nil] at hm
              have hm2 : m = 0 ∨ m = 1 := by omega
              rcases hm2 with rfl | rfl
              · exact ⟨_, vs1, rfl, fun _ => hvalxA1, by omega, by omega⟩
              · refine ⟨_, vs2, rfl, ?_, ?_, ?_⟩
                · omega
                · intro _ hmle; simp only [List.length_nil] at hmle; omega
                · intro _; exact hvalxA2
            · rw [hσeq1, hσ2eq, hσ2nil]
              simp only [guessAXOuterBlockElems, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc, List.nil_append, List.cons_append]
        | some j0 =>
            have hne : I.α j0 ≠ [] := I.hα j0
            have hpos : 0 < (I.α j0).length := List.length_pos_of_ne_nil hne
            have hlen0' : (I.α j0).length = (I.α j0).length - 1 + 1 := by omega
            have hrest0lt : rest0.length < n := by
              have heq : (Sum.inl (some j0) :: rest0).length = n := hslen
              simp only [List.length_cons] at heq
              omega
            obtain ⟨js, outerRest, hseq2, hlen2, houterIH, houterLastIH, hvalIH, hbIH, hbxAIH,
              hσeqIH⟩ :=
              ih rest0.length hrest0lt rest0 rfl ((I.α j0).length - 1) j0 hlen0' φ1 hfst1 cntF
                hcnt1 haux1 (cntY0 + 1) hcntY1 N σ1x φ' hrun1
            have hcntFeq1' : cntF.val = (cnt0.val + (K0 + 1)) % 4 := by rw [hcntFeq1]
            refine ⟨j0 :: js,
              ((Val.cnt (cntY0 + 1), Val.cntAux (cntY0 + 1) (some w0)), vs1) :: outerRest,
              ?_, by simp [hlen2], ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hseq2]; simp only [List.map_cons, List.cons_append]
            · intro m hm
              cases m with
              | zero => exact ⟨_, vs1, K0, rfl, rfl, hlen1⟩
              | succ m =>
                  simp only [List.length_cons] at hm
                  have hm' : m < js.length + 1 := by omega
                  obtain ⟨b, vs, km, hbv, hksm, hlenvs⟩ := houterIH m hm'
                  refine ⟨b, vs, km, by simpa using hbv, ?_, hlenvs⟩
                  change (guessAXJsToKs I (j0 :: js))[m]? = some km
                  rw [show guessAXJsToKs I (j0 :: js)
                      = ((I.α j0).length - 1) :: guessAXJsToKs I js from rfl]
                  exact hksm
            · obtain ⟨b, vs, hbv, hlenvs⟩ := houterLastIH
              exact ⟨b, vs, by simpa using hbv, hlenvs⟩
            · intro m hm
              cases m with
              | zero =>
                refine ⟨_, vs1, rfl, ?_⟩
                intro n hn
                obtain ⟨e, he, he22, he21⟩ := hval1 n hn
                refine ⟨e, he, ?_, ?_⟩
                · rw [he22]; congr 1
                · rw [he21]; congr 1
              | succ m =>
                simp only [List.length_cons] at hm
                have hm' : m < js.length + 2 := by omega
                obtain ⟨b, vs, hbv, hval'⟩ := hvalIH m hm'
                refine ⟨b, vs, by simpa using hbv, ?_⟩
                intro n hn
                obtain ⟨e, he, he22, he21⟩ := hval' n hn
                have hks : ksPrefix (K0 :: guessAXJsToKs I (j0 :: js)) (m + 1)
                    = (K0 + 1) + ksPrefix (((I.α j0).length - 1) :: guessAXJsToKs I js) m := by
                  rw [show guessAXJsToKs I (j0 :: js)
                      = ((I.α j0).length - 1) :: guessAXJsToKs I js from rfl]
                  exact ksPrefix_cons K0 (((I.α j0).length - 1) :: guessAXJsToKs I js) m
                refine ⟨e, he, ?_, ?_⟩
                · rw [he22]
                  congr 1
                  apply Fin.ext
                  show (cntF.val + ksPrefix (((I.α j0).length - 1) :: guessAXJsToKs I js) m + n)
                      % 4 =
                    (cnt0.val + ksPrefix (K0 :: guessAXJsToKs I (j0 :: js)) (m + 1) + n) % 4
                  rw [hks]; omega
                · rw [he21]
                  congr 1
                  apply Fin.ext
                  show (cntF.val + ksPrefix (((I.α j0).length - 1) :: guessAXJsToKs I js) m + n
                      + 1) % 4 =
                    (cnt0.val + ksPrefix (K0 :: guessAXJsToKs I (j0 :: js)) (m + 1) + n + 1) % 4
                  rw [hks]; omega
            · intro m hm
              cases m with
              | zero =>
                refine ⟨_, vs1, rfl, ?_, ?_, ?_, ?_⟩
                · rfl
                · intro _; rfl
                · intro h; omega
                · intro heq; simp only [List.length_cons] at heq; omega
              | succ m =>
                simp only [List.length_cons] at hm
                have hm' : m < js.length + 2 := by omega
                obtain ⟨b, vs, hbv, hb1, hb2z, hb2m, hb2last⟩ := hbIH m hm'
                refine ⟨b, vs, by simpa using hbv, ?_, ?_, ?_, ?_⟩
                · rw [hb1]; congr 1; simp [Fin.add_def]; omega
                · intro h; omega
                · intro _ hmle
                  have hmle' : m + 1 ≤ js.length + 1 := by simpa [List.length_cons] using hmle
                  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
                  · subst hm0
                    have hb2z' := hb2z rfl
                    refine ⟨j0, rfl, ?_⟩
                    rw [hb2z']; congr 1; apply Fin.ext; simp [Fin.add_def]
                  · have hm'le : m ≤ js.length := by omega
                    obtain ⟨w, hw, hb2⟩ := hb2m (by omega) hm'le
                    refine ⟨w, ?_, ?_⟩
                    · show (j0 :: js)[m]? = some w
                      rw [show m = (m - 1) + 1 from by omega, List.getElem?_cons_succ]
                      exact hw
                    · rw [hb2]; congr 1; simp [Fin.add_def]; omega
                · intro heq
                  simp only [List.length_cons] at heq
                  have hm'eq : m = js.length + 1 := by omega
                  have hlast := hb2last hm'eq
                  rw [hlast]; congr 1; apply Fin.ext; simp [Fin.add_def]; omega
            · intro m hm
              cases m with
              | zero => exact ⟨_, vs1, rfl, fun _ => hvalxA1, by omega, by omega⟩
              | succ m =>
                simp only [List.length_cons] at hm
                have hm' : m < js.length + 2 := by omega
                obtain ⟨b, vs, hbv, hbxA0, hbxAm, hbxAlast⟩ := hbxAIH m hm'
                refine ⟨b, vs, by simpa using hbv, ?_, ?_, ?_⟩
                · intro h; omega
                · intro _ hmle
                  have hmle' : m + 1 ≤ js.length + 1 := by simpa [List.length_cons] using hmle
                  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
                  · subst hm0
                    refine ⟨j0, rfl, ?_⟩
                    exact hbxA0 rfl
                  · have hm'le : m ≤ js.length := by omega
                    obtain ⟨w, hw, hbxA⟩ := hbxAm (by omega) hm'le
                    refine ⟨w, ?_, hbxA⟩
                    show (j0 :: js)[m]? = some w
                    rw [show m = (m - 1) + 1 from by omega, List.getElem?_cons_succ]
                    exact hw
                · intro heq
                  simp only [List.length_cons] at heq
                  have hm'eq : m = js.length + 1 := by omega
                  exact hbxAlast hm'eq
            · rw [hσeq1, hσeqIH]
              simp only [guessAXOuterBlockElems, List.flatMap_cons, List.append_assoc,
                List.nil_append, List.cons_append]
      · -- Sum.inr: ill-shaped, ruled out the same way as the empty case.
        exfalso
        cases N with
        | zero =>
            simp only [Command.runFuel] at hpost
            injection hpost with h1'
            injection h1'
        | succ N' =>
            have hnotmem : (Sum.inr c0' : GuessAX.Vals I) ∉ GuessAX.auxSetBot I := by
              simp only [GuessAX.auxSetBot, Finset.mem_image, Finset.mem_univ, true_and]
              rintro ⟨v', hv'⟩
              exact absurd hv' (by simp)
            have hstep : Command.step Tid.guessAX
                (Command.loopSeq (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                  (GuessAX.auxSetBot_nonempty I)) (guessAXLoop I)) φ2 (Sum.inr c0' :: rest0) =
                none := by
              simp only [Command.step]
              split_ifs with hmem
              · exact absurd hmem hnotmem
              · rfl
            simp only [Command.runFuel] at hpost
            have hpost' := hstep ▸ hpost
            injection hpost' with h1' h2'
            injection h2' with h3' h4'
            injection h4' with h5' h6'
            simp only [Prod.mk.injEq] at h5'
            exact absurd h5'.1 (by rintro ⟨⟩)

/-- `c ∈ GuessAX.auxSet I` iff `c = Sum.inl (some v)` for some `v : Fin I.n`. -/
theorem GuessAX.mem_auxSet_iff {I : PCPInstance} (c : GuessAX.Vals I) :
    c ∈ GuessAX.auxSet I ↔ ∃ v, c = Sum.inl (some v) := by
  unfold GuessAX.auxSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv.symm⟩, fun ⟨v, hv⟩ => ⟨v, hv.symm⟩⟩

/-- The converse of `GuessAX.program`'s leading `NDet({1,…,n})` draw: a run
consuming at least two more steps draws some `v0 : Fin I.n` as the head of
`s`. -/
theorem guessAX_lead_step_inv (I : PCPInstance) (s : List (GuessAX.Vals I)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessAX)) (φ' : (GuessAX.Vocab I).Store)
    (h : Command.runFuel Tid.guessAX (GuessAX.program I,
      (GuessAX.Vocab I).mkStore (fun v => match v with
        | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
        | _ => none) (Sum.inl none)) s (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v0 : Fin I.n) (rest : List (GuessAX.Vals I)),
      s = Sum.inl (some v0) :: rest ∧
      Command.runFuel Tid.guessAX
        ((guessAXLoop I).seq Command.term,
          Function.update ((GuessAX.Vocab I).mkStore (fun v => match v with
            | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
            | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
            | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
            | _ => none) (Sum.inl none)) GuessAX.Vars.aux (Sum.inl (some v0))) rest N =
        (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel, Command.step, GuessAX.program] at h
      have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
      exact absurd h2 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.runFuel, Command.step, GuessAX.program] at h
      split_ifs at h with hc
      · obtain ⟨v0, rfl⟩ := (GuessAX.mem_auxSet_iff c).mp hc
        simp only [Command.step, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨v0, rest, rfl, ?_⟩
        change Command.runFuel Tid.guessAX
            ((Command.whileLoop GuessAX.BExpr.tt (GuessAX.outerBody I)).seq Command.term,
              Function.update ((GuessAX.Vocab I).mkStore (fun v => match v with
                | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
                | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
                | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
                | _ => none) (Sum.inl none)) GuessAX.Vars.aux (Sum.inl (some v0))) rest N = _
        exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
      · have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
        exact absurd h2 (by rintro ⟨⟩)

/-- **The word characterization of the threads, `GuessAX`.** The converse of
`guessAX_shape`/`guessAX_general_run`: a term-reaching run of
`GuessAX.program` from its initial store draws some `v0 : Fin I.n`
(`guessAX_lead_step_inv`), with `K0 = (I.α v0).length - 1`; the next draw `v0'`
is determined as in `guessAX_chain_shape_inv`; the first outer iteration is
`guessAX_outer0_step_inv`, after which either `v0' = none` and the loop ends
(`guessAX_outerRest_break_step_inv`) or `v0' = some j0` and the chain
continues (`guessAX_chain_shape_inv`). -/
theorem guessAX_shape_inv (I : PCPInstance) {s : List (GuessAX.Vals I)}
    {φ' : (GuessAX.Vocab I).Store} {cLast : Config (domainOf I) (GuessAX.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.guessAX)}
    (hrun : Command.Run Tid.guessAX s
      (GuessAX.program I, (GuessAX.Vocab I).mkStore (fun v => match v with
        | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : Fin I.n) (K0 : ℕ) (js : List (Fin I.n)) (v1 v2 : Val I) (vB0 : Val I × Val I)
      (inner0Rest : List (Val I × Val I × Val I))
      (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))),
      (I.α v0).length = K0 + 1 ∧
      s = Sum.inl (some v0) ::
        (js.map (fun idx => (Sum.inl (some idx) : GuessAX.Vals I)) ++ [Sum.inl none]) ∧
      inner0Rest.length = K0 ∧
      outerRest.length = js.length + 1 ∧
      (∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
        (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1) ∧
      (∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1) ∧
      v2 = Val.cnt (1 : Fin 4) ∧
      (∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4)) ∧
      (∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
        ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
          e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix (guessAXJsToKs I js) m + n) % 4,
            by omega⟩ : Fin 4) ∧
          e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix (guessAXJsToKs I js) m + n + 1) % 4,
            by omega⟩ : Fin 4)) ∧
      vB0.1 = Val.cnt (1 : Fin 4) ∧
      vB0.2 = Val.cntAux (1 : Fin 4) (some v0) ∧
      (∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
        b.1 = Val.cnt (⟨(2 + m) % 4, by omega⟩ : Fin 4) ∧
        (m < js.length → ∃ w, js[m]? = some w ∧
          b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) (some w)) ∧
        (m = js.length → b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) none)) ∧
      (∃ j : Fin (GuessAX.maxLen I + 2), j.val = 1 ∧
        v1 = Val.xTag (Tid.guessAX, true) (GuessAX.jthLetter I (some v0) j)) ∧
      (∀ n, n < inner0Rest.length → ∃ e j, inner0Rest[n]? = some e ∧ j.val = n + 2 ∧
        e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some v0) j)) ∧
      (∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
        (m < js.length → ∃ w, js[m]? = some w ∧
          ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
            e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some w) j)) ∧
        (m = js.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I none j))) ∧
      σ = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest := by
  have hterm_stuck : ∀ (φt : (GuessAX.Vocab I).Store) (r : List (GuessAX.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.guessAX)) (φt' : (GuessAX.Vocab I).Store),
      Command.runFuel Tid.guessAX (Command.skip, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      False := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        injection hm with hh1
        injection hh1
    | succ m =>
        have hskip : Command.step Tid.guessAX Command.skip φt r = none := rfl
        simp only [Command.runFuel, hskip] at hm
        injection hm with hh1 hh2
        injection hh2 with hh3 hh4
        injection hh4 with hh5 hh6
        simp only [Prod.mk.injEq] at hh5
        exact absurd hh5.1 (by rintro ⟨⟩)
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := guessAX_lead_step_inv I s n σ φ' hn2
  have hne : I.α v0 ≠ [] := I.hα v0
  have hpos : 0 < (I.α v0).length := List.length_pos_of_ne_nil hne
  set K0 : ℕ := (I.α v0).length - 1 with hK0def
  have hlen0 : (I.α v0).length = K0 + 1 := by omega
  have hfst1 : Function.update ((GuessAX.Vocab I).mkStore (fun v => match v with
      | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
      | _ => none) (Sum.inl none)) GuessAX.Vars.aux (Sum.inl (some v0))
      GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)) := by
    have hne' : GuessAX.Vars.fst ≠ GuessAX.Vars.aux := by decide
    exact Function.update_of_ne hne' _ _
  have hcnt1 : Function.update ((GuessAX.Vocab I).mkStore (fun v => match v with
      | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
      | _ => none) (Sum.inl none)) GuessAX.Vars.aux (Sum.inl (some v0))
      GuessAX.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne' : GuessAX.Vars.cnt ≠ GuessAX.Vars.aux := by decide
    exact Function.update_of_ne hne' _ _
  have hcntY1 : Function.update ((GuessAX.Vocab I).mkStore (fun v => match v with
      | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
      | _ => none) (Sum.inl none)) GuessAX.Vars.aux (Sum.inl (some v0))
      GuessAX.Vars.cntY = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne' : GuessAX.Vars.cntY ≠ GuessAX.Vars.aux := by decide
    exact Function.update_of_ne hne' _ _
  set φ0 : (GuessAX.Vocab I).Store :=
    Function.update ((GuessAX.Vocab I).mkStore (fun v => match v with
      | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
      | _ => none) (Sum.inl none)) GuessAX.Vars.aux (Sum.inl (some v0)) with hφ0
  have haux0 : φ0 GuessAX.Vars.aux = Sum.inl (some v0) := Function.update_self _ _ _
  -- Remove the `.seq _ Command.term` wrapper (`Command.runFuel_seqTerm_stuck_unwrap`),
  -- reaching `guessAXLoop I` with target `(Command.skip, φ')`.
  obtain ⟨n', hneq, h2bare⟩ :=
    Command.runFuel_seqTerm_stuck_unwrap n (guessAXLoop I) φ0 rest σ φ' h2
  have hpre : Command.runFuel Tid.guessAX (guessAXLoop I, φ0) rest
      (n' + (9 + 14 * (K0 + 1) + 2 + 4)) = (.stuck, σ, (Command.skip, φ'), []) :=
    Command.runFuel_stuck_stable h2bare (9 + 14 * (K0 + 1) + 2 + 4)
  have hpad : n' + (9 + 14 * (K0 + 1) + 2 + 4) = (n' + 14 * (K0 + 1) + 2 + 4) + 9 := by omega
  rw [hpad] at hpre
  obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
    guessAXOuterHead_step_inv I rest φ0 (some v0) haux0 0 hcntY1
      (n' + 14 * (K0 + 1) + 2 + 4) σ (Command.skip, φ') [] hpre
  have hNOf_h' : (GuessAX.NOf I φh).val = (I.α v0).length := by
    rw [hNOf_h]; simp [GuessAX.extAlpha, List.length_map]
  have hNOf_hK : (GuessAX.NOf I φh).val = K0 + 1 := by rw [hNOf_h', hlen0]
  have hfst_head : φh GuessAX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)) := by
    rw [hfst_h, hfst1]
  have hcnt_head : φh GuessAX.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by rw [hcnt_h, hcnt1]
  have hmaxpos := GuessAX.maxLen_pos I
  have hNbound_head : (GuessAX.NOf I φh).val ≤ GuessAX.maxLen I := by
    rw [hNOf_hK]
    have hextle := GuessAX.extAlpha_length_le I (some v0)
    simp only [GuessAX.extAlpha, List.length_map] at hextle
    omega
  have hguard_first : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φh = true := by
    simp only [GuessAX.Vocab, GuessAX.evalB, decide_eq_true_eq, Fin.le_def]
    omega
  obtain ⟨φ1, hfst1', hcnt1', hj1, haux1, hcntY1', hN1, hstep14⟩ :=
    guessAX_innerLoop_first_step_outOfFuel I rest φh hguard_first hfst_head
      (0 : Fin 4) hcnt_head
  set C2 : Command (domainOf I) (GuessAX.Vocab I) :=
    Command.seq (Command.read Loc.ellAyx GuessAX.VExpr.cntYAuxVal)
      (Command.seq (Command.ite GuessAX.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
          (GuessAX.auxSetBot_nonempty I))) with hC2
  have hstep14_seq :=
    Command.runFuel_seqCongr_outOfFuel 14 (guessAXInnerLoop I) C2 φh rest
      (guessAXInnerLoop I) φ1 _ rest hstep14
  have hstep14_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 14 (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φh rest (Command.seq (guessAXInnerLoop I) C2) φ1 _ rest hstep14_seq
  have hjOf1val : (GuessAX.jOf I φ1).val = (GuessAX.jOf I φh).val + 1 := by
    have heval : GuessAX.jOf I φ1 = GuessAX.jOf I φh + 1 := by
      simp only [GuessAX.jOf, hj1, GuessAX.eval]
    have h1val : (1 : Fin (GuessAX.maxLen I + 2)).val = 1 := by simp [Fin.val_one']
    rw [heval, Fin.val_add_eq_of_add_lt (by rw [h1val]; omega), h1val]
  have hNOf1 : (GuessAX.NOf I φ1).val = (GuessAX.NOf I φh).val := by
    simp only [GuessAX.NOf, hN1]
  have hNbound1 : (GuessAX.NOf I φ1).val ≤ GuessAX.maxLen I := by rw [hNOf1]; exact hNbound_head
  have hK1 : (GuessAX.jOf I φ1).val + K0 = (GuessAX.NOf I φ1).val + 1 := by
    rw [hjOf1val, hjOf_h, hNOf1, hNOf_hK]; omega
  obtain ⟨vsc, φ2, hvslenc, hcntfc, hauxfc, hcntYfc, hNfc, hfstfc, hjfc, hvalc, hvalxc,
    hstepChain⟩ :=
    guessAXInnerLoop_chain_outOfFuel I K0 rest φ1 hK1 (0 + 1 : Fin 4) hcnt1' hfst1' hNbound1
  have hstepChain_seq :=
    Command.runFuel_seqCongr_outOfFuel (14 * K0) (guessAXInnerLoop I) C2 φ1 rest
      (guessAXInnerLoop I) φ2 _ rest hstepChain
  have hstepChain_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel (14 * K0) (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φ1 rest (Command.seq (guessAXInnerLoop I) C2) φ2 _ rest hstepChain_seq
  have hcomb1 :=
    Command.runFuel_outOfFuel_append 14
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh) rest _ _ _
      hstep14_loop (14 * K0) _ _ _ _ hstepChain_loop
  have hguardFalse2 : (GuessAX.Vocab I).evalB GuessAX.BExpr.jLeN φ2 = false := by
    simp only [GuessAX.Vocab, GuessAX.evalB, decide_eq_false_iff_not, Fin.le_def]
    have hNOf2 : (GuessAX.NOf I φ2).val = (GuessAX.NOf I φh).val := by
      have hNOf2' : (GuessAX.NOf I φ2).val = (GuessAX.NOf I φ1).val := by
        simp only [GuessAX.NOf, hNfc]
      rw [hNOf2', hNOf1]
    omega
  have hexit := guessAXOuterExit_step_outOfFuel I rest φ2 C2 hguardFalse2
  have hexit_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessAXInnerLoop I) C2)
      (guessAXLoop I) φ2 rest C2 φ2 [] rest hexit
  have hcomb2 :=
    Command.runFuel_outOfFuel_append (14 + 14 * K0)
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh) rest _ _ _
      hcomb1 2 _ _ _ _ hexit_loop
  have hauxOf_φ2 : φ2 GuessAX.Vars.aux = Sum.inl (some v0) := by
    rw [hauxfc, haux1, haux_h, haux0]
  have hcntY_φ2 : φ2 GuessAX.Vars.cntY = Sum.inr (Sum.inl (0 + 1 : Fin 4)) := by
    rw [hcntYfc, hcntY1', hcntY_h]
  have hpref := guessAXOuterTail_continue_pre_step_outOfFuel I rest φ2 (0 + 1 : Fin 4) hcntY_φ2
    v0 hauxOf_φ2
  have hcombAll :=
    Command.runFuel_outOfFuel_append (14 + 14 * K0 + 2)
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh) rest _ _ _
      hcomb2 4 _ _ _ _ hpref
  have hfuel1 : n' + 14 * (K0 + 1) + 2 + 4 = (14 + 14 * K0 + 2 + 4) + n' := by omega
  rw [hfuel1] at runH
  obtain ⟨σ1b, hpost, hσ1eq⟩ :=
    Command.runFuel_outOfFuel_split (14 + 14 * K0 + 2 + 4)
      (Command.loopSeq (Command.seq (guessAXInnerLoop I) C2) (guessAXLoop I), φh) rest _ _ _
      hcombAll n' _ σ1a (Command.skip, φ') [] runH
  rcases rest with _ | ⟨c0, rest0⟩
  · exfalso
    cases n' with
    | zero =>
        simp only [Command.runFuel] at hpost
        injection hpost with h1'
        injection h1'
    | succ n'' =>
        have hstep : Command.step Tid.guessAX
            (Command.loopSeq (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
              (GuessAX.auxSetBot_nonempty I)) (guessAXLoop I)) φ2 [] = none := by
          simp only [Command.step, Command.step_ndetAssign_nil]
        simp only [Command.runFuel] at hpost
        have hpost' := hstep ▸ hpost
        injection hpost' with h1' h2'
        injection h2' with h3' h4'
        injection h4' with h5' h6'
        simp only [Prod.mk.injEq] at h5'
        exact absurd h5'.1 (by rintro ⟨⟩)
  · rcases c0 with v0' | c0'
    · -- Sum.inl v0': dispatch via `guessAX_outer0_step_inv`, bare, directly
      -- (`h2bare` is already unwrapped, so no further lifting is needed).
      have h3 : Command.runFuel Tid.guessAX (guessAXLoop I, φ0) (Sum.inl v0' :: rest0)
          (n' + 31 + 14 * K0) = (.stuck, σ, (Command.skip, φ'), []) := by
        have h3' := Command.runFuel_stuck_stable h2bare (31 + 14 * K0)
        have hpad2 : n' + (31 + 14 * K0) = n' + 31 + 14 * K0 := by omega
        rwa [hpad2] at h3'
      obtain ⟨v1, v2, vs1, φ3, σ1c, hvslen3, hv2eq, ⟨j1, hj1val, hv1eq⟩, hval3, hvalxA3, hfst3,
        haux3, ⟨cntF3, hcnt3, hcntFeq3⟩, hcntY3, hσeq3, h4⟩ :=
        guessAX_outer0_step_inv I K0 v0 hlen0 rest0 φ0 hfst1 (0 : Fin 4) hcnt1 haux0
          (0 : Fin 4) hcntY1 v0' n' σ (Command.skip, φ') [] h3
      have hks0 : ksPrefix (guessAXJsToKs I ([] : List (Fin I.n))) 0 = 0 := rfl
      cases v0' with
      | none =>
          -- `js = []`: the terminating iteration.
          have h4' := Command.runFuel_stuck_stable h4 30
          obtain ⟨vs2, φ5, σ2, hlen2, hval2, hvalxA2, hσ2eq, hrun2⟩ :=
            guessAX_outerRest_break_step_inv I rest0 φ3 hfst3 cntF3 hcnt3 haux3 (0 + 1 : Fin 4)
              hcntY3 n' σ1c (Command.skip, φ') [] h4'
          have hrest0nil : rest0 = [] ∧ σ2 = [] ∧ φ5 = φ' := by
            cases n' with
            | zero =>
                exfalso
                simp only [Command.runFuel] at hrun2
                injection hrun2 with hz1
                injection hz1
            | succ n''' =>
                have hskipstep : Command.step Tid.guessAX Command.skip φ5 rest0 = none := rfl
                simp only [Command.runFuel, hskipstep] at hrun2
                injection hrun2 with e1 e2
                injection e2 with e3 e4
                injection e4 with e5 e6
                injection e5 with e7 e8
                exact ⟨e6, e3.symm, e8⟩
          obtain ⟨hrest0nil', hσ2nil, hφ5eq⟩ := hrest0nil
          subst hrest0nil'
          refine ⟨v0, K0, [], v1, v2, (Val.cnt 1, Val.cntAux 1 (some v0)), vs1,
            [((Val.cnt 2, Val.cntAux 2 none), vs2)], hlen0, ?_, hvslen3, rfl, ?_, ?_, ?_, hval3,
            ?_, rfl, rfl, ?_, ⟨j1, hj1val, hv1eq⟩, hvalxA3, ?_, ?_⟩
          · simp [hs]
          · intro m hm
            simp only [List.length_nil] at hm
            exact absurd hm (by omega)
          · exact ⟨_, vs2, rfl, hlen2⟩
          · rw [hv2eq]; rfl
          · intro m hm
            simp only [List.length_nil] at hm
            have hm0 : m = 0 := by omega
            subst hm0
            refine ⟨_, vs2, rfl, ?_⟩
            intro n hn
            obtain ⟨e, he, he22, he21⟩ := hval2 n hn
            refine ⟨e, he, ?_, ?_⟩
            · rw [he22]; congr 1; apply Fin.ext
              show (cntF3.val + n) % 4 = (1 + K0 + 0 + n) % 4
              rw [hcntFeq3]; simp only [Fin.ext_iff] at hks0 ⊢; omega
            · rw [he21]; congr 1; apply Fin.ext
              show (cntF3.val + n + 1) % 4 = (1 + K0 + 0 + n + 1) % 4
              rw [hcntFeq3]; simp only [Fin.ext_iff] at hks0 ⊢; omega
          · intro m hm
            simp only [List.length_nil] at hm
            have hm0 : m = 0 := by omega
            subst hm0
            refine ⟨_, vs2, rfl, rfl, ?_, ?_⟩
            · intro h; simp only [List.length_nil] at h; omega
            · intro _; rfl
          · intro m hm
            simp only [List.length_nil] at hm
            have hm0 : m = 0 := by omega
            subst hm0
            refine ⟨_, vs2, rfl, ?_, fun _ => hvalxA2⟩
            intro h; simp only [List.length_nil] at h; omega
          · rw [hσeq3, hσ2eq, hσ2nil]
            simp only [guessAXBlockWord, guessAXOuterBlockElems, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, List.append_assoc, List.nil_append,
              List.cons_append, show (0 + 1 : Fin 4) = 1 from rfl, show (1 + 1 : Fin 4) = 2 from rfl]
      | some j0 =>
          have hne : I.α j0 ≠ [] := I.hα j0
          have hpos : 0 < (I.α j0).length := List.length_pos_of_ne_nil hne
          have hlen0' : (I.α j0).length = (I.α j0).length - 1 + 1 := by omega
          obtain ⟨js, outerRest, hseq2, hlen2, houterC, houterLastC, hvalC, hbC, hbxAC, hσeqIH⟩ :=
            guessAX_chain_shape_inv I rest0.length rest0 rfl ((I.α j0).length - 1) j0 hlen0' φ3
              hfst3 cntF3 hcnt3 haux3 (0 + 1 : Fin 4) hcntY3 n' σ1c φ' h4
          refine ⟨v0, K0, j0 :: js, v1, v2, (Val.cnt 1, Val.cntAux 1 (some v0)), vs1, outerRest,
            hlen0, ?_, hvslen3, ?_, ?_, ?_, ?_, hval3, ?_, rfl, rfl, ?_,
            ⟨j1, hj1val, hv1eq⟩, hvalxA3, ?_, ?_⟩
          · simp [hs, hseq2]
          · simpa [List.length_cons] using hlen2
          · intro m hm
            exact houterC m hm
          · exact houterLastC
          · rw [hv2eq]; rfl
          · intro m hm
            obtain ⟨b, vs, hbv, hval'⟩ := hvalC m (by simp only [List.length_cons] at hm; omega)
            refine ⟨b, vs, hbv, ?_⟩
            intro n hn
            obtain ⟨e, he, he22, he21⟩ := hval' n hn
            have hcntF3' : cntF3.val = (1 + K0) % 4 := by rw [hcntFeq3]; rfl
            have hks : guessAXJsToKs I (j0 :: js) = ((I.α j0).length - 1) :: guessAXJsToKs I js := by
              simp only [guessAXJsToKs, List.map_cons]
            refine ⟨e, he, ?_, ?_⟩
            · rw [he22]; congr 1; apply Fin.ext
              show (cntF3.val +
                  ksPrefix (((I.α j0).length - 1) :: guessAXJsToKs I js) m + n) % 4 =
                (1 + K0 + ksPrefix (guessAXJsToKs I (j0 :: js)) m + n) % 4
              rw [hcntF3', hks]; omega
            · rw [he21]; congr 1; apply Fin.ext
              show (cntF3.val +
                  ksPrefix (((I.α j0).length - 1) :: guessAXJsToKs I js) m + n + 1) % 4 =
                (1 + K0 + ksPrefix (guessAXJsToKs I (j0 :: js)) m + n + 1) % 4
              rw [hcntF3', hks]; omega
          · intro m hm
            obtain ⟨b, vs, hbv, hb1, hb2z, hb2m, hb2last⟩ := hbC m (by simp only [List.length_cons] at hm; omega)
            refine ⟨b, vs, hbv, ?_, ?_, ?_⟩
            · rw [hb1]; congr 1
            · intro hmlt
              rcases Nat.eq_zero_or_pos m with hm0 | hmpos
              · subst hm0
                obtain hb2z' := hb2z rfl
                exact ⟨j0, rfl, by rw [hb2z']; congr 1⟩
              · have hm'le : m ≤ js.length := by
                  simp only [List.length_cons] at hm hmlt; omega
                obtain ⟨w, hw, hb2⟩ := hb2m (by omega) hm'le
                refine ⟨w, ?_, ?_⟩
                · show (j0 :: js)[m]? = some w
                  rw [show m = (m - 1) + 1 from by omega, List.getElem?_cons_succ]
                  exact hw
                · rw [hb2]; congr 1
            · intro hmeq
              simp only [List.length_cons] at hmeq
              have hb2last' := hb2last (by omega)
              rw [hb2last']; congr 1
          · intro m hm
            obtain ⟨b, vs, hbv, hbxA0, hbxAm, hbxAlast⟩ :=
              hbxAC m (by simp only [List.length_cons] at hm; omega)
            refine ⟨b, vs, hbv, ?_, ?_⟩
            · intro hmlt
              rcases Nat.eq_zero_or_pos m with hm0 | hmpos
              · subst hm0
                exact ⟨j0, rfl, hbxA0 rfl⟩
              · have hm'le : m ≤ js.length := by
                  simp only [List.length_cons] at hm hmlt; omega
                obtain ⟨w, hw, hbxA⟩ := hbxAm (by omega) hm'le
                refine ⟨w, ?_, hbxA⟩
                show (j0 :: js)[m]? = some w
                rw [show m = (m - 1) + 1 from by omega, List.getElem?_cons_succ]
                exact hw
            · intro hmeq
              simp only [List.length_cons] at hmeq
              exact hbxAlast (by omega)
          · rw [hσeq3, hσeqIH]
            simp only [guessAXBlockWord, List.cons_append, List.append_assoc,
              List.nil_append, List.append_nil, show (0 + 1 : Fin 4) = 1 from rfl]
    · -- Sum.inr: ill-shaped, ruled out the same way as the nil case above.
      exfalso
      cases n' with
      | zero =>
          simp only [Command.runFuel] at hpost
          injection hpost with h1'
          injection h1'
      | succ n'' =>
          have hnotmem : (Sum.inr c0' : GuessAX.Vals I) ∉ GuessAX.auxSetBot I := by
            simp only [GuessAX.auxSetBot, Finset.mem_image, Finset.mem_univ, true_and]
            rintro ⟨v', hv'⟩
            exact absurd hv' (by simp)
          have hstep : Command.step Tid.guessAX
              (Command.loopSeq (Command.ndetAssign GuessAX.Vars.aux (GuessAX.auxSetBot I)
                (GuessAX.auxSetBot_nonempty I)) (guessAXLoop I)) φ2 (Sum.inr c0' :: rest0) =
              none := by
            simp only [Command.step]
            split_ifs with hmem
            · exact absurd hmem hnotmem
            · rfl
          simp only [Command.runFuel] at hpost
          have hpost' := hstep ▸ hpost
          injection hpost' with h1' h2'
          injection h2' with h3' h4'
          injection h4' with h5' h6'
          simp only [Prod.mk.injEq] at h5'
          exact absurd h5'.1 (by rintro ⟨⟩)

/-! ## `PrimeCheckY`

As for `PrimeCheckX`, with `x` replaced by `y`. -/

theorem primeCheckY_iter_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (PrimeCheckY.Vocab I))
    (s : List PrimeCheckY.Vals) (φ : (PrimeCheckY.Vocab I).Store)
    (hb : φ PrimeCheckY.Vars.b = Sum.inr true) (cnt0 : Fin 4)
    (hcnt0 : φ PrimeCheckY.Vars.cnt = Sum.inl cnt0) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeCheckY)) (φ' : (PrimeCheckY.Vocab I).Store)
    (h : Command.runFuel Tid.primeCheckY ((primeCheckYLoop I).seq C2, φ) s (N + 17) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v : Bool) (rest : List PrimeCheckY.Vals)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.primeCheckY)),
      s = Sum.inr v :: rest ∧
      σ = [ ⟨EventLabel.wt Tid.primeCheckY Loc.yA' (Val.primeTag Tid.primeCheckY (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.wt Tid.primeCheckY Loc.yB' (Val.primeTag Tid.primeCheckY (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.primeCheckY Loc.yA' (Val.primeTag Tid.primeAY 0), rfl⟩
          , ⟨EventLabel.rd Tid.primeCheckY Loc.yB' (Val.primeTag Tid.primeBY 0), rfl⟩
          , ⟨EventLabel.rd Tid.primeCheckY Loc.yA
              (Val.primeTag Tid.checkY (cnt0 + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.primeCheckY Loc.yB
              (Val.primeTag Tid.checkY (cnt0 + 1)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.primeCheckY
        ((primeCheckYLoop I).seq C2,
          Function.update (Function.update φ PrimeCheckY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeCheckY.Vars.b (Sum.inr v)) rest N =
        (.stuck, σ1, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeCheckYLoop, PrimeCheckY.Vocab,
    PrimeCheckY.evalB, hb, if_true, PrimeCheckY.evalV, primeCheckYLoopBody, PrimeCheckY.body,
    hcnt0, PrimeCheckY.cntOf, PrimeCheckY.eval, Prod.mk.injEq] at h
  cases s with
  | nil =>
      simp only [Command.step] at h
      exact absurd h.2.2.1 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.step, PrimeCheckY.X, Finset.mem_insert, Finset.mem_singleton] at h
      split_ifs at h with hc
      · obtain ⟨v, rfl⟩ : ∃ v : Bool, c = Sum.inr v := by
          rcases hc with rfl | rfl
          · exact ⟨false, rfl⟩
          · exact ⟨true, rfl⟩
        simp only [Command.step] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨v, rest, _, rfl, h2.symm, ?_⟩
        change Command.runFuel Tid.primeCheckY
            ((Command.whileLoop PrimeCheckY.BExpr.isB
                (((Command.assign PrimeCheckY.Vars.cnt PrimeCheckY.Expr.nextCnt).seq
                      ((Command.write Loc.yA' PrimeCheckY.VExpr.cntTagVal).seq
                        ((Command.write Loc.yB' PrimeCheckY.VExpr.cntTagVal).seq
                          ((Command.read Loc.yA' PrimeCheckY.VExpr.yApExpect).seq
                            ((Command.read Loc.yB' PrimeCheckY.VExpr.yBpExpect).seq
                              ((Command.read Loc.yA PrimeCheckY.VExpr.checkExpect).seq
                                (Command.read Loc.yB PrimeCheckY.VExpr.checkExpect))))))).seq
                  (Command.ndetAssign PrimeCheckY.Vars.b PrimeCheckY.X
                    PrimeCheckY.X_nonempty))).seq C2,
              Function.update (Function.update φ PrimeCheckY.Vars.cnt (Sum.inl (cnt0 + 1)))
                PrimeCheckY.Vars.b (Sum.inr v)) rest N = _
        exact Prod.ext h1 (Prod.ext rfl (Prod.ext h3 h4))
      · exact absurd h.2.2.1 (by rintro ⟨⟩)

theorem primeCheckY_lead_hstep_nil (I : PCPInstance) :
    Command.step Tid.primeCheckY (PrimeCheckY.program I)
      ((PrimeCheckY.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      ([] : List PrimeCheckY.Vals) = none := rfl

theorem primeCheckY_lead_hstep_inl (I : PCPInstance) (k : Fin 4)
    (rest : List PrimeCheckY.Vals) :
    Command.step Tid.primeCheckY (PrimeCheckY.program I)
      ((PrimeCheckY.Vocab I).mkStore
        (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      (Sum.inl k :: rest) = none := rfl

theorem primeCheckY_lead_step_inv (I : PCPInstance) (s : List PrimeCheckY.Vals) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeCheckY)) (φ' : (PrimeCheckY.Vocab I).Store)
    (h : Command.runFuel Tid.primeCheckY (PrimeCheckY.program I, (PrimeCheckY.Vocab I).mkStore
      (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0)) s
      (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (b0 : Bool) (rest : List PrimeCheckY.Vals),
      s = Sum.inr b0 :: rest ∧
      Command.runFuel Tid.primeCheckY
        ((primeCheckYLoop I).seq Command.term,
          Function.update ((PrimeCheckY.Vocab I).mkStore
            (fun v => match v with | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
            PrimeCheckY.Vars.b (Sum.inr b0)) rest N = (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel] at h
      have h2 := primeCheckY_lead_hstep_nil I ▸ h
      dsimp only at h2
      have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
      exact absurd h3 (by rintro ⟨⟩)
  | cons c rest =>
      rcases c with k | b0
      · simp only [Command.runFuel] at h
        have h2 := primeCheckY_lead_hstep_inl I k rest ▸ h
        dsimp only at h2
        have h3 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h2))
        exact absurd h3 (by rintro ⟨⟩)
      · rcases b0 with rfl | rfl
        · simp only [Command.runFuel] at h
          exact ⟨false, rest, rfl, h⟩
        · simp only [Command.runFuel] at h
          exact ⟨true, rest, rfl, h⟩

theorem primeCheckY_stop_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (PrimeCheckY.Vocab I)) (s : List PrimeCheckY.Vals)
    (φ : (PrimeCheckY.Vocab I).Store) (hb : φ PrimeCheckY.Vars.b = Sum.inr false) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.primeCheckY)) (φ' : (PrimeCheckY.Vocab I).Store)
    (h : Command.runFuel Tid.primeCheckY ((primeCheckYLoop I).seq C2, φ) s (N + 2) =
      (.stuck, σ, (Command.term, φ'), [])) :
    Command.runFuel Tid.primeCheckY (C2, φ) s N = (.stuck, σ, (Command.term, φ'), []) := by
  simp only [Command.runFuel, Command.step, primeCheckYLoop, PrimeCheckY.Vocab,
    PrimeCheckY.evalB, hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))

theorem primeCheckY_loop_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List PrimeCheckY.Vals), s.length = n →
      ∀ (φ : (PrimeCheckY.Vocab I).Store) (cnt0 : Fin 4)
        (_hb : φ PrimeCheckY.Vars.b = Sum.inr true)
        (_hcnt0 : φ PrimeCheckY.Vars.cnt = Sum.inl cnt0)
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.primeCheckY))
        (φ' : (PrimeCheckY.Vocab I).Store),
        Command.runFuel Tid.primeCheckY ((primeCheckYLoop I).seq Command.term, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (M' : ℕ) (cnts : List (Fin 4)),
          s = List.replicate M' (Sum.inr true) ++ [Sum.inr false] ∧
          cnts.length = M' + 1 ∧
          (∀ i, i < cnts.length →
            cnts[i]? = some (⟨(cnt0.val + i + 1) % 4, by omega⟩ : Fin 4)) ∧
          σ = primeCheckYBlockWord I cnts := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen φ cnt0 hb hcnt0 N σ φ' h
    have h17 := Command.runFuel_stuck_stable h 17
    obtain ⟨v, rest, σ1, hseq, hσeq, h2⟩ :=
      primeCheckY_iter_step_inv I Command.term s φ hb cnt0 hcnt0 N σ φ' h17
    subst hseq
    cases v with
    | false =>
        have h2' := Command.runFuel_stuck_stable h2 2
        have hbf : Function.update (Function.update φ PrimeCheckY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeCheckY.Vars.b (Sum.inr false) PrimeCheckY.Vars.b = Sum.inr false :=
          Function.update_self _ _ _
        have h3 := primeCheckY_stop_step_inv I Command.term rest _ hbf N σ1 φ' h2'
        have hrest : rest = [] ∧ σ1 = ([] : Word (ThreadLabel (domainOf I) Tid.primeCheckY)) := by
          rcases N with _ | N'
          · simp only [Command.runFuel] at h3
            exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
          · simp only [Command.runFuel, Command.step] at h3
            refine ⟨?_, ?_⟩
            · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
            · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
        obtain ⟨hrest0, hσ10⟩ := hrest
        subst hrest0
        refine ⟨0, [cnt0 + 1], rfl, rfl, ?_, ?_⟩
        · intro i hi
          have hi0 : i = 0 := by simpa using hi
          subst hi0
          simp only [List.getElem?_cons_zero, Option.some.injEq]
          apply Fin.ext
          simp [Fin.add_def]
        · simp only [hσeq, hσ10, List.append_nil, primeCheckYBlockWord, List.flatMap_cons,
            List.flatMap_nil, List.append_nil]
    | true =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inr true :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        have hbnew : Function.update (Function.update φ PrimeCheckY.Vars.cnt (Sum.inl (cnt0 + 1)))
            PrimeCheckY.Vars.b (Sum.inr true) PrimeCheckY.Vars.b = Sum.inr true :=
          Function.update_self _ _ _
        have hne_cntb : PrimeCheckY.Vars.cnt ≠ PrimeCheckY.Vars.b := by decide
        have hcntnew :
            Function.update (Function.update φ PrimeCheckY.Vars.cnt (Sum.inl (cnt0 + 1)))
              PrimeCheckY.Vars.b (Sum.inr true) PrimeCheckY.Vars.cnt = Sum.inl (cnt0 + 1) :=
          (Function.update_of_ne hne_cntb (Sum.inr true) _).trans (Function.update_self _ _ _)
        obtain ⟨M'', cnts'', hrest_eq, hcnts_len, hcnts_val, hσ1⟩ :=
          ih rest.length hrest_len rest rfl
            (Function.update (Function.update φ PrimeCheckY.Vars.cnt (Sum.inl (cnt0 + 1)))
              PrimeCheckY.Vars.b (Sum.inr true))
            (cnt0 + 1) hbnew hcntnew N σ1 φ' h2
        refine ⟨M'' + 1, (cnt0 + 1) :: cnts'', ?_, ?_, ?_, ?_⟩
        · rw [hrest_eq, List.replicate_succ, List.cons_append]
        · simp [hcnts_len]
        · intro i hi
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq]
              apply Fin.ext
              simp [Fin.add_def]
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < cnts''.length := by omega
              have hval' := hcnts_val i hi'
              simp only [List.getElem?_cons_succ]
              rw [hval']
              congr 1
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · rw [hσeq, hσ1]
          simp only [primeCheckYBlockWord, List.flatMap_cons]

/-- **The word characterization of the threads, `PrimeCheckY`.** As
`primeCheckX_shape_inv`. -/
theorem primeCheckY_shape_inv (I : PCPInstance) {s : List PrimeCheckY.Vals}
    {φ' : (PrimeCheckY.Vocab I).Store} {cLast : Config (domainOf I) (PrimeCheckY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.primeCheckY)}
    (hrun : Command.Run Tid.primeCheckY s
      (PrimeCheckY.program I, (PrimeCheckY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
      σ cLast [] (Command.term, φ')) :
    ∃ (M : ℕ) (cnts : List (Fin 4)),
      s = List.replicate M (Sum.inr true) ++ [Sum.inr false] ∧
      cnts.length = M ∧
      (∀ i, i < cnts.length → cnts[i]? = some (⟨(i + 1) % 4, by omega⟩ : Fin 4)) ∧
      σ = primeCheckYBlockWord I cnts := by
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨b0, rest, hs, h2⟩ := primeCheckY_lead_step_inv I s n σ φ' hn2
  cases b0 with
  | false =>
      have hbf : Function.update ((PrimeCheckY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeCheckY.Vars.b (Sum.inr false) PrimeCheckY.Vars.b = Sum.inr false :=
        Function.update_self _ _ _
      have h2' := Command.runFuel_stuck_stable h2 2
      have h3 := primeCheckY_stop_step_inv I Command.term rest _ hbf n σ φ' h2'
      have hrest : rest = [] ∧ σ = ([] : Word (ThreadLabel (domainOf I) Tid.primeCheckY)) := by
        rcases n with _ | n'
        · simp only [Command.runFuel] at h3
          exact absurd (congrArg Prod.fst h3) (by rintro ⟨⟩)
        · simp only [Command.runFuel, Command.step] at h3
          refine ⟨?_, ?_⟩
          · exact congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd h3))
          · exact (congrArg Prod.fst (congrArg Prod.snd h3)).symm
      obtain ⟨hrest0, hσ0⟩ := hrest
      refine ⟨0, [], ?_, rfl, ?_, ?_⟩
      · simp [hs, hrest0]
      · intro i hi; simp at hi
      · simp [hσ0, primeCheckYBlockWord]
  | true =>
      have hb2 : Function.update ((PrimeCheckY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeCheckY.Vars.b (Sum.inr true) PrimeCheckY.Vars.b = Sum.inr true :=
        Function.update_self _ _ _
      have hcnt2 : Function.update ((PrimeCheckY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4)) | .b => none) (Sum.inl 0))
          PrimeCheckY.Vars.b (Sum.inr true) PrimeCheckY.Vars.cnt = Sum.inl (0 : Fin 4) := by
        have hne : PrimeCheckY.Vars.cnt ≠ PrimeCheckY.Vars.b := by decide
        exact Function.update_of_ne hne _ _
      obtain ⟨M', cnts, hrest_eq, hcnts_len, hcnts_val, hσeq⟩ :=
        primeCheckY_loop_shape_inv I rest.length rest rfl _ 0 hb2 hcnt2 n σ φ' h2
      refine ⟨M' + 1, cnts, ?_, ?_, ?_, hσeq⟩
      · rw [hs, hrest_eq, List.replicate_succ, List.cons_append]
      · omega
      · intro i hi
        have := hcnts_val i hi
        simpa using this

/-! ## `CheckY`

As for `CheckX`, with `x` replaced by `y`; `aux` ranges over `Fin I.n`
instead of `I.Γ`. -/

theorem CheckY.mem_auxSet_iff {I : PCPInstance} (c : CheckY.Vals I) :
    c ∈ CheckY.auxSet I ↔ ∃ v, c = Sum.inl (some v) := by
  unfold CheckY.auxSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv.symm⟩, fun ⟨v, hv⟩ => ⟨v, hv.symm⟩⟩

/-- The converse of `CheckY.program`'s leading `NDet({1,…,n})` draw: a run
consuming at least two more steps draws some `v0 : Fin I.n` as the head of
`s`. -/
theorem checkY_lead_step_inv (I : PCPInstance) (s : List (CheckY.Vals I)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.checkY)) (φ' : (CheckY.Vocab I).Store)
    (h : Command.runFuel Tid.checkY (CheckY.program I,
      (CheckY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none)) s (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v0 : (Fin I.n)) (rest : List (CheckY.Vals I)),
      s = Sum.inl (some v0) :: rest ∧
      Command.runFuel Tid.checkY
        ((checkYLoop I).seq Command.term,
          Function.update ((CheckY.Vocab I).mkStore (fun v => match v with
            | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
            | .fst => some (Sum.inr (Sum.inr true))
            | _ => none) (Sum.inl none)) CheckY.Vars.aux (Sum.inl (some v0))) rest N =
        (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel, Command.step, CheckY.program] at h
      have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
      exact absurd h2 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.runFuel, Command.step, CheckY.program] at h
      split_ifs at h with hc
      · obtain ⟨v0, rfl⟩ := (CheckY.mem_auxSet_iff c).mp hc
        simp only [Command.step, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨v0, rest, rfl, ?_⟩
        change Command.runFuel Tid.checkY
            ((Command.whileLoop CheckY.BExpr.tt (CheckY.body I)).seq Command.term,
              Function.update ((CheckY.Vocab I).mkStore (fun v => match v with
                | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
                | .fst => some (Sum.inr (Sum.inr true))
                | _ => none) (Sum.inl none)) CheckY.Vars.aux (Sum.inl (some v0))) rest N = _
        exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
      · have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
        exact absurd h2 (by rintro ⟨⟩)

/-- `c ∈ CheckY.auxSetBot I` iff `c = Sum.inl w` for some
`w : Option (Fin I.n)`. -/
theorem CheckY.mem_auxSetBot_iff {I : PCPInstance} (c : CheckY.Vals I) :
    c ∈ CheckY.auxSetBot I ↔ ∃ w : Option (Fin I.n), c = Sum.inl w := by
  unfold CheckY.auxSetBot
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, hw.symm⟩, fun ⟨w, hw⟩ => ⟨w, hw.symm⟩⟩

/-- The converse of `checkY_block0_step`: a run taking at least 20 more steps
from a store with `fst = true`, `cnt = 0`, `aux = some v0` emits
`checkYBlock0Elems I v0`, consumes some `Sum.inl w` as the head of `s`, and
returns to `checkYLoop` with `fst = false`, `cnt = 1`, `aux = Sum.inl w`. -/
theorem checkY_block0_step_inv (I : PCPInstance) (C2 : Command (domainOf I) (CheckY.Vocab I))
    (s : List (CheckY.Vals I)) (φ : (CheckY.Vocab I).Store)
    (hfst : φ CheckY.Vars.fst = Sum.inr (Sum.inr true))
    (hcnt0 : φ CheckY.Vars.cnt = Sum.inr (Sum.inl 0))
    (v0 : (Fin I.n)) (haux0 : φ CheckY.Vars.aux = Sum.inl (some v0)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.checkY)) (φ' : (CheckY.Vocab I).Store)
    (h : Command.runFuel Tid.checkY ((checkYLoop I).seq C2, φ) s (N + 20) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (w : Option (Fin I.n)) (rest : List (CheckY.Vals I))
      (σ1 : Word (ThreadLabel (domainOf I) Tid.checkY)),
      s = Sum.inl w :: rest ∧
      σ = checkYBlock0Elems I v0 ++ σ1 ∧
      ∃ (φ3 : (CheckY.Vocab I).Store),
        φ3 CheckY.Vars.fst = Sum.inr (Sum.inr false) ∧
        φ3 CheckY.Vars.cnt = Sum.inr (Sum.inl 1) ∧
        φ3 CheckY.Vars.aux = Sum.inl w ∧
        Command.runFuel Tid.checkY ((checkYLoop I).seq C2, φ3) rest N =
          (.stuck, σ1, (Command.term, φ'), []) := by
  set φ1 : (CheckY.Vocab I).Store :=
    Function.update φ CheckY.Vars.prev (CheckY.eval I CheckY.Expr.readCnt φ) with hφ1
  set φ2 : (CheckY.Vocab I).Store :=
    Function.update φ1 CheckY.Vars.cnt (CheckY.eval I CheckY.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 CheckY.Vars.cnt = φ CheckY.Vars.cnt := rfl
  have hcnt2eq : φ2 CheckY.Vars.cnt = CheckY.eval I CheckY.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2 : CheckY.cntOf I φ2 = 1 := by
    simp only [CheckY.cntOf, hcnt2eq, CheckY.eval, hcnt_φ1, hcnt0]
    decide
  have hne_aux_cnt : CheckY.Vars.aux ≠ CheckY.Vars.cnt := by decide
  have haux_φ1 : φ1 CheckY.Vars.aux = φ CheckY.Vars.aux := rfl
  have haux2 : φ2 CheckY.Vars.aux = Sum.inl (some v0) := by
    have h1' : φ2 CheckY.Vars.aux = φ1 CheckY.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    rw [h1', haux_φ1, haux0]
  have hcnt1val : (CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2
      = Val.primeTag Tid.checkY 1 := by
    simp only [CheckY.Vocab, CheckY.evalV, hcnt2]
    rfl
  have hne_fst_cnt : CheckY.Vars.fst ≠ CheckY.Vars.cnt := by decide
  have hfst_φ1 : φ1 CheckY.Vars.fst = φ CheckY.Vars.fst := rfl
  have hfst2 : φ2 CheckY.Vars.fst = Sum.inr (Sum.inr true) := by
    have h1' : φ2 CheckY.Vars.fst = φ1 CheckY.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1', hfst_φ1, hfst]
  set φ3 : (CheckY.Vocab I).Store :=
    Function.update φ2 CheckY.Vars.fst (CheckY.eval I CheckY.Expr.fstFalse φ2) with hφ3
  have hne_aux_fst : CheckY.Vars.aux ≠ CheckY.Vars.fst := by decide
  have haux3 : φ3 CheckY.Vars.aux = Sum.inl (some v0) := by
    have h1' : φ3 CheckY.Vars.aux = φ2 CheckY.Vars.aux := Function.update_of_ne hne_aux_fst _ _
    rw [h1', haux2]
  have hxAFirst : (CheckY.Vocab I).evalV CheckY.VExpr.yAFirst φ3
      = Val.yTag (Tid.guessAY, true) (some v0) := by
    simp only [CheckY.Vocab, CheckY.evalV, CheckY.auxOf, haux3]
    rfl
  have hxBFirst : (CheckY.Vocab I).evalV CheckY.VExpr.yBFirst φ3
      = Val.yTag (Tid.guessBY, true) (some v0) := by
    simp only [CheckY.Vocab, CheckY.evalV, CheckY.auxOf, haux3]
    rfl
  have hisBot3 : CheckY.evalB I CheckY.BExpr.isBot φ3 = false := by
    simp only [CheckY.evalB]
    cases hφ : φ3 CheckY.Vars.aux with
    | inl w => cases w with
        | none => rw [haux3] at hφ; injection hφ with hφ2; injection hφ2
        | some _ => simp
    | inr w => simp
  have hcnt2raw : φ2 CheckY.Vars.cnt = Sum.inr (Sum.inl 1) := by
    simp only [hcnt2eq, CheckY.eval, CheckY.cntOf, hcnt_φ1, hcnt0]
    rfl
  have hcnt3 : φ3 CheckY.Vars.cnt = Sum.inr (Sum.inl 1) :=
    (Function.update_of_ne hne_fst_cnt.symm _ _).trans hcnt2raw
  have hfst3 : φ3 CheckY.Vars.fst = Sum.inr (Sum.inr false) := Function.update_self _ _ _
  -- Step 1: unwrap the loop guard (constant `tt`).
  have hs1 : Command.step Tid.checkY (checkYLoop I) φ s =
      some (none, Command.loopSeq (CheckY.body I) (checkYLoop I), φ, s) := by
    simp only [checkYLoop, Command.step, CheckY.Vocab, CheckY.evalB, if_true]
  -- Step 2: `prev ← readCnt`.
  have hs2 : Command.step Tid.checkY (Command.loopSeq (CheckY.body I) (checkYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I))))))
        (checkYLoop I), φ1, s) := by
    change Command.step Tid.checkY (Command.loopSeq (CheckY.body I) (checkYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I))))))
        (checkYLoop I),
        Function.update φ CheckY.Vars.prev (CheckY.eval I CheckY.Expr.readCnt φ), s)
    simp only [CheckY.body, Command.step, CheckY.Vocab]
    rfl
  -- Step 3: `.seq Command.skip _` elimination.
  have hs3 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 4: `cnt ← nextCnt`.
  have hs4 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ2, s) := by
    change Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I),
        Function.update φ1 CheckY.Vars.cnt (CheckY.eval I CheckY.Expr.nextCnt φ1), s)
    simp only [Command.step, CheckY.Vocab]
    rfl
  -- Step 5: `.seq Command.skip _` elimination (before writing `xA`).
  have hs5 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 6: `w(xA, cntTagVal)`.
  have hs6 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I))))
      (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkY Loc.yA
        ((CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab]
  -- Step 7: `.seq Command.skip _` elimination (before writing `xB`).
  have hs7 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
        (Command.seq (checkYIteFirst I) (checkYTail I))))
      (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 8: `w(xB, cntTagVal)`.
  have hs8 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
        (Command.seq (checkYIteFirst I) (checkYTail I)))
      (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkY Loc.yB
        ((CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab]
  -- Step 9: `.seq Command.skip _` elimination (before `Command.firstIt`'s guard).
  have hs9 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkYIteFirst I) (checkYTail I)) (checkYLoop I),
        φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 10: `Command.firstIt`'s guard, resolved true via `hfst2`.
  have hs10 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (checkYIteFirst I) (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkYFirstBranch I) (checkYTail I))
        (checkYLoop I), φ2, s) := by
    simp only [checkYIteFirst, Command.step, CheckY.Vocab, CheckY.evalB, hfst2, if_true]
  -- Step 11: `fst ← False`, entering `checkYFirstBranch`.
  have hs11 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (checkYFirstBranch I) (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst))) (checkYTail I)) (checkYLoop I),
        φ3, s) := by
    change Command.step Tid.checkY
      (Command.loopSeq (Command.seq (checkYFirstBranch I) (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst))) (checkYTail I)) (checkYLoop I),
        Function.update φ2 CheckY.Vars.fst (CheckY.eval I CheckY.Expr.fstFalse φ2), s)
    simp only [checkYFirstBranch, Command.step, CheckY.Vocab]
    rfl
  -- Step 12: `.seq Command.skip _` elimination (before reading `xA`).
  have hs12 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst))) (checkYTail I)) (checkYLoop I)) φ3 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst)) (checkYTail I)) (checkYLoop I),
        φ3, s) := by
    simp only [Command.step]
    rfl
  -- Step 13: `r(xA, xAFirst)`.
  have hs13 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst)) (checkYTail I)) (checkYLoop I)) φ3 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yA
        ((CheckY.Vocab I).evalV CheckY.VExpr.yAFirst φ3), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.read Loc.yB CheckY.VExpr.yBFirst)) (checkYTail I)) (checkYLoop I),
        φ3, s) := by
    simp only [Command.step, CheckY.Vocab]
  -- Step 14: `.seq Command.skip _` elimination (before reading `xB`).
  have hs14 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.yB CheckY.VExpr.yBFirst)) (checkYTail I)) (checkYLoop I)) φ3 s =
      some (none, Command.loopSeq (Command.seq (Command.read Loc.yB CheckY.VExpr.yBFirst)
        (checkYTail I)) (checkYLoop I), φ3, s) := by
    simp only [Command.step]
    rfl
  -- Step 15: `r(xB, xBFirst)`.
  have hs15 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.read Loc.yB CheckY.VExpr.yBFirst) (checkYTail I))
        (checkYLoop I)) φ3 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yB
        ((CheckY.Vocab I).evalV CheckY.VExpr.yBFirst φ3), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (checkYTail I)) (checkYLoop I), φ3, s) := by
    simp only [Command.step, CheckY.Vocab]
  -- Step 16: `.seq Command.skip _` elimination (before `checkYTail`).
  have hs16 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq Command.skip (checkYTail I)) (checkYLoop I)) φ3 s =
      some (none, Command.loopSeq (checkYTail I) (checkYLoop I), φ3, s) := by
    simp only [Command.step]
    rfl
  -- Step 17: `if aux = ⊥ then break endif` resolves false, via `hisBot3`.
  have hs17 : Command.step Tid.checkY (Command.loopSeq (checkYTail I) (checkYLoop I)) φ3 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I)))
        (checkYLoop I), φ3, s) := by
    simp only [checkYTail, Command.step, CheckY.Vocab, hisBot3, Bool.false_eq_true, if_false]
  -- Step 18: `.seq Command.skip _` elimination (before the trailing `NDet` draw).
  have hs18 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I)))
      (checkYLoop I)) φ3 s =
      some (none, Command.loopSeq
        (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I))
        (checkYLoop I), φ3, s) := by
    simp only [Command.step]
    rfl
  -- Transport steps 1-18 (which do not depend on the resolution) into `h`,
  -- one at a time.
  have hrs1 : Command.RunStep Tid.checkY s none (checkYLoop I, φ) s
      (Command.loopSeq (CheckY.body I) (checkYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (CheckY.body I) (checkYLoop I), φ) s
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I))))))
        (checkYLoop I), φ1) := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I))))))
        (checkYLoop I), φ1) s
      (Command.loopSeq
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ1) := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 : Command.RunStep Tid.checkY s none
      (Command.loopSeq
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ1) s
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ2) s
      (Command.loopSeq
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 : Command.RunStep Tid.checkY s
      (some ⟨EventLabel.wt Tid.checkY Loc.yA
        ((CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2) s
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2) s
      (Command.loopSeq
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 : Command.RunStep Tid.checkY s
      (some ⟨EventLabel.wt Tid.checkY Loc.yB
        ((CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2) s
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2) := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2) s
      (Command.loopSeq (Command.seq (checkYIteFirst I) (checkYTail I)) (checkYLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq (checkYIteFirst I) (checkYTail I)) (checkYLoop I), φ2) s
      (Command.loopSeq (Command.seq (checkYFirstBranch I) (checkYTail I)) (checkYLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq (checkYFirstBranch I) (checkYTail I)) (checkYLoop I), φ2) s
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst))) (checkYTail I)) (checkYLoop I),
        φ3) := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst))) (checkYTail I)) (checkYLoop I), φ3) s
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst)) (checkYTail I)) (checkYLoop I),
        φ3) := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 : Command.RunStep Tid.checkY s
      (some ⟨EventLabel.rd Tid.checkY Loc.yA
        ((CheckY.Vocab I).evalV CheckY.VExpr.yAFirst φ3), rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yA CheckY.VExpr.yAFirst)
          (Command.read Loc.yB CheckY.VExpr.yBFirst)) (checkYTail I)) (checkYLoop I), φ3) s
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.yB CheckY.VExpr.yBFirst)) (checkYTail I)) (checkYLoop I),
        φ3) := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.yB CheckY.VExpr.yBFirst)) (checkYTail I)) (checkYLoop I), φ3) s
      (Command.loopSeq (Command.seq (Command.read Loc.yB CheckY.VExpr.yBFirst)
        (checkYTail I)) (checkYLoop I), φ3) := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 : Command.RunStep Tid.checkY s
      (some ⟨EventLabel.rd Tid.checkY Loc.yB
        ((CheckY.Vocab I).evalV CheckY.VExpr.yBFirst φ3), rfl⟩)
      (Command.loopSeq (Command.seq (Command.read Loc.yB CheckY.VExpr.yBFirst) (checkYTail I))
        (checkYLoop I), φ3) s
      (Command.loopSeq (Command.seq Command.skip (checkYTail I)) (checkYLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq Command.skip (checkYTail I)) (checkYLoop I), φ3) s
      (Command.loopSeq (checkYTail I) (checkYLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (checkYTail I) (checkYLoop I), φ3) s
      (Command.loopSeq (Command.seq Command.skip
        (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I)))
        (checkYLoop I), φ3) := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 : Command.RunStep Tid.checkY s none
      (Command.loopSeq (Command.seq Command.skip
        (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I)))
        (checkYLoop I), φ3) s
      (Command.loopSeq
        (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I))
        (checkYLoop I), φ3) := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  cases s with
  | nil =>
      have hnone : Command.step Tid.checkY
          ((Command.loopSeq (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I)
            (CheckY.auxSetBot_nonempty I)) (checkYLoop I)).seq C2) φ3 [] = none :=
        Command.step_seq_loopSeq_ndetAssign_nil _ _ _ _ _ _
      have h' := hnone ▸ h
      injection h' with _ h2
      injection h2 with _ h4
      injection h4 with h5 _
      exact absurd h5 (by rintro ⟨⟩)
  | cons c rest =>
      rcases Classical.em (c ∈ CheckY.auxSetBot I) with hc | hc
      · obtain ⟨w, rfl⟩ := (CheckY.mem_auxSetBot_iff c).mp hc
        have hcpos := Command.step_ndetAssign_cons_pos (t := Tid.checkY) CheckY.Vars.aux
          (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I) φ3 (Sum.inl w) rest hc
        have hrs19a : Command.RunStep Tid.checkY (Sum.inl w :: rest) none
            (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I)
              (CheckY.auxSetBot_nonempty I), φ3) rest
            (Command.skip, Function.update φ3 CheckY.Vars.aux (Sum.inl w)) :=
          Command.step_sound _ _ _ _ _ _ _ hcpos
        have hrs19 := Command.RunStep.loopCongr (C2 := checkYLoop I) hrs19a
        have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
        have h := hw19 ▸ h
        dsimp only at h
        have hrs20 : Command.RunStep Tid.checkY rest none
            (Command.loopSeq Command.skip (checkYLoop I),
              Function.update φ3 CheckY.Vars.aux (Sum.inl w)) rest
            (checkYLoop I, Function.update φ3 CheckY.Vars.aux (Sum.inl w)) :=
          Command.RunStep.loopSkip
        have hw20 : Command.step Tid.checkY
            ((Command.loopSeq Command.skip (checkYLoop I)).seq C2)
            (Function.update φ3 CheckY.Vars.aux (Sum.inl w)) rest =
            some (none, (checkYLoop I).seq C2,
              Function.update φ3 CheckY.Vars.aux (Sum.inl w), rest) :=
          Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs20)
        have h := hw20 ▸ h
        have hne_fst_aux2 : CheckY.Vars.fst ≠ CheckY.Vars.aux := by decide
        have hne_cnt_aux2 : CheckY.Vars.cnt ≠ CheckY.Vars.aux := by decide
        rw [hcnt1val, hxAFirst, hxBFirst] at h
        injection h with hh1 hrest1
        injection hrest1 with hh2 hrest2
        injection hrest2 with hh3 hh4
        refine ⟨w, rest,
          (Command.runFuel Tid.checkY ((checkYLoop I).seq C2,
            Function.update φ3 CheckY.Vars.aux (Sum.inl w)) rest N).2.1,
          rfl, hh2.symm, Function.update φ3 CheckY.Vars.aux (Sum.inl w),
          (Function.update_of_ne hne_fst_aux2 (Sum.inl w) φ3).trans hfst3,
          (Function.update_of_ne hne_cnt_aux2 (Sum.inl w) φ3).trans hcnt3,
          Function.update_self _ _ _, Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩
      · exfalso
        have hs19' : Command.step Tid.checkY
            ((Command.loopSeq
              (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I)
                (CheckY.auxSetBot_nonempty I)) (checkYLoop I)).seq C2) φ3 (c :: rest) = none :=
          Command.step_seq_loopSeq_ndetAssign_cons_neg (t := Tid.checkY) CheckY.Vars.aux
            (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I) φ3 (checkYLoop I) C2 c rest hc
        have h' := hs19' ▸ h
        injection h' with _ h2
        injection h2 with _ h4
        injection h4 with h5 _
        exact absurd h5 (by rintro ⟨⟩)

/-- The converse of `checkY_blockRest_continue_step`. -/
theorem checkY_blockRest_continue_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (CheckY.Vocab I))
    (s : List (CheckY.Vals I)) (φ : (CheckY.Vocab I).Store)
    (hfst : φ CheckY.Vars.fst = Sum.inr (Sum.inr false)) (k : Fin 4)
    (hcnt0 : φ CheckY.Vars.cnt = Sum.inr (Sum.inl k))
    (w : (Fin I.n)) (haux0 : φ CheckY.Vars.aux = Sum.inl (some w)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.checkY)) (φ' : (CheckY.Vocab I).Store)
    (h : Command.runFuel Tid.checkY ((checkYLoop I).seq C2, φ) s (N + 22) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (w' : Option (Fin I.n)) (rest : List (CheckY.Vals I))
      (σ1 : Word (ThreadLabel (domainOf I) Tid.checkY)),
      s = Sum.inl w' :: rest ∧
      σ = checkYBlockRestElems I (k, some w) ++ σ1 ∧
      ∃ (φ2u : (CheckY.Vocab I).Store),
        φ2u CheckY.Vars.fst = Sum.inr (Sum.inr false) ∧
        φ2u CheckY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
        φ2u CheckY.Vars.aux = Sum.inl w' ∧
        Command.runFuel Tid.checkY ((checkYLoop I).seq C2, φ2u) rest N =
          (.stuck, σ1, (Command.term, φ'), []) := by
  set φ1 : (CheckY.Vocab I).Store :=
    Function.update φ CheckY.Vars.prev (CheckY.eval I CheckY.Expr.readCnt φ) with hφ1
  set φ2 : (CheckY.Vocab I).Store :=
    Function.update φ1 CheckY.Vars.cnt (CheckY.eval I CheckY.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 CheckY.Vars.cnt = φ CheckY.Vars.cnt := rfl
  have hcnt2eq : φ2 CheckY.Vars.cnt = CheckY.eval I CheckY.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2raw : φ2 CheckY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt2eq, CheckY.eval, CheckY.cntOf, hcnt_φ1, hcnt0]
    rfl
  have hcnt2 : CheckY.cntOf I φ2 = k + 1 := by simp only [CheckY.cntOf, hcnt2raw]
  have hne_aux_cnt : CheckY.Vars.aux ≠ CheckY.Vars.cnt := by decide
  have haux_φ1 : φ1 CheckY.Vars.aux = φ CheckY.Vars.aux := rfl
  have haux2 : φ2 CheckY.Vars.aux = Sum.inl (some w) := by
    have h1' : φ2 CheckY.Vars.aux = φ1 CheckY.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    rw [h1', haux_φ1, haux0]
  have hcnt1val : (CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2
      = Val.primeTag Tid.checkY (k + 1) := by
    simp only [CheckY.Vocab, CheckY.evalV, hcnt2]
    rfl
  have hprev_φ1 : CheckY.prevOf I φ1 = k := by
    simp only [hφ1, CheckY.prevOf, CheckY.eval, hcnt0]
    rfl
  have hne_fst_cnt : CheckY.Vars.fst ≠ CheckY.Vars.cnt := by decide
  have hfst_φ1 : φ1 CheckY.Vars.fst = φ CheckY.Vars.fst := rfl
  have hfst2 : φ2 CheckY.Vars.fst = Sum.inr (Sum.inr false) := by
    have h1' : φ2 CheckY.Vars.fst = φ1 CheckY.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1', hfst_φ1, hfst]
  have hne_prev_cnt : CheckY.Vars.prev ≠ CheckY.Vars.cnt := by decide
  have hprev_φ2 : CheckY.prevOf I φ2 = k := by
    have h1' : φ2 CheckY.Vars.prev = φ1 CheckY.Vars.prev :=
      Function.update_of_ne hne_prev_cnt _ _
    simp only [CheckY.prevOf, h1']
    exact hprev_φ1
  have hxARest : (CheckY.Vocab I).evalV CheckY.VExpr.yARest φ2
      = Val.yTag (Tid.guessAY, false) (some w) := by
    simp only [CheckY.Vocab, CheckY.evalV, CheckY.auxOf, haux2]
    rfl
  have hxBRest : (CheckY.Vocab I).evalV CheckY.VExpr.yBRest φ2
      = Val.yTag (Tid.guessBY, false) (some w) := by
    simp only [CheckY.Vocab, CheckY.evalV, CheckY.auxOf, haux2]
    rfl
  have hprimeCheck : (CheckY.Vocab I).evalV CheckY.VExpr.primeCheckVal φ2
      = Val.primeTag Tid.primeCheckY k := by
    simp only [CheckY.Vocab, CheckY.evalV, hprev_φ2]
    rfl
  have hisBot2 : CheckY.evalB I CheckY.BExpr.isBot φ2 = false := by
    simp only [CheckY.evalB]
    cases hφ : φ2 CheckY.Vars.aux with
    | inl w' => cases w' with
        | none => rw [haux2] at hφ; injection hφ with hφ2; injection hφ2
        | some _ => simp
    | inr w' => simp
  have hs1 : Command.step Tid.checkY (checkYLoop I) φ s =
      some (none, Command.loopSeq (CheckY.body I) (checkYLoop I), φ, s) := by
    simp only [checkYLoop, Command.step, CheckY.Vocab, CheckY.evalB, if_true]
  have hs2 : Command.step Tid.checkY (Command.loopSeq (CheckY.body I) (checkYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I))))))
        (checkYLoop I), φ1, s) := by
    change Command.step Tid.checkY (Command.loopSeq (CheckY.body I) (checkYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I))))))
        (checkYLoop I),
        Function.update φ CheckY.Vars.prev (CheckY.eval I CheckY.Expr.readCnt φ), s)
    simp only [CheckY.body, Command.step, CheckY.Vocab]
    rfl
  have hs3 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  have hs4 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ2, s) := by
    change Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I),
        Function.update φ1 CheckY.Vars.cnt (CheckY.eval I CheckY.Expr.nextCnt φ1), s)
    simp only [Command.step, CheckY.Vocab]
    rfl
  have hs5 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs6 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I))))
      (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkY Loc.yA
        ((CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab]
  have hs7 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
        (Command.seq (checkYIteFirst I) (checkYTail I))))
      (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs8 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
        (Command.seq (checkYIteFirst I) (checkYTail I)))
      (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkY Loc.yB
        ((CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab]
  have hs9 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkYIteFirst I) (checkYTail I)) (checkYLoop I),
        φ2, s) := by
    simp only [Command.step]
    rfl
  have hs10 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (checkYIteFirst I) (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkYElseBranch I) (checkYTail I))
        (checkYLoop I), φ2, s) := by
    simp only [checkYIteFirst, Command.step, CheckY.Vocab, CheckY.evalB, hfst2]
    rfl
  have hs11 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (checkYElseBranch I) (checkYTail I)) (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yA
        ((CheckY.Vocab I).evalV CheckY.VExpr.yARest φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.seq (Command.read Loc.yB CheckY.VExpr.yBRest)
            (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
              (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))))
          (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [checkYElseBranch, Command.step, CheckY.Vocab, CheckY.evalV]
  have hs12 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yB CheckY.VExpr.yBRest)
          (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
            (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yB CheckY.VExpr.yBRest)
          (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
            (Command.read Loc.yB' CheckY.VExpr.primeCheckVal)))
        (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs13 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yB CheckY.VExpr.yBRest)
          (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
            (Command.read Loc.yB' CheckY.VExpr.primeCheckVal)))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yB
        ((CheckY.Vocab I).evalV CheckY.VExpr.yBRest φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
            (Command.read Loc.yB' CheckY.VExpr.primeCheckVal)))
          (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab, CheckY.evalV]
  have hs14 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
          (Command.read Loc.yB' CheckY.VExpr.primeCheckVal)))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
          (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))
        (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs15 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
          (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yA'
        ((CheckY.Vocab I).evalV CheckY.VExpr.primeCheckVal φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))
          (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab, CheckY.evalV]
  have hs16 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.read Loc.yB' CheckY.VExpr.primeCheckVal) (checkYTail I))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs17 : Command.step Tid.checkY
      (Command.loopSeq
        (Command.seq (Command.read Loc.yB' CheckY.VExpr.primeCheckVal) (checkYTail I))
        (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yB'
        ((CheckY.Vocab I).evalV CheckY.VExpr.primeCheckVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab, CheckY.evalV]
  have hs18 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq Command.skip (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (checkYTail I) (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs19 : Command.step Tid.checkY
      (Command.loopSeq (checkYTail I) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I)))
        (checkYLoop I), φ2, s) := by
    simp only [checkYTail, Command.step, CheckY.Vocab, hisBot2, Bool.false_eq_true, if_false]
  have hs20 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I)))
      (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hrs1 : Command.RunStep Tid.checkY s none (checkYLoop I, φ) s
      (Command.loopSeq (CheckY.body I) (checkYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  have hrs19 := Command.step_sound _ _ _ _ _ _ _ hs19
  have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
  simp only [hw19] at h
  have hrs20 := Command.step_sound _ _ _ _ _ _ _ hs20
  have hw20 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs20)
  simp only [hw20] at h
  cases s with
  | nil =>
      have hnone : Command.step Tid.checkY
          ((Command.loopSeq (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I)
            (CheckY.auxSetBot_nonempty I)) (checkYLoop I)).seq C2) φ2 [] = none :=
        Command.step_seq_loopSeq_ndetAssign_nil _ _ _ _ _ _
      have h' := hnone ▸ h
      injection h' with _ h2
      injection h2 with _ h4
      injection h4 with h5 _
      exact absurd h5 (by rintro ⟨⟩)
  | cons c rest =>
      rcases Classical.em (c ∈ CheckY.auxSetBot I) with hc | hc
      · obtain ⟨w', rfl⟩ := (CheckY.mem_auxSetBot_iff c).mp hc
        have hcpos := Command.step_ndetAssign_cons_pos (t := Tid.checkY) CheckY.Vars.aux
          (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I) φ2 (Sum.inl w') rest hc
        have hrs21a : Command.RunStep Tid.checkY (Sum.inl w' :: rest) none
            (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I)
              (CheckY.auxSetBot_nonempty I), φ2) rest
            (Command.skip, Function.update φ2 CheckY.Vars.aux (Sum.inl w')) :=
          Command.step_sound _ _ _ _ _ _ _ hcpos
        have hrs21 := Command.RunStep.loopCongr (C2 := checkYLoop I) hrs21a
        have hw21 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs21)
        have h := hw21 ▸ h
        dsimp only at h
        have hrs22 : Command.RunStep Tid.checkY rest none
            (Command.loopSeq Command.skip (checkYLoop I),
              Function.update φ2 CheckY.Vars.aux (Sum.inl w')) rest
            (checkYLoop I, Function.update φ2 CheckY.Vars.aux (Sum.inl w')) :=
          Command.RunStep.loopSkip
        have hw22 : Command.step Tid.checkY
            ((Command.loopSeq Command.skip (checkYLoop I)).seq C2)
            (Function.update φ2 CheckY.Vars.aux (Sum.inl w')) rest =
            some (none, (checkYLoop I).seq C2,
              Function.update φ2 CheckY.Vars.aux (Sum.inl w'), rest) :=
          Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs22)
        have h := hw22 ▸ h
        rw [hcnt1val, hxARest, hxBRest, hprimeCheck] at h
        injection h with hh1 hrest1
        injection hrest1 with hh2 hrest2
        injection hrest2 with hh3 hh4
        have hne_fst_aux2 : CheckY.Vars.fst ≠ CheckY.Vars.aux := by decide
        have hne_cnt_aux2 : CheckY.Vars.cnt ≠ CheckY.Vars.aux := by decide
        refine ⟨w', rest,
          (Command.runFuel Tid.checkY ((checkYLoop I).seq C2,
            Function.update φ2 CheckY.Vars.aux (Sum.inl w')) rest N).2.1,
          rfl, hh2.symm, Function.update φ2 CheckY.Vars.aux (Sum.inl w'),
          (Function.update_of_ne hne_fst_aux2 (Sum.inl w') φ2).trans hfst2,
          (Function.update_of_ne hne_cnt_aux2 (Sum.inl w') φ2).trans hcnt2raw,
          Function.update_self _ _ _, Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩
      · exfalso
        have hs21' : Command.step Tid.checkY
            ((Command.loopSeq
              (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I)
                (CheckY.auxSetBot_nonempty I)) (checkYLoop I)).seq C2) φ2 (c :: rest) = none :=
          Command.step_seq_loopSeq_ndetAssign_cons_neg (t := Tid.checkY) CheckY.Vars.aux
            (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I) φ2 (checkYLoop I) C2 c rest hc
        have h' := hs21' ▸ h
        injection h' with _ h2
        injection h2 with _ h4
        injection h4 with h5 _
        exact absurd h5 (by rintro ⟨⟩)

/-- The converse of `checkY_blockRest_break_step`: consumes nothing and
reaches `(C2, φ2)`. -/
theorem checkY_blockRest_break_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (CheckY.Vocab I))
    (s : List (CheckY.Vals I)) (φ : (CheckY.Vocab I).Store)
    (hfst : φ CheckY.Vars.fst = Sum.inr (Sum.inr false)) (k : Fin 4)
    (hcnt0 : φ CheckY.Vars.cnt = Sum.inr (Sum.inl k))
    (haux0 : φ CheckY.Vars.aux = Sum.inl none) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.checkY)) (φ' : (CheckY.Vocab I).Store)
    (h : Command.runFuel Tid.checkY ((checkYLoop I).seq C2, φ) s (N + 22) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (σ1 : Word (ThreadLabel (domainOf I) Tid.checkY)) (φ2u : (CheckY.Vocab I).Store),
      φ2u CheckY.Vars.fst = Sum.inr (Sum.inr false) ∧
      φ2u CheckY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
      φ2u CheckY.Vars.aux = Sum.inl none ∧
      σ = checkYBlockRestElems I (k, none) ++ σ1 ∧
      Command.runFuel Tid.checkY (C2, φ2u) s N = (.stuck, σ1, (Command.term, φ'), []) := by
  set φ1 : (CheckY.Vocab I).Store :=
    Function.update φ CheckY.Vars.prev (CheckY.eval I CheckY.Expr.readCnt φ) with hφ1
  set φ2 : (CheckY.Vocab I).Store :=
    Function.update φ1 CheckY.Vars.cnt (CheckY.eval I CheckY.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 CheckY.Vars.cnt = φ CheckY.Vars.cnt := rfl
  have hcnt2eq : φ2 CheckY.Vars.cnt = CheckY.eval I CheckY.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2raw : φ2 CheckY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt2eq, CheckY.eval, CheckY.cntOf, hcnt_φ1, hcnt0]
    rfl
  have hcnt2 : CheckY.cntOf I φ2 = k + 1 := by simp only [CheckY.cntOf, hcnt2raw]
  have hne_aux_cnt : CheckY.Vars.aux ≠ CheckY.Vars.cnt := by decide
  have haux_φ1 : φ1 CheckY.Vars.aux = φ CheckY.Vars.aux := rfl
  have haux2 : φ2 CheckY.Vars.aux = Sum.inl none := by
    have h1' : φ2 CheckY.Vars.aux = φ1 CheckY.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    rw [h1', haux_φ1, haux0]
  have hcnt1val : (CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2
      = Val.primeTag Tid.checkY (k + 1) := by
    simp only [CheckY.Vocab, CheckY.evalV, hcnt2]
    rfl
  have hprev_φ1 : CheckY.prevOf I φ1 = k := by
    simp only [hφ1, CheckY.prevOf, CheckY.eval, hcnt0]
    rfl
  have hne_fst_cnt : CheckY.Vars.fst ≠ CheckY.Vars.cnt := by decide
  have hfst_φ1 : φ1 CheckY.Vars.fst = φ CheckY.Vars.fst := rfl
  have hfst2 : φ2 CheckY.Vars.fst = Sum.inr (Sum.inr false) := by
    have h1' : φ2 CheckY.Vars.fst = φ1 CheckY.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1', hfst_φ1, hfst]
  have hne_prev_cnt : CheckY.Vars.prev ≠ CheckY.Vars.cnt := by decide
  have hprev_φ2 : CheckY.prevOf I φ2 = k := by
    have h1' : φ2 CheckY.Vars.prev = φ1 CheckY.Vars.prev :=
      Function.update_of_ne hne_prev_cnt _ _
    simp only [CheckY.prevOf, h1']
    exact hprev_φ1
  have hxARest : (CheckY.Vocab I).evalV CheckY.VExpr.yARest φ2
      = Val.yTag (Tid.guessAY, false) none := by
    simp only [CheckY.Vocab, CheckY.evalV, CheckY.auxOf, haux2]
    rfl
  have hxBRest : (CheckY.Vocab I).evalV CheckY.VExpr.yBRest φ2
      = Val.yTag (Tid.guessBY, false) none := by
    simp only [CheckY.Vocab, CheckY.evalV, CheckY.auxOf, haux2]
    rfl
  have hprimeCheck : (CheckY.Vocab I).evalV CheckY.VExpr.primeCheckVal φ2
      = Val.primeTag Tid.primeCheckY k := by
    simp only [CheckY.Vocab, CheckY.evalV, hprev_φ2]
    rfl
  have hisBot2 : CheckY.evalB I CheckY.BExpr.isBot φ2 = true := by
    simp only [CheckY.evalB, haux2]
  have hs1 : Command.step Tid.checkY (checkYLoop I) φ s =
      some (none, Command.loopSeq (CheckY.body I) (checkYLoop I), φ, s) := by
    simp only [checkYLoop, Command.step, CheckY.Vocab, CheckY.evalB, if_true]
  have hs2 : Command.step Tid.checkY (Command.loopSeq (CheckY.body I) (checkYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I))))))
        (checkYLoop I), φ1, s) := by
    change Command.step Tid.checkY (Command.loopSeq (CheckY.body I) (checkYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I))))))
        (checkYLoop I),
        Function.update φ CheckY.Vars.prev (CheckY.eval I CheckY.Expr.readCnt φ), s)
    simp only [CheckY.body, Command.step, CheckY.Vocab]
    rfl
  have hs3 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
          (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
            (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
              (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  have hs4 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I), φ2, s) := by
    change Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.assign CheckY.Vars.cnt CheckY.Expr.nextCnt)
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ1 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I)))))
        (checkYLoop I),
        Function.update φ1 CheckY.Vars.cnt (CheckY.eval I CheckY.Expr.nextCnt φ1), s)
    simp only [Command.step, CheckY.Vocab]
    rfl
  have hs5 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I)))))
      (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs6 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.write Loc.yA CheckY.VExpr.cntTagVal)
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I))))
      (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkY Loc.yA
        ((CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip
          (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
            (Command.seq (checkYIteFirst I) (checkYTail I))))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab]
  have hs7 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
        (Command.seq (checkYIteFirst I) (checkYTail I))))
      (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
          (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs8 : Command.step Tid.checkY (Command.loopSeq
      (Command.seq (Command.write Loc.yB CheckY.VExpr.cntTagVal)
        (Command.seq (checkYIteFirst I) (checkYTail I)))
      (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.checkY Loc.yB
        ((CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab]
  have hs9 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq Command.skip (Command.seq (checkYIteFirst I) (checkYTail I)))
        (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkYIteFirst I) (checkYTail I)) (checkYLoop I),
        φ2, s) := by
    simp only [Command.step]
    rfl
  have hs10 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (checkYIteFirst I) (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq (checkYElseBranch I) (checkYTail I))
        (checkYLoop I), φ2, s) := by
    simp only [checkYIteFirst, Command.step, CheckY.Vocab, CheckY.evalB, hfst2]
    rfl
  have hs11 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (checkYElseBranch I) (checkYTail I)) (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yA
        ((CheckY.Vocab I).evalV CheckY.VExpr.yARest φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.seq (Command.read Loc.yB CheckY.VExpr.yBRest)
            (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
              (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))))
          (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [checkYElseBranch, Command.step, CheckY.Vocab, CheckY.evalV]
  have hs12 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yB CheckY.VExpr.yBRest)
          (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
            (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yB CheckY.VExpr.yBRest)
          (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
            (Command.read Loc.yB' CheckY.VExpr.primeCheckVal)))
        (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs13 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yB CheckY.VExpr.yBRest)
          (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
            (Command.read Loc.yB' CheckY.VExpr.primeCheckVal)))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yB
        ((CheckY.Vocab I).evalV CheckY.VExpr.yBRest φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
            (Command.read Loc.yB' CheckY.VExpr.primeCheckVal)))
          (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab, CheckY.evalV]
  have hs14 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
          (Command.read Loc.yB' CheckY.VExpr.primeCheckVal)))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
          (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))
        (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs15 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq
        (Command.seq (Command.read Loc.yA' CheckY.VExpr.primeCheckVal)
          (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yA'
        ((CheckY.Vocab I).evalV CheckY.VExpr.primeCheckVal φ2), rfl⟩,
        Command.loopSeq (Command.seq (Command.seq Command.skip
          (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))
          (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab, CheckY.evalV]
  have hs16 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.read Loc.yB' CheckY.VExpr.primeCheckVal))
        (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.read Loc.yB' CheckY.VExpr.primeCheckVal) (checkYTail I))
        (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs17 : Command.step Tid.checkY
      (Command.loopSeq
        (Command.seq (Command.read Loc.yB' CheckY.VExpr.primeCheckVal) (checkYTail I))
        (checkYLoop I)) φ2 s =
      some (some ⟨EventLabel.rd Tid.checkY Loc.yB'
        ((CheckY.Vocab I).evalV CheckY.VExpr.primeCheckVal φ2), rfl⟩,
        Command.loopSeq (Command.seq Command.skip (checkYTail I)) (checkYLoop I), φ2, s) := by
    simp only [Command.step, CheckY.Vocab, CheckY.evalV]
  have hs18 : Command.step Tid.checkY
      (Command.loopSeq (Command.seq Command.skip (checkYTail I)) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (checkYTail I) (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs19 : Command.step Tid.checkY
      (Command.loopSeq (checkYTail I) (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq (Command.seq Command.brk
        (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I)))
        (checkYLoop I), φ2, s) := by
    simp only [checkYTail, Command.step, CheckY.Vocab, hisBot2, if_true]
  have hs20 : Command.step Tid.checkY (Command.loopSeq (Command.seq Command.brk
      (Command.ndetAssign CheckY.Vars.aux (CheckY.auxSetBot I) (CheckY.auxSetBot_nonempty I)))
      (checkYLoop I)) φ2 s =
      some (none, Command.loopSeq Command.brk (checkYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  have hs21 : Command.step Tid.checkY
      (Command.loopSeq Command.brk (checkYLoop I)) φ2 s =
      some (none, Command.skip, φ2, s) := by
    simp only [Command.step]
    rfl
  have hs22 : Command.step Tid.checkY (Command.seq Command.skip C2) φ2 s =
      some (none, C2, φ2, s) := by
    simp only [Command.step]
    rfl
  have hrs1 : Command.RunStep Tid.checkY s none (checkYLoop I, φ) s
      (Command.loopSeq (CheckY.body I) (checkYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  have hrs19 := Command.step_sound _ _ _ _ _ _ _ hs19
  have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
  simp only [hw19] at h
  have hrs20 := Command.step_sound _ _ _ _ _ _ _ hs20
  have hw20 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs20)
  simp only [hw20] at h
  have hrs21 := Command.step_sound _ _ _ _ _ _ _ hs21
  have hw21 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs21)
  simp only [hw21] at h
  simp only [hs22] at h
  rw [hcnt1val, hxARest, hxBRest, hprimeCheck] at h
  injection h with hh1 hrest1
  injection hrest1 with hh2 hrest2
  injection hrest2 with hh3 hh4
  refine ⟨(Command.runFuel Tid.checkY (C2, φ2) s N).2.1, φ2, hfst2, hcnt2raw, haux2, hh2.symm,
    Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩

/-- The converse of `checkYChain_shape_val`. By strong induction on
`s.length`. -/
theorem checkY_chain_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (CheckY.Vals I)), s.length = n →
      ∀ (C2 : Command (domainOf I) (CheckY.Vocab I)) (φ : (CheckY.Vocab I).Store)
        (_hfst : φ CheckY.Vars.fst = Sum.inr (Sum.inr false))
        (k0 : Fin 4) (_hcnt0 : φ CheckY.Vars.cnt = Sum.inr (Sum.inl k0))
        (w0 : (Fin I.n)) (_haux0 : φ CheckY.Vars.aux = Sum.inl (some w0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.checkY))
        (φ' : (CheckY.Vocab I).Store),
        Command.runFuel Tid.checkY ((checkYLoop I).seq C2, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (ws : List (Fin I.n)) (rest0 : List (CheckY.Vals I))
          (kws : List (Fin 4 × Option (Fin I.n))) (φ2u : (CheckY.Vocab I).Store)
          (σ1 : Word (ThreadLabel (domainOf I) Tid.checkY)),
          s = ws.map (fun w => (Sum.inl (some w) : CheckY.Vals I)) ++
            Sum.inl none :: rest0 ∧
          kws.length = ws.length + 2 ∧
          (∀ i, i < kws.length →
            ∃ w, kws[i]? = some (⟨(k0.val + i) % 4, by omega⟩, w)) ∧
          σ = kws.flatMap (checkYBlockRestElems I) ++ σ1 ∧
          Command.runFuel Tid.checkY (C2, φ2u) rest0 N =
            (.stuck, σ1, (Command.term, φ'), []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen C2 φ hfst k0 hcnt0 w0 haux0 N σ φ' h
    have h22 := Command.runFuel_stuck_stable h 22
    obtain ⟨w', rest, σ1, hseq, hσeq, φ2u, hfst2, hcnt2, haux2, h2⟩ :=
      checkY_blockRest_continue_step_inv I C2 s φ hfst k0 hcnt0 w0 haux0 N σ φ' h22
    subst hseq
    cases w' with
    | none =>
        have h2' := Command.runFuel_stuck_stable h2 22
        obtain ⟨σ1', φ3u, hfst3, hcnt3, haux3, hσ1eq, h3⟩ :=
          checkY_blockRest_break_step_inv I C2 rest φ2u hfst2 (k0 + 1) hcnt2 haux2 N σ1 φ' h2'
        refine ⟨[], rest, [(k0, some w0), (k0 + 1, none)], φ3u, σ1', rfl, rfl, ?_, ?_, h3⟩
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · refine ⟨some w0, ?_⟩
            simp only [List.getElem?_cons_zero]
            congr 2
            apply Fin.ext
            have hk0 := k0.isLt
            simp only [Nat.add_zero]
            omega
          · refine ⟨none, ?_⟩
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
            congr 2
        · rw [hσeq, hσ1eq]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | some w1 =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inl (some w1) :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        obtain ⟨ws', rest0, kws', φ2u', σ1', hseq', hlen', hval', hσeq', h3⟩ :=
          ih rest.length hrest_len rest rfl C2 φ2u hfst2 (k0 + 1) hcnt2 w1 haux2 N σ1 φ' h2
        refine ⟨w1 :: ws', rest0, (k0, some w0) :: kws', φ2u', σ1',
          by simp [hseq'], by simp [hlen'], ?_, ?_, h3⟩
        · intro i hi
          cases i with
          | zero =>
              refine ⟨some w0, ?_⟩
              simp only [List.getElem?_cons_zero]
              congr 2
              apply Fin.ext
              have hk0 := k0.isLt
              simp only [Nat.add_zero]
              omega
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              obtain ⟨w, hw⟩ := hval' i hi'
              refine ⟨w, ?_⟩
              simp only [List.getElem?_cons_succ]
              rw [hw]
              congr 2
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · rw [hσeq, hσeq']
          simp only [List.flatMap_cons, List.append_assoc]

/-- **The word characterization of the threads, `CheckY`.** The converse of
`checkY_general_run_val`, as `checkX_shape_inv`. -/
theorem checkY_shape_inv (I : PCPInstance) {s : List (CheckY.Vals I)}
    {φ' : (CheckY.Vocab I).Store} {cLast : Config (domainOf I) (CheckY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.checkY)}
    (hrun : Command.Run Tid.checkY s
      (CheckY.program I, (CheckY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : (Fin I.n)) (js : List (Fin I.n)) (kws : List (Fin 4 × Option (Fin I.n))),
      s = Sum.inl (some v0) ::
        (js.map (fun w => (Sum.inl (some w) : CheckY.Vals I)) ++ [Sum.inl none]) ∧
      kws.length = js.length + 1 ∧
      (∀ i, i < kws.length → ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w)) ∧
      σ = checkYBlockWord I v0 kws := by
  have hterm_stuck : ∀ (φt : (CheckY.Vocab I).Store) (r : List (CheckY.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.checkY)) (φt' : (CheckY.Vocab I).Store),
      Command.runFuel Tid.checkY (Command.term, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      r = [] ∧ σt = [] ∧ φt' = φt := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        exact absurd (congrArg Prod.fst hm) (by rintro ⟨⟩)
    | succ m =>
        simp only [Command.runFuel, Command.step] at hm
        injection hm with hh1 hrest
        injection hrest with hh2 hrest2
        injection hrest2 with hh3 hh4
        exact ⟨hh4, hh2.symm, (congrArg Prod.snd hh3).symm⟩
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := checkY_lead_step_inv I s n σ φ' hn2
  have hfst1 : Function.update ((CheckY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) CheckY.Vars.aux (Sum.inl (some v0))
      CheckY.Vars.fst = Sum.inr (Sum.inr true) := by
    have hne : CheckY.Vars.fst ≠ CheckY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have hcnt1 : Function.update ((CheckY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) CheckY.Vars.aux (Sum.inl (some v0))
      CheckY.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne : CheckY.Vars.cnt ≠ CheckY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have h20 := Command.runFuel_stuck_stable h2 20
  obtain ⟨w, rest2, σ1, hs2, hσ2, φ3, hfst3, hcnt3, haux3, h3⟩ :=
    checkY_block0_step_inv I Command.term rest _ hfst1 hcnt1 v0 (Function.update_self _ _ _)
      n σ φ' h20
  cases w with
  | none =>
      have h22 := Command.runFuel_stuck_stable h3 22
      obtain ⟨σ1', φ4, hfst4, hcnt4, haux4, hσ1eq, h4⟩ :=
        checkY_blockRest_break_step_inv I Command.term rest2 φ3 hfst3 1 hcnt3 haux3 n σ1 φ' h22
      obtain ⟨hrest2nil, hσ1'nil, hφ4eq⟩ := hterm_stuck φ4 rest2 n σ1' φ' h4
      refine ⟨v0, [], [(1, none)], ?_, rfl, ?_, ?_⟩
      · simp [hs, hs2, hrest2nil]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨none, rfl⟩
      · simp [hσ2, hσ1eq, hσ1'nil, checkYBlockWord, List.flatMap_cons, List.flatMap_nil]
  | some w1 =>
      obtain ⟨ws, rest0, kws, φ2u, σ1', hseq', hlen', hval', hσeq', h4⟩ :=
        checkY_chain_shape_inv I rest2.length rest2 rfl Command.term φ3 hfst3 1 hcnt3 w1 haux3
          n σ1 φ' h3
      obtain ⟨hrest0nil, hσ1'nil, hφ2ueq⟩ := hterm_stuck φ2u rest0 n σ1' φ' h4
      refine ⟨v0, w1 :: ws, kws, ?_, by omega, ?_, ?_⟩
      · rw [hs, hs2, hseq', hrest0nil]
        simp
      · intro i hi
        have := hval' i hi
        simpa using this
      · rw [hσ2, hσeq', hσ1'nil, List.append_nil]
        rfl

/-- `checkY_chain_shape_inv`, with the second components of `kws` determined
(as `checkX_chain_shape_inv_vals`). -/
theorem checkY_chain_shape_inv_vals (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (CheckY.Vals I)), s.length = n →
      ∀ (C2 : Command (domainOf I) (CheckY.Vocab I)) (φ : (CheckY.Vocab I).Store)
        (_hfst : φ CheckY.Vars.fst = Sum.inr (Sum.inr false))
        (k0 : Fin 4) (_hcnt0 : φ CheckY.Vars.cnt = Sum.inr (Sum.inl k0))
        (w0 : (Fin I.n)) (_haux0 : φ CheckY.Vars.aux = Sum.inl (some w0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.checkY))
        (φ' : (CheckY.Vocab I).Store),
        Command.runFuel Tid.checkY ((checkYLoop I).seq C2, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (ws : List (Fin I.n)) (rest0 : List (CheckY.Vals I))
          (kws : List (Fin 4 × Option (Fin I.n))) (φ2u : (CheckY.Vocab I).Store)
          (σ1 : Word (ThreadLabel (domainOf I) Tid.checkY)),
          s = ws.map (fun w => (Sum.inl (some w) : CheckY.Vals I)) ++
            Sum.inl none :: rest0 ∧
          kws.length = ws.length + 2 ∧
          (∀ i, i < kws.length →
            ∃ w, kws[i]? = some (⟨(k0.val + i) % 4, by omega⟩, w)) ∧
          (∀ i, i < kws.length → kws[i]?.map Prod.snd = some ((w0 :: ws)[i]?)) ∧
          σ = kws.flatMap (checkYBlockRestElems I) ++ σ1 ∧
          Command.runFuel Tid.checkY (C2, φ2u) rest0 N =
            (.stuck, σ1, (Command.term, φ'), []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen C2 φ hfst k0 hcnt0 w0 haux0 N σ φ' h
    have h22 := Command.runFuel_stuck_stable h 22
    obtain ⟨w', rest, σ1, hseq, hσeq, φ2u, hfst2, hcnt2, haux2, h2⟩ :=
      checkY_blockRest_continue_step_inv I C2 s φ hfst k0 hcnt0 w0 haux0 N σ φ' h22
    subst hseq
    cases w' with
    | none =>
        have h2' := Command.runFuel_stuck_stable h2 22
        obtain ⟨σ1', φ3u, hfst3, hcnt3, haux3, hσ1eq, h3⟩ :=
          checkY_blockRest_break_step_inv I C2 rest φ2u hfst2 (k0 + 1) hcnt2 haux2 N σ1 φ' h2'
        refine ⟨[], rest, [(k0, some w0), (k0 + 1, none)], φ3u, σ1', rfl, rfl, ?_, ?_, ?_, h3⟩
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · refine ⟨some w0, ?_⟩
            simp only [List.getElem?_cons_zero]
            congr 2
            apply Fin.ext
            have hk0 := k0.isLt
            simp only [Nat.add_zero]
            omega
          · refine ⟨none, ?_⟩
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
            congr 2
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · simp
          · simp
        · rw [hσeq, hσ1eq]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | some w1 =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inl (some w1) :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        obtain ⟨ws', rest0, kws', φ2u', σ1', hseq', hlen', hval', hval2', hσeq', h4⟩ :=
          ih rest.length hrest_len rest rfl C2 φ2u hfst2 (k0 + 1) hcnt2 w1 haux2 N σ1 φ' h2
        refine ⟨w1 :: ws', rest0, (k0, some w0) :: kws', φ2u', σ1',
          by simp [hseq'], by simp [hlen'], ?_, ?_, ?_, h4⟩
        · intro i hi
          cases i with
          | zero =>
              refine ⟨some w0, ?_⟩
              simp only [List.getElem?_cons_zero]
              congr 2
              apply Fin.ext
              have hk0 := k0.isLt
              simp only [Nat.add_zero]
              omega
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              obtain ⟨w, hw⟩ := hval' i hi'
              refine ⟨w, ?_⟩
              simp only [List.getElem?_cons_succ]
              rw [hw]
              congr 2
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · intro i hi
          cases i with
          | zero => simp
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              have := hval2' i hi'
              simpa using this
        · rw [hσeq, hσeq']
          simp only [List.flatMap_cons, List.append_assoc]

/-- `checkY_shape_inv`, with the second components of `kws` determined (as
`checkX_shape_inv_vals`). -/
theorem checkY_shape_inv_vals (I : PCPInstance) {s : List (CheckY.Vals I)}
    {φ' : (CheckY.Vocab I).Store} {cLast : Config (domainOf I) (CheckY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.checkY)}
    (hrun : Command.Run Tid.checkY s
      (CheckY.program I, (CheckY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : (Fin I.n)) (js : List (Fin I.n)) (kws : List (Fin 4 × Option (Fin I.n))),
      s = Sum.inl (some v0) ::
        (js.map (fun w => (Sum.inl (some w) : CheckY.Vals I)) ++ [Sum.inl none]) ∧
      kws.length = js.length + 1 ∧
      (∀ i, i < kws.length → ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w)) ∧
      (∀ i, i < kws.length → kws[i]?.map Prod.snd = some (js[i]?)) ∧
      σ = checkYBlockWord I v0 kws := by
  have hterm_stuck : ∀ (φt : (CheckY.Vocab I).Store) (r : List (CheckY.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.checkY)) (φt' : (CheckY.Vocab I).Store),
      Command.runFuel Tid.checkY (Command.term, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      r = [] ∧ σt = [] ∧ φt' = φt := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        exact absurd (congrArg Prod.fst hm) (by rintro ⟨⟩)
    | succ m =>
        simp only [Command.runFuel, Command.step] at hm
        injection hm with hh1 hrest
        injection hrest with hh2 hrest2
        injection hrest2 with hh3 hh4
        exact ⟨hh4, hh2.symm, (congrArg Prod.snd hh3).symm⟩
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := checkY_lead_step_inv I s n σ φ' hn2
  have hfst1 : Function.update ((CheckY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) CheckY.Vars.aux (Sum.inl (some v0))
      CheckY.Vars.fst = Sum.inr (Sum.inr true) := by
    have hne : CheckY.Vars.fst ≠ CheckY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have hcnt1 : Function.update ((CheckY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) CheckY.Vars.aux (Sum.inl (some v0))
      CheckY.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne : CheckY.Vars.cnt ≠ CheckY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have h20 := Command.runFuel_stuck_stable h2 20
  obtain ⟨w, rest2, σ1, hs2, hσ2, φ3, hfst3, hcnt3, haux3, h3⟩ :=
    checkY_block0_step_inv I Command.term rest _ hfst1 hcnt1 v0 (Function.update_self _ _ _)
      n σ φ' h20
  cases w with
  | none =>
      have h22 := Command.runFuel_stuck_stable h3 22
      obtain ⟨σ1', φ4, hfst4, hcnt4, haux4, hσ1eq, h4⟩ :=
        checkY_blockRest_break_step_inv I Command.term rest2 φ3 hfst3 1 hcnt3 haux3 n σ1 φ' h22
      obtain ⟨hrest2nil, hσ1'nil, hφ4eq⟩ := hterm_stuck φ4 rest2 n σ1' φ' h4
      refine ⟨v0, [], [(1, none)], ?_, rfl, ?_, ?_, ?_⟩
      · simp [hs, hs2, hrest2nil]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨none, rfl⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp
      · simp [hσ2, hσ1eq, hσ1'nil, checkYBlockWord, List.flatMap_cons, List.flatMap_nil]
  | some w1 =>
      obtain ⟨ws, rest0, kws, φ2u, σ1', hseq', hlen', hval', hval2', hσeq', h4⟩ :=
        checkY_chain_shape_inv_vals I rest2.length rest2 rfl Command.term φ3 hfst3 1 hcnt3 w1 haux3
          n σ1 φ' h3
      obtain ⟨hrest0nil, hσ1'nil, hφ2ueq⟩ := hterm_stuck φ2u rest0 n σ1' φ' h4
      refine ⟨v0, w1 :: ws, kws, ?_, by omega, ?_, ?_, ?_⟩
      · rw [hs, hs2, hseq', hrest0nil]
        simp
      · intro i hi
        have := hval' i hi
        simpa using this
      · intro i hi
        have := hval2' i hi
        simpa using this
      · rw [hσ2, hσeq', hσ1'nil, List.append_nil]
        rfl

/-- One iteration of `guessBXInnerLoop` after the first call, as an
`.outOfFuel` result after exactly 14 steps. -/
theorem guessBX_innerLoop_rest_step_outOfFuel (I : PCPInstance) (rest : List (GuessBX.Vals I))
    (φ : (GuessBX.Vocab I).Store)
    (hguard : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ = true)
    (hfst : φ GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)))
    (k : Fin 4) (hcnt0 : φ GuessBX.Vars.cnt = Sum.inr (Sum.inl k)) :
    ∃ (φ' : (GuessBX.Vocab I).Store),
      φ' GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
      φ' GuessBX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
      φ' GuessBX.Vars.j = GuessBX.eval I GuessBX.Expr.jIncr φ ∧
      φ' GuessBX.Vars.aux = φ GuessBX.Vars.aux ∧
      φ' GuessBX.Vars.cntY = φ GuessBX.Vars.cntY ∧
      φ' GuessBX.Vars.N = φ GuessBX.Vars.N ∧
      Command.runFuel Tid.guessBX (guessBXInnerLoop I, φ) rest 14 =
        (.outOfFuel,
          [ ⟨EventLabel.wt Tid.guessBX Loc.xB
              (Val.xTag (Tid.guessBX, false)
                (GuessBX.jthLetter I (GuessBX.auxOf I φ) (GuessBX.jOf I φ))), rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt (k + 1)), rfl⟩
          , ⟨EventLabel.rd Tid.guessBX Loc.zBxx' (Val.cnt k), rfl⟩ ],
          (guessBXInnerLoop I, φ'), rest) := by
  set φ1 : (GuessBX.Vocab I).Store :=
    Function.update φ GuessBX.Vars.prev (GuessBX.eval I GuessBX.Expr.readCnt φ) with hφ1
  set φ2 : (GuessBX.Vocab I).Store :=
    Function.update φ1 GuessBX.Vars.cnt (GuessBX.eval I GuessBX.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 GuessBX.Vars.cnt = φ GuessBX.Vars.cnt := rfl
  have hcntOf_φ1 : GuessBX.cntOf I φ1 = k := by
    simp only [GuessBX.cntOf, hcnt_φ1, hcnt0]
  have hcnt2eq : φ2 GuessBX.Vars.cnt = GuessBX.eval I GuessBX.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2raw : φ2 GuessBX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt2eq, GuessBX.eval, hcntOf_φ1]; rfl
  have hguard' : GuessBX.evalB I GuessBX.BExpr.jLeN φ = true := hguard
  have hne_prev_cnt : GuessBX.Vars.prev ≠ GuessBX.Vars.cnt := by decide
  have hprev_φ1 : GuessBX.prevOf I φ1 = k := by
    simp only [hφ1, GuessBX.prevOf, GuessBX.eval, hcnt0]; rfl
  have hprev_φ2 : GuessBX.prevOf I φ2 = k := by
    have h1x : φ2 GuessBX.Vars.prev = φ1 GuessBX.Vars.prev := Function.update_of_ne hne_prev_cnt _ _
    simp only [GuessBX.prevOf, h1x]
    exact hprev_φ1
  have hne_fst_cnt : GuessBX.Vars.fst ≠ GuessBX.Vars.cnt := by decide
  have hne_fst_prev : GuessBX.Vars.fst ≠ GuessBX.Vars.prev := by decide
  have hfst_φ1 : φ1 GuessBX.Vars.fst = φ GuessBX.Vars.fst := rfl
  have hfst2 : φ2 GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    have h1x : φ2 GuessBX.Vars.fst = φ1 GuessBX.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1x, hfst_φ1, hfst]
  have hisFirst2 : (GuessBX.Vocab I).evalB GuessBX.BExpr.isFirst φ2 = false := by
    simp [GuessBX.Vocab, GuessBX.evalB, hfst2]
  have hisFirst2' : GuessBX.evalB I GuessBX.BExpr.isFirst φ2 = false := hisFirst2
  have hne_aux_cnt : GuessBX.Vars.aux ≠ GuessBX.Vars.cnt := by decide
  have hne_aux_prev : GuessBX.Vars.aux ≠ GuessBX.Vars.prev := by decide
  have haux_φ2 : φ2 GuessBX.Vars.aux = φ GuessBX.Vars.aux := by
    have h1x : φ2 GuessBX.Vars.aux = φ1 GuessBX.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    have h2x : φ1 GuessBX.Vars.aux = φ GuessBX.Vars.aux := Function.update_of_ne hne_aux_prev _ _
    rw [h1x, h2x]
  have hj_φ2 : GuessBX.jOf I φ2 = GuessBX.jOf I φ := by
    have hne1 : GuessBX.Vars.j ≠ GuessBX.Vars.cnt := by decide
    have hne2 : GuessBX.Vars.j ≠ GuessBX.Vars.prev := by decide
    have h1x : φ2 GuessBX.Vars.j = φ1 GuessBX.Vars.j := Function.update_of_ne hne1 _ _
    have h2x : φ1 GuessBX.Vars.j = φ GuessBX.Vars.j := Function.update_of_ne hne2 _ _
    simp only [GuessBX.jOf, h1x, h2x]
  have hxTagRest2 : (GuessBX.Vocab I).evalV GuessBX.VExpr.xTagRest φ2 =
      Val.xTag (Tid.guessBX, false)
        (GuessBX.jthLetter I (GuessBX.auxOf I φ) (GuessBX.jOf I φ)) := by
    simp only [GuessBX.Vocab, GuessBX.evalV, GuessBX.auxOf, haux_φ2, hj_φ2]; rfl
  have hcntVal2 : (GuessBX.Vocab I).evalV GuessBX.VExpr.cntVal φ2 = Val.cnt (k + 1) := by
    have hcnt2 : GuessBX.cntOf I φ2 = k + 1 := by simp only [GuessBX.cntOf, hcnt2raw]
    simp only [GuessBX.Vocab, GuessBX.evalV, hcnt2]; rfl
  have hprevVal2 : (GuessBX.Vocab I).evalV GuessBX.VExpr.prevVal φ2 = Val.cnt k := by
    simp only [GuessBX.Vocab, GuessBX.evalV, hprev_φ2]; rfl
  have h1 : Command.RunStep Tid.guessBX rest none (guessBXInnerLoop I, φ) rest
      (Command.loopSeq (Command.seq (GuessBX.innerBody I)
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [guessBXInnerLoop, Command.step, GuessBX.Vocab, hguard', if_true])
  have h2 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq (GuessBX.innerBody I)
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.assign GuessBX.Vars.cnt GuessBX.Expr.nextCnt)
          (Command.ite GuessBX.BExpr.isFirst
            (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
                (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
                (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ1) := by
    rw [hφ1]
    exact Command.step_sound _ _ _ _ _ _ _ (by
      simp only [GuessBX.innerBody, Command.firstIt, Command.step, GuessBX.Vocab]; rfl)
  have h3 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.assign GuessBX.Vars.cnt GuessBX.Expr.nextCnt)
          (Command.ite GuessBX.BExpr.isFirst
            (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
                (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
                (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ1) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessBX.Vars.cnt GuessBX.Expr.nextCnt)
          (Command.ite GuessBX.BExpr.isFirst
            (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
                (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
                (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ1) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h4 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessBX.Vars.cnt GuessBX.Expr.nextCnt)
          (Command.ite GuessBX.BExpr.isFirst
            (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
                (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
                (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ1) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.ite GuessBX.BExpr.isFirst
          (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
              (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
              (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) := by
    rw [hφ2]
    exact Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessBX.Vocab])
  have h5 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.ite GuessBX.BExpr.isFirst
          (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
              (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
              (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.ite GuessBX.BExpr.isFirst
          (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
              (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
              (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h6 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        (Command.ite GuessBX.BExpr.isFirst
          (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
              (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
              (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
          (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
            (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [Command.step, GuessBX.Vocab, hisFirst2']; rfl)
  have h7 : Command.RunStep Tid.guessBX rest
      (some ⟨EventLabel.wt Tid.guessBX Loc.xB ((GuessBX.Vocab I).evalV GuessBX.VExpr.xTagRest φ2),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
          (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
            (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
            (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h8 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
            (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
          (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h9 : Command.RunStep Tid.guessBX rest
      (some ⟨EventLabel.wt Tid.guessBX Loc.zBx'x ((GuessBX.Vocab I).evalV GuessBX.VExpr.cntVal φ2),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
          (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h10 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h11 : Command.RunStep Tid.guessBX rest
      (some ⟨EventLabel.rd Tid.guessBX Loc.zBxx' ((GuessBX.Vocab I).evalV GuessBX.VExpr.prevVal φ2),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        Command.skip (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I),
        φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h12 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        Command.skip (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I),
        φ2) rest
      (Command.loopSeq (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr) (guessBXInnerLoop I),
        φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have h13 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr) (guessBXInnerLoop I),
        φ2) rest
      (Command.loopSeq Command.skip (guessBXInnerLoop I),
        Function.update φ2 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ2)) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessBX.Vocab])
  have h14 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq Command.skip (guessBXInnerLoop I),
        Function.update φ2 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ2)) rest
      (guessBXInnerLoop I,
        Function.update φ2 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ2)) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  have w2 := Command.step_complete h2
  have w3 := Command.step_complete h3
  have w4 := Command.step_complete h4
  have w5 := Command.step_complete h5
  have w6 := Command.step_complete h6
  have w7 := Command.step_complete h7
  have w8 := Command.step_complete h8
  have w9 := Command.step_complete h9
  have w10 := Command.step_complete h10
  have w11 := Command.step_complete h11
  have w12 := Command.step_complete h12
  have w13 := Command.step_complete h13
  have w14 := Command.step_complete h14
  set φ3 : (GuessBX.Vocab I).Store :=
    Function.update φ2 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ2) with hφ3
  have hfst3 : φ3 GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    have hne : GuessBX.Vars.fst ≠ GuessBX.Vars.j := by decide
    simp only [hφ3, Function.update_of_ne hne]; exact hfst2
  have hcnt3 : φ3 GuessBX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    have hne : GuessBX.Vars.cnt ≠ GuessBX.Vars.j := by decide
    simp only [hφ3, Function.update_of_ne hne]; exact hcnt2raw
  have hj3 : φ3 GuessBX.Vars.j = GuessBX.eval I GuessBX.Expr.jIncr φ2 := by
    rw [hφ3]; exact Function.update_self _ _ _
  have hj3' : φ3 GuessBX.Vars.j = GuessBX.eval I GuessBX.Expr.jIncr φ := by
    rw [hj3]; simp only [GuessBX.eval, hj_φ2]; rfl
  have haux3 : φ3 GuessBX.Vars.aux = φ GuessBX.Vars.aux := by
    have hne : GuessBX.Vars.aux ≠ GuessBX.Vars.j := by decide
    simp only [hφ3, Function.update_of_ne hne]; exact haux_φ2
  have hcntY_φ2 : φ2 GuessBX.Vars.cntY = φ GuessBX.Vars.cntY := by
    have hne_cnt : GuessBX.Vars.cntY ≠ GuessBX.Vars.cnt := by decide
    have hne_prev : GuessBX.Vars.cntY ≠ GuessBX.Vars.prev := by decide
    have hh1 : φ2 GuessBX.Vars.cntY = φ1 GuessBX.Vars.cntY := Function.update_of_ne hne_cnt _ _
    have hh2 : φ1 GuessBX.Vars.cntY = φ GuessBX.Vars.cntY := Function.update_of_ne hne_prev _ _
    rw [hh1, hh2]
  have hN_φ2 : φ2 GuessBX.Vars.N = φ GuessBX.Vars.N := by
    have hne_cnt : GuessBX.Vars.N ≠ GuessBX.Vars.cnt := by decide
    have hne_prev : GuessBX.Vars.N ≠ GuessBX.Vars.prev := by decide
    have hh1 : φ2 GuessBX.Vars.N = φ1 GuessBX.Vars.N := Function.update_of_ne hne_cnt _ _
    have hh2 : φ1 GuessBX.Vars.N = φ GuessBX.Vars.N := Function.update_of_ne hne_prev _ _
    rw [hh1, hh2]
  have hne_cntY_j : GuessBX.Vars.cntY ≠ GuessBX.Vars.j := by decide
  have hne_N_j : GuessBX.Vars.N ≠ GuessBX.Vars.j := by decide
  have hcntY3 : φ3 GuessBX.Vars.cntY = φ GuessBX.Vars.cntY := by
    have hh : φ3 GuessBX.Vars.cntY = φ2 GuessBX.Vars.cntY := Function.update_of_ne hne_cntY_j _ _
    rw [hh, hcntY_φ2]
  have hN3 : φ3 GuessBX.Vars.N = φ GuessBX.Vars.N := by
    have hh : φ3 GuessBX.Vars.N = φ2 GuessBX.Vars.N := Function.update_of_ne hne_N_j _ _
    rw [hh, hN_φ2]
  refine ⟨φ3, hfst3, hcnt3, hj3', haux3, hcntY3, hN3, ?_⟩
  simp only [Command.runFuel, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    hxTagRest2, hcntVal2, hprevVal2]
  rfl


/-! ## `GuessBX`'s outer loop

As for `GuessAX`. -/

/-- `rem` iterations of `guessBXInnerLoop` after the first call, as an
`.outOfFuel` result. -/
theorem guessBXInnerLoop_chain_outOfFuel (I : PCPInstance) :
    ∀ (rem : ℕ) (rest : List (GuessBX.Vals I)) (φ : (GuessBX.Vocab I).Store),
      (GuessBX.jOf I φ).val + rem = (GuessBX.NOf I φ).val + 1 →
      (k0 : Fin 4) → φ GuessBX.Vars.cnt = Sum.inr (Sum.inl k0) →
      φ GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) →
      (GuessBX.NOf I φ).val ≤ GuessBX.maxLen I →
      ∃ (vs : List (Val I × Val I × Val I)) (φf : (GuessBX.Vocab I).Store),
        vs.length = rem ∧
        φf GuessBX.Vars.cnt = Sum.inr (Sum.inl (⟨(k0.val + rem) % 4, by omega⟩ : Fin 4)) ∧
        φf GuessBX.Vars.aux = φ GuessBX.Vars.aux ∧
        φf GuessBX.Vars.cntY = φ GuessBX.Vars.cntY ∧
        φf GuessBX.Vars.N = φ GuessBX.Vars.N ∧
        φf GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
        (GuessBX.jOf I φf).val = (GuessBX.jOf I φ).val + rem ∧
        (∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
          e.2.2 = Val.cnt (⟨(k0.val + n) % 4, by omega⟩ : Fin 4) ∧
          e.2.1 = Val.cnt (⟨(k0.val + n + 1) % 4, by omega⟩ : Fin 4)) ∧
        (∀ n, n < rem → ∃ e j, vs[n]? = some e ∧ j.val = (GuessBX.jOf I φ).val + n ∧
          e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (GuessBX.auxOf I φ) j)) ∧
        Command.runFuel Tid.guessBX (guessBXInnerLoop I, φ) rest (14 * rem) =
          (.outOfFuel, vs.flatMap (guessBXInnerBlockElems I), (guessBXInnerLoop I, φf), rest) := by
  intro rem
  induction rem with
  | zero =>
      intro rest φ hrem k0 hcnt0 hfst hNbound
      refine ⟨[], φ, rfl, ?_, rfl, rfl, rfl, hfst, by omega, ?_, ?_, ?_⟩
      · have heq0 : (⟨(k0.val + 0) % 4, by omega⟩ : Fin 4) = k0 := by
          apply Fin.ext; show (k0.val + 0) % 4 = k0.val; omega
        rw [heq0]; exact hcnt0
      · intro n hn; simp at hn
      · intro n hn; omega
      · simp only [Command.runFuel, List.flatMap_nil]; rfl
  | succ rem ih =>
      intro rest φ hrem k0 hcnt0 hfst hNbound
      have hguardT' : GuessBX.evalB I GuessBX.BExpr.jLeN φ = true := by
        simp only [GuessBX.evalB, decide_eq_true_eq, Fin.le_def]
        omega
      have hguardT : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ = true := hguardT'
      obtain ⟨φ', hfst', hcnt', hj', haux', hcntY', hN', hstep14⟩ :=
        guessBX_innerLoop_rest_step_outOfFuel I rest φ hguardT hfst k0 hcnt0
      have hjleN : (GuessBX.jOf I φ).val ≤ (GuessBX.NOf I φ).val := by
        have hb := hguardT'
        simp only [GuessBX.evalB, decide_eq_true_eq, Fin.le_def] at hb
        exact hb
      have hjbound : (GuessBX.jOf I φ).val ≤ GuessBX.maxLen I := by omega
      have h1val : (1 : Fin (GuessBX.maxLen I + 2)).val = 1 := by
        simp [Fin.val_one']
      have hjOf' : (GuessBX.jOf I φ').val = (GuessBX.jOf I φ).val + 1 := by
        have heval : GuessBX.jOf I φ' = GuessBX.jOf I φ + 1 := by
          simp only [GuessBX.jOf, hj', GuessBX.eval]
        rw [heval, Fin.val_add_eq_of_add_lt (by rw [h1val]; omega), h1val]
      have hNOf' : (GuessBX.NOf I φ').val = (GuessBX.NOf I φ).val := by
        simp only [GuessBX.NOf, hN']
      have hrem' : (GuessBX.jOf I φ').val + rem = (GuessBX.NOf I φ').val + 1 := by
        rw [hjOf', hNOf']; omega
      have hNbound' : (GuessBX.NOf I φ').val ≤ GuessBX.maxLen I := by rw [hNOf']; exact hNbound
      obtain ⟨vs, φf, hvslen, hcntf, hauxf, hcntYf, hNf, hfstf, hjf, hval, hvalx, hstepRem⟩ :=
        ih rest φ' hrem' (k0 + 1) hcnt' hfst' hNbound'
      have hfuel : 14 * (rem + 1) = 14 + 14 * rem := by omega
      refine ⟨(Val.xTag (Tid.guessBX, false)
          (GuessBX.jthLetter I (GuessBX.auxOf I φ) (GuessBX.jOf I φ)),
          Val.cnt (k0 + 1), Val.cnt k0) :: vs, φf, by simp [hvslen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_⟩
      · rw [hcntf]; congr 2; apply Fin.ext; show ((k0.val + 1) % 4 + rem) % 4 = (k0.val + (rem + 1)) % 4
        omega
      · rw [hauxf, haux']
      · rw [hcntYf, hcntY']
      · rw [hNf, hN']
      · exact hfstf
      · rw [hjf, hjOf']; omega
      · intro n hn
        cases n with
        | zero =>
            refine ⟨_, rfl, ?_, ?_⟩
            · show Val.cnt k0 = Val.cnt (⟨(k0.val + 0) % 4, by omega⟩ : Fin 4)
              congr 1; apply Fin.ext; show k0.val = (k0.val + 0) % 4; omega
            · show Val.cnt (k0 + 1) = Val.cnt (⟨(k0.val + 0 + 1) % 4, by omega⟩ : Fin 4)
              congr 1
        | succ n =>
            simp only [List.length_cons] at hn
            have hn' : n < vs.length := by omega
            obtain ⟨e, hevs, he1, he2⟩ := hval n hn'
            refine ⟨e, ?_, ?_, ?_⟩
            · simpa using hevs
            · rw [he1]; congr 1; apply Fin.ext
              simp only [Fin.val_add]
              omega
            · rw [he2]; congr 1; apply Fin.ext
              simp only [Fin.val_add]
              omega
      · intro n hn
        cases n with
        | zero =>
            refine ⟨_, GuessBX.jOf I φ, rfl, by simp, rfl⟩
        | succ n =>
            simp only [Nat.add_lt_add_iff_right] at hn
            obtain ⟨e, j, hevs, hjval, he1⟩ := hvalx n hn
            refine ⟨e, j, ?_, ?_, ?_⟩
            · simpa using hevs
            · rw [hjval, hjOf']; omega
            · rw [he1]; simp only [GuessBX.auxOf, haux']
      · rw [hfuel]
        have hcomb := Command.runFuel_outOfFuel_append 14 (guessBXInnerLoop I, φ) rest _ _ _
          hstep14 (14 * rem) _ _ _ _ hstepRem
        rw [show
          ((Val.xTag (Tid.guessBX, false)
              (GuessBX.jthLetter I (GuessBX.auxOf I φ) (GuessBX.jOf I φ)),
              Val.cnt (k0 + 1), Val.cnt k0) :: vs).flatMap (guessBXInnerBlockElems I) =
            [ ⟨EventLabel.wt Tid.guessBX Loc.xB
                (Val.xTag (Tid.guessBX, false)
                  (GuessBX.jthLetter I (GuessBX.auxOf I φ) (GuessBX.jOf I φ))), rfl⟩
            , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt (k0 + 1)), rfl⟩
            , ⟨EventLabel.rd Tid.guessBX Loc.zBxx' (Val.cnt k0), rfl⟩ ] ++
              vs.flatMap (guessBXInnerBlockElems I) from by
            simp only [List.flatMap_cons]; congr 1]
        exact hcomb

/-- The exit of `guessBXInnerLoop`, as an `.outOfFuel` result. -/
theorem guessBXOuterExit_step_outOfFuel (I : PCPInstance) (rest : List (GuessBX.Vals I))
    (φ : (GuessBX.Vocab I).Store) (C2 : Command (domainOf I) (GuessBX.Vocab I))
    (hguard : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ = false) :
    Command.runFuel Tid.guessBX (Command.seq (guessBXInnerLoop I) C2, φ) rest 2 =
      (.outOfFuel, [], (C2, φ), rest) := by
  have hguard' : GuessBX.evalB I GuessBX.BExpr.jLeN φ = false := hguard
  have h1 : Command.RunStep Tid.guessBX rest none
      (Command.seq (guessBXInnerLoop I) C2, φ) rest
      (Command.seq Command.skip C2, φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [guessBXInnerLoop, Command.step, GuessBX.Vocab, hguard']; rfl)
  have h2 : Command.RunStep Tid.guessBX rest none
      (Command.seq Command.skip C2, φ) rest (C2, φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  have w2 := Command.step_complete h2
  simp only [Command.runFuel, w1, w2]
  rfl

/-- The first four steps of `guessBXOuterTail_continue_step_inv`, up to the
`ndetAssign` draw, as an `.outOfFuel` result for an arbitrary resolution
`s`. -/
theorem guessBXOuterTail_continue_pre_step_outOfFuel (I : PCPInstance)
    (s : List (GuessBX.Vals I)) (φ : (GuessBX.Vocab I).Store)
    (cntY0 : Fin 4) (hcntY0 : φ GuessBX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (v : Fin I.n) (haux : φ GuessBX.Vars.aux = Sum.inl (some v)) :
    Command.runFuel Tid.guessBX
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ) s 4 =
      (.outOfFuel,
        [⟨EventLabel.rd Tid.guessBX Loc.ellByx (Val.cntAux cntY0 (some v)), rfl⟩],
        (Command.loopSeq
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I))
          (guessBXLoop I), φ), s) := by
  have hellVal :
      (GuessBX.Vocab I).evalV GuessBX.VExpr.cntYAuxVal φ = Val.cntAux cntY0 (some v) := by
    have hcntYOfφ : GuessBX.cntYOf I φ = cntY0 := by simp only [GuessBX.cntYOf, hcntY0]
    have hauxOfφ : GuessBX.auxOf I φ = some v := by simp only [GuessBX.auxOf, haux]
    simp only [GuessBX.Vocab, GuessBX.evalV, hcntYOfφ, hauxOfφ]; rfl
  have h1 : Command.RunStep Tid.guessBX s
      (some ⟨EventLabel.rd Tid.guessBX Loc.ellByx
        ((GuessBX.Vocab I).evalV GuessBX.VExpr.cntYAuxVal φ), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ)
      s
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  have h2 : Command.RunStep Tid.guessBX s none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ)
      s
      (Command.loopSeq
        (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w2 := Command.step_complete h2
  have haux' : (GuessBX.Vocab I).evalB GuessBX.BExpr.isBot φ = false := by
    simp [GuessBX.Vocab, GuessBX.evalB, haux]
  have h3 : Command.RunStep Tid.guessBX s none
      (Command.loopSeq
        (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ)
      s
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp [Command.step, haux'])
  have w3 := Command.step_complete h3
  have h4 : Command.RunStep Tid.guessBX s none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ)
      s
      (Command.loopSeq
        (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
          (GuessBX.auxSetBot_nonempty I))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w4 := Command.step_complete h4
  simp only [Command.runFuel, w1, w2, w3, w4, hellVal]
  rfl

/-- The converse of `guessBXOuterTail_continue_step`, for a given drawn value
`v0'`. -/
theorem guessBXOuterTail_continue_step_inv (I : PCPInstance) (v0' : Option (Fin I.n))
    (rest : List (GuessBX.Vals I))
    (φ : (GuessBX.Vocab I).Store)
    (cntY0 : Fin 4) (hcntY0 : φ GuessBX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (v : Fin I.n) (haux : φ GuessBX.Vars.aux = Sum.inl (some v))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBX))
    (cf : Config (domainOf I) (GuessBX.Vocab I)) (sf : List (GuessBX.Vals I))
    (h : Command.runFuel Tid.guessBX
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ) (Sum.inl v0' :: rest) (N + 6) = (.stuck, σ, cf, sf)) :
    ∃ σ1, σ = [⟨EventLabel.rd Tid.guessBX Loc.ellByx (Val.cntAux cntY0 (some v)), rfl⟩] ++ σ1 ∧
      Command.runFuel Tid.guessBX (guessBXLoop I,
        Function.update φ GuessBX.Vars.aux (Sum.inl v0')) rest N = (.stuck, σ1, cf, sf) := by
  have hellVal :
      (GuessBX.Vocab I).evalV GuessBX.VExpr.cntYAuxVal φ = Val.cntAux cntY0 (some v) := by
    have hcntYOfφ : GuessBX.cntYOf I φ = cntY0 := by simp only [GuessBX.cntYOf, hcntY0]
    have hauxOfφ : GuessBX.auxOf I φ = some v := by simp only [GuessBX.auxOf, haux]
    simp only [GuessBX.Vocab, GuessBX.evalV, hcntYOfφ, hauxOfφ]; rfl
  have h1 : Command.RunStep Tid.guessBX (Sum.inl v0' :: rest)
      (some ⟨EventLabel.rd Tid.guessBX Loc.ellByx
        ((GuessBX.Vocab I).evalV GuessBX.VExpr.cntYAuxVal φ), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ)
      (Sum.inl v0' :: rest)
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  simp only [Command.runFuel, w1] at h
  have h2 : Command.RunStep Tid.guessBX (Sum.inl v0' :: rest) none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ)
      (Sum.inl v0' :: rest)
      (Command.loopSeq
        (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w2 := Command.step_complete h2
  simp only [w2] at h
  have haux' : (GuessBX.Vocab I).evalB GuessBX.BExpr.isBot φ = false := by
    simp [GuessBX.Vocab, GuessBX.evalB, haux]
  have h3 : Command.RunStep Tid.guessBX (Sum.inl v0' :: rest) none
      (Command.loopSeq
        (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ)
      (Sum.inl v0' :: rest)
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp [Command.step, haux'])
  have w3 := Command.step_complete h3
  simp only [w3] at h
  have h4 : Command.RunStep Tid.guessBX (Sum.inl v0' :: rest) none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ)
      (Sum.inl v0' :: rest)
      (Command.loopSeq
        (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
          (GuessBX.auxSetBot_nonempty I))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w4 := Command.step_complete h4
  simp only [w4] at h
  have hmem : (Sum.inl v0' : GuessBX.Vals I) ∈ GuessBX.auxSetBot I := by
    simp only [GuessBX.auxSetBot, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨v0', rfl⟩
  have h5 : Command.RunStep Tid.guessBX (Sum.inl v0' :: rest) none
      (Command.loopSeq
        (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
          (GuessBX.auxSetBot_nonempty I))
        (guessBXLoop I), φ)
      rest
      (Command.loopSeq Command.skip (guessBXLoop I),
        Function.update φ GuessBX.Vars.aux (Sum.inl v0')) := by
    apply Command.step_sound
    simp only [Command.step]
    split_ifs with hif
    · rfl
    · exact absurd hmem hif
  have w5 := Command.step_complete h5
  simp only [w5] at h
  have h6 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq Command.skip (guessBXLoop I),
        Function.update φ GuessBX.Vars.aux (Sum.inl v0'))
      rest
      (guessBXLoop I, Function.update φ GuessBX.Vars.aux (Sum.inl v0')) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w6 := Command.step_complete h6
  simp only [w6] at h
  injection h with hres h'
  injection h' with hwd h''
  injection h'' with hcf hsf
  rw [hellVal] at hwd
  exact ⟨(Command.runFuel Tid.guessBX (guessBXLoop I,
    Function.update φ GuessBX.Vars.aux (Sum.inl v0')) rest N).2.1, hwd.symm,
    by rw [← hres, ← hcf, ← hsf]; rfl⟩

/-- The converse of `guessBXOuterTail_break_step`. -/
theorem guessBXOuterTail_break_step_inv (I : PCPInstance) (rest : List (GuessBX.Vals I))
    (φ : (GuessBX.Vocab I).Store)
    (cntY0 : Fin 4) (hcntY0 : φ GuessBX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (haux : φ GuessBX.Vars.aux = Sum.inl none)
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBX))
    (cf : Config (domainOf I) (GuessBX.Vocab I)) (sf : List (GuessBX.Vals I))
    (h : Command.runFuel Tid.guessBX
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ) rest (N + 5) = (.stuck, σ, cf, sf)) :
    ∃ σ1, σ = [⟨EventLabel.rd Tid.guessBX Loc.ellByx (Val.cntAux cntY0 none), rfl⟩] ++ σ1 ∧
      Command.runFuel Tid.guessBX (Command.skip, φ) rest N = (.stuck, σ1, cf, sf) := by
  have hellVal :
      (GuessBX.Vocab I).evalV GuessBX.VExpr.cntYAuxVal φ = Val.cntAux cntY0 none := by
    have hcntYOfφ : GuessBX.cntYOf I φ = cntY0 := by simp only [GuessBX.cntYOf, hcntY0]
    have hauxOfφ : GuessBX.auxOf I φ = none := by simp only [GuessBX.auxOf, haux]
    simp only [GuessBX.Vocab, GuessBX.evalV, hcntYOfφ, hauxOfφ]; rfl
  have h1 : Command.RunStep Tid.guessBX rest
      (some ⟨EventLabel.rd Tid.guessBX Loc.ellByx
        ((GuessBX.Vocab I).evalV GuessBX.VExpr.cntYAuxVal φ), rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ)
      rest
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w1 := Command.step_complete h1
  simp only [Command.runFuel, w1] at h
  have h2 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I))))
        (guessBXLoop I), φ)
      rest
      (Command.loopSeq
        (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w2 := Command.step_complete h2
  simp only [w2] at h
  have haux' : (GuessBX.Vocab I).evalB GuessBX.BExpr.isBot φ = true := by
    simp [GuessBX.Vocab, GuessBX.evalB, haux]
  have h3 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq
        (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ)
      rest
      (Command.loopSeq
        (Command.seq Command.brk
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp [Command.step, haux'])
  have w3 := Command.step_complete h3
  simp only [w3] at h
  have h4 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq
        (Command.seq Command.brk
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I)))
        (guessBXLoop I), φ)
      rest
      (Command.loopSeq Command.brk (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w4 := Command.step_complete h4
  simp only [w4] at h
  have h5 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq Command.brk (guessBXLoop I), φ)
      rest
      (Command.skip, φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w5 := Command.step_complete h5
  simp only [w5] at h
  injection h with hres h'
  injection h' with hwd h''
  injection h'' with hcf hsf
  rw [hellVal] at hwd
  exact ⟨(Command.runFuel Tid.guessBX (Command.skip, φ) rest N).2.1, hwd.symm,
    by rw [← hres, ← hcf, ← hsf]; rfl⟩

/-- The converse of `guessBXOuterHead_step`. -/
theorem guessBXOuterHead_step_inv (I : PCPInstance) (rest : List (GuessBX.Vals I))
    (φ : (GuessBX.Vocab I).Store)
    (aux0 : Option (Fin I.n)) (haux0 : φ GuessBX.Vars.aux = Sum.inl aux0)
    (cntY0 : Fin 4) (hcntY0 : φ GuessBX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBX))
    (cf : Config (domainOf I) (GuessBX.Vocab I)) (sf : List (GuessBX.Vals I))
    (h : Command.runFuel Tid.guessBX (guessBXLoop I, φ) rest (N + 9) = (.stuck, σ, cf, sf)) :
    ∃ (φ' : (GuessBX.Vocab I).Store) (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBX)),
      σ = [⟨EventLabel.wt Tid.guessBX Loc.zBxy (Val.cnt (cntY0 + 1)), rfl⟩] ++ σ1 ∧
      φ' GuessBX.Vars.cnt = φ GuessBX.Vars.cnt ∧
      φ' GuessBX.Vars.fst = φ GuessBX.Vars.fst ∧
      φ' GuessBX.Vars.aux = φ GuessBX.Vars.aux ∧
      φ' GuessBX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) ∧
      (GuessBX.jOf I φ').val = 1 ∧
      (GuessBX.NOf I φ').val = (GuessBX.extBeta I aux0).length ∧
      Command.runFuel Tid.guessBX
        (Command.loopSeq (Command.seq (guessBXInnerLoop I)
          (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
            (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                (GuessBX.auxSetBot_nonempty I)))))
          (guessBXLoop I), φ') rest N = (.stuck, σ1, cf, sf) := by
  set φ0 : (GuessBX.Vocab I).Store :=
    Function.update φ GuessBX.Vars.cntY (GuessBX.eval I GuessBX.Expr.nextCntY φ) with hφ0
  set φ0j : (GuessBX.Vocab I).Store :=
    Function.update φ0 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.one φ0) with hφ0j
  set φ0jN : (GuessBX.Vocab I).Store :=
    Function.update φ0j GuessBX.Vars.N (GuessBX.eval I GuessBX.Expr.betaLen φ0j) with hφ0jN
  have hcntYOfφ : GuessBX.cntYOf I φ = cntY0 := by simp only [GuessBX.cntYOf, hcntY0]
  have hcntY0eq : φ0 GuessBX.Vars.cntY = GuessBX.eval I GuessBX.Expr.nextCntY φ :=
    Function.update_self _ _ _
  have hcntY0raw : φ0 GuessBX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
    simp only [hcntY0eq, GuessBX.eval, hcntYOfφ]; rfl
  have hne_cnt_cntY : GuessBX.Vars.cnt ≠ GuessBX.Vars.cntY := by decide
  have hne_fst_cntY : GuessBX.Vars.fst ≠ GuessBX.Vars.cntY := by decide
  have hne_aux_cntY : GuessBX.Vars.aux ≠ GuessBX.Vars.cntY := by decide
  have hcnt0' : φ0 GuessBX.Vars.cnt = φ GuessBX.Vars.cnt := Function.update_of_ne hne_cnt_cntY _ _
  have hfst0' : φ0 GuessBX.Vars.fst = φ GuessBX.Vars.fst := Function.update_of_ne hne_fst_cntY _ _
  have haux0' : φ0 GuessBX.Vars.aux = φ GuessBX.Vars.aux := Function.update_of_ne hne_aux_cntY _ _
  have hcntYVal0 : (GuessBX.Vocab I).evalV GuessBX.VExpr.cntYVal φ0 = Val.cnt (cntY0 + 1) := by
    have hh : GuessBX.cntYOf I φ0 = cntY0 + 1 := by simp only [GuessBX.cntYOf, hcntY0raw]
    simp only [GuessBX.Vocab, GuessBX.evalV, hh]; rfl
  have hj0eq : φ0j GuessBX.Vars.j = GuessBX.eval I GuessBX.Expr.one φ0 := Function.update_self _ _ _
  have hjOf0jVal : (GuessBX.jOf I φ0j).val = 1 := by
    simp only [hj0eq, GuessBX.jOf, GuessBX.eval]
  have hne_cnt_j : GuessBX.Vars.cnt ≠ GuessBX.Vars.j := by decide
  have hne_fst_j : GuessBX.Vars.fst ≠ GuessBX.Vars.j := by decide
  have hne_aux_j : GuessBX.Vars.aux ≠ GuessBX.Vars.j := by decide
  have hne_cntY_j : GuessBX.Vars.cntY ≠ GuessBX.Vars.j := by decide
  have hcnt0j : φ0j GuessBX.Vars.cnt = φ0 GuessBX.Vars.cnt := Function.update_of_ne hne_cnt_j _ _
  have hfst0j : φ0j GuessBX.Vars.fst = φ0 GuessBX.Vars.fst := Function.update_of_ne hne_fst_j _ _
  have haux0j : φ0j GuessBX.Vars.aux = φ0 GuessBX.Vars.aux := Function.update_of_ne hne_aux_j _ _
  have hcntY0j : φ0j GuessBX.Vars.cntY = φ0 GuessBX.Vars.cntY :=
    Function.update_of_ne hne_cntY_j _ _
  have haux0j' : φ0j GuessBX.Vars.aux = Sum.inl aux0 := by rw [haux0j, haux0', haux0]
  have hauxOf0j : GuessBX.auxOf I φ0j = aux0 := by simp only [GuessBX.auxOf, haux0j']
  have hN0jeq : φ0jN GuessBX.Vars.N = GuessBX.eval I GuessBX.Expr.betaLen φ0j :=
    Function.update_self _ _ _
  have hNOf0jNVal : (GuessBX.NOf I φ0jN).val = (GuessBX.extBeta I aux0).length := by
    simp only [hN0jeq, GuessBX.NOf, GuessBX.eval, hauxOf0j]
  have hne_cnt_N : GuessBX.Vars.cnt ≠ GuessBX.Vars.N := by decide
  have hne_fst_N : GuessBX.Vars.fst ≠ GuessBX.Vars.N := by decide
  have hne_aux_N : GuessBX.Vars.aux ≠ GuessBX.Vars.N := by decide
  have hne_j_N : GuessBX.Vars.j ≠ GuessBX.Vars.N := by decide
  have hne_cntY_N : GuessBX.Vars.cntY ≠ GuessBX.Vars.N := by decide
  have hcnt0jN : φ0jN GuessBX.Vars.cnt = φ0j GuessBX.Vars.cnt := Function.update_of_ne hne_cnt_N _ _
  have hfst0jN : φ0jN GuessBX.Vars.fst = φ0j GuessBX.Vars.fst := Function.update_of_ne hne_fst_N _ _
  have haux0jN : φ0jN GuessBX.Vars.aux = φ0j GuessBX.Vars.aux := Function.update_of_ne hne_aux_N _ _
  have hj0jN : φ0jN GuessBX.Vars.j = φ0j GuessBX.Vars.j := Function.update_of_ne hne_j_N _ _
  have hcntY0jN : φ0jN GuessBX.Vars.cntY = φ0j GuessBX.Vars.cntY :=
    Function.update_of_ne hne_cntY_N _ _
  have hjOf0jNVal : (GuessBX.jOf I φ0jN).val = 1 := by
    have heq : GuessBX.jOf I φ0jN = GuessBX.jOf I φ0j := by simp only [GuessBX.jOf, hj0jN]
    rw [heq]; exact hjOf0jVal
  have h1 : Command.RunStep Tid.guessBX rest none (guessBXLoop I, φ) rest
      (Command.loopSeq (GuessBX.outerBody I) (guessBXLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [guessBXLoop, Command.step, GuessBX.Vocab, GuessBX.evalB, if_true])
  have w1 := Command.step_complete h1
  simp only [Command.runFuel, w1] at h
  have h2 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (GuessBX.outerBody I) (guessBXLoop I), φ) rest
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.zBxy GuessBX.VExpr.cntYVal)
          (Command.seq (Command.forLoop GuessBX.Vars.j GuessBX.Vars.N GuessBX.Expr.betaLen
              GuessBX.Expr.one GuessBX.BExpr.jLeN GuessBX.Expr.jIncr (GuessBX.innerBody I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))))
        (guessBXLoop I), φ0) := by
    rw [hφ0]
    exact Command.step_sound _ _ _ _ _ _ _ (by
      simp only [GuessBX.outerBody, Command.step, GuessBX.Vocab]; rfl)
  have w2 := Command.step_complete h2
  simp only [w2] at h
  have h3 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.write Loc.zBxy GuessBX.VExpr.cntYVal)
          (Command.seq (Command.forLoop GuessBX.Vars.j GuessBX.Vars.N GuessBX.Expr.betaLen
              GuessBX.Expr.one GuessBX.BExpr.jLeN GuessBX.Expr.jIncr (GuessBX.innerBody I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))))
        (guessBXLoop I), φ0) rest
      (Command.loopSeq
        (Command.seq (Command.write Loc.zBxy GuessBX.VExpr.cntYVal)
          (Command.seq (Command.forLoop GuessBX.Vars.j GuessBX.Vars.N GuessBX.Expr.betaLen
              GuessBX.Expr.one GuessBX.BExpr.jLeN GuessBX.Expr.jIncr (GuessBX.innerBody I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I))))))
        (guessBXLoop I), φ0) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w3 := Command.step_complete h3
  simp only [w3] at h
  have h4 : Command.RunStep Tid.guessBX rest
      (some ⟨EventLabel.wt Tid.guessBX Loc.zBxy ((GuessBX.Vocab I).evalV GuessBX.VExpr.cntYVal φ0),
        rfl⟩)
      (Command.loopSeq
        (Command.seq (Command.write Loc.zBxy GuessBX.VExpr.cntYVal)
          (Command.seq (Command.forLoop GuessBX.Vars.j GuessBX.Vars.N GuessBX.Expr.betaLen
              GuessBX.Expr.one GuessBX.BExpr.jLeN GuessBX.Expr.jIncr (GuessBX.innerBody I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I))))))
        (guessBXLoop I), φ0) rest
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.forLoop GuessBX.Vars.j GuessBX.Vars.N GuessBX.Expr.betaLen
              GuessBX.Expr.one GuessBX.BExpr.jLeN GuessBX.Expr.jIncr (GuessBX.innerBody I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I))))))
        (guessBXLoop I), φ0) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w4 := Command.step_complete h4
  simp only [Command.runFuel, w4] at h
  have h5 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq
        (Command.seq Command.skip
          (Command.seq (Command.forLoop GuessBX.Vars.j GuessBX.Vars.N GuessBX.Expr.betaLen
              GuessBX.Expr.one GuessBX.BExpr.jLeN GuessBX.Expr.jIncr (GuessBX.innerBody I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I))))))
        (guessBXLoop I), φ0) rest
      (Command.loopSeq
        (Command.seq (Command.forLoop GuessBX.Vars.j GuessBX.Vars.N GuessBX.Expr.betaLen
              GuessBX.Expr.one GuessBX.BExpr.jLeN GuessBX.Expr.jIncr (GuessBX.innerBody I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w5 := Command.step_complete h5
  simp only [w5] at h
  have h6 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq
        (Command.seq (Command.forLoop GuessBX.Vars.j GuessBX.Vars.N GuessBX.Expr.betaLen
              GuessBX.Expr.one GuessBX.BExpr.jLeN GuessBX.Expr.jIncr (GuessBX.innerBody I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0) rest
      (Command.loopSeq
        (Command.seq (Command.seq Command.skip
            (Command.seq (Command.assign GuessBX.Vars.N GuessBX.Expr.betaLen)
              (guessBXInnerLoop I)))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0j) := by
    rw [hφ0j]
    exact Command.step_sound _ _ _ _ _ _ _ (by
      simp only [Command.forLoop, guessBXInnerLoop, Command.step, GuessBX.Vocab]; rfl)
  have w6 := Command.step_complete h6
  simp only [w6] at h
  have h7 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq
        (Command.seq (Command.seq Command.skip
            (Command.seq (Command.assign GuessBX.Vars.N GuessBX.Expr.betaLen)
              (guessBXInnerLoop I)))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0j) rest
      (Command.loopSeq
        (Command.seq
            (Command.seq (Command.assign GuessBX.Vars.N GuessBX.Expr.betaLen)
              (guessBXInnerLoop I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0j) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w7 := Command.step_complete h7
  simp only [w7] at h
  have h8 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq
        (Command.seq
            (Command.seq (Command.assign GuessBX.Vars.N GuessBX.Expr.betaLen)
              (guessBXInnerLoop I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0j) rest
      (Command.loopSeq
        (Command.seq
            (Command.seq Command.skip (guessBXInnerLoop I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0jN) := by
    rw [hφ0jN]
    exact Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessBX.Vocab])
  have w8 := Command.step_complete h8
  simp only [w8] at h
  have h9 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq
        (Command.seq
            (Command.seq Command.skip (guessBXInnerLoop I))
            (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
              (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
                (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0jN) rest
      (Command.loopSeq (Command.seq (guessBXInnerLoop I)
          (Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
            (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                (GuessBX.auxSetBot_nonempty I)))))
        (guessBXLoop I), φ0jN) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w9 := Command.step_complete h9
  simp only [w9] at h
  injection h with h1' h2'
  injection h2' with hwd h3'
  injection h3' with hcf hsf
  rw [hcntYVal0] at hwd
  refine ⟨φ0jN, _, hwd.symm, ?_, ?_, ?_, ?_, hjOf0jNVal, hNOf0jNVal,
    by rw [← h1', ← hcf, ← hsf]; rfl⟩
  · rw [hcnt0jN, hcnt0j, hcnt0']
  · rw [hfst0jN, hfst0j, hfst0']
  · rw [haux0jN, haux0j, haux0']
  · rw [hcntY0jN, hcntY0j, hcntY0raw]

/-- The first call of `guessBXInnerLoop`, as an `.outOfFuel` result after
exactly 14 steps. -/
theorem guessBX_innerLoop_first_step_outOfFuel (I : PCPInstance) (rest : List (GuessBX.Vals I))
    (φ : (GuessBX.Vocab I).Store)
    (hguard : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ = true)
    (hfst : φ GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)))
    (k : Fin 4) (hcnt0 : φ GuessBX.Vars.cnt = Sum.inr (Sum.inl k)) :
    ∃ (φ' : (GuessBX.Vocab I).Store),
      φ' GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
      φ' GuessBX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
      φ' GuessBX.Vars.j = GuessBX.eval I GuessBX.Expr.jIncr φ ∧
      φ' GuessBX.Vars.aux = φ GuessBX.Vars.aux ∧
      φ' GuessBX.Vars.cntY = φ GuessBX.Vars.cntY ∧
      φ' GuessBX.Vars.N = φ GuessBX.Vars.N ∧
      Command.runFuel Tid.guessBX (guessBXInnerLoop I, φ) rest 14 =
        (.outOfFuel,
          [ ⟨EventLabel.wt Tid.guessBX Loc.xB
              (Val.xTag (Tid.guessBX, true)
                (GuessBX.jthLetter I (GuessBX.auxOf I φ) (GuessBX.jOf I φ))), rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt (k + 1)), rfl⟩ ],
          (guessBXInnerLoop I, φ'), rest) := by
  set φ1 : (GuessBX.Vocab I).Store :=
    Function.update φ GuessBX.Vars.prev (GuessBX.eval I GuessBX.Expr.readCnt φ) with hφ1
  set φ2 : (GuessBX.Vocab I).Store :=
    Function.update φ1 GuessBX.Vars.cnt (GuessBX.eval I GuessBX.Expr.nextCnt φ1) with hφ2
  have hcnt_φ1 : φ1 GuessBX.Vars.cnt = φ GuessBX.Vars.cnt := rfl
  have hcntOf_φ1 : GuessBX.cntOf I φ1 = k := by simp only [GuessBX.cntOf, hcnt_φ1, hcnt0]
  have hcnt2eq : φ2 GuessBX.Vars.cnt = GuessBX.eval I GuessBX.Expr.nextCnt φ1 :=
    Function.update_self _ _ _
  have hcnt2raw : φ2 GuessBX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt2eq, GuessBX.eval, hcntOf_φ1]; rfl
  have hguard' : GuessBX.evalB I GuessBX.BExpr.jLeN φ = true := hguard
  have hne_fst_cnt : GuessBX.Vars.fst ≠ GuessBX.Vars.cnt := by decide
  have hne_fst_prev : GuessBX.Vars.fst ≠ GuessBX.Vars.prev := by decide
  have hfst_φ1 : φ1 GuessBX.Vars.fst = φ GuessBX.Vars.fst := rfl
  have hfst2 : φ2 GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)) := by
    have h1x : φ2 GuessBX.Vars.fst = φ1 GuessBX.Vars.fst := Function.update_of_ne hne_fst_cnt _ _
    rw [h1x, hfst_φ1, hfst]
  have hisFirst2 : (GuessBX.Vocab I).evalB GuessBX.BExpr.isFirst φ2 = true := by
    simp [GuessBX.Vocab, GuessBX.evalB, hfst2]
  have hisFirst2' : GuessBX.evalB I GuessBX.BExpr.isFirst φ2 = true := hisFirst2
  set φ3 : (GuessBX.Vocab I).Store :=
    Function.update φ2 GuessBX.Vars.fst (GuessBX.eval I GuessBX.Expr.fstFalse φ2) with hφ3
  have hfst3 : φ3 GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    have h1x : φ3 GuessBX.Vars.fst = GuessBX.eval I GuessBX.Expr.fstFalse φ2 :=
      Function.update_self _ _ _
    simp only [h1x, GuessBX.eval]; rfl
  have hne_cnt_fst : GuessBX.Vars.cnt ≠ GuessBX.Vars.fst := by decide
  have hcnt3raw : φ3 GuessBX.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    have h1x : φ3 GuessBX.Vars.cnt = φ2 GuessBX.Vars.cnt := Function.update_of_ne hne_cnt_fst _ _
    rw [h1x, hcnt2raw]
  have hne_aux_cnt : GuessBX.Vars.aux ≠ GuessBX.Vars.cnt := by decide
  have hne_aux_prev : GuessBX.Vars.aux ≠ GuessBX.Vars.prev := by decide
  have hne_aux_fst : GuessBX.Vars.aux ≠ GuessBX.Vars.fst := by decide
  have haux_φ2 : φ2 GuessBX.Vars.aux = φ GuessBX.Vars.aux := by
    have h1x : φ2 GuessBX.Vars.aux = φ1 GuessBX.Vars.aux := Function.update_of_ne hne_aux_cnt _ _
    have h2x : φ1 GuessBX.Vars.aux = φ GuessBX.Vars.aux := Function.update_of_ne hne_aux_prev _ _
    rw [h1x, h2x]
  have haux_φ3 : φ3 GuessBX.Vars.aux = φ GuessBX.Vars.aux := by
    have h1x : φ3 GuessBX.Vars.aux = φ2 GuessBX.Vars.aux := Function.update_of_ne hne_aux_fst _ _
    rw [h1x, haux_φ2]
  have hne_j_cnt : GuessBX.Vars.j ≠ GuessBX.Vars.cnt := by decide
  have hne_j_prev : GuessBX.Vars.j ≠ GuessBX.Vars.prev := by decide
  have hne_j_fst : GuessBX.Vars.j ≠ GuessBX.Vars.fst := by decide
  have hj_φ2 : GuessBX.jOf I φ2 = GuessBX.jOf I φ := by
    have h1x : φ2 GuessBX.Vars.j = φ1 GuessBX.Vars.j := Function.update_of_ne hne_j_cnt _ _
    have h2x : φ1 GuessBX.Vars.j = φ GuessBX.Vars.j := Function.update_of_ne hne_j_prev _ _
    simp only [GuessBX.jOf, h1x, h2x]
  have hj_φ3 : GuessBX.jOf I φ3 = GuessBX.jOf I φ := by
    have h1x : φ3 GuessBX.Vars.j = φ2 GuessBX.Vars.j := Function.update_of_ne hne_j_fst _ _
    simp only [GuessBX.jOf, h1x]; exact hj_φ2
  have hxTagFirst3 : (GuessBX.Vocab I).evalV GuessBX.VExpr.xTagFirst φ3 =
      Val.xTag (Tid.guessBX, true) (GuessBX.jthLetter I (GuessBX.auxOf I φ) (GuessBX.jOf I φ)) := by
    simp only [GuessBX.Vocab, GuessBX.evalV, GuessBX.auxOf, haux_φ3, hj_φ3]; rfl
  have hcntVal3 : (GuessBX.Vocab I).evalV GuessBX.VExpr.cntVal φ3 = Val.cnt (k + 1) := by
    have hcnt3 : GuessBX.cntOf I φ3 = k + 1 := by simp only [GuessBX.cntOf, hcnt3raw]
    simp only [GuessBX.Vocab, GuessBX.evalV, hcnt3]; rfl
  have h1 : Command.RunStep Tid.guessBX rest none (guessBXInnerLoop I, φ) rest
      (Command.loopSeq (Command.seq (GuessBX.innerBody I)
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [guessBXInnerLoop, Command.step, GuessBX.Vocab, hguard', if_true])
  have w1 := Command.step_complete h1
  have h2 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq (GuessBX.innerBody I)
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.assign GuessBX.Vars.cnt GuessBX.Expr.nextCnt)
          (Command.ite GuessBX.BExpr.isFirst
            (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
                (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
                (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ1) := by
    rw [hφ1]
    exact Command.step_sound _ _ _ _ _ _ _ (by
      simp only [GuessBX.innerBody, Command.firstIt, Command.step, GuessBX.Vocab]; rfl)
  have w2 := Command.step_complete h2
  have h3 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.assign GuessBX.Vars.cnt GuessBX.Expr.nextCnt)
          (Command.ite GuessBX.BExpr.isFirst
            (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
                (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
                (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ1) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessBX.Vars.cnt GuessBX.Expr.nextCnt)
          (Command.ite GuessBX.BExpr.isFirst
            (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
                (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
                (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ1) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w3 := Command.step_complete h3
  have h4 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessBX.Vars.cnt GuessBX.Expr.nextCnt)
          (Command.ite GuessBX.BExpr.isFirst
            (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
              (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
                (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
              (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
                (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ1) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.ite GuessBX.BExpr.isFirst
          (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
              (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
              (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) := by
    rw [hφ2]
    exact Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessBX.Vocab])
  have w4 := Command.step_complete h4
  have h5 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.ite GuessBX.BExpr.isFirst
          (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
              (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
              (Command.read Loc.zBxx' GuessBX.VExpr.prevVal)))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.ite GuessBX.BExpr.isFirst
          (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
              (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
              (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w5 := Command.step_complete h5
  have h6 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        (Command.ite GuessBX.BExpr.isFirst
          (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
            (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
              (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagRest)
            (Command.seq (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
              (Command.read Loc.zBxx' GuessBX.VExpr.prevVal))))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
            (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) :=
    Command.step_sound _ _ _ _ _ _ _ (by
      simp only [Command.step, GuessBX.Vocab, hisFirst2']; rfl)
  have w6 := Command.step_complete h6
  have h7 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        (Command.seq (Command.assign GuessBX.Vars.fst GuessBX.Expr.fstFalse)
          (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
            (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ2) rest
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
          (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ3) := by
    rw [hφ3]
    exact Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessBX.Vocab])
  have w7 := Command.step_complete h7
  have h8 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq (Command.seq Command.skip
        (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
          (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ3) rest
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
          (Command.write Loc.zBx'x GuessBX.VExpr.cntVal))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w8 := Command.step_complete h8
  have h9 : Command.RunStep Tid.guessBX rest
      (some ⟨EventLabel.wt Tid.guessBX Loc.xB ((GuessBX.Vocab I).evalV GuessBX.VExpr.xTagFirst φ3),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.seq (Command.write Loc.xB GuessBX.VExpr.xTagFirst)
          (Command.write Loc.zBx'x GuessBX.VExpr.cntVal))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ3) rest
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip
          (Command.write Loc.zBx'x GuessBX.VExpr.cntVal))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w9 := Command.step_complete h9
  have h10 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        (Command.seq Command.skip
          (Command.write Loc.zBx'x GuessBX.VExpr.cntVal))
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ3) rest
      (Command.loopSeq (Command.seq
        (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w10 := Command.step_complete h10
  have h11 : Command.RunStep Tid.guessBX rest
      (some ⟨EventLabel.wt Tid.guessBX Loc.zBx'x ((GuessBX.Vocab I).evalV GuessBX.VExpr.cntVal φ3),
        rfl⟩)
      (Command.loopSeq (Command.seq
        (Command.write Loc.zBx'x GuessBX.VExpr.cntVal)
        (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I), φ3) rest
      (Command.loopSeq (Command.seq
        Command.skip (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I),
        φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w11 := Command.step_complete h11
  have h12 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.seq
        Command.skip (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr)) (guessBXInnerLoop I),
        φ3) rest
      (Command.loopSeq (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr) (guessBXInnerLoop I),
        φ3) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w12 := Command.step_complete h12
  have h13 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq (Command.assign GuessBX.Vars.j GuessBX.Expr.jIncr) (guessBXInnerLoop I),
        φ3) rest
      (Command.loopSeq Command.skip (guessBXInnerLoop I),
        Function.update φ3 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ3)) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step, GuessBX.Vocab])
  have w13 := Command.step_complete h13
  have h14 : Command.RunStep Tid.guessBX rest none
      (Command.loopSeq Command.skip (guessBXInnerLoop I),
        Function.update φ3 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ3)) rest
      (guessBXInnerLoop I,
        Function.update φ3 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ3)) :=
    Command.step_sound _ _ _ _ _ _ _ (by simp only [Command.step])
  have w14 := Command.step_complete h14
  have hj_final : Function.update φ3 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ3)
      GuessBX.Vars.j = GuessBX.eval I GuessBX.Expr.jIncr φ := by
    have hself : Function.update φ3 GuessBX.Vars.j (GuessBX.eval I GuessBX.Expr.jIncr φ3)
        GuessBX.Vars.j = GuessBX.eval I GuessBX.Expr.jIncr φ3 := Function.update_self _ _ _
    rw [hself]
    have hjeq : GuessBX.eval I GuessBX.Expr.jIncr φ3 = GuessBX.eval I GuessBX.Expr.jIncr φ := by
      simp only [GuessBX.eval, hj_φ3]
    rw [hjeq]
  have hne_j_aux : GuessBX.Vars.j ≠ GuessBX.Vars.aux := by decide
  have hne_j_cntY : GuessBX.Vars.j ≠ GuessBX.Vars.cntY := by decide
  have hne_j_N : GuessBX.Vars.j ≠ GuessBX.Vars.N := by decide
  have hne_cntY_cnt : GuessBX.Vars.cntY ≠ GuessBX.Vars.cnt := by decide
  have hne_cntY_prev : GuessBX.Vars.cntY ≠ GuessBX.Vars.prev := by decide
  have hne_cntY_fst : GuessBX.Vars.cntY ≠ GuessBX.Vars.fst := by decide
  have hcntY_φ2 : φ2 GuessBX.Vars.cntY = φ GuessBX.Vars.cntY := by
    have h1x : φ2 GuessBX.Vars.cntY = φ1 GuessBX.Vars.cntY := Function.update_of_ne hne_cntY_cnt _ _
    have h2x : φ1 GuessBX.Vars.cntY = φ GuessBX.Vars.cntY := Function.update_of_ne hne_cntY_prev _ _
    rw [h1x, h2x]
  have hcntY_φ3 : φ3 GuessBX.Vars.cntY = φ GuessBX.Vars.cntY := by
    have h1x : φ3 GuessBX.Vars.cntY = φ2 GuessBX.Vars.cntY := Function.update_of_ne hne_cntY_fst _ _
    rw [h1x, hcntY_φ2]
  have hne_N_cnt : GuessBX.Vars.N ≠ GuessBX.Vars.cnt := by decide
  have hne_N_prev : GuessBX.Vars.N ≠ GuessBX.Vars.prev := by decide
  have hne_N_fst : GuessBX.Vars.N ≠ GuessBX.Vars.fst := by decide
  have hN_φ2 : φ2 GuessBX.Vars.N = φ GuessBX.Vars.N := by
    have h1x : φ2 GuessBX.Vars.N = φ1 GuessBX.Vars.N := Function.update_of_ne hne_N_cnt _ _
    have h2x : φ1 GuessBX.Vars.N = φ GuessBX.Vars.N := Function.update_of_ne hne_N_prev _ _
    rw [h1x, h2x]
  have hN_φ3 : φ3 GuessBX.Vars.N = φ GuessBX.Vars.N := by
    have h1x : φ3 GuessBX.Vars.N = φ2 GuessBX.Vars.N := Function.update_of_ne hne_N_fst _ _
    rw [h1x, hN_φ2]
  refine ⟨_,
    (Function.update_of_ne hne_j_fst.symm _ _).trans hfst3,
    (Function.update_of_ne hne_j_cnt.symm _ _).trans hcnt3raw,
    hj_final,
    (Function.update_of_ne hne_j_aux.symm _ _).trans haux_φ3,
    (Function.update_of_ne hne_j_cntY.symm _ _).trans hcntY_φ3,
    (Function.update_of_ne hne_j_N.symm _ _).trans hN_φ3, ?_⟩
  simp only [Command.runFuel, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    hxTagFirst3, hcntVal3]
  rfl

/-- The converse of `guessBX_outer0_step`: the first outer iteration of
`GuessBX`. Fuel `N + 31 + 14 * K`. -/
theorem guessBX_outer0_step_inv (I : PCPInstance) (K : ℕ) (v0 : Fin I.n)
    (hlen : (I.β v0).length = K + 1)
    (rest : List (GuessBX.Vals I)) (φ : (GuessBX.Vocab I).Store)
    (hfst0 : φ GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)))
    (cnt0 : Fin 4) (hcnt0 : φ GuessBX.Vars.cnt = Sum.inr (Sum.inl cnt0))
    (haux0 : φ GuessBX.Vars.aux = Sum.inl (some v0))
    (cntY0 : Fin 4) (hcntY0 : φ GuessBX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (v0' : Option (Fin I.n))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBX))
    (cf : Config (domainOf I) (GuessBX.Vocab I)) (sf : List (GuessBX.Vals I))
    (h : Command.runFuel Tid.guessBX (guessBXLoop I, φ) (Sum.inl v0' :: rest) (N + 31 + 14 * K) =
      (.stuck, σ, cf, sf)) :
    ∃ (v1 v2 : Val I) (vs : List (Val I × Val I × Val I)) (φ' : (GuessBX.Vocab I).Store)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBX)),
      vs.length = K ∧
      v2 = Val.cnt (cnt0 + 1) ∧
      (∃ j : Fin (GuessBX.maxLen I + 2), j.val = 1 ∧
        v1 = Val.xTag (Tid.guessBX, true) (GuessBX.jthLetter I (some v0) j)) ∧
      (∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨((cnt0 + 1).val + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨((cnt0 + 1).val + n + 1) % 4, by omega⟩ : Fin 4)) ∧
      (∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 2 ∧
        e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some v0) j)) ∧
      φ' GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
      φ' GuessBX.Vars.aux = Sum.inl v0' ∧
      (∃ cntF : Fin 4, φ' GuessBX.Vars.cnt = Sum.inr (Sum.inl cntF) ∧
        cntF = (⟨((cnt0 + 1).val + K) % 4, by omega⟩ : Fin 4)) ∧
      φ' GuessBX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) ∧
      σ = [ ⟨EventLabel.wt Tid.guessBX Loc.zBxy (Val.cnt (cntY0 + 1)), rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
          vs.flatMap (guessBXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx (Val.cntAux (cntY0 + 1) (some v0)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.guessBX (guessBXLoop I, φ') rest N = (.stuck, σ1, cf, sf) := by
  have hfuel0 : N + 31 + 14 * K = (N + 14 + 14 * K + 2 + 6) + 9 := by omega
  rw [hfuel0] at h
  obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
    guessBXOuterHead_step_inv I (Sum.inl v0' :: rest) φ (some v0) haux0 cntY0 hcntY0
      (N + 14 + 14 * K + 2 + 6) σ cf sf h
  have hNOf_h' : (GuessBX.NOf I φh).val = (I.β v0).length := by
    rw [hNOf_h]; simp [GuessBX.extBeta, List.length_map]
  have hNOf_hK : (GuessBX.NOf I φh).val = K + 1 := by rw [hNOf_h', hlen]
  have hfst_head : φh GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)) := by
    rw [hfst_h, hfst0]
  have hcnt_head : φh GuessBX.Vars.cnt = Sum.inr (Sum.inl cnt0) := by rw [hcnt_h, hcnt0]
  have hmaxpos := GuessBX.maxLen_pos I
  have hguard_first : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φh = true := by
    simp only [GuessBX.Vocab, GuessBX.evalB, decide_eq_true_eq, Fin.le_def]
    omega
  obtain ⟨φ1, hfst1, hcnt1, hj1, haux1, hcntY1, hN1, hstep14⟩ :=
    guessBX_innerLoop_first_step_outOfFuel I (Sum.inl v0' :: rest) φh hguard_first hfst_head
      cnt0 hcnt_head
  set C2 : Command (domainOf I) (GuessBX.Vocab I) :=
    Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
      (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
          (GuessBX.auxSetBot_nonempty I))) with hC2
  have hstep14_seq :=
    Command.runFuel_seqCongr_outOfFuel 14 (guessBXInnerLoop I) C2 φh (Sum.inl v0' :: rest)
      (guessBXInnerLoop I) φ1 _ (Sum.inl v0' :: rest) hstep14
  have hstep14_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 14 (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φh (Sum.inl v0' :: rest) (Command.seq (guessBXInnerLoop I) C2) φ1 _
      (Sum.inl v0' :: rest) hstep14_seq
  have hjOf1val : (GuessBX.jOf I φ1).val = (GuessBX.jOf I φh).val + 1 := by
    have heval : GuessBX.jOf I φ1 = GuessBX.jOf I φh + 1 := by
      simp only [GuessBX.jOf, hj1, GuessBX.eval]
    have h1val : (1 : Fin (GuessBX.maxLen I + 2)).val = 1 := by simp [Fin.val_one']
    rw [heval, Fin.val_add_eq_of_add_lt (by rw [h1val]; omega), h1val]
  have hNOf1 : (GuessBX.NOf I φ1).val = (GuessBX.NOf I φh).val := by
    simp only [GuessBX.NOf, hN1]
  have hNbound1 : (GuessBX.NOf I φ1).val ≤ GuessBX.maxLen I := by
    rw [hNOf1, hNOf_hK]
    have hextle := GuessBX.extBeta_length_le I (some v0)
    simp only [GuessBX.extBeta, List.length_map] at hextle
    omega
  have hK1 : (GuessBX.jOf I φ1).val + K = (GuessBX.NOf I φ1).val + 1 := by
    rw [hjOf1val, hjOf_h, hNOf1, hNOf_hK]; omega
  obtain ⟨vs, φ2, hvslen, hcntf, hauxf, hcntYf, hNf, hfstf, hjf, hval, hvalx, hstepChain⟩ :=
    guessBXInnerLoop_chain_outOfFuel I K (Sum.inl v0' :: rest) φ1 hK1 (cnt0 + 1) hcnt1 hfst1
      hNbound1
  have hstepChain_seq :=
    Command.runFuel_seqCongr_outOfFuel (14 * K) (guessBXInnerLoop I) C2 φ1
      (Sum.inl v0' :: rest) (guessBXInnerLoop I) φ2 _ (Sum.inl v0' :: rest) hstepChain
  have hstepChain_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel (14 * K) (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φ1 (Sum.inl v0' :: rest) (Command.seq (guessBXInnerLoop I) C2) φ2 _
      (Sum.inl v0' :: rest) hstepChain_seq
  have hcomb14K :=
    Command.runFuel_outOfFuel_append 14
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hstep14_loop (14 * K) _ _ _ _ hstepChain_loop
  have hNOf2 : (GuessBX.NOf I φ2).val = (GuessBX.NOf I φ1).val := by
    simp only [GuessBX.NOf, hNf]
  have hguardFalse2 : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ2 = false := by
    simp only [GuessBX.Vocab, GuessBX.evalB, decide_eq_false_iff_not, Fin.le_def]
    omega
  have hexit := guessBXOuterExit_step_outOfFuel I (Sum.inl v0' :: rest) φ2 C2 hguardFalse2
  have hexit_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φ2 (Sum.inl v0' :: rest) C2 φ2 [] (Sum.inl v0' :: rest) hexit
  have hcombAll :=
    Command.runFuel_outOfFuel_append (14 + 14 * K)
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hcomb14K 2 _ _ _ _ hexit_loop
  have hfuel1 : N + 14 + 14 * K + 2 + 6 = (14 + 14 * K + 2) + (N + 6) := by omega
  rw [hfuel1] at runH
  obtain ⟨σ1b, runTailPre, hσ1eq⟩ :=
    Command.runFuel_outOfFuel_split (14 + 14 * K + 2)
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hcombAll (N + 6) _ σ1a cf sf runH
  have hauxOf_φ2 : φ2 GuessBX.Vars.aux = Sum.inl (some v0) := by
    rw [hauxf, haux1, haux_h, haux0]
  have hcntY_φ2 : φ2 GuessBX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
    rw [hcntYf, hcntY1, hcntY_h]
  obtain ⟨σ1c, hσ1beq, runFinal⟩ :=
    guessBXOuterTail_continue_step_inv I v0' rest φ2 (cntY0 + 1) hcntY_φ2 v0 hauxOf_φ2
      (N + 6 - 6) σ1b cf sf (by rw [show N + 6 - 6 = N from by omega]; exact runTailPre)
  refine ⟨Val.xTag (Tid.guessBX, true)
      (GuessBX.jthLetter I (GuessBX.auxOf I φh) (GuessBX.jOf I φh)),
    Val.cnt (cnt0 + 1), vs, Function.update φ2 GuessBX.Vars.aux (Sum.inl v0'), σ1c,
    hvslen, rfl, ⟨GuessBX.jOf I φh, hjOf_h, ?_⟩, hval, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · rw [show GuessBX.auxOf I φh = some v0 from by simp only [GuessBX.auxOf, haux_h, haux0]]
  · intro n hn
    have hn' : n < K := by rw [← hvslen]; exact hn
    obtain ⟨e, j, he, hjval, he1⟩ := hvalx n hn'
    refine ⟨e, j, he, ?_, ?_⟩
    · rw [hjval, hjOf1val, hjOf_h]; omega
    · rw [he1]
      congr 1
      simp only [GuessBX.auxOf, haux1, haux_h, haux0]
  · have hne_aux_fst : GuessBX.Vars.aux ≠ GuessBX.Vars.fst := by decide
    exact (Function.update_of_ne hne_aux_fst.symm _ _).trans hfstf
  · exact ⟨(⟨((cnt0 + 1).val + K) % 4, by omega⟩ : Fin 4),
      by
        have hne_aux_cnt : GuessBX.Vars.aux ≠ GuessBX.Vars.cnt := by decide
        exact (Function.update_of_ne hne_aux_cnt.symm _ _).trans hcntf,
      rfl⟩
  · have hne_aux_cntY : GuessBX.Vars.aux ≠ GuessBX.Vars.cntY := by decide
    exact (Function.update_of_ne hne_aux_cntY.symm _ _).trans hcntY_φ2
  · rw [hσeq, hσ1eq, hσ1beq]
    simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]
  · exact runFinal

/-- The converse of `guessBX_outerRest_continue_step`. Fuel
`N + 31 + 14 * K`. -/
theorem guessBX_outerRest_continue_step_inv (I : PCPInstance) (K : ℕ) (w : Fin I.n)
    (hlen : (I.β w).length = K + 1)
    (rest : List (GuessBX.Vals I)) (φ : (GuessBX.Vocab I).Store)
    (hfst : φ GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)))
    (cnt0 : Fin 4) (hcnt0 : φ GuessBX.Vars.cnt = Sum.inr (Sum.inl cnt0))
    (haux : φ GuessBX.Vars.aux = Sum.inl (some w))
    (cntY0 : Fin 4) (hcntY0 : φ GuessBX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (v0' : Option (Fin I.n))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBX))
    (cf : Config (domainOf I) (GuessBX.Vocab I)) (sf : List (GuessBX.Vals I))
    (h : Command.runFuel Tid.guessBX (guessBXLoop I, φ) (Sum.inl v0' :: rest) (N + 31 + 14 * K) =
      (.stuck, σ, cf, sf)) :
    ∃ (vs : List (Val I × Val I × Val I)) (φ' : (GuessBX.Vocab I).Store)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBX)),
      vs.length = K + 1 ∧
      φ' GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) ∧
      φ' GuessBX.Vars.aux = Sum.inl v0' ∧
      (∃ cntF : Fin 4, φ' GuessBX.Vars.cnt = Sum.inr (Sum.inl cntF) ∧
        cntF = (⟨(cnt0.val + (K + 1)) % 4, by omega⟩ : Fin 4)) ∧
      φ' GuessBX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) ∧
      (∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(cnt0.val + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(cnt0.val + n + 1) % 4, by omega⟩ : Fin 4)) ∧
      (∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some w) j)) ∧
      σ = [ ⟨EventLabel.wt Tid.guessBX Loc.zBxy (Val.cnt (cntY0 + 1)), rfl⟩ ] ++
          vs.flatMap (guessBXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx (Val.cntAux (cntY0 + 1) (some w)), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.guessBX (guessBXLoop I, φ') rest N = (.stuck, σ1, cf, sf) := by
  have hfuel0 : N + 31 + 14 * K = (N + 14 * (K + 1) + 2 + 6) + 9 := by omega
  rw [hfuel0] at h
  obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
    guessBXOuterHead_step_inv I (Sum.inl v0' :: rest) φ (some w) haux cntY0 hcntY0
      (N + 14 * (K + 1) + 2 + 6) σ cf sf h
  have hNOf_h' : (GuessBX.NOf I φh).val = (I.β w).length := by
    rw [hNOf_h]; simp [GuessBX.extBeta, List.length_map]
  have hNOf_hK : (GuessBX.NOf I φh).val = K + 1 := by rw [hNOf_h', hlen]
  have hfst_head : φh GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    rw [hfst_h, hfst]
  have hcnt_head : φh GuessBX.Vars.cnt = Sum.inr (Sum.inl cnt0) := by rw [hcnt_h, hcnt0]
  have hmaxpos := GuessBX.maxLen_pos I
  have hNbound_head : (GuessBX.NOf I φh).val ≤ GuessBX.maxLen I := by
    rw [hNOf_hK]
    have hextle := GuessBX.extBeta_length_le I (some w)
    simp only [GuessBX.extBeta, List.length_map] at hextle
    omega
  have hK_head : (GuessBX.jOf I φh).val + (K + 1) = (GuessBX.NOf I φh).val + 1 := by
    rw [hjOf_h, hNOf_hK]; omega
  set C2 : Command (domainOf I) (GuessBX.Vocab I) :=
    Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
      (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
          (GuessBX.auxSetBot_nonempty I))) with hC2
  obtain ⟨vs, φ2, hvslen, hcntf, hauxf, hcntYf, hNf, hfstf, hjf, hval, hvalx, hstepChain⟩ :=
    guessBXInnerLoop_chain_outOfFuel I (K + 1) (Sum.inl v0' :: rest) φh hK_head cnt0 hcnt_head
      hfst_head hNbound_head
  have hstepChain_seq :=
    Command.runFuel_seqCongr_outOfFuel (14 * (K + 1)) (guessBXInnerLoop I) C2 φh
      (Sum.inl v0' :: rest) (guessBXInnerLoop I) φ2 _ (Sum.inl v0' :: rest) hstepChain
  have hstepChain_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel (14 * (K + 1)) (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φh (Sum.inl v0' :: rest) (Command.seq (guessBXInnerLoop I) C2) φ2 _
      (Sum.inl v0' :: rest) hstepChain_seq
  have hNOf2 : (GuessBX.NOf I φ2).val = (GuessBX.NOf I φh).val := by
    simp only [GuessBX.NOf, hNf]
  have hguardFalse2 : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ2 = false := by
    simp only [GuessBX.Vocab, GuessBX.evalB, decide_eq_false_iff_not, Fin.le_def]
    omega
  have hexit := guessBXOuterExit_step_outOfFuel I (Sum.inl v0' :: rest) φ2 C2 hguardFalse2
  have hexit_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φ2 (Sum.inl v0' :: rest) C2 φ2 [] (Sum.inl v0' :: rest) hexit
  have hcombAll :=
    Command.runFuel_outOfFuel_append (14 * (K + 1))
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hstepChain_loop 2 _ _ _ _ hexit_loop
  have hfuel1 : N + 14 * (K + 1) + 2 + 6 = (14 * (K + 1) + 2) + (N + 6) := by omega
  rw [hfuel1] at runH
  obtain ⟨σ1b, runTailPre, hσ1eq⟩ :=
    Command.runFuel_outOfFuel_split (14 * (K + 1) + 2)
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh)
      (Sum.inl v0' :: rest) _ _ _ hcombAll (N + 6) _ σ1a cf sf runH
  have hauxOf_φ2 : φ2 GuessBX.Vars.aux = Sum.inl (some w) := by
    rw [hauxf, haux_h, haux]
  have hcntY_φ2 : φ2 GuessBX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
    rw [hcntYf, hcntY_h]
  obtain ⟨σ1c, hσ1beq, runFinal⟩ :=
    guessBXOuterTail_continue_step_inv I v0' rest φ2 (cntY0 + 1) hcntY_φ2 w hauxOf_φ2
      N σ1b cf sf runTailPre
  refine ⟨vs, Function.update φ2 GuessBX.Vars.aux (Sum.inl v0'), σ1c, hvslen, ?_, rfl,
    ⟨(⟨(cnt0.val + (K + 1)) % 4, by omega⟩ : Fin 4), ?_, rfl⟩, ?_, hval, ?_, ?_, runFinal⟩
  · have hne_aux_fst : GuessBX.Vars.aux ≠ GuessBX.Vars.fst := by decide
    exact (Function.update_of_ne hne_aux_fst.symm _ _).trans hfstf
  · have hne_aux_cnt : GuessBX.Vars.aux ≠ GuessBX.Vars.cnt := by decide
    exact (Function.update_of_ne hne_aux_cnt.symm _ _).trans hcntf
  · have hne_aux_cntY : GuessBX.Vars.aux ≠ GuessBX.Vars.cntY := by decide
    exact (Function.update_of_ne hne_aux_cntY.symm _ _).trans hcntY_φ2
  · intro n hn
    have hn' : n < K + 1 := by rw [← hvslen]; exact hn
    obtain ⟨e, j, he, hjval, he1⟩ := hvalx n hn'
    refine ⟨e, j, he, ?_, ?_⟩
    · rw [hjval, hjOf_h]; omega
    · rw [he1]; congr 1; simp only [GuessBX.auxOf, haux_h, haux]
  · rw [hσeq, hσ1eq, hσ1beq]
    simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]

/-- The converse of `guessBX_outerRest_break_step` (`extBeta I none =
[none]`). Fuel `N + 30`. -/
theorem guessBX_outerRest_break_step_inv (I : PCPInstance)
    (rest : List (GuessBX.Vals I)) (φ : (GuessBX.Vocab I).Store)
    (hfst : φ GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)))
    (cnt0 : Fin 4) (hcnt0 : φ GuessBX.Vars.cnt = Sum.inr (Sum.inl cnt0))
    (haux : φ GuessBX.Vars.aux = Sum.inl none)
    (cntY0 : Fin 4) (hcntY0 : φ GuessBX.Vars.cntY = Sum.inr (Sum.inl cntY0))
    (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBX))
    (cf : Config (domainOf I) (GuessBX.Vocab I)) (sf : List (GuessBX.Vals I))
    (h : Command.runFuel Tid.guessBX (guessBXLoop I, φ) rest (N + 30) = (.stuck, σ, cf, sf)) :
    ∃ (vs : List (Val I × Val I × Val I)) (φ' : (GuessBX.Vocab I).Store)
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBX)),
      vs.length = 1 ∧
      (∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(cnt0.val + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(cnt0.val + n + 1) % 4, by omega⟩ : Fin 4)) ∧
      (∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I none j)) ∧
      σ = [ ⟨EventLabel.wt Tid.guessBX Loc.zBxy (Val.cnt (cntY0 + 1)), rfl⟩ ] ++
          vs.flatMap (guessBXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx (Val.cntAux (cntY0 + 1) none), rfl⟩ ] ++ σ1 ∧
      Command.runFuel Tid.guessBX (Command.skip, φ') rest N = (.stuck, σ1, cf, sf) := by
  have hfuel0 : N + 30 = (N + 14 + 2 + 5) + 9 := by omega
  rw [hfuel0] at h
  obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
    guessBXOuterHead_step_inv I rest φ none haux cntY0 hcntY0 (N + 14 + 2 + 5) σ cf sf h
  have hNOf_hK : (GuessBX.NOf I φh).val = 1 := by
    rw [hNOf_h]; simp [GuessBX.extBeta]
  have hfst_head : φh GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
    rw [hfst_h, hfst]
  have hcnt_head : φh GuessBX.Vars.cnt = Sum.inr (Sum.inl cnt0) := by rw [hcnt_h, hcnt0]
  have hmaxpos := GuessBX.maxLen_pos I
  have hNbound_head : (GuessBX.NOf I φh).val ≤ GuessBX.maxLen I := by rw [hNOf_hK]; omega
  have hK_head : (GuessBX.jOf I φh).val + 1 = (GuessBX.NOf I φh).val + 1 := by
    rw [hjOf_h, hNOf_hK]
  set C2 : Command (domainOf I) (GuessBX.Vocab I) :=
    Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
      (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
          (GuessBX.auxSetBot_nonempty I))) with hC2
  obtain ⟨vs, φ2, hvslen, hcntf, hauxf, hcntYf, hNf, hfstf, hjf, hval, hvalx, hstepChain⟩ :=
    guessBXInnerLoop_chain_outOfFuel I 1 rest φh hK_head cnt0 hcnt_head hfst_head hNbound_head
  have hstepChain_seq :=
    Command.runFuel_seqCongr_outOfFuel 14 (guessBXInnerLoop I) C2 φh rest
      (guessBXInnerLoop I) φ2 _ rest hstepChain
  have hstepChain_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 14 (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φh rest (Command.seq (guessBXInnerLoop I) C2) φ2 _ rest hstepChain_seq
  have hNOf2 : (GuessBX.NOf I φ2).val = (GuessBX.NOf I φh).val := by
    simp only [GuessBX.NOf, hNf]
  have hguardFalse2 : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ2 = false := by
    simp only [GuessBX.Vocab, GuessBX.evalB, decide_eq_false_iff_not, Fin.le_def]
    omega
  have hexit := guessBXOuterExit_step_outOfFuel I rest φ2 C2 hguardFalse2
  have hexit_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φ2 rest C2 φ2 [] rest hexit
  have hcombAll :=
    Command.runFuel_outOfFuel_append 14
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh)
      rest _ _ _ hstepChain_loop 2 _ _ _ _ hexit_loop
  have hfuel1 : N + 14 + 2 + 5 = (14 + 2) + (N + 5) := by omega
  rw [hfuel1] at runH
  obtain ⟨σ1b, runTailPre, hσ1eq⟩ :=
    Command.runFuel_outOfFuel_split (14 + 2)
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh)
      rest _ _ _ hcombAll (N + 5) _ σ1a cf sf runH
  have hauxOf_φ2 : φ2 GuessBX.Vars.aux = Sum.inl none := by
    rw [hauxf, haux_h, haux]
  have hcntY_φ2 : φ2 GuessBX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
    rw [hcntYf, hcntY_h]
  obtain ⟨σ1c, hσ1beq, runFinal⟩ :=
    guessBXOuterTail_break_step_inv I rest φ2 (cntY0 + 1) hcntY_φ2 hauxOf_φ2 N σ1b cf sf runTailPre
  refine ⟨vs, φ2, σ1c, hvslen, hval, ?_, ?_, runFinal⟩
  · intro n hn
    have hn' : n < 1 := by rw [← hvslen]; exact hn
    obtain ⟨e, j, he, hjval, he1⟩ := hvalx n hn'
    refine ⟨e, j, he, ?_, ?_⟩
    · rw [hjval, hjOf_h]; omega
    · rw [he1]; congr 1; simp only [GuessBX.auxOf, haux_h, haux]
  · rw [hσeq, hσ1eq, hσ1beq]
    simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]

/-- The converse of `guessBXChain_shape`, as `guessAX_chain_shape_inv`. -/
theorem guessBX_chain_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (GuessBX.Vals I)), s.length = n →
      ∀ (K0 : ℕ) (w0 : Fin I.n) (hlen0 : (I.β w0).length = K0 + 1)
        (φ : (GuessBX.Vocab I).Store)
        (hfst : φ GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)))
        (cnt0 : Fin 4) (hcnt0 : φ GuessBX.Vars.cnt = Sum.inr (Sum.inl cnt0))
        (haux0 : φ GuessBX.Vars.aux = Sum.inl (some w0))
        (cntY0 : Fin 4) (hcntY0 : φ GuessBX.Vars.cntY = Sum.inr (Sum.inl cntY0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBX))
        (φ' : (GuessBX.Vocab I).Store),
        Command.runFuel Tid.guessBX (guessBXLoop I, φ) s N =
          (.stuck, σ, (Command.skip, φ'), []) →
        ∃ (js : List (Fin I.n))
          (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))),
          s = js.map (fun idx => (Sum.inl (some idx) : GuessBX.Vals I)) ++ [Sum.inl none] ∧
          outerRest.length = js.length + 2 ∧
          (∀ m, m < js.length + 1 → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
            (K0 :: guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1) ∧
          (∃ b vs, outerRest[js.length + 1]? = some (b, vs) ∧ vs.length = 1) ∧
          (∀ m, m < js.length + 2 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
            ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
              e.2.2 = Val.cnt (⟨(cnt0.val + ksPrefix (K0 :: guessBXJsToKs I js) m + n) % 4,
                by omega⟩ : Fin 4) ∧
              e.2.1 = Val.cnt (⟨(cnt0.val + ksPrefix (K0 :: guessBXJsToKs I js) m + n + 1) % 4,
                by omega⟩ : Fin 4)) ∧
          (∀ m, m < js.length + 2 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
            b.1 = Val.cnt (⟨(cntY0.val + 1 + m) % 4, by omega⟩ : Fin 4) ∧
            (m = 0 → b.2 = Val.cntAux (⟨(cntY0.val + 1 + m) % 4, by omega⟩ : Fin 4) (some w0)) ∧
            (1 ≤ m → m ≤ js.length → ∃ w, js[m - 1]? = some w ∧
              b.2 = Val.cntAux (⟨(cntY0.val + 1 + m) % 4, by omega⟩ : Fin 4) (some w)) ∧
            (m = js.length + 1 →
              b.2 = Val.cntAux (⟨(cntY0.val + 1 + m) % 4, by omega⟩ : Fin 4) none)) ∧
          (∀ m, m < js.length + 2 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
            (m = 0 → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
              e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some w0) j)) ∧
            (1 ≤ m → m ≤ js.length → ∃ w, js[m - 1]? = some w ∧
              ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
                e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some w) j)) ∧
            (m = js.length + 1 → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
              e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I none j))) ∧
          σ = outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen K0 w0 hlen0 φ hfst cnt0 hcnt0 haux0 cntY0 hcntY0 N σ φ' h
    -- Run up to the `ndetAssign` draw, with `s` untouched, to determine the
    -- head of `s`.
    have hpre : Command.runFuel Tid.guessBX (guessBXLoop I, φ) s
        (N + (9 + 14 * (K0 + 1) + 2 + 4)) = (.stuck, σ, (Command.skip, φ'), []) :=
      Command.runFuel_stuck_stable h (9 + 14 * (K0 + 1) + 2 + 4)
    have hpad : N + (9 + 14 * (K0 + 1) + 2 + 4) = (N + 14 * (K0 + 1) + 2 + 4) + 9 := by omega
    rw [hpad] at hpre
    obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
      guessBXOuterHead_step_inv I s φ (some w0) haux0 cntY0 hcntY0
        (N + 14 * (K0 + 1) + 2 + 4) σ (Command.skip, φ') [] hpre
    have hNOf_h' : (GuessBX.NOf I φh).val = (I.β w0).length := by
      rw [hNOf_h]; simp [GuessBX.extBeta, List.length_map]
    have hNOf_hK : (GuessBX.NOf I φh).val = K0 + 1 := by rw [hNOf_h', hlen0]
    have hfst_head : φh GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr false)) := by
      rw [hfst_h, hfst]
    have hcnt_head : φh GuessBX.Vars.cnt = Sum.inr (Sum.inl cnt0) := by rw [hcnt_h, hcnt0]
    have hmaxpos := GuessBX.maxLen_pos I
    have hNbound_head : (GuessBX.NOf I φh).val ≤ GuessBX.maxLen I := by
      rw [hNOf_hK]
      have hextle := GuessBX.extBeta_length_le I (some w0)
      simp only [GuessBX.extBeta, List.length_map] at hextle
      omega
    have hK_head : (GuessBX.jOf I φh).val + (K0 + 1) = (GuessBX.NOf I φh).val + 1 := by
      rw [hjOf_h, hNOf_hK]; omega
    set C2 : Command (domainOf I) (GuessBX.Vocab I) :=
      Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
        (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
            (GuessBX.auxSetBot_nonempty I))) with hC2
    obtain ⟨vsc, φ2, hvslenc, hcntfc, hauxfc, hcntYfc, hNfc, hfstfc, hjfc, hvalc, hvalxc,
      hstepChain⟩ :=
      guessBXInnerLoop_chain_outOfFuel I (K0 + 1) s φh hK_head cnt0 hcnt_head hfst_head
        hNbound_head
    have hstepChain_seq :=
      Command.runFuel_seqCongr_outOfFuel (14 * (K0 + 1)) (guessBXInnerLoop I) C2 φh s
        (guessBXInnerLoop I) φ2 _ s hstepChain
    have hstepChain_loop :=
      Command.runFuel_loopSeqCongr_outOfFuel (14 * (K0 + 1)) (Command.seq (guessBXInnerLoop I) C2)
        (guessBXLoop I) φh s (Command.seq (guessBXInnerLoop I) C2) φ2 _ s hstepChain_seq
    have hNOf2 : (GuessBX.NOf I φ2).val = (GuessBX.NOf I φh).val := by
      simp only [GuessBX.NOf, hNfc]
    have hguardFalse2 : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ2 = false := by
      simp only [GuessBX.Vocab, GuessBX.evalB, decide_eq_false_iff_not, Fin.le_def]
      omega
    have hexit := guessBXOuterExit_step_outOfFuel I s φ2 C2 hguardFalse2
    have hexit_loop :=
      Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessBXInnerLoop I) C2)
        (guessBXLoop I) φ2 s C2 φ2 [] s hexit
    have hcomb1 :=
      Command.runFuel_outOfFuel_append (14 * (K0 + 1))
        (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh) s _ _ _
        hstepChain_loop 2 _ _ _ _ hexit_loop
    have hauxOf_φ2 : φ2 GuessBX.Vars.aux = Sum.inl (some w0) := by
      rw [hauxfc, haux_h, haux0]
    have hcntY_φ2 : φ2 GuessBX.Vars.cntY = Sum.inr (Sum.inl (cntY0 + 1)) := by
      rw [hcntYfc, hcntY_h]
    have hpref := guessBXOuterTail_continue_pre_step_outOfFuel I s φ2 (cntY0 + 1) hcntY_φ2 w0
      hauxOf_φ2
    have hcombAll :=
      Command.runFuel_outOfFuel_append (14 * (K0 + 1) + 2)
        (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh) s _ _ _
        hcomb1 4 _ _ _ _ hpref
    have hfuel1 : N + 14 * (K0 + 1) + 2 + 4 = (14 * (K0 + 1) + 2 + 4) + N := by omega
    rw [hfuel1] at runH
    obtain ⟨σ1b, hpost, hσ1eq⟩ :=
      Command.runFuel_outOfFuel_split (14 * (K0 + 1) + 2 + 4)
        (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh) s _ _ _
        hcombAll N _ σ1a (Command.skip, φ') [] runH
    -- The head of `s`: empty or ill-typed is impossible, since the run would
    -- be stuck at the draw rather than at `(Command.skip, φ')`.
    rcases s with _ | ⟨c0, rest0⟩
    · exfalso
      cases N with
      | zero =>
          simp only [Command.runFuel] at hpost
          injection hpost with h1'
          injection h1'
      | succ N' =>
          have hstep : Command.step Tid.guessBX
              (Command.loopSeq (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                (GuessBX.auxSetBot_nonempty I)) (guessBXLoop I)) φ2 [] = none := by
            simp only [Command.step, Command.step_ndetAssign_nil]
          simp only [Command.runFuel, hstep] at hpost
          injection hpost with h1' h2'
          injection h2' with h3' h4'
          injection h4' with h5' h6'
          simp only [Prod.mk.injEq] at h5'
          exact absurd h5'.1 (by rintro ⟨⟩)
    · rcases c0 with v0' | c0'
      · -- Sum.inl v0': proceed via the padded original hypothesis.
        have h2 : Command.runFuel Tid.guessBX (guessBXLoop I, φ) (Sum.inl v0' :: rest0)
            (N + 31 + 14 * K0) = (.stuck, σ, (Command.skip, φ'), []) := by
          have h2' := Command.runFuel_stuck_stable h (31 + 14 * K0)
          have hpad2 : N + (31 + 14 * K0) = N + 31 + 14 * K0 := by omega
          rwa [hpad2] at h2'
        obtain ⟨vs1, φ1, σ1x, hlen1, hfst1, haux1, ⟨cntF, hcnt1, hcntFeq1⟩, hcntY1, hval1,
          hvalxA1, hσeq1, hrun1⟩ :=
          guessBX_outerRest_continue_step_inv I K0 w0 hlen0 rest0 φ hfst cnt0 hcnt0 haux0 cntY0
            hcntY0 v0' N σ (Command.skip, φ') [] h2
        cases v0' with
        | none =>
            have hrun1' := Command.runFuel_stuck_stable hrun1 30
            obtain ⟨vs2, φ3, σ2, hlen2, hval2, hvalxA2, hσ2eq, hrun2⟩ :=
              guessBX_outerRest_break_step_inv I rest0 φ1 hfst1 cntF hcnt1 haux1 (cntY0 + 1)
                hcntY1 N σ1x (Command.skip, φ') [] hrun1'
            have hrest0nil : rest0 = [] ∧ σ2 = [] ∧ φ3 = φ' := by
              cases N with
              | zero =>
                  exfalso
                  simp only [Command.runFuel] at hrun2
                  injection hrun2 with hz1
                  injection hz1
              | succ N'' =>
                  have hskipstep : Command.step Tid.guessBX Command.skip φ3 rest0 = none := rfl
                  simp only [Command.runFuel, hskipstep] at hrun2
                  injection hrun2 with e1 e2
                  injection e2 with e3 e4
                  injection e4 with e5 e6
                  injection e5 with e7 e8
                  exact ⟨e6, e3.symm, e8⟩
            obtain ⟨hrest0nil', hσ2nil, hφ3eq⟩ := hrest0nil
            subst hrest0nil'
            refine ⟨[], [((Val.cnt (cntY0 + 1), Val.cntAux (cntY0 + 1) (some w0)), vs1),
                ((Val.cnt (cntY0 + 1 + 1), Val.cntAux (cntY0 + 1 + 1) none), vs2)],
              rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro m hm
              simp only [List.length_nil] at hm
              have hm0 : m = 0 := by omega
              subst hm0
              exact ⟨_, vs1, K0, rfl, rfl, hlen1⟩
            · exact ⟨_, vs2, rfl, hlen2⟩
            · have hcntFeq1' : cntF.val = (cnt0.val + (K0 + 1)) % 4 := by rw [hcntFeq1]
              have hks0 : ksPrefix (K0 :: guessBXJsToKs I ([] : List (Fin I.n))) 0 = 0 := rfl
              have hks1 : ksPrefix (K0 :: guessBXJsToKs I ([] : List (Fin I.n))) 1 = K0 + 1 := by
                rw [show (1 : ℕ) = 0 + 1 from rfl, ksPrefix_cons]
                simp [ksPrefix]
              intro m hm
              have hm2 : m = 0 ∨ m = 1 := by simp only [List.length_nil] at hm; omega
              rcases hm2 with rfl | rfl
              · refine ⟨_, vs1, rfl, ?_⟩
                intro n hn
                obtain ⟨e, he, he22, he21⟩ := hval1 n hn
                refine ⟨e, he, ?_, ?_⟩
                · rw [he22]; simp only [Val.cnt.injEq, Fin.ext_iff]; omega
                · rw [he21]; simp only [Val.cnt.injEq, Fin.ext_iff]; omega
              · refine ⟨_, vs2, rfl, ?_⟩
                intro n hn
                obtain ⟨e, he, he22, he21⟩ := hval2 n hn
                refine ⟨e, he, ?_, ?_⟩
                · rw [he22]; simp only [Val.cnt.injEq, Fin.ext_iff]; omega
                · rw [he21]; simp only [Val.cnt.injEq, Fin.ext_iff]; omega
            · intro m hm
              simp only [List.length_nil] at hm
              have hm2 : m = 0 ∨ m = 1 := by omega
              rcases hm2 with rfl | rfl
              · refine ⟨_, vs1, rfl, ?_, ?_, ?_, ?_⟩
                · rfl
                · intro _; rfl
                · omega
                · omega
              · refine ⟨_, vs2, rfl, ?_, ?_, ?_, ?_⟩
                · dsimp only; first | rfl | (congr 1; apply Fin.ext; simp [Fin.add_def])
                · omega
                · intro _ hmle; simp only [List.length_nil] at hmle; omega
                · intro _; dsimp only; first | rfl | (congr 1; apply Fin.ext; simp [Fin.add_def])
            · intro m hm
              simp only [List.length_nil] at hm
              have hm2 : m = 0 ∨ m = 1 := by omega
              rcases hm2 with rfl | rfl
              · exact ⟨_, vs1, rfl, fun _ => hvalxA1, by omega, by omega⟩
              · refine ⟨_, vs2, rfl, ?_, ?_, ?_⟩
                · omega
                · intro _ hmle; simp only [List.length_nil] at hmle; omega
                · intro _; exact hvalxA2
            · rw [hσeq1, hσ2eq, hσ2nil]
              simp only [guessBXOuterBlockElems, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc, List.nil_append, List.cons_append]
        | some j0 =>
            have hne : I.β j0 ≠ [] := I.hβ j0
            have hpos : 0 < (I.β j0).length := List.length_pos_of_ne_nil hne
            have hlen0' : (I.β j0).length = (I.β j0).length - 1 + 1 := by omega
            have hrest0lt : rest0.length < n := by
              have heq : (Sum.inl (some j0) :: rest0).length = n := hslen
              simp only [List.length_cons] at heq
              omega
            obtain ⟨js, outerRest, hseq2, hlen2, houterIH, houterLastIH, hvalIH, hbIH, hbxAIH,
              hσeqIH⟩ :=
              ih rest0.length hrest0lt rest0 rfl ((I.β j0).length - 1) j0 hlen0' φ1 hfst1 cntF
                hcnt1 haux1 (cntY0 + 1) hcntY1 N σ1x φ' hrun1
            have hcntFeq1' : cntF.val = (cnt0.val + (K0 + 1)) % 4 := by rw [hcntFeq1]
            refine ⟨j0 :: js,
              ((Val.cnt (cntY0 + 1), Val.cntAux (cntY0 + 1) (some w0)), vs1) :: outerRest,
              ?_, by simp [hlen2], ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [hseq2]; simp only [List.map_cons, List.cons_append]
            · intro m hm
              cases m with
              | zero => exact ⟨_, vs1, K0, rfl, rfl, hlen1⟩
              | succ m =>
                  simp only [List.length_cons] at hm
                  have hm' : m < js.length + 1 := by omega
                  obtain ⟨b, vs, km, hbv, hksm, hlenvs⟩ := houterIH m hm'
                  refine ⟨b, vs, km, by simpa using hbv, ?_, hlenvs⟩
                  change (guessBXJsToKs I (j0 :: js))[m]? = some km
                  rw [show guessBXJsToKs I (j0 :: js)
                      = ((I.β j0).length - 1) :: guessBXJsToKs I js from rfl]
                  exact hksm
            · obtain ⟨b, vs, hbv, hlenvs⟩ := houterLastIH
              exact ⟨b, vs, by simpa using hbv, hlenvs⟩
            · intro m hm
              cases m with
              | zero =>
                refine ⟨_, vs1, rfl, ?_⟩
                intro n hn
                obtain ⟨e, he, he22, he21⟩ := hval1 n hn
                refine ⟨e, he, ?_, ?_⟩
                · rw [he22]; congr 1
                · rw [he21]; congr 1
              | succ m =>
                simp only [List.length_cons] at hm
                have hm' : m < js.length + 2 := by omega
                obtain ⟨b, vs, hbv, hval'⟩ := hvalIH m hm'
                refine ⟨b, vs, by simpa using hbv, ?_⟩
                intro n hn
                obtain ⟨e, he, he22, he21⟩ := hval' n hn
                have hks : ksPrefix (K0 :: guessBXJsToKs I (j0 :: js)) (m + 1)
                    = (K0 + 1) + ksPrefix (((I.β j0).length - 1) :: guessBXJsToKs I js) m := by
                  rw [show guessBXJsToKs I (j0 :: js)
                      = ((I.β j0).length - 1) :: guessBXJsToKs I js from rfl]
                  exact ksPrefix_cons K0 (((I.β j0).length - 1) :: guessBXJsToKs I js) m
                refine ⟨e, he, ?_, ?_⟩
                · rw [he22]
                  congr 1
                  apply Fin.ext
                  show (cntF.val + ksPrefix (((I.β j0).length - 1) :: guessBXJsToKs I js) m + n)
                      % 4 =
                    (cnt0.val + ksPrefix (K0 :: guessBXJsToKs I (j0 :: js)) (m + 1) + n) % 4
                  rw [hks]; omega
                · rw [he21]
                  congr 1
                  apply Fin.ext
                  show (cntF.val + ksPrefix (((I.β j0).length - 1) :: guessBXJsToKs I js) m + n
                      + 1) % 4 =
                    (cnt0.val + ksPrefix (K0 :: guessBXJsToKs I (j0 :: js)) (m + 1) + n + 1) % 4
                  rw [hks]; omega
            · intro m hm
              cases m with
              | zero =>
                refine ⟨_, vs1, rfl, ?_, ?_, ?_, ?_⟩
                · rfl
                · intro _; rfl
                · intro h; omega
                · intro heq; simp only [List.length_cons] at heq; omega
              | succ m =>
                simp only [List.length_cons] at hm
                have hm' : m < js.length + 2 := by omega
                obtain ⟨b, vs, hbv, hb1, hb2z, hb2m, hb2last⟩ := hbIH m hm'
                refine ⟨b, vs, by simpa using hbv, ?_, ?_, ?_, ?_⟩
                · rw [hb1]; congr 1; simp [Fin.add_def]; omega
                · intro h; omega
                · intro _ hmle
                  have hmle' : m + 1 ≤ js.length + 1 := by simpa [List.length_cons] using hmle
                  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
                  · subst hm0
                    have hb2z' := hb2z rfl
                    refine ⟨j0, rfl, ?_⟩
                    rw [hb2z']; congr 1; apply Fin.ext; simp [Fin.add_def]
                  · have hm'le : m ≤ js.length := by omega
                    obtain ⟨w, hw, hb2⟩ := hb2m (by omega) hm'le
                    refine ⟨w, ?_, ?_⟩
                    · show (j0 :: js)[m]? = some w
                      rw [show m = (m - 1) + 1 from by omega, List.getElem?_cons_succ]
                      exact hw
                    · rw [hb2]; congr 1; simp [Fin.add_def]; omega
                · intro heq
                  simp only [List.length_cons] at heq
                  have hm'eq : m = js.length + 1 := by omega
                  have hlast := hb2last hm'eq
                  rw [hlast]; congr 1; apply Fin.ext; simp [Fin.add_def]; omega
            · intro m hm
              cases m with
              | zero => exact ⟨_, vs1, rfl, fun _ => hvalxA1, by omega, by omega⟩
              | succ m =>
                simp only [List.length_cons] at hm
                have hm' : m < js.length + 2 := by omega
                obtain ⟨b, vs, hbv, hbxA0, hbxAm, hbxAlast⟩ := hbxAIH m hm'
                refine ⟨b, vs, by simpa using hbv, ?_, ?_, ?_⟩
                · intro h; omega
                · intro _ hmle
                  have hmle' : m + 1 ≤ js.length + 1 := by simpa [List.length_cons] using hmle
                  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
                  · subst hm0
                    refine ⟨j0, rfl, ?_⟩
                    exact hbxA0 rfl
                  · have hm'le : m ≤ js.length := by omega
                    obtain ⟨w, hw, hbxA⟩ := hbxAm (by omega) hm'le
                    refine ⟨w, ?_, hbxA⟩
                    show (j0 :: js)[m]? = some w
                    rw [show m = (m - 1) + 1 from by omega, List.getElem?_cons_succ]
                    exact hw
                · intro heq
                  simp only [List.length_cons] at heq
                  have hm'eq : m = js.length + 1 := by omega
                  exact hbxAlast hm'eq
            · rw [hσeq1, hσeqIH]
              simp only [guessBXOuterBlockElems, List.flatMap_cons, List.append_assoc,
                List.nil_append, List.cons_append]
      · -- Sum.inr: ill-shaped, ruled out the same way as the empty case.
        exfalso
        cases N with
        | zero =>
            simp only [Command.runFuel] at hpost
            injection hpost with h1'
            injection h1'
        | succ N' =>
            have hnotmem : (Sum.inr c0' : GuessBX.Vals I) ∉ GuessBX.auxSetBot I := by
              simp only [GuessBX.auxSetBot, Finset.mem_image, Finset.mem_univ, true_and]
              rintro ⟨v', hv'⟩
              exact absurd hv' (by simp)
            have hstep : Command.step Tid.guessBX
                (Command.loopSeq (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                  (GuessBX.auxSetBot_nonempty I)) (guessBXLoop I)) φ2 (Sum.inr c0' :: rest0) =
                none := by
              simp only [Command.step]
              split_ifs with hmem
              · exact absurd hmem hnotmem
              · rfl
            simp only [Command.runFuel] at hpost
            have hpost' := hstep ▸ hpost
            injection hpost' with h1' h2'
            injection h2' with h3' h4'
            injection h4' with h5' h6'
            simp only [Prod.mk.injEq] at h5'
            exact absurd h5'.1 (by rintro ⟨⟩)

/-- `c ∈ GuessBX.auxSet I` iff `c = Sum.inl (some v)` for some `v : Fin I.n`. -/
theorem GuessBX.mem_auxSet_iff {I : PCPInstance} (c : GuessBX.Vals I) :
    c ∈ GuessBX.auxSet I ↔ ∃ v, c = Sum.inl (some v) := by
  unfold GuessBX.auxSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv.symm⟩, fun ⟨v, hv⟩ => ⟨v, hv.symm⟩⟩

/-- The converse of `GuessBX.program`'s leading `NDet({1,…,n})` draw. -/
theorem guessBX_lead_step_inv (I : PCPInstance) (s : List (GuessBX.Vals I)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessBX)) (φ' : (GuessBX.Vocab I).Store)
    (h : Command.runFuel Tid.guessBX (GuessBX.program I,
      (GuessBX.Vocab I).mkStore (fun v => match v with
        | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
        | _ => none) (Sum.inl none)) s (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v0 : Fin I.n) (rest : List (GuessBX.Vals I)),
      s = Sum.inl (some v0) :: rest ∧
      Command.runFuel Tid.guessBX
        ((guessBXLoop I).seq Command.term,
          Function.update ((GuessBX.Vocab I).mkStore (fun v => match v with
            | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
            | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
            | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
            | _ => none) (Sum.inl none)) GuessBX.Vars.aux (Sum.inl (some v0))) rest N =
        (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel, Command.step, GuessBX.program] at h
      have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
      exact absurd h2 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.runFuel, Command.step, GuessBX.program] at h
      split_ifs at h with hc
      · obtain ⟨v0, rfl⟩ := (GuessBX.mem_auxSet_iff c).mp hc
        simp only [Command.step, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨v0, rest, rfl, ?_⟩
        change Command.runFuel Tid.guessBX
            ((Command.whileLoop GuessBX.BExpr.tt (GuessBX.outerBody I)).seq Command.term,
              Function.update ((GuessBX.Vocab I).mkStore (fun v => match v with
                | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
                | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
                | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
                | _ => none) (Sum.inl none)) GuessBX.Vars.aux (Sum.inl (some v0))) rest N = _
        exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
      · have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
        exact absurd h2 (by rintro ⟨⟩)

/-- **The word characterization of the threads, `GuessBX`.** The converse of
`guessBX_shape`/`guessBX_general_run`, as `guessAX_shape_inv`, with
`K0 = (I.β v0).length - 1`. -/
theorem guessBX_shape_inv (I : PCPInstance) {s : List (GuessBX.Vals I)}
    {φ' : (GuessBX.Vocab I).Store} {cLast : Config (domainOf I) (GuessBX.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.guessBX)}
    (hrun : Command.Run Tid.guessBX s
      (GuessBX.program I, (GuessBX.Vocab I).mkStore (fun v => match v with
        | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : Fin I.n) (K0 : ℕ) (js : List (Fin I.n)) (v1 v2 : Val I) (vB0 : Val I × Val I)
      (inner0Rest : List (Val I × Val I × Val I))
      (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))),
      (I.β v0).length = K0 + 1 ∧
      s = Sum.inl (some v0) ::
        (js.map (fun idx => (Sum.inl (some idx) : GuessBX.Vals I)) ++ [Sum.inl none]) ∧
      inner0Rest.length = K0 ∧
      outerRest.length = js.length + 1 ∧
      (∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
        (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1) ∧
      (∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1) ∧
      v2 = Val.cnt (1 : Fin 4) ∧
      (∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4)) ∧
      (∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
        ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
          e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix (guessBXJsToKs I js) m + n) % 4,
            by omega⟩ : Fin 4) ∧
          e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix (guessBXJsToKs I js) m + n + 1) % 4,
            by omega⟩ : Fin 4)) ∧
      vB0.1 = Val.cnt (1 : Fin 4) ∧
      vB0.2 = Val.cntAux (1 : Fin 4) (some v0) ∧
      (∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
        b.1 = Val.cnt (⟨(2 + m) % 4, by omega⟩ : Fin 4) ∧
        (m < js.length → ∃ w, js[m]? = some w ∧
          b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) (some w)) ∧
        (m = js.length → b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) none)) ∧
      (∃ j : Fin (GuessBX.maxLen I + 2), j.val = 1 ∧
        v1 = Val.xTag (Tid.guessBX, true) (GuessBX.jthLetter I (some v0) j)) ∧
      (∀ n, n < inner0Rest.length → ∃ e j, inner0Rest[n]? = some e ∧ j.val = n + 2 ∧
        e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some v0) j)) ∧
      (∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
        (m < js.length → ∃ w, js[m]? = some w ∧
          ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
            e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some w) j)) ∧
        (m = js.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I none j))) ∧
      σ = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest := by
  have hterm_stuck : ∀ (φt : (GuessBX.Vocab I).Store) (r : List (GuessBX.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.guessBX)) (φt' : (GuessBX.Vocab I).Store),
      Command.runFuel Tid.guessBX (Command.skip, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      False := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        injection hm with hh1
        injection hh1
    | succ m =>
        have hskip : Command.step Tid.guessBX Command.skip φt r = none := rfl
        simp only [Command.runFuel, hskip] at hm
        injection hm with hh1 hh2
        injection hh2 with hh3 hh4
        injection hh4 with hh5 hh6
        simp only [Prod.mk.injEq] at hh5
        exact absurd hh5.1 (by rintro ⟨⟩)
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := guessBX_lead_step_inv I s n σ φ' hn2
  have hne : I.β v0 ≠ [] := I.hβ v0
  have hpos : 0 < (I.β v0).length := List.length_pos_of_ne_nil hne
  set K0 : ℕ := (I.β v0).length - 1 with hK0def
  have hlen0 : (I.β v0).length = K0 + 1 := by omega
  have hfst1 : Function.update ((GuessBX.Vocab I).mkStore (fun v => match v with
      | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
      | _ => none) (Sum.inl none)) GuessBX.Vars.aux (Sum.inl (some v0))
      GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)) := by
    have hne' : GuessBX.Vars.fst ≠ GuessBX.Vars.aux := by decide
    exact Function.update_of_ne hne' _ _
  have hcnt1 : Function.update ((GuessBX.Vocab I).mkStore (fun v => match v with
      | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
      | _ => none) (Sum.inl none)) GuessBX.Vars.aux (Sum.inl (some v0))
      GuessBX.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne' : GuessBX.Vars.cnt ≠ GuessBX.Vars.aux := by decide
    exact Function.update_of_ne hne' _ _
  have hcntY1 : Function.update ((GuessBX.Vocab I).mkStore (fun v => match v with
      | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
      | _ => none) (Sum.inl none)) GuessBX.Vars.aux (Sum.inl (some v0))
      GuessBX.Vars.cntY = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne' : GuessBX.Vars.cntY ≠ GuessBX.Vars.aux := by decide
    exact Function.update_of_ne hne' _ _
  set φ0 : (GuessBX.Vocab I).Store :=
    Function.update ((GuessBX.Vocab I).mkStore (fun v => match v with
      | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
      | _ => none) (Sum.inl none)) GuessBX.Vars.aux (Sum.inl (some v0)) with hφ0
  have haux0 : φ0 GuessBX.Vars.aux = Sum.inl (some v0) := Function.update_self _ _ _
  -- Remove the `.seq _ Command.term` wrapper (`Command.runFuel_seqTerm_stuck_unwrap`),
  -- reaching `guessBXLoop I` with target `(Command.skip, φ')`.
  obtain ⟨n', hneq, h2bare⟩ :=
    Command.runFuel_seqTerm_stuck_unwrap n (guessBXLoop I) φ0 rest σ φ' h2
  have hpre : Command.runFuel Tid.guessBX (guessBXLoop I, φ0) rest
      (n' + (9 + 14 * (K0 + 1) + 2 + 4)) = (.stuck, σ, (Command.skip, φ'), []) :=
    Command.runFuel_stuck_stable h2bare (9 + 14 * (K0 + 1) + 2 + 4)
  have hpad : n' + (9 + 14 * (K0 + 1) + 2 + 4) = (n' + 14 * (K0 + 1) + 2 + 4) + 9 := by omega
  rw [hpad] at hpre
  obtain ⟨φh, σ1a, hσeq, hcnt_h, hfst_h, haux_h, hcntY_h, hjOf_h, hNOf_h, runH⟩ :=
    guessBXOuterHead_step_inv I rest φ0 (some v0) haux0 0 hcntY1
      (n' + 14 * (K0 + 1) + 2 + 4) σ (Command.skip, φ') [] hpre
  have hNOf_h' : (GuessBX.NOf I φh).val = (I.β v0).length := by
    rw [hNOf_h]; simp [GuessBX.extBeta, List.length_map]
  have hNOf_hK : (GuessBX.NOf I φh).val = K0 + 1 := by rw [hNOf_h', hlen0]
  have hfst_head : φh GuessBX.Vars.fst = Sum.inr (Sum.inr (Sum.inr true)) := by
    rw [hfst_h, hfst1]
  have hcnt_head : φh GuessBX.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by rw [hcnt_h, hcnt1]
  have hmaxpos := GuessBX.maxLen_pos I
  have hNbound_head : (GuessBX.NOf I φh).val ≤ GuessBX.maxLen I := by
    rw [hNOf_hK]
    have hextle := GuessBX.extBeta_length_le I (some v0)
    simp only [GuessBX.extBeta, List.length_map] at hextle
    omega
  have hguard_first : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φh = true := by
    simp only [GuessBX.Vocab, GuessBX.evalB, decide_eq_true_eq, Fin.le_def]
    omega
  obtain ⟨φ1, hfst1', hcnt1', hj1, haux1, hcntY1', hN1, hstep14⟩ :=
    guessBX_innerLoop_first_step_outOfFuel I rest φh hguard_first hfst_head
      (0 : Fin 4) hcnt_head
  set C2 : Command (domainOf I) (GuessBX.Vocab I) :=
    Command.seq (Command.read Loc.ellByx GuessBX.VExpr.cntYAuxVal)
      (Command.seq (Command.ite GuessBX.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
          (GuessBX.auxSetBot_nonempty I))) with hC2
  have hstep14_seq :=
    Command.runFuel_seqCongr_outOfFuel 14 (guessBXInnerLoop I) C2 φh rest
      (guessBXInnerLoop I) φ1 _ rest hstep14
  have hstep14_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 14 (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φh rest (Command.seq (guessBXInnerLoop I) C2) φ1 _ rest hstep14_seq
  have hjOf1val : (GuessBX.jOf I φ1).val = (GuessBX.jOf I φh).val + 1 := by
    have heval : GuessBX.jOf I φ1 = GuessBX.jOf I φh + 1 := by
      simp only [GuessBX.jOf, hj1, GuessBX.eval]
    have h1val : (1 : Fin (GuessBX.maxLen I + 2)).val = 1 := by simp [Fin.val_one']
    rw [heval, Fin.val_add_eq_of_add_lt (by rw [h1val]; omega), h1val]
  have hNOf1 : (GuessBX.NOf I φ1).val = (GuessBX.NOf I φh).val := by
    simp only [GuessBX.NOf, hN1]
  have hNbound1 : (GuessBX.NOf I φ1).val ≤ GuessBX.maxLen I := by rw [hNOf1]; exact hNbound_head
  have hK1 : (GuessBX.jOf I φ1).val + K0 = (GuessBX.NOf I φ1).val + 1 := by
    rw [hjOf1val, hjOf_h, hNOf1, hNOf_hK]; omega
  obtain ⟨vsc, φ2, hvslenc, hcntfc, hauxfc, hcntYfc, hNfc, hfstfc, hjfc, hvalc, hvalxc,
    hstepChain⟩ :=
    guessBXInnerLoop_chain_outOfFuel I K0 rest φ1 hK1 (0 + 1 : Fin 4) hcnt1' hfst1' hNbound1
  have hstepChain_seq :=
    Command.runFuel_seqCongr_outOfFuel (14 * K0) (guessBXInnerLoop I) C2 φ1 rest
      (guessBXInnerLoop I) φ2 _ rest hstepChain
  have hstepChain_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel (14 * K0) (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φ1 rest (Command.seq (guessBXInnerLoop I) C2) φ2 _ rest hstepChain_seq
  have hcomb1 :=
    Command.runFuel_outOfFuel_append 14
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh) rest _ _ _
      hstep14_loop (14 * K0) _ _ _ _ hstepChain_loop
  have hguardFalse2 : (GuessBX.Vocab I).evalB GuessBX.BExpr.jLeN φ2 = false := by
    simp only [GuessBX.Vocab, GuessBX.evalB, decide_eq_false_iff_not, Fin.le_def]
    have hNOf2 : (GuessBX.NOf I φ2).val = (GuessBX.NOf I φh).val := by
      have hNOf2' : (GuessBX.NOf I φ2).val = (GuessBX.NOf I φ1).val := by
        simp only [GuessBX.NOf, hNfc]
      rw [hNOf2', hNOf1]
    omega
  have hexit := guessBXOuterExit_step_outOfFuel I rest φ2 C2 hguardFalse2
  have hexit_loop :=
    Command.runFuel_loopSeqCongr_outOfFuel 2 (Command.seq (guessBXInnerLoop I) C2)
      (guessBXLoop I) φ2 rest C2 φ2 [] rest hexit
  have hcomb2 :=
    Command.runFuel_outOfFuel_append (14 + 14 * K0)
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh) rest _ _ _
      hcomb1 2 _ _ _ _ hexit_loop
  have hauxOf_φ2 : φ2 GuessBX.Vars.aux = Sum.inl (some v0) := by
    rw [hauxfc, haux1, haux_h, haux0]
  have hcntY_φ2 : φ2 GuessBX.Vars.cntY = Sum.inr (Sum.inl (0 + 1 : Fin 4)) := by
    rw [hcntYfc, hcntY1', hcntY_h]
  have hpref := guessBXOuterTail_continue_pre_step_outOfFuel I rest φ2 (0 + 1 : Fin 4) hcntY_φ2
    v0 hauxOf_φ2
  have hcombAll :=
    Command.runFuel_outOfFuel_append (14 + 14 * K0 + 2)
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh) rest _ _ _
      hcomb2 4 _ _ _ _ hpref
  have hfuel1 : n' + 14 * (K0 + 1) + 2 + 4 = (14 + 14 * K0 + 2 + 4) + n' := by omega
  rw [hfuel1] at runH
  obtain ⟨σ1b, hpost, hσ1eq⟩ :=
    Command.runFuel_outOfFuel_split (14 + 14 * K0 + 2 + 4)
      (Command.loopSeq (Command.seq (guessBXInnerLoop I) C2) (guessBXLoop I), φh) rest _ _ _
      hcombAll n' _ σ1a (Command.skip, φ') [] runH
  rcases rest with _ | ⟨c0, rest0⟩
  · exfalso
    cases n' with
    | zero =>
        simp only [Command.runFuel] at hpost
        injection hpost with h1'
        injection h1'
    | succ n'' =>
        have hstep : Command.step Tid.guessBX
            (Command.loopSeq (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
              (GuessBX.auxSetBot_nonempty I)) (guessBXLoop I)) φ2 [] = none := by
          simp only [Command.step, Command.step_ndetAssign_nil]
        simp only [Command.runFuel] at hpost
        have hpost' := hstep ▸ hpost
        injection hpost' with h1' h2'
        injection h2' with h3' h4'
        injection h4' with h5' h6'
        simp only [Prod.mk.injEq] at h5'
        exact absurd h5'.1 (by rintro ⟨⟩)
  · rcases c0 with v0' | c0'
    · -- Sum.inl v0': dispatch via `guessBX_outer0_step_inv`, bare, directly
      -- (`h2bare` is already unwrapped, so no further lifting is needed).
      have h3 : Command.runFuel Tid.guessBX (guessBXLoop I, φ0) (Sum.inl v0' :: rest0)
          (n' + 31 + 14 * K0) = (.stuck, σ, (Command.skip, φ'), []) := by
        have h3' := Command.runFuel_stuck_stable h2bare (31 + 14 * K0)
        have hpad2 : n' + (31 + 14 * K0) = n' + 31 + 14 * K0 := by omega
        rwa [hpad2] at h3'
      obtain ⟨v1, v2, vs1, φ3, σ1c, hvslen3, hv2eq, ⟨j1, hj1val, hv1eq⟩, hval3, hvalxA3, hfst3,
        haux3, ⟨cntF3, hcnt3, hcntFeq3⟩, hcntY3, hσeq3, h4⟩ :=
        guessBX_outer0_step_inv I K0 v0 hlen0 rest0 φ0 hfst1 (0 : Fin 4) hcnt1 haux0
          (0 : Fin 4) hcntY1 v0' n' σ (Command.skip, φ') [] h3
      have hks0 : ksPrefix (guessBXJsToKs I ([] : List (Fin I.n))) 0 = 0 := rfl
      cases v0' with
      | none =>
          -- `js = []`: the terminating iteration.
          have h4' := Command.runFuel_stuck_stable h4 30
          obtain ⟨vs2, φ5, σ2, hlen2, hval2, hvalxA2, hσ2eq, hrun2⟩ :=
            guessBX_outerRest_break_step_inv I rest0 φ3 hfst3 cntF3 hcnt3 haux3 (0 + 1 : Fin 4)
              hcntY3 n' σ1c (Command.skip, φ') [] h4'
          have hrest0nil : rest0 = [] ∧ σ2 = [] ∧ φ5 = φ' := by
            cases n' with
            | zero =>
                exfalso
                simp only [Command.runFuel] at hrun2
                injection hrun2 with hz1
                injection hz1
            | succ n''' =>
                have hskipstep : Command.step Tid.guessBX Command.skip φ5 rest0 = none := rfl
                simp only [Command.runFuel, hskipstep] at hrun2
                injection hrun2 with e1 e2
                injection e2 with e3 e4
                injection e4 with e5 e6
                injection e5 with e7 e8
                exact ⟨e6, e3.symm, e8⟩
          obtain ⟨hrest0nil', hσ2nil, hφ5eq⟩ := hrest0nil
          subst hrest0nil'
          refine ⟨v0, K0, [], v1, v2, (Val.cnt 1, Val.cntAux 1 (some v0)), vs1,
            [((Val.cnt 2, Val.cntAux 2 none), vs2)], hlen0, ?_, hvslen3, rfl, ?_, ?_, ?_, hval3,
            ?_, rfl, rfl, ?_, ⟨j1, hj1val, hv1eq⟩, hvalxA3, ?_, ?_⟩
          · simp [hs]
          · intro m hm
            simp only [List.length_nil] at hm
            exact absurd hm (by omega)
          · exact ⟨_, vs2, rfl, hlen2⟩
          · rw [hv2eq]; rfl
          · intro m hm
            simp only [List.length_nil] at hm
            have hm0 : m = 0 := by omega
            subst hm0
            refine ⟨_, vs2, rfl, ?_⟩
            intro n hn
            obtain ⟨e, he, he22, he21⟩ := hval2 n hn
            refine ⟨e, he, ?_, ?_⟩
            · rw [he22]; congr 1; apply Fin.ext
              show (cntF3.val + n) % 4 = (1 + K0 + 0 + n) % 4
              rw [hcntFeq3]; simp only [Fin.ext_iff] at hks0 ⊢; omega
            · rw [he21]; congr 1; apply Fin.ext
              show (cntF3.val + n + 1) % 4 = (1 + K0 + 0 + n + 1) % 4
              rw [hcntFeq3]; simp only [Fin.ext_iff] at hks0 ⊢; omega
          · intro m hm
            simp only [List.length_nil] at hm
            have hm0 : m = 0 := by omega
            subst hm0
            refine ⟨_, vs2, rfl, rfl, ?_, ?_⟩
            · intro h; simp only [List.length_nil] at h; omega
            · intro _; rfl
          · intro m hm
            simp only [List.length_nil] at hm
            have hm0 : m = 0 := by omega
            subst hm0
            refine ⟨_, vs2, rfl, ?_, fun _ => hvalxA2⟩
            intro h; simp only [List.length_nil] at h; omega
          · rw [hσeq3, hσ2eq, hσ2nil]
            simp only [guessBXBlockWord, guessBXOuterBlockElems, List.flatMap_cons,
              List.flatMap_nil, List.append_nil, List.append_assoc, List.nil_append,
              List.cons_append, show (0 + 1 : Fin 4) = 1 from rfl, show (1 + 1 : Fin 4) = 2 from rfl]
      | some j0 =>
          have hne : I.β j0 ≠ [] := I.hβ j0
          have hpos : 0 < (I.β j0).length := List.length_pos_of_ne_nil hne
          have hlen0' : (I.β j0).length = (I.β j0).length - 1 + 1 := by omega
          obtain ⟨js, outerRest, hseq2, hlen2, houterC, houterLastC, hvalC, hbC, hbxAC, hσeqIH⟩ :=
            guessBX_chain_shape_inv I rest0.length rest0 rfl ((I.β j0).length - 1) j0 hlen0' φ3
              hfst3 cntF3 hcnt3 haux3 (0 + 1 : Fin 4) hcntY3 n' σ1c φ' h4
          refine ⟨v0, K0, j0 :: js, v1, v2, (Val.cnt 1, Val.cntAux 1 (some v0)), vs1, outerRest,
            hlen0, ?_, hvslen3, ?_, ?_, ?_, ?_, hval3, ?_, rfl, rfl, ?_,
            ⟨j1, hj1val, hv1eq⟩, hvalxA3, ?_, ?_⟩
          · simp [hs, hseq2]
          · simpa [List.length_cons] using hlen2
          · intro m hm
            exact houterC m hm
          · exact houterLastC
          · rw [hv2eq]; rfl
          · intro m hm
            obtain ⟨b, vs, hbv, hval'⟩ := hvalC m (by simp only [List.length_cons] at hm; omega)
            refine ⟨b, vs, hbv, ?_⟩
            intro n hn
            obtain ⟨e, he, he22, he21⟩ := hval' n hn
            have hcntF3' : cntF3.val = (1 + K0) % 4 := by rw [hcntFeq3]; rfl
            have hks : guessBXJsToKs I (j0 :: js) = ((I.β j0).length - 1) :: guessBXJsToKs I js := by
              simp only [guessBXJsToKs, List.map_cons]
            refine ⟨e, he, ?_, ?_⟩
            · rw [he22]; congr 1; apply Fin.ext
              show (cntF3.val +
                  ksPrefix (((I.β j0).length - 1) :: guessBXJsToKs I js) m + n) % 4 =
                (1 + K0 + ksPrefix (guessBXJsToKs I (j0 :: js)) m + n) % 4
              rw [hcntF3', hks]; omega
            · rw [he21]; congr 1; apply Fin.ext
              show (cntF3.val +
                  ksPrefix (((I.β j0).length - 1) :: guessBXJsToKs I js) m + n + 1) % 4 =
                (1 + K0 + ksPrefix (guessBXJsToKs I (j0 :: js)) m + n + 1) % 4
              rw [hcntF3', hks]; omega
          · intro m hm
            obtain ⟨b, vs, hbv, hb1, hb2z, hb2m, hb2last⟩ := hbC m (by simp only [List.length_cons] at hm; omega)
            refine ⟨b, vs, hbv, ?_, ?_, ?_⟩
            · rw [hb1]; congr 1
            · intro hmlt
              rcases Nat.eq_zero_or_pos m with hm0 | hmpos
              · subst hm0
                obtain hb2z' := hb2z rfl
                exact ⟨j0, rfl, by rw [hb2z']; congr 1⟩
              · have hm'le : m ≤ js.length := by
                  simp only [List.length_cons] at hm hmlt; omega
                obtain ⟨w, hw, hb2⟩ := hb2m (by omega) hm'le
                refine ⟨w, ?_, ?_⟩
                · show (j0 :: js)[m]? = some w
                  rw [show m = (m - 1) + 1 from by omega, List.getElem?_cons_succ]
                  exact hw
                · rw [hb2]; congr 1
            · intro hmeq
              simp only [List.length_cons] at hmeq
              have hb2last' := hb2last (by omega)
              rw [hb2last']; congr 1
          · intro m hm
            obtain ⟨b, vs, hbv, hbxA0, hbxAm, hbxAlast⟩ :=
              hbxAC m (by simp only [List.length_cons] at hm; omega)
            refine ⟨b, vs, hbv, ?_, ?_⟩
            · intro hmlt
              rcases Nat.eq_zero_or_pos m with hm0 | hmpos
              · subst hm0
                exact ⟨j0, rfl, hbxA0 rfl⟩
              · have hm'le : m ≤ js.length := by
                  simp only [List.length_cons] at hm hmlt; omega
                obtain ⟨w, hw, hbxA⟩ := hbxAm (by omega) hm'le
                refine ⟨w, ?_, hbxA⟩
                show (j0 :: js)[m]? = some w
                rw [show m = (m - 1) + 1 from by omega, List.getElem?_cons_succ]
                exact hw
            · intro hmeq
              simp only [List.length_cons] at hmeq
              exact hbxAlast (by omega)
          · rw [hσeq3, hσeqIH]
            simp only [guessBXBlockWord, List.cons_append, List.append_assoc,
              List.nil_append, List.append_nil, show (0 + 1 : Fin 4) = 1 from rfl]
    · -- Sum.inr: ill-shaped, ruled out the same way as the nil case above.
      exfalso
      cases n' with
      | zero =>
          simp only [Command.runFuel] at hpost
          injection hpost with h1'
          injection h1'
      | succ n'' =>
          have hnotmem : (Sum.inr c0' : GuessBX.Vals I) ∉ GuessBX.auxSetBot I := by
            simp only [GuessBX.auxSetBot, Finset.mem_image, Finset.mem_univ, true_and]
            rintro ⟨v', hv'⟩
            exact absurd hv' (by simp)
          have hstep : Command.step Tid.guessBX
              (Command.loopSeq (Command.ndetAssign GuessBX.Vars.aux (GuessBX.auxSetBot I)
                (GuessBX.auxSetBot_nonempty I)) (guessBXLoop I)) φ2 (Sum.inr c0' :: rest0) =
              none := by
            simp only [Command.step]
            split_ifs with hmem
            · exact absurd hmem hnotmem
            · rfl
          simp only [Command.runFuel] at hpost
          have hpost' := hstep ▸ hpost
          injection hpost' with h1' h2'
          injection h2' with h3' h4'
          injection h4' with h5' h6'
          simp only [Prod.mk.injEq] at h5'
          exact absurd h5'.1 (by rintro ⟨⟩)

/-! ## `GuessAY`

`GuessAY` (`g_α^y`) has a single loop with no inner `for` loop. Its
`First()` branch contains both writes and reads (three writes and two reads
in the `else` branch). -/

theorem GuessAY.mem_auxSet_iff {I : PCPInstance} (c : GuessAY.Vals I) :
    c ∈ GuessAY.auxSet I ↔ ∃ v, c = Sum.inl (some v) := by
  unfold GuessAY.auxSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv.symm⟩, fun ⟨v, hv⟩ => ⟨v, hv.symm⟩⟩

/-- The converse of `GuessAY.program`'s leading `NDet({1,…,n})` draw. -/
theorem guessAY_lead_step_inv (I : PCPInstance) (s : List (GuessAY.Vals I)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessAY)) (φ' : (GuessAY.Vocab I).Store)
    (h : Command.runFuel Tid.guessAY (GuessAY.program I,
      (GuessAY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none)) s (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v0 : Fin I.n) (rest : List (GuessAY.Vals I)),
      s = Sum.inl (some v0) :: rest ∧
      Command.runFuel Tid.guessAY
        ((guessAYLoop I).seq Command.term,
          Function.update ((GuessAY.Vocab I).mkStore (fun v => match v with
            | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
            | .fst => some (Sum.inr (Sum.inr true))
            | _ => none) (Sum.inl none)) GuessAY.Vars.aux (Sum.inl (some v0))) rest N =
        (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel, Command.step, GuessAY.program] at h
      have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
      exact absurd h2 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.runFuel, Command.step, GuessAY.program] at h
      split_ifs at h with hc
      · obtain ⟨v0, rfl⟩ := (GuessAY.mem_auxSet_iff c).mp hc
        simp only [Command.step, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨v0, rest, rfl, ?_⟩
        change Command.runFuel Tid.guessAY
            ((Command.whileLoop GuessAY.BExpr.tt (GuessAY.loopBody I)).seq Command.term,
              Function.update ((GuessAY.Vocab I).mkStore (fun v => match v with
                | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
                | .fst => some (Sum.inr (Sum.inr true))
                | _ => none) (Sum.inl none)) GuessAY.Vars.aux (Sum.inl (some v0))) rest N = _
        exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
      · have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
        exact absurd h2 (by rintro ⟨⟩)


theorem GuessAY.mem_auxSetBot_iff {I : PCPInstance} (c : GuessAY.Vals I) :
    c ∈ GuessAY.auxSetBot I ↔ ∃ w : Option (Fin I.n), c = Sum.inl w := by
  unfold GuessAY.auxSetBot
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, hw.symm⟩, fun ⟨w, hw⟩ => ⟨w, hw.symm⟩⟩

theorem guessAY_block0_step_inv (I : PCPInstance) (C2 : Command (domainOf I) (GuessAY.Vocab I))
    (s : List (GuessAY.Vals I)) (φ : (GuessAY.Vocab I).Store)
    (hfst : φ GuessAY.Vars.fst = Sum.inr (Sum.inr true))
    (hcnt0 : φ GuessAY.Vars.cnt = Sum.inr (Sum.inl 0))
    (v0 : Fin I.n) (haux0 : φ GuessAY.Vars.aux = Sum.inl (some v0)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessAY)) (φ' : (GuessAY.Vocab I).Store)
    (h : Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2, φ) s (N + 18) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (w : Option (Fin I.n)) (rest : List (GuessAY.Vals I))
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAY)),
      s = Sum.inl w :: rest ∧
      σ = guessAYBlock0Elems I v0 ++ σ1 ∧
      ∃ (φ3 : (GuessAY.Vocab I).Store),
        φ3 GuessAY.Vars.fst = Sum.inr (Sum.inr false) ∧
        φ3 GuessAY.Vars.cnt = Sum.inr (Sum.inl 1) ∧
        φ3 GuessAY.Vars.aux = Sum.inl w ∧
        Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2, φ3) rest N =
          (.stuck, σ1, (Command.term, φ'), []) := by
  set φ0 : (GuessAY.Vocab I).Store :=
    Function.update φ GuessAY.Vars.prev (GuessAY.eval I GuessAY.Expr.readCnt φ) with hφ0
  set φ1 : (GuessAY.Vocab I).Store :=
    Function.update φ0 GuessAY.Vars.cnt (GuessAY.eval I GuessAY.Expr.nextCnt φ0) with hφ1
  have hne1 : GuessAY.Vars.fst ≠ GuessAY.Vars.cnt := by decide
  have hne2 : GuessAY.Vars.fst ≠ GuessAY.Vars.prev := by decide
  have hfst1 : φ1 GuessAY.Vars.fst = Sum.inr (Sum.inr true) :=
    (Function.update_of_ne hne1 _ _).trans ((Function.update_of_ne hne2 _ _).trans hfst)
  set φ2 : (GuessAY.Vocab I).Store :=
    Function.update φ1 GuessAY.Vars.fst (GuessAY.eval I GuessAY.Expr.fstFalse φ1) with hφ2
  have hne3 : GuessAY.Vars.aux ≠ GuessAY.Vars.fst := by decide
  have hne4 : GuessAY.Vars.aux ≠ GuessAY.Vars.cnt := by decide
  have hne5 : GuessAY.Vars.aux ≠ GuessAY.Vars.prev := by decide
  have haux2 : φ2 GuessAY.Vars.aux = Sum.inl (some v0) :=
    (Function.update_of_ne hne3 _ _).trans ((Function.update_of_ne hne4 _ _).trans
      ((Function.update_of_ne hne5 _ _).trans haux0))
  have hcnt_φ0 : φ0 GuessAY.Vars.cnt = φ GuessAY.Vars.cnt := rfl
  have hcnt1eq : φ1 GuessAY.Vars.cnt = GuessAY.eval I GuessAY.Expr.nextCnt φ0 :=
    Function.update_self _ _ _
  have hcnt1raw : φ1 GuessAY.Vars.cnt = Sum.inr (Sum.inl 1) := by
    simp only [hcnt1eq, GuessAY.eval, hcnt_φ0, hcnt0]; rfl
  have hcnt2raw : φ2 GuessAY.Vars.cnt = Sum.inr (Sum.inl 1) :=
    (Function.update_of_ne hne1.symm _ _).trans hcnt1raw
  have hell2 : (GuessAY.Vocab I).evalV GuessAY.VExpr.cntAuxVal φ2 = Val.cntAux 1 (some v0) := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.cntOf, GuessAY.auxOf, hcnt2raw, haux2]; rfl
  have hz2 : (GuessAY.Vocab I).evalV GuessAY.VExpr.cntVal φ2 = Val.cnt 1 := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.cntOf, hcnt2raw]; rfl
  have hy2 : (GuessAY.Vocab I).evalV GuessAY.VExpr.yTagFirst φ2 = Val.yTag (Tid.guessAY, true) (some v0) := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.auxOf, haux2]; rfl
  -- Step 1: unwrap the loop guard (constant `tt`).
  have hs1 : Command.step Tid.guessAY (guessAYLoop I) φ s =
      some (none, Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I), φ, s) := by
    simp only [guessAYLoop, Command.step, GuessAY.Vocab, GuessAY.evalB, if_true]
  -- Step 2: `prev ← readCnt`.
  have hs2 : Command.step Tid.guessAY (Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessAY.BExpr.isFirst
              (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                    (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                      (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))))
        (guessAYLoop I), φ0, s) := by
    rw [hφ0]
    simp only [GuessAY.loopBody, Command.firstIt, Command.step, GuessAY.Vocab]
    rfl
  -- Step 3: `.seq Command.skip _` elimination.
  have hs3 : Command.step Tid.guessAY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))))
      (guessAYLoop I)) φ0 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessAY.BExpr.isFirst
              (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                    (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                      (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I)))))
        (guessAYLoop I), φ0, s) := by
    simp only [Command.step]
    rfl
  -- Step 4: `cnt ← nextCnt`.
  have hs4 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
      (guessAYLoop I)) φ0 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
        (guessAYLoop I), φ1, s) := by
    rw [hφ1]
    simp only [Command.step, GuessAY.Vocab]
  -- Step 5: `.seq Command.skip _` elimination.
  have hs5 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 6: `Command.ite isFirst` resolves true (`hfst1`).
  have hs6 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.ite GuessAY.BExpr.isFirst
          (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
          (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                  (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step, GuessAY.Vocab, GuessAY.evalB, hfst1, if_true]
  -- Step 7: `fst ← False`.
  have hs7 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
          (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
            (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
              (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq Command.skip
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ2, s) := by
    rw [hφ2]
    simp only [Command.step, GuessAY.Vocab]
  -- Step 8: `.seq Command.skip _` elimination.
  have hs8 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
            (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
              (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
            (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
              (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 9: `w(yA, yTagFirst)`.
  have hs9 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.yA
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.yTagFirst φ2), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 10: `.seq Command.skip _` elimination.
  have hs10 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 11: `w(ellAyx, cntAuxVal)`.
  have hs11 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
          (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.ellAyx
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.cntAuxVal φ2), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 12: `.seq Command.skip _` elimination.
  have hs12 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 13: `w(zAy'y, cntVal)`.
  have hs13 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.zAy'y
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.cntVal φ2), rfl⟩,
        Command.loopSeq
          (Command.seq
            Command.skip
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 14: `.seq Command.skip _` elimination.
  have hs14 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        Command.skip
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I)))
        (guessAYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 15: `if aux = ⊥ then break endif` resolves false (`haux2`).
  have hs15 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
          (GuessAY.auxSetBot_nonempty I)))
      (guessAYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I)))
        (guessAYLoop I), φ2, s) := by
    simp [Command.step, GuessAY.Vocab, GuessAY.evalB, haux2]
  -- Step 16: `.seq Command.skip _` elimination (before the trailing `NDet` draw).
  have hs16 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq Command.skip
        (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
          (GuessAY.auxSetBot_nonempty I)))
      (guessAYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
          (GuessAY.auxSetBot_nonempty I))
        (guessAYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Transport steps 1-16 (which do not depend on the resolution) into `h`.
  have hrs1 : Command.RunStep Tid.guessAY s none (guessAYLoop I, φ) s
      (Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  cases s with
  | nil =>
      have hnone : Command.step Tid.guessAY
          ((Command.loopSeq (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I)) (guessAYLoop I)).seq C2) φ2 [] = none :=
        Command.step_seq_loopSeq_ndetAssign_nil _ _ _ _ _ _
      have h' := hnone ▸ h
      injection h' with _ h2
      injection h2 with _ h4
      injection h4 with h5 _
      exact absurd h5 (by rintro ⟨⟩)
  | cons c rest =>
      rcases Classical.em (c ∈ GuessAY.auxSetBot I) with hc | hc
      · obtain ⟨w, rfl⟩ := (GuessAY.mem_auxSetBot_iff c).mp hc
        have hcpos := Command.step_ndetAssign_cons_pos (t := Tid.guessAY) GuessAY.Vars.aux
          (GuessAY.auxSetBot I) (GuessAY.auxSetBot_nonempty I) φ2 (Sum.inl w) rest hc
        have hrs17a : Command.RunStep Tid.guessAY (Sum.inl w :: rest) none
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I), φ2) rest
            (Command.skip, Function.update φ2 GuessAY.Vars.aux (Sum.inl w)) :=
          Command.step_sound _ _ _ _ _ _ _ hcpos
        have hrs17 := Command.RunStep.loopCongr (C2 := guessAYLoop I) hrs17a
        have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
        have h := hw17 ▸ h
        dsimp only at h
        have hrs18 : Command.RunStep Tid.guessAY rest none
            (Command.loopSeq Command.skip (guessAYLoop I),
              Function.update φ2 GuessAY.Vars.aux (Sum.inl w)) rest
            (guessAYLoop I, Function.update φ2 GuessAY.Vars.aux (Sum.inl w)) :=
          Command.RunStep.loopSkip
        have hw18 : Command.step Tid.guessAY
            ((Command.loopSeq Command.skip (guessAYLoop I)).seq C2)
            (Function.update φ2 GuessAY.Vars.aux (Sum.inl w)) rest =
            some (none, (guessAYLoop I).seq C2,
              Function.update φ2 GuessAY.Vars.aux (Sum.inl w), rest) :=
          Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
        have h := hw18 ▸ h
        have hne_fst_aux2 : GuessAY.Vars.fst ≠ GuessAY.Vars.aux := by decide
        have hne_cnt_aux2 : GuessAY.Vars.cnt ≠ GuessAY.Vars.aux := by decide
        have hfst2 : φ2 GuessAY.Vars.fst = Sum.inr (Sum.inr false) := by
          rw [hφ2]; exact Function.update_self _ _ _
        rw [hy2, hell2, hz2] at h
        injection h with hh1 hrest1
        injection hrest1 with hh2 hrest2
        injection hrest2 with hh3 hh4
        refine ⟨w, rest,
          (Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2,
            Function.update φ2 GuessAY.Vars.aux (Sum.inl w)) rest N).2.1,
          rfl, hh2.symm, Function.update φ2 GuessAY.Vars.aux (Sum.inl w),
          (Function.update_of_ne hne_fst_aux2 (Sum.inl w) φ2).trans hfst2,
          (Function.update_of_ne hne_cnt_aux2 (Sum.inl w) φ2).trans hcnt2raw,
          Function.update_self _ _ _, Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩
      · exfalso
        have hs17' : Command.step Tid.guessAY
            ((Command.loopSeq
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I)) (guessAYLoop I)).seq C2) φ2 (c :: rest) = none :=
          Command.step_seq_loopSeq_ndetAssign_cons_neg (t := Tid.guessAY) GuessAY.Vars.aux
            (GuessAY.auxSetBot I) (GuessAY.auxSetBot_nonempty I) φ2 (guessAYLoop I) C2 c rest hc
        have h' := hs17' ▸ h
        injection h' with _ h2
        injection h2 with _ h4
        injection h4 with h5 _
        exact absurd h5 (by rintro ⟨⟩)

theorem guessAY_blockRest_continue_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (GuessAY.Vocab I))
    (s : List (GuessAY.Vals I)) (φ : (GuessAY.Vocab I).Store)
    (hfst : φ GuessAY.Vars.fst = Sum.inr (Sum.inr false)) (k : Fin 4)
    (hcnt0 : φ GuessAY.Vars.cnt = Sum.inr (Sum.inl k))
    (v : Fin I.n) (haux0 : φ GuessAY.Vars.aux = Sum.inl (some v)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessAY)) (φ' : (GuessAY.Vocab I).Store)
    (h : Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2, φ) s (N + 20) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (w : Option (Fin I.n)) (rest : List (GuessAY.Vals I))
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAY)),
      s = Sum.inl w :: rest ∧
      σ = guessAYBlockRestElems I (k, some v) ++ σ1 ∧
      ∃ (φ2u : (GuessAY.Vocab I).Store),
        φ2u GuessAY.Vars.fst = Sum.inr (Sum.inr false) ∧
        φ2u GuessAY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
        φ2u GuessAY.Vars.aux = Sum.inl w ∧
        Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2, φ2u) rest N =
          (.stuck, σ1, (Command.term, φ'), []) := by
  set φ0 : (GuessAY.Vocab I).Store :=
    Function.update φ GuessAY.Vars.prev (GuessAY.eval I GuessAY.Expr.readCnt φ) with hφ0
  set φ1 : (GuessAY.Vocab I).Store :=
    Function.update φ0 GuessAY.Vars.cnt (GuessAY.eval I GuessAY.Expr.nextCnt φ0) with hφ1
  have hne1 : GuessAY.Vars.fst ≠ GuessAY.Vars.cnt := by decide
  have hne2 : GuessAY.Vars.fst ≠ GuessAY.Vars.prev := by decide
  have hfst1 : φ1 GuessAY.Vars.fst = Sum.inr (Sum.inr false) :=
    (Function.update_of_ne hne1 _ _).trans ((Function.update_of_ne hne2 _ _).trans hfst)
  have hne4 : GuessAY.Vars.aux ≠ GuessAY.Vars.cnt := by decide
  have hne5 : GuessAY.Vars.aux ≠ GuessAY.Vars.prev := by decide
  have haux1 : φ1 GuessAY.Vars.aux = Sum.inl (some v) :=
    (Function.update_of_ne hne4 _ _).trans ((Function.update_of_ne hne5 _ _).trans haux0)
  have hne_prev_cnt : GuessAY.Vars.prev ≠ GuessAY.Vars.cnt := by decide
  have hcnt_φ0 : φ0 GuessAY.Vars.cnt = φ GuessAY.Vars.cnt := rfl
  have hcnt1eq : φ1 GuessAY.Vars.cnt = GuessAY.eval I GuessAY.Expr.nextCnt φ0 :=
    Function.update_self _ _ _
  have hcnt1raw : φ1 GuessAY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt1eq, GuessAY.eval, hcnt_φ0, hcnt0]; rfl
  have hprev0eq : φ0 GuessAY.Vars.prev = GuessAY.eval I GuessAY.Expr.readCnt φ :=
    Function.update_self _ _ _
  have hprev0raw : φ0 GuessAY.Vars.prev = Sum.inr (Sum.inl k) := by
    simp only [hprev0eq, GuessAY.eval, hcnt0]; rfl
  have hprev1raw : φ1 GuessAY.Vars.prev = Sum.inr (Sum.inl k) :=
    (Function.update_of_ne hne_prev_cnt _ _).trans hprev0raw
  have hell1 : (GuessAY.Vocab I).evalV GuessAY.VExpr.cntAuxVal φ1
      = Val.cntAux (k + 1) (some v) := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.cntOf, GuessAY.auxOf, hcnt1raw, haux1]; rfl
  have hz1 : (GuessAY.Vocab I).evalV GuessAY.VExpr.cntVal φ1 = Val.cnt (k + 1) := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.cntOf, hcnt1raw]; rfl
  have hprevVal1 : (GuessAY.Vocab I).evalV GuessAY.VExpr.prevVal φ1 = Val.cnt k := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.prevOf, hprev1raw]; rfl
  have hyRest1 : (GuessAY.Vocab I).evalV GuessAY.VExpr.yTagRest φ1
      = Val.yTag (Tid.guessAY, false) (some v) := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.auxOf, haux1]; rfl
  -- Step 1: unwrap the loop guard.
  have hs1 : Command.step Tid.guessAY (guessAYLoop I) φ s =
      some (none, Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I), φ, s) := by
    simp only [guessAYLoop, Command.step, GuessAY.Vocab, GuessAY.evalB, if_true]
  -- Step 2: `prev ← readCnt`.
  have hs2 : Command.step Tid.guessAY (Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessAY.BExpr.isFirst
              (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                    (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                      (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))))
        (guessAYLoop I), φ0, s) := by
    rw [hφ0]
    simp only [GuessAY.loopBody, Command.firstIt, Command.step, GuessAY.Vocab]
    rfl
  -- Step 3: `.seq Command.skip _` elimination.
  have hs3 : Command.step Tid.guessAY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))))
      (guessAYLoop I)) φ0 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessAY.BExpr.isFirst
              (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                    (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                      (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I)))))
        (guessAYLoop I), φ0, s) := by
    simp only [Command.step]
    rfl
  -- Step 4: `cnt ← nextCnt`.
  have hs4 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
      (guessAYLoop I)) φ0 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
        (guessAYLoop I), φ1, s) := by
    rw [hφ1]
    simp only [Command.step, GuessAY.Vocab]
  -- Step 5: `.seq Command.skip _` elimination.
  have hs5 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 6: `Command.ite isFirst` resolves false (`hfst1`), entering ELSE.
  have hs6 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.ite GuessAY.BExpr.isFirst
          (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
          (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                  (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                  (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp [Command.step, GuessAY.Vocab, GuessAY.evalB, hfst1]
  -- Step 7: `w(yA, yTagRest)`.
  have hs7 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.yA
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.yTagRest φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 8: `.seq Command.skip _` elimination.
  have hs8 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 9: `w(ellAyx, cntAuxVal)`.
  have hs9 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
          (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
              (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.ellAyx
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.cntAuxVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                  (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 10: `.seq Command.skip _` elimination.
  have hs10 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
              (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
              (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 11: `w(zAy'y, cntVal)`.
  have hs11 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
          (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
            (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.zAy'y
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.cntVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 12: `.seq Command.skip _` elimination.
  have hs12 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
            (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
            (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 13: `r(zAxy, prevVal)`.
  have hs13 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
          (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.rd Tid.guessAY Loc.zAxy
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.prevVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 14: `.seq Command.skip _` elimination.
  have hs14 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 15: `r(zAyy', prevVal)`.
  have hs15 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.rd Tid.guessAY Loc.zAyy'
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.prevVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            Command.skip
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 16: `.seq Command.skip _` elimination.
  have hs16 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        Command.skip
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I)))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 17: `if aux = ⊥ then break endif` resolves false (`haux1`).
  have hs17 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
          (GuessAY.auxSetBot_nonempty I)))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I)))
        (guessAYLoop I), φ1, s) := by
    simp [Command.step, GuessAY.Vocab, GuessAY.evalB, haux1]
  -- Step 18: `.seq Command.skip _` elimination (before the trailing `NDet` draw).
  have hs18 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq Command.skip
        (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
          (GuessAY.auxSetBot_nonempty I)))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
          (GuessAY.auxSetBot_nonempty I))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Bridge steps 1-18 (all resolution-independent) into `h`.
  have hrs1 : Command.RunStep Tid.guessAY s none (guessAYLoop I, φ) s
      (Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  cases s with
  | nil =>
      have hnone : Command.step Tid.guessAY
          ((Command.loopSeq (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I)) (guessAYLoop I)).seq C2) φ1 [] = none :=
        Command.step_seq_loopSeq_ndetAssign_nil _ _ _ _ _ _
      have h' := hnone ▸ h
      injection h' with _ h2
      injection h2 with _ h4
      injection h4 with h5 _
      exact absurd h5 (by rintro ⟨⟩)
  | cons c rest =>
      rcases Classical.em (c ∈ GuessAY.auxSetBot I) with hc | hc
      · obtain ⟨w, rfl⟩ := (GuessAY.mem_auxSetBot_iff c).mp hc
        have hcpos := Command.step_ndetAssign_cons_pos (t := Tid.guessAY) GuessAY.Vars.aux
          (GuessAY.auxSetBot I) (GuessAY.auxSetBot_nonempty I) φ1 (Sum.inl w) rest hc
        have hrs19a : Command.RunStep Tid.guessAY (Sum.inl w :: rest) none
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I), φ1) rest
            (Command.skip, Function.update φ1 GuessAY.Vars.aux (Sum.inl w)) :=
          Command.step_sound _ _ _ _ _ _ _ hcpos
        have hrs19 := Command.RunStep.loopCongr (C2 := guessAYLoop I) hrs19a
        have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
        have h := hw19 ▸ h
        dsimp only at h
        have hrs20 : Command.RunStep Tid.guessAY rest none
            (Command.loopSeq Command.skip (guessAYLoop I),
              Function.update φ1 GuessAY.Vars.aux (Sum.inl w)) rest
            (guessAYLoop I, Function.update φ1 GuessAY.Vars.aux (Sum.inl w)) :=
          Command.RunStep.loopSkip
        have hw20 : Command.step Tid.guessAY
            ((Command.loopSeq Command.skip (guessAYLoop I)).seq C2)
            (Function.update φ1 GuessAY.Vars.aux (Sum.inl w)) rest =
            some (none, (guessAYLoop I).seq C2,
              Function.update φ1 GuessAY.Vars.aux (Sum.inl w), rest) :=
          Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs20)
        have h := hw20 ▸ h
        have hne_fst_aux2 : GuessAY.Vars.fst ≠ GuessAY.Vars.aux := by decide
        have hne_cnt_aux2 : GuessAY.Vars.cnt ≠ GuessAY.Vars.aux := by decide
        rw [hyRest1, hell1, hz1, hprevVal1] at h
        injection h with hh1 hrest1
        injection hrest1 with hh2 hrest2
        injection hrest2 with hh3 hh4
        refine ⟨w, rest,
          (Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2,
            Function.update φ1 GuessAY.Vars.aux (Sum.inl w)) rest N).2.1,
          rfl, hh2.symm, Function.update φ1 GuessAY.Vars.aux (Sum.inl w),
          (Function.update_of_ne hne_fst_aux2 (Sum.inl w) φ1).trans hfst1,
          (Function.update_of_ne hne_cnt_aux2 (Sum.inl w) φ1).trans hcnt1raw,
          Function.update_self _ _ _, Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩
      · exfalso
        have hs19' : Command.step Tid.guessAY
            ((Command.loopSeq
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I)) (guessAYLoop I)).seq C2) φ1 (c :: rest) = none :=
          Command.step_seq_loopSeq_ndetAssign_cons_neg (t := Tid.guessAY) GuessAY.Vars.aux
            (GuessAY.auxSetBot I) (GuessAY.auxSetBot_nonempty I) φ1 (guessAYLoop I) C2 c rest hc
        have h' := hs19' ▸ h
        injection h' with _ h2
        injection h2 with _ h4
        injection h4 with h5 _
        exact absurd h5 (by rintro ⟨⟩)

theorem guessAY_blockRest_break_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (GuessAY.Vocab I))
    (s : List (GuessAY.Vals I)) (φ : (GuessAY.Vocab I).Store)
    (hfst : φ GuessAY.Vars.fst = Sum.inr (Sum.inr false)) (k : Fin 4)
    (hcnt0 : φ GuessAY.Vars.cnt = Sum.inr (Sum.inl k))
    (haux0 : φ GuessAY.Vars.aux = Sum.inl none) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessAY)) (φ' : (GuessAY.Vocab I).Store)
    (h : Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2, φ) s (N + 20) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAY)) (φ2u : (GuessAY.Vocab I).Store),
      φ2u GuessAY.Vars.fst = Sum.inr (Sum.inr false) ∧
      φ2u GuessAY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
      φ2u GuessAY.Vars.aux = Sum.inl none ∧
      σ = guessAYBlockRestElems I (k, none) ++ σ1 ∧
      Command.runFuel Tid.guessAY (C2, φ2u) s N = (.stuck, σ1, (Command.term, φ'), []) := by
  set φ0 : (GuessAY.Vocab I).Store :=
    Function.update φ GuessAY.Vars.prev (GuessAY.eval I GuessAY.Expr.readCnt φ) with hφ0
  set φ1 : (GuessAY.Vocab I).Store :=
    Function.update φ0 GuessAY.Vars.cnt (GuessAY.eval I GuessAY.Expr.nextCnt φ0) with hφ1
  have hne1 : GuessAY.Vars.fst ≠ GuessAY.Vars.cnt := by decide
  have hne2 : GuessAY.Vars.fst ≠ GuessAY.Vars.prev := by decide
  have hfst1 : φ1 GuessAY.Vars.fst = Sum.inr (Sum.inr false) :=
    (Function.update_of_ne hne1 _ _).trans ((Function.update_of_ne hne2 _ _).trans hfst)
  have hne4 : GuessAY.Vars.aux ≠ GuessAY.Vars.cnt := by decide
  have hne5 : GuessAY.Vars.aux ≠ GuessAY.Vars.prev := by decide
  have haux1 : φ1 GuessAY.Vars.aux = Sum.inl none :=
    (Function.update_of_ne hne4 _ _).trans ((Function.update_of_ne hne5 _ _).trans haux0)
  have hne_prev_cnt : GuessAY.Vars.prev ≠ GuessAY.Vars.cnt := by decide
  have hcnt_φ0 : φ0 GuessAY.Vars.cnt = φ GuessAY.Vars.cnt := rfl
  have hcnt1eq : φ1 GuessAY.Vars.cnt = GuessAY.eval I GuessAY.Expr.nextCnt φ0 :=
    Function.update_self _ _ _
  have hcnt1raw : φ1 GuessAY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt1eq, GuessAY.eval, hcnt_φ0, hcnt0]; rfl
  have hprev0eq : φ0 GuessAY.Vars.prev = GuessAY.eval I GuessAY.Expr.readCnt φ :=
    Function.update_self _ _ _
  have hprev0raw : φ0 GuessAY.Vars.prev = Sum.inr (Sum.inl k) := by
    simp only [hprev0eq, GuessAY.eval, hcnt0]; rfl
  have hprev1raw : φ1 GuessAY.Vars.prev = Sum.inr (Sum.inl k) :=
    (Function.update_of_ne hne_prev_cnt _ _).trans hprev0raw
  have hell1 : (GuessAY.Vocab I).evalV GuessAY.VExpr.cntAuxVal φ1 = Val.cntAux (k + 1) none := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.cntOf, GuessAY.auxOf, hcnt1raw, haux1]; rfl
  have hz1 : (GuessAY.Vocab I).evalV GuessAY.VExpr.cntVal φ1 = Val.cnt (k + 1) := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.cntOf, hcnt1raw]; rfl
  have hprevVal1 : (GuessAY.Vocab I).evalV GuessAY.VExpr.prevVal φ1 = Val.cnt k := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.prevOf, hprev1raw]; rfl
  have hyRest1 : (GuessAY.Vocab I).evalV GuessAY.VExpr.yTagRest φ1
      = Val.yTag (Tid.guessAY, false) none := by
    simp only [GuessAY.Vocab, GuessAY.evalV, GuessAY.auxOf, haux1]; rfl
  have haux1' : (GuessAY.Vocab I).evalB GuessAY.BExpr.isBot φ1 = true := by
    simp [GuessAY.Vocab, GuessAY.evalB, haux1]
  -- Step 1: unwrap the loop guard.
  have hs1 : Command.step Tid.guessAY (guessAYLoop I) φ s =
      some (none, Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I), φ, s) := by
    simp only [guessAYLoop, Command.step, GuessAY.Vocab, GuessAY.evalB, if_true]
  -- Step 2: `prev ← readCnt`.
  have hs2 : Command.step Tid.guessAY (Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessAY.BExpr.isFirst
              (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                    (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                      (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))))
        (guessAYLoop I), φ0, s) := by
    rw [hφ0]
    simp only [GuessAY.loopBody, Command.firstIt, Command.step, GuessAY.Vocab]
    rfl
  -- Step 3: `.seq Command.skip _` elimination.
  have hs3 : Command.step Tid.guessAY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))))
      (guessAYLoop I)) φ0 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessAY.BExpr.isFirst
              (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                    (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                      (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I)))))
        (guessAYLoop I), φ0, s) := by
    simp only [Command.step]
    rfl
  -- Step 4: `cnt ← nextCnt`.
  have hs4 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq (Command.assign GuessAY.Vars.cnt GuessAY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
      (guessAYLoop I)) φ0 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
        (guessAYLoop I), φ1, s) := by
    rw [hφ1]
    simp only [Command.step, GuessAY.Vocab]
  -- Step 5: `.seq Command.skip _` elimination.
  have hs5 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I)))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.ite GuessAY.BExpr.isFirst
            (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                  (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 6: `Command.ite isFirst` resolves false (`hfst1`), entering ELSE.
  have hs6 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.ite GuessAY.BExpr.isFirst
          (Command.seq (Command.assign GuessAY.Vars.fst GuessAY.Expr.fstFalse)
            (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.write Loc.zAy'y GuessAY.VExpr.cntVal))))
          (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                  (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                  (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp [Command.step, GuessAY.Vocab, GuessAY.evalB, hfst1]
  -- Step 7: `w(yA, yTagRest)`.
  have hs7 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.yA GuessAY.VExpr.yTagRest)
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.yA
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.yTagRest φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                    (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 8: `.seq Command.skip _` elimination.
  have hs8 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 9: `w(ellAyx, cntAuxVal)`.
  have hs9 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.ellAyx GuessAY.VExpr.cntAuxVal)
          (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
              (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.ellAyx
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.cntAuxVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                  (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 10: `.seq Command.skip _` elimination.
  have hs10 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
              (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
              (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 11: `w(zAy'y, cntVal)`.
  have hs11 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.zAy'y GuessAY.VExpr.cntVal)
          (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
            (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessAY Loc.zAy'y
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.cntVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
                (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 12: `.seq Command.skip _` elimination.
  have hs12 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
            (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
            (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 13: `r(zAxy, prevVal)`.
  have hs13 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.read Loc.zAxy GuessAY.VExpr.prevVal)
          (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.rd Tid.guessAY Loc.zAxy
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.prevVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 14: `.seq Command.skip _` elimination.
  have hs14 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip (Command.read Loc.zAyy' GuessAY.VExpr.prevVal))
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)
          (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
              (GuessAY.auxSetBot_nonempty I))))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 15: `r(zAyy', prevVal)`.
  have hs15 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        (Command.read Loc.zAyy' GuessAY.VExpr.prevVal)
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (some ⟨EventLabel.rd Tid.guessAY Loc.zAyy'
        ((GuessAY.Vocab I).evalV GuessAY.VExpr.prevVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            Command.skip
            (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
                (GuessAY.auxSetBot_nonempty I))))
          (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 16: `.seq Command.skip _` elimination.
  have hs16 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq
        Command.skip
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I))))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I)))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 17: `if aux = ⊥ then break endif` resolves true (`haux1'`).
  have hs17 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq (Command.ite GuessAY.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
          (GuessAY.auxSetBot_nonempty I)))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq Command.brk
          (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
            (GuessAY.auxSetBot_nonempty I)))
        (guessAYLoop I), φ1, s) := by
    simp only [Command.step, haux1']
    rfl
  -- Step 18: `.seq Command.brk _` collapses (loop propagates the break).
  have hs18 : Command.step Tid.guessAY (Command.loopSeq
      (Command.seq Command.brk
        (Command.ndetAssign GuessAY.Vars.aux (GuessAY.auxSetBot I)
          (GuessAY.auxSetBot_nonempty I)))
      (guessAYLoop I)) φ1 s =
      some (none, Command.loopSeq Command.brk (guessAYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 19: `loopSeq brk _` exits to bare `skip`.
  have hs19 : Command.step Tid.guessAY (Command.loopSeq Command.brk (guessAYLoop I)) φ1 s =
      some (none, Command.skip, φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 20: `.seq skip C2` steps to `C2`.
  have hs20 : Command.step Tid.guessAY (Command.seq Command.skip C2) φ1 s =
      some (none, C2, φ1, s) := by
    simp only [Command.step]
    rfl
  have hrs1 : Command.RunStep Tid.guessAY s none (guessAYLoop I, φ) s
      (Command.loopSeq (GuessAY.loopBody I) (guessAYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  have hrs19 := Command.step_sound _ _ _ _ _ _ _ hs19
  have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
  simp only [hw19] at h
  simp only [hs20] at h
  rw [hyRest1, hell1, hz1, hprevVal1] at h
  injection h with hh1 hrest1
  injection hrest1 with hh2 hrest2
  injection hrest2 with hh3 hh4
  refine ⟨(Command.runFuel Tid.guessAY (C2, φ1) s N).2.1, φ1, hfst1, hcnt1raw, haux1, hh2.symm,
    Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩

theorem guessAY_chain_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (GuessAY.Vals I)), s.length = n →
      ∀ (C2 : Command (domainOf I) (GuessAY.Vocab I)) (φ : (GuessAY.Vocab I).Store)
        (_hfst : φ GuessAY.Vars.fst = Sum.inr (Sum.inr false))
        (k0 : Fin 4) (_hcnt0 : φ GuessAY.Vars.cnt = Sum.inr (Sum.inl k0))
        (w0 : Fin I.n) (_haux0 : φ GuessAY.Vars.aux = Sum.inl (some w0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAY))
        (φ' : (GuessAY.Vocab I).Store),
        Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (ws : List (Fin I.n)) (rest0 : List (GuessAY.Vals I))
          (kws : List (Fin 4 × Option (Fin I.n))) (φ2u : (GuessAY.Vocab I).Store)
          (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAY)),
          s = ws.map (fun w => (Sum.inl (some w) : GuessAY.Vals I)) ++
            Sum.inl none :: rest0 ∧
          kws.length = ws.length + 2 ∧
          (∀ i, i < kws.length →
            ∃ w, kws[i]? = some (⟨(k0.val + i) % 4, by omega⟩, w)) ∧
          σ = kws.flatMap (guessAYBlockRestElems I) ++ σ1 ∧
          Command.runFuel Tid.guessAY (C2, φ2u) rest0 N =
            (.stuck, σ1, (Command.term, φ'), []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen C2 φ hfst k0 hcnt0 w0 haux0 N σ φ' h
    have h20 := Command.runFuel_stuck_stable h 20
    obtain ⟨w', rest, σ1, hseq, hσeq, φ2u, hfst2, hcnt2, haux2, h2⟩ :=
      guessAY_blockRest_continue_step_inv I C2 s φ hfst k0 hcnt0 w0 haux0 N σ φ' h20
    subst hseq
    cases w' with
    | none =>
        have h2' := Command.runFuel_stuck_stable h2 20
        obtain ⟨σ1', φ3u, hfst3, hcnt3, haux3, hσ1eq, h3⟩ :=
          guessAY_blockRest_break_step_inv I C2 rest φ2u hfst2 (k0 + 1) hcnt2 haux2 N σ1 φ' h2'
        refine ⟨[], rest, [(k0, some w0), (k0 + 1, none)], φ3u, σ1', rfl, rfl, ?_, ?_, h3⟩
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · refine ⟨some w0, ?_⟩
            simp only [List.getElem?_cons_zero]
            congr 2
            apply Fin.ext
            have hk0 := k0.isLt
            simp only [Nat.add_zero]
            omega
          · refine ⟨none, ?_⟩
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
            congr 2
        · rw [hσeq, hσ1eq]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | some w1 =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inl (some w1) :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        obtain ⟨ws', rest0, kws', φ2u', σ1', hseq', hlen', hval', hσeq', h3⟩ :=
          ih rest.length hrest_len rest rfl C2 φ2u hfst2 (k0 + 1) hcnt2 w1 haux2 N σ1 φ' h2
        refine ⟨w1 :: ws', rest0, (k0, some w0) :: kws', φ2u', σ1',
          by simp [hseq'], by simp [hlen'], ?_, ?_, h3⟩
        · intro i hi
          cases i with
          | zero =>
              refine ⟨some w0, ?_⟩
              simp only [List.getElem?_cons_zero]
              congr 2
              apply Fin.ext
              have hk0 := k0.isLt
              simp only [Nat.add_zero]
              omega
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              obtain ⟨w, hw⟩ := hval' i hi'
              refine ⟨w, ?_⟩
              simp only [List.getElem?_cons_succ]
              rw [hw]
              congr 2
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · rw [hσeq, hσeq']
          simp only [List.flatMap_cons, List.append_assoc]

theorem guessAY_shape_inv (I : PCPInstance) {s : List (GuessAY.Vals I)}
    {φ' : (GuessAY.Vocab I).Store} {cLast : Config (domainOf I) (GuessAY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.guessAY)}
    (hrun : Command.Run Tid.guessAY s
      (GuessAY.program I, (GuessAY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : Fin I.n) (js : List (Fin I.n)) (kws : List (Fin 4 × Option (Fin I.n))),
      s = Sum.inl (some v0) ::
        (js.map (fun w => (Sum.inl (some w) : GuessAY.Vals I)) ++ [Sum.inl none]) ∧
      kws.length = js.length + 1 ∧
      (∀ i, i < kws.length → ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w)) ∧
      σ = guessAYBlockWord I v0 kws := by
  have hterm_stuck : ∀ (φt : (GuessAY.Vocab I).Store) (r : List (GuessAY.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.guessAY)) (φt' : (GuessAY.Vocab I).Store),
      Command.runFuel Tid.guessAY (Command.term, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      r = [] ∧ σt = [] ∧ φt' = φt := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        exact absurd (congrArg Prod.fst hm) (by rintro ⟨⟩)
    | succ m =>
        simp only [Command.runFuel, Command.step] at hm
        injection hm with hh1 hrest
        injection hrest with hh2 hrest2
        injection hrest2 with hh3 hh4
        exact ⟨hh4, hh2.symm, (congrArg Prod.snd hh3).symm⟩
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := guessAY_lead_step_inv I s n σ φ' hn2
  have hfst1 : Function.update ((GuessAY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) GuessAY.Vars.aux (Sum.inl (some v0))
      GuessAY.Vars.fst = Sum.inr (Sum.inr true) := by
    have hne : GuessAY.Vars.fst ≠ GuessAY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have hcnt1 : Function.update ((GuessAY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) GuessAY.Vars.aux (Sum.inl (some v0))
      GuessAY.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne : GuessAY.Vars.cnt ≠ GuessAY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have h18 := Command.runFuel_stuck_stable h2 18
  obtain ⟨w, rest2, σ1, hs2, hσ2, φ3, hfst3, hcnt3, haux3, h3⟩ :=
    guessAY_block0_step_inv I Command.term rest _ hfst1 hcnt1 v0 (Function.update_self _ _ _)
      n σ φ' h18
  cases w with
  | none =>
      have h20 := Command.runFuel_stuck_stable h3 20
      obtain ⟨σ1', φ4, hfst4, hcnt4, haux4, hσ1eq, h4⟩ :=
        guessAY_blockRest_break_step_inv I Command.term rest2 φ3 hfst3 1 hcnt3 haux3 n σ1 φ' h20
      obtain ⟨hrest2nil, hσ1'nil, hφ4eq⟩ := hterm_stuck φ4 rest2 n σ1' φ' h4
      refine ⟨v0, [], [(1, none)], ?_, rfl, ?_, ?_⟩
      · simp [hs, hs2, hrest2nil]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨none, rfl⟩
      · simp [hσ2, hσ1eq, hσ1'nil, guessAYBlockWord, List.flatMap_cons, List.flatMap_nil]
  | some w1 =>
      obtain ⟨ws, rest0, kws, φ2u, σ1', hseq', hlen', hval', hσeq', h4⟩ :=
        guessAY_chain_shape_inv I rest2.length rest2 rfl Command.term φ3 hfst3 1 hcnt3 w1 haux3
          n σ1 φ' h3
      obtain ⟨hrest0nil, hσ1'nil, hφ2ueq⟩ := hterm_stuck φ2u rest0 n σ1' φ' h4
      refine ⟨v0, w1 :: ws, kws, ?_, by omega, ?_, ?_⟩
      · rw [hs, hs2, hseq', hrest0nil]
        simp
      · intro i hi
        have := hval' i hi
        simpa using this
      · rw [hσ2, hσeq', hσ1'nil, List.append_nil]
        rfl

/-- `guessAY_chain_shape_inv`, with the second components of `kws` determined
(as `checkX_chain_shape_inv_vals`). -/
theorem guessAY_chain_shape_inv_vals (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (GuessAY.Vals I)), s.length = n →
      ∀ (C2 : Command (domainOf I) (GuessAY.Vocab I)) (φ : (GuessAY.Vocab I).Store)
        (_hfst : φ GuessAY.Vars.fst = Sum.inr (Sum.inr false))
        (k0 : Fin 4) (_hcnt0 : φ GuessAY.Vars.cnt = Sum.inr (Sum.inl k0))
        (w0 : Fin I.n) (_haux0 : φ GuessAY.Vars.aux = Sum.inl (some w0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessAY))
        (φ' : (GuessAY.Vocab I).Store),
        Command.runFuel Tid.guessAY ((guessAYLoop I).seq C2, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (ws : List (Fin I.n)) (rest0 : List (GuessAY.Vals I))
          (kws : List (Fin 4 × Option (Fin I.n))) (φ2u : (GuessAY.Vocab I).Store)
          (σ1 : Word (ThreadLabel (domainOf I) Tid.guessAY)),
          s = ws.map (fun w => (Sum.inl (some w) : GuessAY.Vals I)) ++
            Sum.inl none :: rest0 ∧
          kws.length = ws.length + 2 ∧
          (∀ i, i < kws.length →
            ∃ w, kws[i]? = some (⟨(k0.val + i) % 4, by omega⟩, w)) ∧
          (∀ i, i < kws.length → kws[i]?.map Prod.snd = some ((w0 :: ws)[i]?)) ∧
          σ = kws.flatMap (guessAYBlockRestElems I) ++ σ1 ∧
          Command.runFuel Tid.guessAY (C2, φ2u) rest0 N =
            (.stuck, σ1, (Command.term, φ'), []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen C2 φ hfst k0 hcnt0 w0 haux0 N σ φ' h
    have h20 := Command.runFuel_stuck_stable h 20
    obtain ⟨w', rest, σ1, hseq, hσeq, φ2u, hfst2, hcnt2, haux2, h2⟩ :=
      guessAY_blockRest_continue_step_inv I C2 s φ hfst k0 hcnt0 w0 haux0 N σ φ' h20
    subst hseq
    cases w' with
    | none =>
        have h2' := Command.runFuel_stuck_stable h2 20
        obtain ⟨σ1', φ3u, hfst3, hcnt3, haux3, hσ1eq, h3⟩ :=
          guessAY_blockRest_break_step_inv I C2 rest φ2u hfst2 (k0 + 1) hcnt2 haux2 N σ1 φ' h2'
        refine ⟨[], rest, [(k0, some w0), (k0 + 1, none)], φ3u, σ1', rfl, rfl, ?_, ?_, ?_, h3⟩
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · refine ⟨some w0, ?_⟩
            simp only [List.getElem?_cons_zero]
            congr 2
            apply Fin.ext
            have hk0 := k0.isLt
            simp only [Nat.add_zero]
            omega
          · refine ⟨none, ?_⟩
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
            congr 2
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · simp
          · simp
        · rw [hσeq, hσ1eq]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | some w1 =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inl (some w1) :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        obtain ⟨ws', rest0, kws', φ2u', σ1', hseq', hlen', hval', hval2', hσeq', h3⟩ :=
          ih rest.length hrest_len rest rfl C2 φ2u hfst2 (k0 + 1) hcnt2 w1 haux2 N σ1 φ' h2
        refine ⟨w1 :: ws', rest0, (k0, some w0) :: kws', φ2u', σ1',
          by simp [hseq'], by simp [hlen'], ?_, ?_, ?_, h3⟩
        · intro i hi
          cases i with
          | zero =>
              refine ⟨some w0, ?_⟩
              simp only [List.getElem?_cons_zero]
              congr 2
              apply Fin.ext
              have hk0 := k0.isLt
              simp only [Nat.add_zero]
              omega
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              obtain ⟨w, hw⟩ := hval' i hi'
              refine ⟨w, ?_⟩
              simp only [List.getElem?_cons_succ]
              rw [hw]
              congr 2
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · intro i hi
          cases i with
          | zero => simp
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              have := hval2' i hi'
              simpa using this
        · rw [hσeq, hσeq']
          simp only [List.flatMap_cons, List.append_assoc]

/-- `guessAY_shape_inv`, with the second components of `kws` determined (as
`checkX_shape_inv_vals`). -/
theorem guessAY_shape_inv_vals (I : PCPInstance) {s : List (GuessAY.Vals I)}
    {φ' : (GuessAY.Vocab I).Store} {cLast : Config (domainOf I) (GuessAY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.guessAY)}
    (hrun : Command.Run Tid.guessAY s
      (GuessAY.program I, (GuessAY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : Fin I.n) (js : List (Fin I.n)) (kws : List (Fin 4 × Option (Fin I.n))),
      s = Sum.inl (some v0) ::
        (js.map (fun w => (Sum.inl (some w) : GuessAY.Vals I)) ++ [Sum.inl none]) ∧
      kws.length = js.length + 1 ∧
      (∀ i, i < kws.length → ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w)) ∧
      (∀ i, i < kws.length → kws[i]?.map Prod.snd = some (js[i]?)) ∧
      σ = guessAYBlockWord I v0 kws := by
  have hterm_stuck : ∀ (φt : (GuessAY.Vocab I).Store) (r : List (GuessAY.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.guessAY)) (φt' : (GuessAY.Vocab I).Store),
      Command.runFuel Tid.guessAY (Command.term, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      r = [] ∧ σt = [] ∧ φt' = φt := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        exact absurd (congrArg Prod.fst hm) (by rintro ⟨⟩)
    | succ m =>
        simp only [Command.runFuel, Command.step] at hm
        injection hm with hh1 hrest
        injection hrest with hh2 hrest2
        injection hrest2 with hh3 hh4
        exact ⟨hh4, hh2.symm, (congrArg Prod.snd hh3).symm⟩
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := guessAY_lead_step_inv I s n σ φ' hn2
  have hfst1 : Function.update ((GuessAY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) GuessAY.Vars.aux (Sum.inl (some v0))
      GuessAY.Vars.fst = Sum.inr (Sum.inr true) := by
    have hne : GuessAY.Vars.fst ≠ GuessAY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have hcnt1 : Function.update ((GuessAY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) GuessAY.Vars.aux (Sum.inl (some v0))
      GuessAY.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne : GuessAY.Vars.cnt ≠ GuessAY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have h18 := Command.runFuel_stuck_stable h2 18
  obtain ⟨w, rest2, σ1, hs2, hσ2, φ3, hfst3, hcnt3, haux3, h3⟩ :=
    guessAY_block0_step_inv I Command.term rest _ hfst1 hcnt1 v0 (Function.update_self _ _ _)
      n σ φ' h18
  cases w with
  | none =>
      have h20 := Command.runFuel_stuck_stable h3 20
      obtain ⟨σ1', φ4, hfst4, hcnt4, haux4, hσ1eq, h4⟩ :=
        guessAY_blockRest_break_step_inv I Command.term rest2 φ3 hfst3 1 hcnt3 haux3 n σ1 φ' h20
      obtain ⟨hrest2nil, hσ1'nil, hφ4eq⟩ := hterm_stuck φ4 rest2 n σ1' φ' h4
      refine ⟨v0, [], [(1, none)], ?_, rfl, ?_, ?_, ?_⟩
      · simp [hs, hs2, hrest2nil]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨none, rfl⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp
      · simp [hσ2, hσ1eq, hσ1'nil, guessAYBlockWord, List.flatMap_cons, List.flatMap_nil]
  | some w1 =>
      obtain ⟨ws, rest0, kws, φ2u, σ1', hseq', hlen', hval', hval2', hσeq', h4⟩ :=
        guessAY_chain_shape_inv_vals I rest2.length rest2 rfl Command.term φ3 hfst3 1 hcnt3 w1 haux3
          n σ1 φ' h3
      obtain ⟨hrest0nil, hσ1'nil, hφ2ueq⟩ := hterm_stuck φ2u rest0 n σ1' φ' h4
      refine ⟨v0, w1 :: ws, kws, ?_, by omega, ?_, ?_, ?_⟩
      · rw [hs, hs2, hseq', hrest0nil]
        simp
      · intro i hi
        have := hval' i hi
        simpa using this
      · intro i hi
        have := hval2' i hi
        simpa using this
      · rw [hσ2, hσeq', hσ1'nil, List.append_nil]
        rfl

/-! ## `GuessBY`

As for `GuessAY`, with `α` replaced by `β`. -/

theorem GuessBY.mem_auxSet_iff {I : PCPInstance} (c : GuessBY.Vals I) :
    c ∈ GuessBY.auxSet I ↔ ∃ v, c = Sum.inl (some v) := by
  unfold GuessBY.auxSet
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, hv.symm⟩, fun ⟨v, hv⟩ => ⟨v, hv.symm⟩⟩

/-- The converse of `GuessBY.program`'s leading `NDet({1,…,n})` draw. -/
theorem guessBY_lead_step_inv (I : PCPInstance) (s : List (GuessBY.Vals I)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessBY)) (φ' : (GuessBY.Vocab I).Store)
    (h : Command.runFuel Tid.guessBY (GuessBY.program I,
      (GuessBY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none)) s (N + 2) = (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (v0 : Fin I.n) (rest : List (GuessBY.Vals I)),
      s = Sum.inl (some v0) :: rest ∧
      Command.runFuel Tid.guessBY
        ((guessBYLoop I).seq Command.term,
          Function.update ((GuessBY.Vocab I).mkStore (fun v => match v with
            | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
            | .fst => some (Sum.inr (Sum.inr true))
            | _ => none) (Sum.inl none)) GuessBY.Vars.aux (Sum.inl (some v0))) rest N =
        (.stuck, σ, (Command.term, φ'), []) := by
  cases s with
  | nil =>
      simp only [Command.runFuel, Command.step, GuessBY.program] at h
      have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
      exact absurd h2 (by rintro ⟨⟩)
  | cons c rest =>
      simp only [Command.runFuel, Command.step, GuessBY.program] at h
      split_ifs at h with hc
      · obtain ⟨v0, rfl⟩ := (GuessBY.mem_auxSet_iff c).mp hc
        simp only [Command.step, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3, h4⟩ := h
        refine ⟨v0, rest, rfl, ?_⟩
        change Command.runFuel Tid.guessBY
            ((Command.whileLoop GuessBY.BExpr.tt (GuessBY.loopBody I)).seq Command.term,
              Function.update ((GuessBY.Vocab I).mkStore (fun v => match v with
                | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
                | .fst => some (Sum.inr (Sum.inr true))
                | _ => none) (Sum.inl none)) GuessBY.Vars.aux (Sum.inl (some v0))) rest N = _
        exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
      · have h2 := congrArg Prod.fst (congrArg Prod.snd (congrArg Prod.snd h))
        exact absurd h2 (by rintro ⟨⟩)


theorem GuessBY.mem_auxSetBot_iff {I : PCPInstance} (c : GuessBY.Vals I) :
    c ∈ GuessBY.auxSetBot I ↔ ∃ w : Option (Fin I.n), c = Sum.inl w := by
  unfold GuessBY.auxSetBot
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, hw.symm⟩, fun ⟨w, hw⟩ => ⟨w, hw.symm⟩⟩

theorem guessBY_block0_step_inv (I : PCPInstance) (C2 : Command (domainOf I) (GuessBY.Vocab I))
    (s : List (GuessBY.Vals I)) (φ : (GuessBY.Vocab I).Store)
    (hfst : φ GuessBY.Vars.fst = Sum.inr (Sum.inr true))
    (hcnt0 : φ GuessBY.Vars.cnt = Sum.inr (Sum.inl 0))
    (v0 : Fin I.n) (haux0 : φ GuessBY.Vars.aux = Sum.inl (some v0)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessBY)) (φ' : (GuessBY.Vocab I).Store)
    (h : Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2, φ) s (N + 18) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (w : Option (Fin I.n)) (rest : List (GuessBY.Vals I))
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBY)),
      s = Sum.inl w :: rest ∧
      σ = guessBYBlock0Elems I v0 ++ σ1 ∧
      ∃ (φ3 : (GuessBY.Vocab I).Store),
        φ3 GuessBY.Vars.fst = Sum.inr (Sum.inr false) ∧
        φ3 GuessBY.Vars.cnt = Sum.inr (Sum.inl 1) ∧
        φ3 GuessBY.Vars.aux = Sum.inl w ∧
        Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2, φ3) rest N =
          (.stuck, σ1, (Command.term, φ'), []) := by
  set φ0 : (GuessBY.Vocab I).Store :=
    Function.update φ GuessBY.Vars.prev (GuessBY.eval I GuessBY.Expr.readCnt φ) with hφ0
  set φ1 : (GuessBY.Vocab I).Store :=
    Function.update φ0 GuessBY.Vars.cnt (GuessBY.eval I GuessBY.Expr.nextCnt φ0) with hφ1
  have hne1 : GuessBY.Vars.fst ≠ GuessBY.Vars.cnt := by decide
  have hne2 : GuessBY.Vars.fst ≠ GuessBY.Vars.prev := by decide
  have hfst1 : φ1 GuessBY.Vars.fst = Sum.inr (Sum.inr true) :=
    (Function.update_of_ne hne1 _ _).trans ((Function.update_of_ne hne2 _ _).trans hfst)
  set φ2 : (GuessBY.Vocab I).Store :=
    Function.update φ1 GuessBY.Vars.fst (GuessBY.eval I GuessBY.Expr.fstFalse φ1) with hφ2
  have hne3 : GuessBY.Vars.aux ≠ GuessBY.Vars.fst := by decide
  have hne4 : GuessBY.Vars.aux ≠ GuessBY.Vars.cnt := by decide
  have hne5 : GuessBY.Vars.aux ≠ GuessBY.Vars.prev := by decide
  have haux2 : φ2 GuessBY.Vars.aux = Sum.inl (some v0) :=
    (Function.update_of_ne hne3 _ _).trans ((Function.update_of_ne hne4 _ _).trans
      ((Function.update_of_ne hne5 _ _).trans haux0))
  have hcnt_φ0 : φ0 GuessBY.Vars.cnt = φ GuessBY.Vars.cnt := rfl
  have hcnt1eq : φ1 GuessBY.Vars.cnt = GuessBY.eval I GuessBY.Expr.nextCnt φ0 :=
    Function.update_self _ _ _
  have hcnt1raw : φ1 GuessBY.Vars.cnt = Sum.inr (Sum.inl 1) := by
    simp only [hcnt1eq, GuessBY.eval, hcnt_φ0, hcnt0]; rfl
  have hcnt2raw : φ2 GuessBY.Vars.cnt = Sum.inr (Sum.inl 1) :=
    (Function.update_of_ne hne1.symm _ _).trans hcnt1raw
  have hell2 : (GuessBY.Vocab I).evalV GuessBY.VExpr.cntAuxVal φ2 = Val.cntAux 1 (some v0) := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.cntOf, GuessBY.auxOf, hcnt2raw, haux2]; rfl
  have hz2 : (GuessBY.Vocab I).evalV GuessBY.VExpr.cntVal φ2 = Val.cnt 1 := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.cntOf, hcnt2raw]; rfl
  have hy2 : (GuessBY.Vocab I).evalV GuessBY.VExpr.yTagFirst φ2 = Val.yTag (Tid.guessBY, true) (some v0) := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.auxOf, haux2]; rfl
  -- Step 1: unwrap the loop guard (constant `tt`).
  have hs1 : Command.step Tid.guessBY (guessBYLoop I) φ s =
      some (none, Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I), φ, s) := by
    simp only [guessBYLoop, Command.step, GuessBY.Vocab, GuessBY.evalB, if_true]
  -- Step 2: `prev ← readCnt`.
  have hs2 : Command.step Tid.guessBY (Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessBY.BExpr.isFirst
              (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                    (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                      (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))))
        (guessBYLoop I), φ0, s) := by
    rw [hφ0]
    simp only [GuessBY.loopBody, Command.firstIt, Command.step, GuessBY.Vocab]
    rfl
  -- Step 3: `.seq Command.skip _` elimination.
  have hs3 : Command.step Tid.guessBY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))))
      (guessBYLoop I)) φ0 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessBY.BExpr.isFirst
              (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                    (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                      (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I)))))
        (guessBYLoop I), φ0, s) := by
    simp only [Command.step]
    rfl
  -- Step 4: `cnt ← nextCnt`.
  have hs4 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
      (guessBYLoop I)) φ0 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
        (guessBYLoop I), φ1, s) := by
    rw [hφ1]
    simp only [Command.step, GuessBY.Vocab]
  -- Step 5: `.seq Command.skip _` elimination.
  have hs5 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 6: `Command.ite isFirst` resolves true (`hfst1`).
  have hs6 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.ite GuessBY.BExpr.isFirst
          (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
          (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                  (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step, GuessBY.Vocab, GuessBY.evalB, hfst1, if_true]
  -- Step 7: `fst ← False`.
  have hs7 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
          (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
            (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
              (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq Command.skip
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ2, s) := by
    rw [hφ2]
    simp only [Command.step, GuessBY.Vocab]
  -- Step 8: `.seq Command.skip _` elimination.
  have hs8 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
            (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
              (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
            (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
              (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 9: `w(yB, yTagFirst)`.
  have hs9 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.yB
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.yTagFirst φ2), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 10: `.seq Command.skip _` elimination.
  have hs10 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 11: `w(ellAyx, cntAuxVal)`.
  have hs11 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
          (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.ellByx
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.cntAuxVal φ2), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 12: `.seq Command.skip _` elimination.
  have hs12 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 13: `w(zAy'y, cntVal)`.
  have hs13 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ2 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.zBy'y
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.cntVal φ2), rfl⟩,
        Command.loopSeq
          (Command.seq
            Command.skip
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 14: `.seq Command.skip _` elimination.
  have hs14 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        Command.skip
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I)))
        (guessBYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Step 15: `if aux = ⊥ then break endif` resolves false (`haux2`).
  have hs15 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
          (GuessBY.auxSetBot_nonempty I)))
      (guessBYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I)))
        (guessBYLoop I), φ2, s) := by
    simp [Command.step, GuessBY.Vocab, GuessBY.evalB, haux2]
  -- Step 16: `.seq Command.skip _` elimination (before the trailing `NDet` draw).
  have hs16 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq Command.skip
        (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
          (GuessBY.auxSetBot_nonempty I)))
      (guessBYLoop I)) φ2 s =
      some (none, Command.loopSeq
        (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
          (GuessBY.auxSetBot_nonempty I))
        (guessBYLoop I), φ2, s) := by
    simp only [Command.step]
    rfl
  -- Transport steps 1-16 (which do not depend on the resolution) into `h`.
  have hrs1 : Command.RunStep Tid.guessBY s none (guessBYLoop I, φ) s
      (Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  cases s with
  | nil =>
      have hnone : Command.step Tid.guessBY
          ((Command.loopSeq (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I)) (guessBYLoop I)).seq C2) φ2 [] = none :=
        Command.step_seq_loopSeq_ndetAssign_nil _ _ _ _ _ _
      have h' := hnone ▸ h
      injection h' with _ h2
      injection h2 with _ h4
      injection h4 with h5 _
      exact absurd h5 (by rintro ⟨⟩)
  | cons c rest =>
      rcases Classical.em (c ∈ GuessBY.auxSetBot I) with hc | hc
      · obtain ⟨w, rfl⟩ := (GuessBY.mem_auxSetBot_iff c).mp hc
        have hcpos := Command.step_ndetAssign_cons_pos (t := Tid.guessBY) GuessBY.Vars.aux
          (GuessBY.auxSetBot I) (GuessBY.auxSetBot_nonempty I) φ2 (Sum.inl w) rest hc
        have hrs17a : Command.RunStep Tid.guessBY (Sum.inl w :: rest) none
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I), φ2) rest
            (Command.skip, Function.update φ2 GuessBY.Vars.aux (Sum.inl w)) :=
          Command.step_sound _ _ _ _ _ _ _ hcpos
        have hrs17 := Command.RunStep.loopCongr (C2 := guessBYLoop I) hrs17a
        have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
        have h := hw17 ▸ h
        dsimp only at h
        have hrs18 : Command.RunStep Tid.guessBY rest none
            (Command.loopSeq Command.skip (guessBYLoop I),
              Function.update φ2 GuessBY.Vars.aux (Sum.inl w)) rest
            (guessBYLoop I, Function.update φ2 GuessBY.Vars.aux (Sum.inl w)) :=
          Command.RunStep.loopSkip
        have hw18 : Command.step Tid.guessBY
            ((Command.loopSeq Command.skip (guessBYLoop I)).seq C2)
            (Function.update φ2 GuessBY.Vars.aux (Sum.inl w)) rest =
            some (none, (guessBYLoop I).seq C2,
              Function.update φ2 GuessBY.Vars.aux (Sum.inl w), rest) :=
          Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
        have h := hw18 ▸ h
        have hne_fst_aux2 : GuessBY.Vars.fst ≠ GuessBY.Vars.aux := by decide
        have hne_cnt_aux2 : GuessBY.Vars.cnt ≠ GuessBY.Vars.aux := by decide
        have hfst2 : φ2 GuessBY.Vars.fst = Sum.inr (Sum.inr false) := by
          rw [hφ2]; exact Function.update_self _ _ _
        rw [hy2, hell2, hz2] at h
        injection h with hh1 hrest1
        injection hrest1 with hh2 hrest2
        injection hrest2 with hh3 hh4
        refine ⟨w, rest,
          (Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2,
            Function.update φ2 GuessBY.Vars.aux (Sum.inl w)) rest N).2.1,
          rfl, hh2.symm, Function.update φ2 GuessBY.Vars.aux (Sum.inl w),
          (Function.update_of_ne hne_fst_aux2 (Sum.inl w) φ2).trans hfst2,
          (Function.update_of_ne hne_cnt_aux2 (Sum.inl w) φ2).trans hcnt2raw,
          Function.update_self _ _ _, Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩
      · exfalso
        have hs17' : Command.step Tid.guessBY
            ((Command.loopSeq
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I)) (guessBYLoop I)).seq C2) φ2 (c :: rest) = none :=
          Command.step_seq_loopSeq_ndetAssign_cons_neg (t := Tid.guessBY) GuessBY.Vars.aux
            (GuessBY.auxSetBot I) (GuessBY.auxSetBot_nonempty I) φ2 (guessBYLoop I) C2 c rest hc
        have h' := hs17' ▸ h
        injection h' with _ h2
        injection h2 with _ h4
        injection h4 with h5 _
        exact absurd h5 (by rintro ⟨⟩)

theorem guessBY_blockRest_continue_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (GuessBY.Vocab I))
    (s : List (GuessBY.Vals I)) (φ : (GuessBY.Vocab I).Store)
    (hfst : φ GuessBY.Vars.fst = Sum.inr (Sum.inr false)) (k : Fin 4)
    (hcnt0 : φ GuessBY.Vars.cnt = Sum.inr (Sum.inl k))
    (v : Fin I.n) (haux0 : φ GuessBY.Vars.aux = Sum.inl (some v)) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessBY)) (φ' : (GuessBY.Vocab I).Store)
    (h : Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2, φ) s (N + 20) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (w : Option (Fin I.n)) (rest : List (GuessBY.Vals I))
      (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBY)),
      s = Sum.inl w :: rest ∧
      σ = guessBYBlockRestElems I (k, some v) ++ σ1 ∧
      ∃ (φ2u : (GuessBY.Vocab I).Store),
        φ2u GuessBY.Vars.fst = Sum.inr (Sum.inr false) ∧
        φ2u GuessBY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
        φ2u GuessBY.Vars.aux = Sum.inl w ∧
        Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2, φ2u) rest N =
          (.stuck, σ1, (Command.term, φ'), []) := by
  set φ0 : (GuessBY.Vocab I).Store :=
    Function.update φ GuessBY.Vars.prev (GuessBY.eval I GuessBY.Expr.readCnt φ) with hφ0
  set φ1 : (GuessBY.Vocab I).Store :=
    Function.update φ0 GuessBY.Vars.cnt (GuessBY.eval I GuessBY.Expr.nextCnt φ0) with hφ1
  have hne1 : GuessBY.Vars.fst ≠ GuessBY.Vars.cnt := by decide
  have hne2 : GuessBY.Vars.fst ≠ GuessBY.Vars.prev := by decide
  have hfst1 : φ1 GuessBY.Vars.fst = Sum.inr (Sum.inr false) :=
    (Function.update_of_ne hne1 _ _).trans ((Function.update_of_ne hne2 _ _).trans hfst)
  have hne4 : GuessBY.Vars.aux ≠ GuessBY.Vars.cnt := by decide
  have hne5 : GuessBY.Vars.aux ≠ GuessBY.Vars.prev := by decide
  have haux1 : φ1 GuessBY.Vars.aux = Sum.inl (some v) :=
    (Function.update_of_ne hne4 _ _).trans ((Function.update_of_ne hne5 _ _).trans haux0)
  have hne_prev_cnt : GuessBY.Vars.prev ≠ GuessBY.Vars.cnt := by decide
  have hcnt_φ0 : φ0 GuessBY.Vars.cnt = φ GuessBY.Vars.cnt := rfl
  have hcnt1eq : φ1 GuessBY.Vars.cnt = GuessBY.eval I GuessBY.Expr.nextCnt φ0 :=
    Function.update_self _ _ _
  have hcnt1raw : φ1 GuessBY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt1eq, GuessBY.eval, hcnt_φ0, hcnt0]; rfl
  have hprev0eq : φ0 GuessBY.Vars.prev = GuessBY.eval I GuessBY.Expr.readCnt φ :=
    Function.update_self _ _ _
  have hprev0raw : φ0 GuessBY.Vars.prev = Sum.inr (Sum.inl k) := by
    simp only [hprev0eq, GuessBY.eval, hcnt0]; rfl
  have hprev1raw : φ1 GuessBY.Vars.prev = Sum.inr (Sum.inl k) :=
    (Function.update_of_ne hne_prev_cnt _ _).trans hprev0raw
  have hell1 : (GuessBY.Vocab I).evalV GuessBY.VExpr.cntAuxVal φ1
      = Val.cntAux (k + 1) (some v) := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.cntOf, GuessBY.auxOf, hcnt1raw, haux1]; rfl
  have hz1 : (GuessBY.Vocab I).evalV GuessBY.VExpr.cntVal φ1 = Val.cnt (k + 1) := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.cntOf, hcnt1raw]; rfl
  have hprevVal1 : (GuessBY.Vocab I).evalV GuessBY.VExpr.prevVal φ1 = Val.cnt k := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.prevOf, hprev1raw]; rfl
  have hyRest1 : (GuessBY.Vocab I).evalV GuessBY.VExpr.yTagRest φ1
      = Val.yTag (Tid.guessBY, false) (some v) := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.auxOf, haux1]; rfl
  -- Step 1: unwrap the loop guard.
  have hs1 : Command.step Tid.guessBY (guessBYLoop I) φ s =
      some (none, Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I), φ, s) := by
    simp only [guessBYLoop, Command.step, GuessBY.Vocab, GuessBY.evalB, if_true]
  -- Step 2: `prev ← readCnt`.
  have hs2 : Command.step Tid.guessBY (Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessBY.BExpr.isFirst
              (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                    (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                      (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))))
        (guessBYLoop I), φ0, s) := by
    rw [hφ0]
    simp only [GuessBY.loopBody, Command.firstIt, Command.step, GuessBY.Vocab]
    rfl
  -- Step 3: `.seq Command.skip _` elimination.
  have hs3 : Command.step Tid.guessBY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))))
      (guessBYLoop I)) φ0 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessBY.BExpr.isFirst
              (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                    (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                      (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I)))))
        (guessBYLoop I), φ0, s) := by
    simp only [Command.step]
    rfl
  -- Step 4: `cnt ← nextCnt`.
  have hs4 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
      (guessBYLoop I)) φ0 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
        (guessBYLoop I), φ1, s) := by
    rw [hφ1]
    simp only [Command.step, GuessBY.Vocab]
  -- Step 5: `.seq Command.skip _` elimination.
  have hs5 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 6: `Command.ite isFirst` resolves false (`hfst1`), entering ELSE.
  have hs6 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.ite GuessBY.BExpr.isFirst
          (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
          (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                  (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                  (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp [Command.step, GuessBY.Vocab, GuessBY.evalB, hfst1]
  -- Step 7: `w(yB, yTagRest)`.
  have hs7 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.yB
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.yTagRest φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 8: `.seq Command.skip _` elimination.
  have hs8 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 9: `w(ellAyx, cntAuxVal)`.
  have hs9 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
          (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
              (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.ellByx
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.cntAuxVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                  (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 10: `.seq Command.skip _` elimination.
  have hs10 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
              (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
              (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 11: `w(zAy'y, cntVal)`.
  have hs11 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
          (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
            (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.zBy'y
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.cntVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 12: `.seq Command.skip _` elimination.
  have hs12 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
            (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
            (Command.read Loc.zByy' GuessBY.VExpr.prevVal))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 13: `r(zAxy, prevVal)`.
  have hs13 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
          (Command.read Loc.zByy' GuessBY.VExpr.prevVal))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.rd Tid.guessBY Loc.zBxy
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.prevVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip (Command.read Loc.zByy' GuessBY.VExpr.prevVal))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 14: `.seq Command.skip _` elimination.
  have hs14 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip (Command.read Loc.zByy' GuessBY.VExpr.prevVal))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.read Loc.zByy' GuessBY.VExpr.prevVal)
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 15: `r(zAyy', prevVal)`.
  have hs15 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.read Loc.zByy' GuessBY.VExpr.prevVal)
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.rd Tid.guessBY Loc.zByy'
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.prevVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            Command.skip
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 16: `.seq Command.skip _` elimination.
  have hs16 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        Command.skip
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I)))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 17: `if aux = ⊥ then break endif` resolves false (`haux1`).
  have hs17 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
          (GuessBY.auxSetBot_nonempty I)))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq Command.skip
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I)))
        (guessBYLoop I), φ1, s) := by
    simp [Command.step, GuessBY.Vocab, GuessBY.evalB, haux1]
  -- Step 18: `.seq Command.skip _` elimination (before the trailing `NDet` draw).
  have hs18 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq Command.skip
        (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
          (GuessBY.auxSetBot_nonempty I)))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
          (GuessBY.auxSetBot_nonempty I))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Bridge steps 1-18 (all resolution-independent) into `h`.
  have hrs1 : Command.RunStep Tid.guessBY s none (guessBYLoop I, φ) s
      (Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  cases s with
  | nil =>
      have hnone : Command.step Tid.guessBY
          ((Command.loopSeq (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I)) (guessBYLoop I)).seq C2) φ1 [] = none :=
        Command.step_seq_loopSeq_ndetAssign_nil _ _ _ _ _ _
      have h' := hnone ▸ h
      injection h' with _ h2
      injection h2 with _ h4
      injection h4 with h5 _
      exact absurd h5 (by rintro ⟨⟩)
  | cons c rest =>
      rcases Classical.em (c ∈ GuessBY.auxSetBot I) with hc | hc
      · obtain ⟨w, rfl⟩ := (GuessBY.mem_auxSetBot_iff c).mp hc
        have hcpos := Command.step_ndetAssign_cons_pos (t := Tid.guessBY) GuessBY.Vars.aux
          (GuessBY.auxSetBot I) (GuessBY.auxSetBot_nonempty I) φ1 (Sum.inl w) rest hc
        have hrs19a : Command.RunStep Tid.guessBY (Sum.inl w :: rest) none
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I), φ1) rest
            (Command.skip, Function.update φ1 GuessBY.Vars.aux (Sum.inl w)) :=
          Command.step_sound _ _ _ _ _ _ _ hcpos
        have hrs19 := Command.RunStep.loopCongr (C2 := guessBYLoop I) hrs19a
        have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
        have h := hw19 ▸ h
        dsimp only at h
        have hrs20 : Command.RunStep Tid.guessBY rest none
            (Command.loopSeq Command.skip (guessBYLoop I),
              Function.update φ1 GuessBY.Vars.aux (Sum.inl w)) rest
            (guessBYLoop I, Function.update φ1 GuessBY.Vars.aux (Sum.inl w)) :=
          Command.RunStep.loopSkip
        have hw20 : Command.step Tid.guessBY
            ((Command.loopSeq Command.skip (guessBYLoop I)).seq C2)
            (Function.update φ1 GuessBY.Vars.aux (Sum.inl w)) rest =
            some (none, (guessBYLoop I).seq C2,
              Function.update φ1 GuessBY.Vars.aux (Sum.inl w), rest) :=
          Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs20)
        have h := hw20 ▸ h
        have hne_fst_aux2 : GuessBY.Vars.fst ≠ GuessBY.Vars.aux := by decide
        have hne_cnt_aux2 : GuessBY.Vars.cnt ≠ GuessBY.Vars.aux := by decide
        rw [hyRest1, hell1, hz1, hprevVal1] at h
        injection h with hh1 hrest1
        injection hrest1 with hh2 hrest2
        injection hrest2 with hh3 hh4
        refine ⟨w, rest,
          (Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2,
            Function.update φ1 GuessBY.Vars.aux (Sum.inl w)) rest N).2.1,
          rfl, hh2.symm, Function.update φ1 GuessBY.Vars.aux (Sum.inl w),
          (Function.update_of_ne hne_fst_aux2 (Sum.inl w) φ1).trans hfst1,
          (Function.update_of_ne hne_cnt_aux2 (Sum.inl w) φ1).trans hcnt1raw,
          Function.update_self _ _ _, Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩
      · exfalso
        have hs19' : Command.step Tid.guessBY
            ((Command.loopSeq
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I)) (guessBYLoop I)).seq C2) φ1 (c :: rest) = none :=
          Command.step_seq_loopSeq_ndetAssign_cons_neg (t := Tid.guessBY) GuessBY.Vars.aux
            (GuessBY.auxSetBot I) (GuessBY.auxSetBot_nonempty I) φ1 (guessBYLoop I) C2 c rest hc
        have h' := hs19' ▸ h
        injection h' with _ h2
        injection h2 with _ h4
        injection h4 with h5 _
        exact absurd h5 (by rintro ⟨⟩)

theorem guessBY_blockRest_break_step_inv (I : PCPInstance)
    (C2 : Command (domainOf I) (GuessBY.Vocab I))
    (s : List (GuessBY.Vals I)) (φ : (GuessBY.Vocab I).Store)
    (hfst : φ GuessBY.Vars.fst = Sum.inr (Sum.inr false)) (k : Fin 4)
    (hcnt0 : φ GuessBY.Vars.cnt = Sum.inr (Sum.inl k))
    (haux0 : φ GuessBY.Vars.aux = Sum.inl none) (N : ℕ)
    (σ : Word (ThreadLabel (domainOf I) Tid.guessBY)) (φ' : (GuessBY.Vocab I).Store)
    (h : Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2, φ) s (N + 20) =
      (.stuck, σ, (Command.term, φ'), [])) :
    ∃ (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBY)) (φ2u : (GuessBY.Vocab I).Store),
      φ2u GuessBY.Vars.fst = Sum.inr (Sum.inr false) ∧
      φ2u GuessBY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) ∧
      φ2u GuessBY.Vars.aux = Sum.inl none ∧
      σ = guessBYBlockRestElems I (k, none) ++ σ1 ∧
      Command.runFuel Tid.guessBY (C2, φ2u) s N = (.stuck, σ1, (Command.term, φ'), []) := by
  set φ0 : (GuessBY.Vocab I).Store :=
    Function.update φ GuessBY.Vars.prev (GuessBY.eval I GuessBY.Expr.readCnt φ) with hφ0
  set φ1 : (GuessBY.Vocab I).Store :=
    Function.update φ0 GuessBY.Vars.cnt (GuessBY.eval I GuessBY.Expr.nextCnt φ0) with hφ1
  have hne1 : GuessBY.Vars.fst ≠ GuessBY.Vars.cnt := by decide
  have hne2 : GuessBY.Vars.fst ≠ GuessBY.Vars.prev := by decide
  have hfst1 : φ1 GuessBY.Vars.fst = Sum.inr (Sum.inr false) :=
    (Function.update_of_ne hne1 _ _).trans ((Function.update_of_ne hne2 _ _).trans hfst)
  have hne4 : GuessBY.Vars.aux ≠ GuessBY.Vars.cnt := by decide
  have hne5 : GuessBY.Vars.aux ≠ GuessBY.Vars.prev := by decide
  have haux1 : φ1 GuessBY.Vars.aux = Sum.inl none :=
    (Function.update_of_ne hne4 _ _).trans ((Function.update_of_ne hne5 _ _).trans haux0)
  have hne_prev_cnt : GuessBY.Vars.prev ≠ GuessBY.Vars.cnt := by decide
  have hcnt_φ0 : φ0 GuessBY.Vars.cnt = φ GuessBY.Vars.cnt := rfl
  have hcnt1eq : φ1 GuessBY.Vars.cnt = GuessBY.eval I GuessBY.Expr.nextCnt φ0 :=
    Function.update_self _ _ _
  have hcnt1raw : φ1 GuessBY.Vars.cnt = Sum.inr (Sum.inl (k + 1)) := by
    simp only [hcnt1eq, GuessBY.eval, hcnt_φ0, hcnt0]; rfl
  have hprev0eq : φ0 GuessBY.Vars.prev = GuessBY.eval I GuessBY.Expr.readCnt φ :=
    Function.update_self _ _ _
  have hprev0raw : φ0 GuessBY.Vars.prev = Sum.inr (Sum.inl k) := by
    simp only [hprev0eq, GuessBY.eval, hcnt0]; rfl
  have hprev1raw : φ1 GuessBY.Vars.prev = Sum.inr (Sum.inl k) :=
    (Function.update_of_ne hne_prev_cnt _ _).trans hprev0raw
  have hell1 : (GuessBY.Vocab I).evalV GuessBY.VExpr.cntAuxVal φ1 = Val.cntAux (k + 1) none := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.cntOf, GuessBY.auxOf, hcnt1raw, haux1]; rfl
  have hz1 : (GuessBY.Vocab I).evalV GuessBY.VExpr.cntVal φ1 = Val.cnt (k + 1) := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.cntOf, hcnt1raw]; rfl
  have hprevVal1 : (GuessBY.Vocab I).evalV GuessBY.VExpr.prevVal φ1 = Val.cnt k := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.prevOf, hprev1raw]; rfl
  have hyRest1 : (GuessBY.Vocab I).evalV GuessBY.VExpr.yTagRest φ1
      = Val.yTag (Tid.guessBY, false) none := by
    simp only [GuessBY.Vocab, GuessBY.evalV, GuessBY.auxOf, haux1]; rfl
  have haux1' : (GuessBY.Vocab I).evalB GuessBY.BExpr.isBot φ1 = true := by
    simp [GuessBY.Vocab, GuessBY.evalB, haux1]
  -- Step 1: unwrap the loop guard.
  have hs1 : Command.step Tid.guessBY (guessBYLoop I) φ s =
      some (none, Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I), φ, s) := by
    simp only [guessBYLoop, Command.step, GuessBY.Vocab, GuessBY.evalB, if_true]
  -- Step 2: `prev ← readCnt`.
  have hs2 : Command.step Tid.guessBY (Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I)) φ s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessBY.BExpr.isFirst
              (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                    (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                      (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))))
        (guessBYLoop I), φ0, s) := by
    rw [hφ0]
    simp only [GuessBY.loopBody, Command.firstIt, Command.step, GuessBY.Vocab]
    rfl
  -- Step 3: `.seq Command.skip _` elimination.
  have hs3 : Command.step Tid.guessBY (Command.loopSeq (Command.seq Command.skip
      (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))))
      (guessBYLoop I)) φ0 s =
      some (none, Command.loopSeq
        (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
          (Command.seq
            (Command.ite GuessBY.BExpr.isFirst
              (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
                (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                  (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                    (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                    (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                      (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I)))))
        (guessBYLoop I), φ0, s) := by
    simp only [Command.step]
    rfl
  -- Step 4: `cnt ← nextCnt`.
  have hs4 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq (Command.assign GuessBY.Vars.cnt GuessBY.Expr.nextCnt)
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
      (guessBYLoop I)) φ0 s =
      some (none, Command.loopSeq (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
        (guessBYLoop I), φ1, s) := by
    rw [hφ1]
    simp only [Command.step, GuessBY.Vocab]
  -- Step 5: `.seq Command.skip _` elimination.
  have hs5 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq Command.skip
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I)))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.ite GuessBY.BExpr.isFirst
            (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
              (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
                (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                  (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 6: `Command.ite isFirst` resolves false (`hfst1`), entering ELSE.
  have hs6 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.ite GuessBY.BExpr.isFirst
          (Command.seq (Command.assign GuessBY.Vars.fst GuessBY.Expr.fstFalse)
            (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagFirst)
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.write Loc.zBy'y GuessBY.VExpr.cntVal))))
          (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                  (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
            (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
              (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                  (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp [Command.step, GuessBY.Vocab, GuessBY.evalB, hfst1]
  -- Step 7: `w(yB, yTagRest)`.
  have hs7 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.yB GuessBY.VExpr.yTagRest)
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.yB
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.yTagRest φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
                (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                  (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                    (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 8: `.seq Command.skip _` elimination.
  have hs8 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
            (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
              (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 9: `w(ellAyx, cntAuxVal)`.
  have hs9 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.ellByx GuessBY.VExpr.cntAuxVal)
          (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
              (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.ellByx
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.cntAuxVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
                (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                  (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 10: `.seq Command.skip _` elimination.
  have hs10 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
              (Command.read Loc.zByy' GuessBY.VExpr.prevVal))))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
            (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
              (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 11: `w(zAy'y, cntVal)`.
  have hs11 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.write Loc.zBy'y GuessBY.VExpr.cntVal)
          (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
            (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.wt Tid.guessBY Loc.zBy'y
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.cntVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip
              (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
                (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 12: `.seq Command.skip _` elimination.
  have hs12 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip
          (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
            (Command.read Loc.zByy' GuessBY.VExpr.prevVal)))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
            (Command.read Loc.zByy' GuessBY.VExpr.prevVal))
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 13: `r(zAxy, prevVal)`.
  have hs13 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq (Command.read Loc.zBxy GuessBY.VExpr.prevVal)
          (Command.read Loc.zByy' GuessBY.VExpr.prevVal))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.rd Tid.guessBY Loc.zBxy
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.prevVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            (Command.seq Command.skip (Command.read Loc.zByy' GuessBY.VExpr.prevVal))
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 14: `.seq Command.skip _` elimination.
  have hs14 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.seq Command.skip (Command.read Loc.zByy' GuessBY.VExpr.prevVal))
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq
          (Command.read Loc.zByy' GuessBY.VExpr.prevVal)
          (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
            (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
              (GuessBY.auxSetBot_nonempty I))))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 15: `r(zAyy', prevVal)`.
  have hs15 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        (Command.read Loc.zByy' GuessBY.VExpr.prevVal)
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (some ⟨EventLabel.rd Tid.guessBY Loc.zByy'
        ((GuessBY.Vocab I).evalV GuessBY.VExpr.prevVal φ1), rfl⟩,
        Command.loopSeq
          (Command.seq
            Command.skip
            (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
              (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
                (GuessBY.auxSetBot_nonempty I))))
          (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 16: `.seq Command.skip _` elimination.
  have hs16 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq
        Command.skip
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I))))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I)))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 17: `if aux = ⊥ then break endif` resolves true (`haux1'`).
  have hs17 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq (Command.ite GuessBY.BExpr.isBot Command.brk Command.skip)
        (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
          (GuessBY.auxSetBot_nonempty I)))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq
        (Command.seq Command.brk
          (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
            (GuessBY.auxSetBot_nonempty I)))
        (guessBYLoop I), φ1, s) := by
    simp only [Command.step, haux1']
    rfl
  -- Step 18: `.seq Command.brk _` collapses (loop propagates the break).
  have hs18 : Command.step Tid.guessBY (Command.loopSeq
      (Command.seq Command.brk
        (Command.ndetAssign GuessBY.Vars.aux (GuessBY.auxSetBot I)
          (GuessBY.auxSetBot_nonempty I)))
      (guessBYLoop I)) φ1 s =
      some (none, Command.loopSeq Command.brk (guessBYLoop I), φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 19: `loopSeq brk _` exits to bare `skip`.
  have hs19 : Command.step Tid.guessBY (Command.loopSeq Command.brk (guessBYLoop I)) φ1 s =
      some (none, Command.skip, φ1, s) := by
    simp only [Command.step]
    rfl
  -- Step 20: `.seq skip C2` steps to `C2`.
  have hs20 : Command.step Tid.guessBY (Command.seq Command.skip C2) φ1 s =
      some (none, C2, φ1, s) := by
    simp only [Command.step]
    rfl
  have hrs1 : Command.RunStep Tid.guessBY s none (guessBYLoop I, φ) s
      (Command.loopSeq (GuessBY.loopBody I) (guessBYLoop I), φ) := Command.step_sound _ _ _ _ _ _ _ hs1
  have hw1 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs1)
  simp only [Command.runFuel, hw1] at h
  have hrs2 := Command.step_sound _ _ _ _ _ _ _ hs2
  have hw2 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs2)
  simp only [hw2] at h
  have hrs3 := Command.step_sound _ _ _ _ _ _ _ hs3
  have hw3 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs3)
  simp only [hw3] at h
  have hrs4 := Command.step_sound _ _ _ _ _ _ _ hs4
  have hw4 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs4)
  simp only [hw4] at h
  have hrs5 := Command.step_sound _ _ _ _ _ _ _ hs5
  have hw5 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs5)
  simp only [hw5] at h
  have hrs6 := Command.step_sound _ _ _ _ _ _ _ hs6
  have hw6 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs6)
  simp only [hw6] at h
  have hrs7 := Command.step_sound _ _ _ _ _ _ _ hs7
  have hw7 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs7)
  simp only [hw7] at h
  have hrs8 := Command.step_sound _ _ _ _ _ _ _ hs8
  have hw8 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs8)
  simp only [hw8] at h
  have hrs9 := Command.step_sound _ _ _ _ _ _ _ hs9
  have hw9 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs9)
  simp only [hw9] at h
  have hrs10 := Command.step_sound _ _ _ _ _ _ _ hs10
  have hw10 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs10)
  simp only [hw10] at h
  have hrs11 := Command.step_sound _ _ _ _ _ _ _ hs11
  have hw11 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs11)
  simp only [hw11] at h
  have hrs12 := Command.step_sound _ _ _ _ _ _ _ hs12
  have hw12 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs12)
  simp only [hw12] at h
  have hrs13 := Command.step_sound _ _ _ _ _ _ _ hs13
  have hw13 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs13)
  simp only [hw13] at h
  have hrs14 := Command.step_sound _ _ _ _ _ _ _ hs14
  have hw14 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs14)
  simp only [hw14] at h
  have hrs15 := Command.step_sound _ _ _ _ _ _ _ hs15
  have hw15 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs15)
  simp only [hw15] at h
  have hrs16 := Command.step_sound _ _ _ _ _ _ _ hs16
  have hw16 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs16)
  simp only [hw16] at h
  have hrs17 := Command.step_sound _ _ _ _ _ _ _ hs17
  have hw17 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs17)
  simp only [hw17] at h
  have hrs18 := Command.step_sound _ _ _ _ _ _ _ hs18
  have hw18 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs18)
  simp only [hw18] at h
  have hrs19 := Command.step_sound _ _ _ _ _ _ _ hs19
  have hw19 := Command.step_complete (Command.RunStep.seqCongr (C2 := C2) hrs19)
  simp only [hw19] at h
  simp only [hs20] at h
  rw [hyRest1, hell1, hz1, hprevVal1] at h
  injection h with hh1 hrest1
  injection hrest1 with hh2 hrest2
  injection hrest2 with hh3 hh4
  refine ⟨(Command.runFuel Tid.guessBY (C2, φ1) s N).2.1, φ1, hfst1, hcnt1raw, haux1, hh2.symm,
    Prod.ext hh1 (Prod.ext rfl (Prod.ext hh3 hh4))⟩

theorem guessBY_chain_shape_inv (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (GuessBY.Vals I)), s.length = n →
      ∀ (C2 : Command (domainOf I) (GuessBY.Vocab I)) (φ : (GuessBY.Vocab I).Store)
        (_hfst : φ GuessBY.Vars.fst = Sum.inr (Sum.inr false))
        (k0 : Fin 4) (_hcnt0 : φ GuessBY.Vars.cnt = Sum.inr (Sum.inl k0))
        (w0 : Fin I.n) (_haux0 : φ GuessBY.Vars.aux = Sum.inl (some w0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBY))
        (φ' : (GuessBY.Vocab I).Store),
        Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (ws : List (Fin I.n)) (rest0 : List (GuessBY.Vals I))
          (kws : List (Fin 4 × Option (Fin I.n))) (φ2u : (GuessBY.Vocab I).Store)
          (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBY)),
          s = ws.map (fun w => (Sum.inl (some w) : GuessBY.Vals I)) ++
            Sum.inl none :: rest0 ∧
          kws.length = ws.length + 2 ∧
          (∀ i, i < kws.length →
            ∃ w, kws[i]? = some (⟨(k0.val + i) % 4, by omega⟩, w)) ∧
          σ = kws.flatMap (guessBYBlockRestElems I) ++ σ1 ∧
          Command.runFuel Tid.guessBY (C2, φ2u) rest0 N =
            (.stuck, σ1, (Command.term, φ'), []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen C2 φ hfst k0 hcnt0 w0 haux0 N σ φ' h
    have h20 := Command.runFuel_stuck_stable h 20
    obtain ⟨w', rest, σ1, hseq, hσeq, φ2u, hfst2, hcnt2, haux2, h2⟩ :=
      guessBY_blockRest_continue_step_inv I C2 s φ hfst k0 hcnt0 w0 haux0 N σ φ' h20
    subst hseq
    cases w' with
    | none =>
        have h2' := Command.runFuel_stuck_stable h2 20
        obtain ⟨σ1', φ3u, hfst3, hcnt3, haux3, hσ1eq, h3⟩ :=
          guessBY_blockRest_break_step_inv I C2 rest φ2u hfst2 (k0 + 1) hcnt2 haux2 N σ1 φ' h2'
        refine ⟨[], rest, [(k0, some w0), (k0 + 1, none)], φ3u, σ1', rfl, rfl, ?_, ?_, h3⟩
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · refine ⟨some w0, ?_⟩
            simp only [List.getElem?_cons_zero]
            congr 2
            apply Fin.ext
            have hk0 := k0.isLt
            simp only [Nat.add_zero]
            omega
          · refine ⟨none, ?_⟩
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
            congr 2
        · rw [hσeq, hσ1eq]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | some w1 =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inl (some w1) :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        obtain ⟨ws', rest0, kws', φ2u', σ1', hseq', hlen', hval', hσeq', h3⟩ :=
          ih rest.length hrest_len rest rfl C2 φ2u hfst2 (k0 + 1) hcnt2 w1 haux2 N σ1 φ' h2
        refine ⟨w1 :: ws', rest0, (k0, some w0) :: kws', φ2u', σ1',
          by simp [hseq'], by simp [hlen'], ?_, ?_, h3⟩
        · intro i hi
          cases i with
          | zero =>
              refine ⟨some w0, ?_⟩
              simp only [List.getElem?_cons_zero]
              congr 2
              apply Fin.ext
              have hk0 := k0.isLt
              simp only [Nat.add_zero]
              omega
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              obtain ⟨w, hw⟩ := hval' i hi'
              refine ⟨w, ?_⟩
              simp only [List.getElem?_cons_succ]
              rw [hw]
              congr 2
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · rw [hσeq, hσeq']
          simp only [List.flatMap_cons, List.append_assoc]

theorem guessBY_shape_inv (I : PCPInstance) {s : List (GuessBY.Vals I)}
    {φ' : (GuessBY.Vocab I).Store} {cLast : Config (domainOf I) (GuessBY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.guessBY)}
    (hrun : Command.Run Tid.guessBY s
      (GuessBY.program I, (GuessBY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : Fin I.n) (js : List (Fin I.n)) (kws : List (Fin 4 × Option (Fin I.n))),
      s = Sum.inl (some v0) ::
        (js.map (fun w => (Sum.inl (some w) : GuessBY.Vals I)) ++ [Sum.inl none]) ∧
      kws.length = js.length + 1 ∧
      (∀ i, i < kws.length → ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w)) ∧
      σ = guessBYBlockWord I v0 kws := by
  have hterm_stuck : ∀ (φt : (GuessBY.Vocab I).Store) (r : List (GuessBY.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.guessBY)) (φt' : (GuessBY.Vocab I).Store),
      Command.runFuel Tid.guessBY (Command.term, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      r = [] ∧ σt = [] ∧ φt' = φt := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        exact absurd (congrArg Prod.fst hm) (by rintro ⟨⟩)
    | succ m =>
        simp only [Command.runFuel, Command.step] at hm
        injection hm with hh1 hrest
        injection hrest with hh2 hrest2
        injection hrest2 with hh3 hh4
        exact ⟨hh4, hh2.symm, (congrArg Prod.snd hh3).symm⟩
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := guessBY_lead_step_inv I s n σ φ' hn2
  have hfst1 : Function.update ((GuessBY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) GuessBY.Vars.aux (Sum.inl (some v0))
      GuessBY.Vars.fst = Sum.inr (Sum.inr true) := by
    have hne : GuessBY.Vars.fst ≠ GuessBY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have hcnt1 : Function.update ((GuessBY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) GuessBY.Vars.aux (Sum.inl (some v0))
      GuessBY.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne : GuessBY.Vars.cnt ≠ GuessBY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have h18 := Command.runFuel_stuck_stable h2 18
  obtain ⟨w, rest2, σ1, hs2, hσ2, φ3, hfst3, hcnt3, haux3, h3⟩ :=
    guessBY_block0_step_inv I Command.term rest _ hfst1 hcnt1 v0 (Function.update_self _ _ _)
      n σ φ' h18
  cases w with
  | none =>
      have h20 := Command.runFuel_stuck_stable h3 20
      obtain ⟨σ1', φ4, hfst4, hcnt4, haux4, hσ1eq, h4⟩ :=
        guessBY_blockRest_break_step_inv I Command.term rest2 φ3 hfst3 1 hcnt3 haux3 n σ1 φ' h20
      obtain ⟨hrest2nil, hσ1'nil, hφ4eq⟩ := hterm_stuck φ4 rest2 n σ1' φ' h4
      refine ⟨v0, [], [(1, none)], ?_, rfl, ?_, ?_⟩
      · simp [hs, hs2, hrest2nil]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨none, rfl⟩
      · simp [hσ2, hσ1eq, hσ1'nil, guessBYBlockWord, List.flatMap_cons, List.flatMap_nil]
  | some w1 =>
      obtain ⟨ws, rest0, kws, φ2u, σ1', hseq', hlen', hval', hσeq', h4⟩ :=
        guessBY_chain_shape_inv I rest2.length rest2 rfl Command.term φ3 hfst3 1 hcnt3 w1 haux3
          n σ1 φ' h3
      obtain ⟨hrest0nil, hσ1'nil, hφ2ueq⟩ := hterm_stuck φ2u rest0 n σ1' φ' h4
      refine ⟨v0, w1 :: ws, kws, ?_, by omega, ?_, ?_⟩
      · rw [hs, hs2, hseq', hrest0nil]
        simp
      · intro i hi
        have := hval' i hi
        simpa using this
      · rw [hσ2, hσeq', hσ1'nil, List.append_nil]
        rfl

/-- `guessBY_chain_shape_inv`, with the second components of `kws` determined
(as `guessAY_chain_shape_inv_vals`). -/
theorem guessBY_chain_shape_inv_vals (I : PCPInstance) :
    ∀ (n : ℕ) (s : List (GuessBY.Vals I)), s.length = n →
      ∀ (C2 : Command (domainOf I) (GuessBY.Vocab I)) (φ : (GuessBY.Vocab I).Store)
        (_hfst : φ GuessBY.Vars.fst = Sum.inr (Sum.inr false))
        (k0 : Fin 4) (_hcnt0 : φ GuessBY.Vars.cnt = Sum.inr (Sum.inl k0))
        (w0 : Fin I.n) (_haux0 : φ GuessBY.Vars.aux = Sum.inl (some w0))
        (N : ℕ) (σ : Word (ThreadLabel (domainOf I) Tid.guessBY))
        (φ' : (GuessBY.Vocab I).Store),
        Command.runFuel Tid.guessBY ((guessBYLoop I).seq C2, φ) s N =
          (.stuck, σ, (Command.term, φ'), []) →
        ∃ (ws : List (Fin I.n)) (rest0 : List (GuessBY.Vals I))
          (kws : List (Fin 4 × Option (Fin I.n))) (φ2u : (GuessBY.Vocab I).Store)
          (σ1 : Word (ThreadLabel (domainOf I) Tid.guessBY)),
          s = ws.map (fun w => (Sum.inl (some w) : GuessBY.Vals I)) ++
            Sum.inl none :: rest0 ∧
          kws.length = ws.length + 2 ∧
          (∀ i, i < kws.length →
            ∃ w, kws[i]? = some (⟨(k0.val + i) % 4, by omega⟩, w)) ∧
          (∀ i, i < kws.length → kws[i]?.map Prod.snd = some ((w0 :: ws)[i]?)) ∧
          σ = kws.flatMap (guessBYBlockRestElems I) ++ σ1 ∧
          Command.runFuel Tid.guessBY (C2, φ2u) rest0 N =
            (.stuck, σ1, (Command.term, φ'), []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hslen C2 φ hfst k0 hcnt0 w0 haux0 N σ φ' h
    have h20 := Command.runFuel_stuck_stable h 20
    obtain ⟨w', rest, σ1, hseq, hσeq, φ2u, hfst2, hcnt2, haux2, h2⟩ :=
      guessBY_blockRest_continue_step_inv I C2 s φ hfst k0 hcnt0 w0 haux0 N σ φ' h20
    subst hseq
    cases w' with
    | none =>
        have h2' := Command.runFuel_stuck_stable h2 20
        obtain ⟨σ1', φ3u, hfst3, hcnt3, haux3, hσ1eq, h3⟩ :=
          guessBY_blockRest_break_step_inv I C2 rest φ2u hfst2 (k0 + 1) hcnt2 haux2 N σ1 φ' h2'
        refine ⟨[], rest, [(k0, some w0), (k0 + 1, none)], φ3u, σ1', rfl, rfl, ?_, ?_, ?_, h3⟩
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · refine ⟨some w0, ?_⟩
            simp only [List.getElem?_cons_zero]
            congr 2
            apply Fin.ext
            have hk0 := k0.isLt
            simp only [Nat.add_zero]
            omega
          · refine ⟨none, ?_⟩
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
            congr 2
        · intro i hi
          simp only [List.length_cons, List.length_nil] at hi
          have hi01 : i = 0 ∨ i = 1 := by omega
          rcases hi01 with rfl | rfl
          · simp
          · simp
        · rw [hσeq, hσ1eq]
          simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    | some w1 =>
        have hrest_len : rest.length < n := by
          have heq : (Sum.inl (some w1) :: rest).length = n := hslen
          simp only [List.length_cons] at heq
          omega
        obtain ⟨ws', rest0, kws', φ2u', σ1', hseq', hlen', hval', hval2', hσeq', h3⟩ :=
          ih rest.length hrest_len rest rfl C2 φ2u hfst2 (k0 + 1) hcnt2 w1 haux2 N σ1 φ' h2
        refine ⟨w1 :: ws', rest0, (k0, some w0) :: kws', φ2u', σ1',
          by simp [hseq'], by simp [hlen'], ?_, ?_, ?_, h3⟩
        · intro i hi
          cases i with
          | zero =>
              refine ⟨some w0, ?_⟩
              simp only [List.getElem?_cons_zero]
              congr 2
              apply Fin.ext
              have hk0 := k0.isLt
              simp only [Nat.add_zero]
              omega
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              obtain ⟨w, hw⟩ := hval' i hi'
              refine ⟨w, ?_⟩
              simp only [List.getElem?_cons_succ]
              rw [hw]
              congr 2
              apply Fin.ext
              simp [Fin.add_def]
              omega
        · intro i hi
          cases i with
          | zero => simp
          | succ i =>
              simp only [List.length_cons] at hi
              have hi' : i < kws'.length := by omega
              have := hval2' i hi'
              simpa using this
        · rw [hσeq, hσeq']
          simp only [List.flatMap_cons, List.append_assoc]

/-- `guessBY_shape_inv`, with the second components of `kws` determined (as
`guessAY_shape_inv_vals`). -/
theorem guessBY_shape_inv_vals (I : PCPInstance) {s : List (GuessBY.Vals I)}
    {φ' : (GuessBY.Vocab I).Store} {cLast : Config (domainOf I) (GuessBY.Vocab I)}
    {σ : Word (ThreadLabel (domainOf I) Tid.guessBY)}
    (hrun : Command.Run Tid.guessBY s
      (GuessBY.program I, (GuessBY.Vocab I).mkStore (fun v => match v with
        | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
        | .fst => some (Sum.inr (Sum.inr true))
        | _ => none) (Sum.inl none))
      σ cLast [] (Command.term, φ')) :
    ∃ (v0 : Fin I.n) (js : List (Fin I.n)) (kws : List (Fin 4 × Option (Fin I.n))),
      s = Sum.inl (some v0) ::
        (js.map (fun w => (Sum.inl (some w) : GuessBY.Vals I)) ++ [Sum.inl none]) ∧
      kws.length = js.length + 1 ∧
      (∀ i, i < kws.length → ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w)) ∧
      (∀ i, i < kws.length → kws[i]?.map Prod.snd = some (js[i]?)) ∧
      σ = guessBYBlockWord I v0 kws := by
  have hterm_stuck : ∀ (φt : (GuessBY.Vocab I).Store) (r : List (GuessBY.Vals I)) (m : ℕ)
      (σt : Word (ThreadLabel (domainOf I) Tid.guessBY)) (φt' : (GuessBY.Vocab I).Store),
      Command.runFuel Tid.guessBY (Command.term, φt) r m =
        (.stuck, σt, (Command.term, φt'), []) →
      r = [] ∧ σt = [] ∧ φt' = φt := by
    intro φt r m σt φt' hm
    cases m with
    | zero =>
        simp only [Command.runFuel] at hm
        exact absurd (congrArg Prod.fst hm) (by rintro ⟨⟩)
    | succ m =>
        simp only [Command.runFuel, Command.step] at hm
        injection hm with hh1 hrest
        injection hrest with hh2 hrest2
        injection hrest2 with hh3 hh4
        exact ⟨hh4, hh2.symm, (congrArg Prod.snd hh3).symm⟩
  obtain ⟨n, hn, -⟩ := Command.Run.exists_runFuel_combined_of_term hrun
  have hn2 := Command.runFuel_stuck_stable hn 2
  obtain ⟨v0, rest, hs, h2⟩ := guessBY_lead_step_inv I s n σ φ' hn2
  have hfst1 : Function.update ((GuessBY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) GuessBY.Vars.aux (Sum.inl (some v0))
      GuessBY.Vars.fst = Sum.inr (Sum.inr true) := by
    have hne : GuessBY.Vars.fst ≠ GuessBY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have hcnt1 : Function.update ((GuessBY.Vocab I).mkStore (fun v => match v with
      | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
      | .fst => some (Sum.inr (Sum.inr true))
      | _ => none) (Sum.inl none)) GuessBY.Vars.aux (Sum.inl (some v0))
      GuessBY.Vars.cnt = Sum.inr (Sum.inl (0 : Fin 4)) := by
    have hne : GuessBY.Vars.cnt ≠ GuessBY.Vars.aux := by decide
    exact Function.update_of_ne hne _ _
  have h18 := Command.runFuel_stuck_stable h2 18
  obtain ⟨w, rest2, σ1, hs2, hσ2, φ3, hfst3, hcnt3, haux3, h3⟩ :=
    guessBY_block0_step_inv I Command.term rest _ hfst1 hcnt1 v0 (Function.update_self _ _ _)
      n σ φ' h18
  cases w with
  | none =>
      have h20 := Command.runFuel_stuck_stable h3 20
      obtain ⟨σ1', φ4, hfst4, hcnt4, haux4, hσ1eq, h4⟩ :=
        guessBY_blockRest_break_step_inv I Command.term rest2 φ3 hfst3 1 hcnt3 haux3 n σ1 φ' h20
      obtain ⟨hrest2nil, hσ1'nil, hφ4eq⟩ := hterm_stuck φ4 rest2 n σ1' φ' h4
      refine ⟨v0, [], [(1, none)], ?_, rfl, ?_, ?_, ?_⟩
      · simp [hs, hs2, hrest2nil]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨none, rfl⟩
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        simp
      · simp [hσ2, hσ1eq, hσ1'nil, guessBYBlockWord, List.flatMap_cons, List.flatMap_nil]
  | some w1 =>
      obtain ⟨ws, rest0, kws, φ2u, σ1', hseq', hlen', hval', hval2', hσeq', h4⟩ :=
        guessBY_chain_shape_inv_vals I rest2.length rest2 rfl Command.term φ3 hfst3 1 hcnt3 w1 haux3
          n σ1 φ' h3
      obtain ⟨hrest0nil, hσ1'nil, hφ2ueq⟩ := hterm_stuck φ2u rest0 n σ1' φ' h4
      refine ⟨v0, w1 :: ws, kws, ?_, by omega, ?_, ?_, ?_⟩
      · rw [hs, hs2, hseq', hrest0nil]
        simp
      · intro i hi
        have := hval' i hi
        simpa using this
      · intro i hi
        have := hval2' i hi
        simpa using this
      · rw [hσ2, hσeq', hσ1'nil, List.append_nil]
        rfl

end RAUndecidability
