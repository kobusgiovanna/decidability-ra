import RAUndecidability.Reduction.Soundness.Words
import RAUndecidability.Reduction.Soundness.NoSkippingPair
import RAUndecidability.Reduction.Completeness.Graph

/-!
# Eq. (15)-(17): the no-skipping pairs

Lemma 3.2 for an arbitrary execution of `ConcProg` reaching its final state,
one theorem per `rf`-edge family. The ten pairs of Eq. (15)/(16) each
discharge `ExecutionGraph.NoSkipPair` (`Soundness/NoSkippingPair.lean`, the
paper's shared argument for them) from the two threads' closed forms, in a
`*_noSkipPair` theorem per pair; the four pairs of Eq. (17) likewise
discharge `ExecutionGraph.CrossPair`, in a `crossPair_*` theorem per pair.
Each pair's two `no_skipping_*` theorems are applications of the shared
argument.
-/

namespace RAUndecidability

/-! ## `Val.writerTid`: the writer's tag

Three of `Val I`'s constructors (`xTag`, `yTag`, `primeTag`) carry the
writing thread's `Tid`. On the locations where values carry it,
`G.rf_matches` alone identifies the writer. `writerTid` extracts the tag
(`none` for the untagged `cnt`/`cntAux`). -/
def Val.writerTid {I : PCPInstance} : Val I → Option Tid
  | .xTag tag _ => some tag.1
  | .yTag tag _ => some tag.1
  | .primeTag t _ => some t
  | .cnt _ => none
  | .cntAux _ _ => none

/-- If a value's `writerTid` is `none` or `some t'`, and is `some t`, then
`t = t'`. -/
theorem tid_eq_of_writerTid_disj {I : PCPInstance} {v : Val I} {t t' : Tid}
    (h : v.writerTid = none ∨ v.writerTid = some t') (htag : v.writerTid = some t) :
    t = t' := by
  rcases h with h | h <;> rw [htag] at h <;> simp_all

/-- For a thread none of whose `VExpr`s evaluates to a value tagged with a
different thread (`hclean`; eight of the twelve threads), every write event
of that thread carries its own tag or none. Via a `Command.Run` of the
thread (`exists_run_of_induced_reaches`) and `Command.Run.write_hasWrite`. -/
theorem writerTid_clean {I : PCPInstance} {V : Vocabulary (domainOf I)} {t : Tid}
    {C_t : Command (domainOf I) V} {φ₀ : V.Store} (G : ExecutionGraph (domainOf I))
    (hex : ∃ (s : List V.LVal) (cLast : Config (domainOf I) V) (φ' : V.Store),
      Command.Run t s (C_t, φ₀) (G.threadLabels t) cLast [] (Command.term, φ'))
    {e : Event (domainOf I)} (he : e ∈ G.Events) (htid : e.tid = t) (hwt : e.op = OpType.wt)
    (hclean : ∀ (vexpr : V.VExpr) (φ : V.Store), e.val = V.evalV vexpr φ →
      e.val.writerTid = none ∨ e.val.writerTid = some t) :
    e.val.writerTid = none ∨ e.val.writerTid = some t := by
  obtain ⟨s, cLast, φ', hrun⟩ := hex
  have hmem := G.mem_threadLabels_of_mem_Events he htid
  obtain ⟨vexpr, -, φ, hval⟩ := hrun.write_hasWrite _ hmem hwt
  exact hclean vexpr φ hval

/-- The only `VExpr` of a write in `CheckX`'s program is `cntTagVal` (the
`xA`/`xB` writes); the others are only used in reads. -/
theorem CheckX.write_hasWrite_cntTagVal (I : PCPInstance) {u : Loc} {e : CheckX.VExpr}
    (h : Command.HasWrite u e (CheckX.program I)) : e = CheckX.VExpr.cntTagVal := by
  unfold CheckX.program CheckX.body Command.firstIt at h
  simp only [Command.HasWrite] at h
  tauto

/-- The only `VExpr` of a write in `PrimeCheckX`'s program is `cntTagVal` (the
`xA'`/`xB'` writes). -/
theorem PrimeCheckX.write_hasWrite_cntTagVal (I : PCPInstance) {u : Loc}
    {e : PrimeCheckX.VExpr} (h : Command.HasWrite u e (PrimeCheckX.program I)) :
    e = PrimeCheckX.VExpr.cntTagVal := by
  unfold PrimeCheckX.program Command.whileNdet PrimeCheckX.body at h
  simp only [Command.HasWrite] at h
  tauto

/-- The only `VExpr` of a write in `CheckY`'s program is `cntTagVal`. -/
theorem CheckY.write_hasWrite_cntTagVal (I : PCPInstance) {u : Loc} {e : CheckY.VExpr}
    (h : Command.HasWrite u e (CheckY.program I)) : e = CheckY.VExpr.cntTagVal := by
  unfold CheckY.program CheckY.body Command.firstIt at h
  simp only [Command.HasWrite] at h
  tauto

/-- The only `VExpr` of a write in `PrimeCheckY`'s program is `cntTagVal`. -/
theorem PrimeCheckY.write_hasWrite_cntTagVal (I : PCPInstance) {u : Loc}
    {e : PrimeCheckY.VExpr} (h : Command.HasWrite u e (PrimeCheckY.program I)) :
    e = PrimeCheckY.VExpr.cntTagVal := by
  unfold PrimeCheckY.program Command.whileNdet PrimeCheckY.body at h
  simp only [Command.HasWrite] at h
  tauto

/-! ## Writer confinement from program syntax

The locations of Eq. (15) carry untagged values (`Val.cnt`/`Val.cntAux`), as
in the paper (`z`-locations hold a bare `i mod 4`), so their writer is
identified from the programs instead: only the threads in `writerTids u`
(`Completeness/Construction.lean`) contain a write to `u`
(`writerTid_confined`). -/

/-- `writerTids` membership facts. (Stated without parameters so that `decide`
applies.) -/
theorem writerTids_checkX : Tid.checkX ∈ writerTids Loc.xA ∧ Tid.checkX ∈ writerTids Loc.xB :=
  by decide

theorem writerTids_checkY : Tid.checkY ∈ writerTids Loc.yA ∧ Tid.checkY ∈ writerTids Loc.yB :=
  by decide

theorem writerTids_primeCheckX :
    Tid.primeCheckX ∈ writerTids Loc.xA' ∧ Tid.primeCheckX ∈ writerTids Loc.xB' := by decide

theorem writerTids_primeCheckY :
    Tid.primeCheckY ∈ writerTids Loc.yA' ∧ Tid.primeCheckY ∈ writerTids Loc.yB' := by decide

theorem writerTids_primeAX : Tid.primeAX ∈ writerTids Loc.xA' ∧ Tid.primeAX ∈ writerTids Loc.zAxx' :=
  by decide

theorem writerTids_primeBX : Tid.primeBX ∈ writerTids Loc.xB' ∧ Tid.primeBX ∈ writerTids Loc.zBxx' :=
  by decide

theorem writerTids_primeAY : Tid.primeAY ∈ writerTids Loc.yA' ∧ Tid.primeAY ∈ writerTids Loc.zAyy' :=
  by decide

theorem writerTids_primeBY : Tid.primeBY ∈ writerTids Loc.yB' ∧ Tid.primeBY ∈ writerTids Loc.zByy' :=
  by decide

theorem writerTids_guessAX : Tid.guessAX ∈ writerTids Loc.xA ∧ Tid.guessAX ∈ writerTids Loc.zAx'x ∧
    Tid.guessAX ∈ writerTids Loc.zAxy := by decide

theorem writerTids_guessBX : Tid.guessBX ∈ writerTids Loc.xB ∧ Tid.guessBX ∈ writerTids Loc.zBx'x ∧
    Tid.guessBX ∈ writerTids Loc.zBxy := by decide

theorem writerTids_guessAY : Tid.guessAY ∈ writerTids Loc.yA ∧ Tid.guessAY ∈ writerTids Loc.ellAyx ∧
    Tid.guessAY ∈ writerTids Loc.zAy'y := by decide

theorem writerTids_guessBY : Tid.guessBY ∈ writerTids Loc.yB ∧ Tid.guessBY ∈ writerTids Loc.ellByx ∧
    Tid.guessBY ∈ writerTids Loc.zBy'y := by decide

theorem CheckX.hasWrite_loc {I : PCPInstance} {u : Loc} {e : CheckX.VExpr}
    (h : Command.HasWrite u e (CheckX.program I)) : Tid.checkX ∈ writerTids u := by
  unfold CheckX.program CheckX.body Command.firstIt at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_checkX.1, writerTids_checkX.2]

theorem CheckY.hasWrite_loc {I : PCPInstance} {u : Loc} {e : CheckY.VExpr}
    (h : Command.HasWrite u e (CheckY.program I)) : Tid.checkY ∈ writerTids u := by
  unfold CheckY.program CheckY.body Command.firstIt at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_checkY.1, writerTids_checkY.2]

theorem PrimeCheckX.hasWrite_loc {I : PCPInstance} {u : Loc} {e : PrimeCheckX.VExpr}
    (h : Command.HasWrite u e (PrimeCheckX.program I)) : Tid.primeCheckX ∈ writerTids u := by
  unfold PrimeCheckX.program Command.whileNdet PrimeCheckX.body at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_primeCheckX.1, writerTids_primeCheckX.2]

theorem PrimeCheckY.hasWrite_loc {I : PCPInstance} {u : Loc} {e : PrimeCheckY.VExpr}
    (h : Command.HasWrite u e (PrimeCheckY.program I)) : Tid.primeCheckY ∈ writerTids u := by
  unfold PrimeCheckY.program Command.whileNdet PrimeCheckY.body at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_primeCheckY.1, writerTids_primeCheckY.2]

theorem PrimeAX.hasWrite_loc {I : PCPInstance} {u : Loc} {e : PrimeAX.VExpr}
    (h : Command.HasWrite u e (PrimeAX.program I)) : Tid.primeAX ∈ writerTids u := by
  unfold PrimeAX.program Command.whileNdet PrimeAX.body at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_primeAX.1, writerTids_primeAX.2]

theorem PrimeBX.hasWrite_loc {I : PCPInstance} {u : Loc} {e : PrimeBX.VExpr}
    (h : Command.HasWrite u e (PrimeBX.program I)) : Tid.primeBX ∈ writerTids u := by
  unfold PrimeBX.program Command.whileNdet PrimeBX.body at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_primeBX.1, writerTids_primeBX.2]

theorem PrimeAY.hasWrite_loc {I : PCPInstance} {u : Loc} {e : PrimeAY.VExpr}
    (h : Command.HasWrite u e (PrimeAY.program I)) : Tid.primeAY ∈ writerTids u := by
  unfold PrimeAY.program Command.whileNdet PrimeAY.body at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_primeAY.1, writerTids_primeAY.2]

theorem PrimeBY.hasWrite_loc {I : PCPInstance} {u : Loc} {e : PrimeBY.VExpr}
    (h : Command.HasWrite u e (PrimeBY.program I)) : Tid.primeBY ∈ writerTids u := by
  unfold PrimeBY.program Command.whileNdet PrimeBY.body at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_primeBY.1, writerTids_primeBY.2]

theorem GuessAX.hasWrite_loc {I : PCPInstance} {u : Loc} {e : GuessAX.VExpr}
    (h : Command.HasWrite u e (GuessAX.program I)) : Tid.guessAX ∈ writerTids u := by
  unfold GuessAX.program GuessAX.outerBody Command.forLoop GuessAX.innerBody
    Command.firstIt at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | (⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_guessAX.2.2, writerTids_guessAX.1, writerTids_guessAX.2.1,
    writerTids_guessAX.1, writerTids_guessAX.2.1]

theorem GuessBX.hasWrite_loc {I : PCPInstance} {u : Loc} {e : GuessBX.VExpr}
    (h : Command.HasWrite u e (GuessBX.program I)) : Tid.guessBX ∈ writerTids u := by
  unfold GuessBX.program GuessBX.outerBody Command.forLoop GuessBX.innerBody
    Command.firstIt at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with ⟨rfl, -⟩ | (⟨rfl, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩ | ⟨rfl, -⟩
  exacts [writerTids_guessBX.2.2, writerTids_guessBX.1, writerTids_guessBX.2.1,
    writerTids_guessBX.1, writerTids_guessBX.2.1]

theorem GuessAY.hasWrite_loc {I : PCPInstance} {u : Loc} {e : GuessAY.VExpr}
    (h : Command.HasWrite u e (GuessAY.program I)) : Tid.guessAY ∈ writerTids u := by
  unfold GuessAY.program GuessAY.loopBody Command.firstIt at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩) | (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩)
  exacts [writerTids_guessAY.1, writerTids_guessAY.2.1, writerTids_guessAY.2.2,
    writerTids_guessAY.1, writerTids_guessAY.2.1, writerTids_guessAY.2.2]

theorem GuessBY.hasWrite_loc {I : PCPInstance} {u : Loc} {e : GuessBY.VExpr}
    (h : Command.HasWrite u e (GuessBY.program I)) : Tid.guessBY ∈ writerTids u := by
  unfold GuessBY.program GuessBY.loopBody Command.firstIt at h
  simp only [Command.HasWrite, false_or, or_false] at h
  rcases h with (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩) | (⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩)
  exacts [writerTids_guessBY.1, writerTids_guessBY.2.1, writerTids_guessBY.2.2,
    writerTids_guessBY.1, writerTids_guessBY.2.1, writerTids_guessBY.2.2]

/-- Writer confinement: in any execution `G` reaching the final state, a write
event's thread is in `writerTids` of its location. By cases on `e.tid`, each
via that thread's `hasWrite_loc`. -/
theorem writerTid_confined (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) {e : Event (domainOf I)}
    (he : e ∈ G.Events) (hwt : e.op = OpType.wt) :
    e.tid ∈ writerTids e.loc := by
  match hty : e.tid with
  | .checkX =>
      obtain ⟨s, cLast, φ, hrun⟩ := checkX_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact CheckX.hasWrite_loc hhw
  | .checkY =>
      obtain ⟨s, cLast, φ, hrun⟩ := checkY_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact CheckY.hasWrite_loc hhw
  | .primeCheckX =>
      obtain ⟨s, cLast, φ, hrun⟩ := primeCheckX_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact PrimeCheckX.hasWrite_loc hhw
  | .primeCheckY =>
      obtain ⟨s, cLast, φ, hrun⟩ := primeCheckY_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact PrimeCheckY.hasWrite_loc hhw
  | .guessAX =>
      obtain ⟨s, cLast, φ, hrun⟩ := guessAX_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact GuessAX.hasWrite_loc hhw
  | .guessBX =>
      obtain ⟨s, cLast, φ, hrun⟩ := guessBX_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact GuessBX.hasWrite_loc hhw
  | .guessAY =>
      obtain ⟨s, cLast, φ, hrun⟩ := guessAY_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact GuessAY.hasWrite_loc hhw
  | .guessBY =>
      obtain ⟨s, cLast, φ, hrun⟩ := guessBY_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact GuessBY.hasWrite_loc hhw
  | .primeAX =>
      obtain ⟨s, cLast, φ, hrun⟩ := primeAX_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact PrimeAX.hasWrite_loc hhw
  | .primeBX =>
      obtain ⟨s, cLast, φ, hrun⟩ := primeBX_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact PrimeBX.hasWrite_loc hhw
  | .primeAY =>
      obtain ⟨s, cLast, φ, hrun⟩ := primeAY_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact PrimeAY.hasWrite_loc hhw
  | .primeBY =>
      obtain ⟨s, cLast, φ, hrun⟩ := primeBY_run_of_reaches I G hG
      have hmem := G.mem_threadLabels_of_mem_Events he hty
      obtain ⟨vexpr, hhw, -⟩ := hrun.write_hasWrite _ hmem hwt
      exact PrimeBY.hasWrite_loc hhw

/-- `G_writer_val_tid`: in any execution `G` reaching the final state, a write
event whose value is tagged with `t` (`xTag`/`yTag`/`primeTag`) is on thread
`t`. By cases on `e.tid`: eight threads never produce a value tagged with
another thread (`writerTid_clean`); `CheckX`/`CheckY`/`PrimeCheckX`/
`PrimeCheckY` have read-only `VExpr`s tagged with other threads, so their
writes are first narrowed to `cntTagVal` (`write_hasWrite_cntTagVal`). -/
theorem G_writer_val_tid (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) {e : Event (domainOf I)}
    (he : e ∈ G.Events) (hwt : e.op = OpType.wt) {t : Tid}
    (htag : e.val.writerTid = some t) : e.tid = t := by
  cases hd : e.tid with
  | guessAX =>
    have hex : ∃ (s : List (GuessAX.Vals I)) (cLast : Config (domainOf I) (GuessAX.Vocab I))
        (φ' : (GuessAX.Vocab I).Store), Command.Run Tid.guessAX s
        (GuessAX.program I, (GuessAX.Vocab I).mkStore (fun v => match v with
          | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.guessAX) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.guessAX).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.guessAX] at h
      exact exists_run_of_induced_reaches h
    have hclean : ∀ (vexpr : (GuessAX.Vocab I).VExpr) (φ : (GuessAX.Vocab I).Store),
        e.val = (GuessAX.Vocab I).evalV vexpr φ →
        e.val.writerTid = none ∨ e.val.writerTid = some Tid.guessAX := by
      intro vexpr φ hv
      rw [hv]
      cases vexpr <;> simp [GuessAX.Vocab, GuessAX.evalV, Val.writerTid]
    exact (tid_eq_of_writerTid_disj (writerTid_clean G hex he hd hwt hclean) htag).symm
  | guessAY =>
    have hex : ∃ (s : List (GuessAY.Vals I)) (cLast : Config (domainOf I) (GuessAY.Vocab I))
        (φ' : (GuessAY.Vocab I).Store), Command.Run Tid.guessAY s
        (GuessAY.program I, (GuessAY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr true))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.guessAY) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.guessAY).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.guessAY] at h
      exact exists_run_of_induced_reaches h
    have hclean : ∀ (vexpr : (GuessAY.Vocab I).VExpr) (φ : (GuessAY.Vocab I).Store),
        e.val = (GuessAY.Vocab I).evalV vexpr φ →
        e.val.writerTid = none ∨ e.val.writerTid = some Tid.guessAY := by
      intro vexpr φ hv
      rw [hv]
      cases vexpr <;> simp [GuessAY.Vocab, GuessAY.evalV, Val.writerTid]
    exact (tid_eq_of_writerTid_disj (writerTid_clean G hex he hd hwt hclean) htag).symm
  | guessBX =>
    have hex : ∃ (s : List (GuessBX.Vals I)) (cLast : Config (domainOf I) (GuessBX.Vocab I))
        (φ' : (GuessBX.Vocab I).Store), Command.Run Tid.guessBX s
        (GuessBX.program I, (GuessBX.Vocab I).mkStore (fun v => match v with
          | .cntY => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr (Sum.inr true)))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.guessBX) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.guessBX).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.guessBX] at h
      exact exists_run_of_induced_reaches h
    have hclean : ∀ (vexpr : (GuessBX.Vocab I).VExpr) (φ : (GuessBX.Vocab I).Store),
        e.val = (GuessBX.Vocab I).evalV vexpr φ →
        e.val.writerTid = none ∨ e.val.writerTid = some Tid.guessBX := by
      intro vexpr φ hv
      rw [hv]
      cases vexpr <;> simp [GuessBX.Vocab, GuessBX.evalV, Val.writerTid]
    exact (tid_eq_of_writerTid_disj (writerTid_clean G hex he hd hwt hclean) htag).symm
  | guessBY =>
    have hex : ∃ (s : List (GuessBY.Vals I)) (cLast : Config (domainOf I) (GuessBY.Vocab I))
        (φ' : (GuessBY.Vocab I).Store), Command.Run Tid.guessBY s
        (GuessBY.program I, (GuessBY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr true))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.guessBY) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.guessBY).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.guessBY] at h
      exact exists_run_of_induced_reaches h
    have hclean : ∀ (vexpr : (GuessBY.Vocab I).VExpr) (φ : (GuessBY.Vocab I).Store),
        e.val = (GuessBY.Vocab I).evalV vexpr φ →
        e.val.writerTid = none ∨ e.val.writerTid = some Tid.guessBY := by
      intro vexpr φ hv
      rw [hv]
      cases vexpr <;> simp [GuessBY.Vocab, GuessBY.evalV, Val.writerTid]
    exact (tid_eq_of_writerTid_disj (writerTid_clean G hex he hd hwt hclean) htag).symm
  | primeAX =>
    have hex : ∃ (s : List PrimeAX.Vals) (cLast : Config (domainOf I) (PrimeAX.Vocab I))
        (φ' : (PrimeAX.Vocab I).Store), Command.Run Tid.primeAX s
        (PrimeAX.program I, (PrimeAX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4))
          | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeAX) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.primeAX).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.primeAX] at h
      exact exists_run_of_induced_reaches h
    have hclean : ∀ (vexpr : (PrimeAX.Vocab I).VExpr) (φ : (PrimeAX.Vocab I).Store),
        e.val = (PrimeAX.Vocab I).evalV vexpr φ →
        e.val.writerTid = none ∨ e.val.writerTid = some Tid.primeAX := by
      intro vexpr φ hv
      rw [hv]
      cases vexpr <;> simp only [PrimeAX.Vocab, PrimeAX.evalV] <;>
        (try split) <;> simp [Val.writerTid]
    exact (tid_eq_of_writerTid_disj (writerTid_clean G hex he hd hwt hclean) htag).symm
  | primeAY =>
    have hex : ∃ (s : List PrimeAY.Vals) (cLast : Config (domainOf I) (PrimeAY.Vocab I))
        (φ' : (PrimeAY.Vocab I).Store), Command.Run Tid.primeAY s
        (PrimeAY.program I, (PrimeAY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4))
          | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeAY) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.primeAY).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.primeAY] at h
      exact exists_run_of_induced_reaches h
    have hclean : ∀ (vexpr : (PrimeAY.Vocab I).VExpr) (φ : (PrimeAY.Vocab I).Store),
        e.val = (PrimeAY.Vocab I).evalV vexpr φ →
        e.val.writerTid = none ∨ e.val.writerTid = some Tid.primeAY := by
      intro vexpr φ hv
      rw [hv]
      cases vexpr <;> simp only [PrimeAY.Vocab, PrimeAY.evalV] <;>
        (try split) <;> simp [Val.writerTid]
    exact (tid_eq_of_writerTid_disj (writerTid_clean G hex he hd hwt hclean) htag).symm
  | primeBX =>
    have hex : ∃ (s : List PrimeBX.Vals) (cLast : Config (domainOf I) (PrimeBX.Vocab I))
        (φ' : (PrimeBX.Vocab I).Store), Command.Run Tid.primeBX s
        (PrimeBX.program I, (PrimeBX.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4))
          | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeBX) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.primeBX).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.primeBX] at h
      exact exists_run_of_induced_reaches h
    have hclean : ∀ (vexpr : (PrimeBX.Vocab I).VExpr) (φ : (PrimeBX.Vocab I).Store),
        e.val = (PrimeBX.Vocab I).evalV vexpr φ →
        e.val.writerTid = none ∨ e.val.writerTid = some Tid.primeBX := by
      intro vexpr φ hv
      rw [hv]
      cases vexpr <;> simp only [PrimeBX.Vocab, PrimeBX.evalV] <;>
        (try split) <;> simp [Val.writerTid]
    exact (tid_eq_of_writerTid_disj (writerTid_clean G hex he hd hwt hclean) htag).symm
  | primeBY =>
    have hex : ∃ (s : List PrimeBY.Vals) (cLast : Config (domainOf I) (PrimeBY.Vocab I))
        (φ' : (PrimeBY.Vocab I).Store), Command.Run Tid.primeBY s
        (PrimeBY.program I, (PrimeBY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4))
          | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeBY) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.primeBY).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.primeBY] at h
      exact exists_run_of_induced_reaches h
    have hclean : ∀ (vexpr : (PrimeBY.Vocab I).VExpr) (φ : (PrimeBY.Vocab I).Store),
        e.val = (PrimeBY.Vocab I).evalV vexpr φ →
        e.val.writerTid = none ∨ e.val.writerTid = some Tid.primeBY := by
      intro vexpr φ hv
      rw [hv]
      cases vexpr <;> simp only [PrimeBY.Vocab, PrimeBY.evalV] <;>
        (try split) <;> simp [Val.writerTid]
    exact (tid_eq_of_writerTid_disj (writerTid_clean G hex he hd hwt hclean) htag).symm
  | checkX =>
    obtain ⟨s, cLast, φ', hrun⟩ := checkX_run_of_reaches I G hG
    have hmem := G.mem_threadLabels_of_mem_Events he hd
    obtain ⟨vexpr, hhw, φ, hval⟩ := hrun.write_hasWrite _ hmem hwt
    have hvexpr := CheckX.write_hasWrite_cntTagVal I hhw
    subst hvexpr
    have hval' : e.val = (CheckX.Vocab I).evalV CheckX.VExpr.cntTagVal φ := hval
    rw [hval'] at htag; simp only [CheckX.Vocab, CheckX.evalV] at htag
    simp only [Val.writerTid, Option.some.injEq] at htag
    exact htag
  | checkY =>
    have hex : ∃ (s : List (CheckY.Vals I)) (cLast : Config (domainOf I) (CheckY.Vocab I))
        (φ' : (CheckY.Vocab I).Store), Command.Run Tid.checkY s
        (CheckY.program I, (CheckY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inr (Sum.inl (0 : Fin 4)))
          | .fst => some (Sum.inr (Sum.inr true))
          | _ => none) (Sum.inl none))
        (G.threadLabels Tid.checkY) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.checkY).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.checkY] at h
      exact exists_run_of_induced_reaches h
    obtain ⟨s, cLast, φ', hrun⟩ := hex
    have hmem := G.mem_threadLabels_of_mem_Events he hd
    obtain ⟨vexpr, hhw, φ, hval⟩ := hrun.write_hasWrite _ hmem hwt
    have hvexpr := CheckY.write_hasWrite_cntTagVal I hhw
    subst hvexpr
    have hval' : e.val = (CheckY.Vocab I).evalV CheckY.VExpr.cntTagVal φ := hval
    rw [hval'] at htag; simp only [CheckY.Vocab, CheckY.evalV] at htag
    simp only [Val.writerTid, Option.some.injEq] at htag
    exact htag
  | primeCheckX =>
    obtain ⟨s, cLast, φ', hrun⟩ := primeCheckX_run_of_reaches I G hG
    have hmem := G.mem_threadLabels_of_mem_Events he hd
    obtain ⟨vexpr, hhw, φ, hval⟩ := hrun.write_hasWrite _ hmem hwt
    have hvexpr := PrimeCheckX.write_hasWrite_cntTagVal I hhw
    subst hvexpr
    have hval' : e.val = (PrimeCheckX.Vocab I).evalV PrimeCheckX.VExpr.cntTagVal φ := hval
    rw [hval'] at htag; simp only [PrimeCheckX.Vocab, PrimeCheckX.evalV] at htag
    simp only [Val.writerTid, Option.some.injEq] at htag
    exact htag
  | primeCheckY =>
    have hex : ∃ (s : List PrimeCheckY.Vals) (cLast : Config (domainOf I) (PrimeCheckY.Vocab I))
        (φ' : (PrimeCheckY.Vocab I).Store), Command.Run Tid.primeCheckY s
        (PrimeCheckY.program I, (PrimeCheckY.Vocab I).mkStore (fun v => match v with
          | .cnt => some (Sum.inl (0 : Fin 4))
          | .b => none) (Sum.inl 0))
        (G.threadLabels Tid.primeCheckY) cLast [] (Command.term, φ') := by
      have h := (hG.2 Tid.primeCheckY).2 rfl
      rw [G.threadWord_eq_map_threadLabels Tid.primeCheckY] at h
      exact exists_run_of_induced_reaches h
    obtain ⟨s, cLast, φ', hrun⟩ := hex
    have hmem := G.mem_threadLabels_of_mem_Events he hd
    obtain ⟨vexpr, hhw, φ, hval⟩ := hrun.write_hasWrite _ hmem hwt
    have hvexpr := PrimeCheckY.write_hasWrite_cntTagVal I hhw
    subst hvexpr
    have hval' : e.val = (PrimeCheckY.Vocab I).evalV PrimeCheckY.VExpr.cntTagVal φ := hval
    rw [hval'] at htag; simp only [PrimeCheckY.Vocab, PrimeCheckY.evalV] at htag
    simp only [Val.writerTid, Option.some.injEq] at htag
    exact htag

/-- `checkX`'s `xA`-write value at filtered position `0` (block 0). -/
theorem checkXBlockWord_xA_write_val0 (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) :
    ((checkXBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.checkX Loc.xA (Val.primeTag Tid.checkX 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkX Loc.xA (Val.primeTag Tid.checkX 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `checkX`'s `xA`-write value at filtered position `i + 1` (block `kws[i]`),
in terms of `kws[i].1`. -/
theorem checkXBlockWord_xA_write_val_succ (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) (i : ℕ) :
    ((checkXBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.checkX Loc.xA (Val.primeTag Tid.checkX
        (kw.1 + 1)), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkX Loc.xA (Val.primeTag Tid.checkX 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkXBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.checkX Loc.xA
        (Val.primeTag Tid.checkX (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.checkX Loc.xA (Val.primeTag Tid.checkX (kw.1 + 1)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkX)] := by
      intro kw
      unfold checkXBlockRestElems
      rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

/-- `primeCheckX`'s `xA`-read value at filtered position `j`:
`Val.primeTag Tid.checkX c` for block `cnts[j] = c`. -/
theorem primeCheckXBlockWord_xA_read_val (I : PCPInstance) (cnts : List (Fin 4)) (j : ℕ) :
    ((primeCheckXBlockWord I cnts).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd))[j]? =
      (cnts[j]?).map (fun c => (⟨EventLabel.rd Tid.primeCheckX Loc.xA
        (Val.primeTag Tid.checkX c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckX)) := by
  have hone : ∀ c : Fin 4, (primeCheckXBlockElems I c).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeCheckX Loc.xA (Val.primeTag Tid.checkX c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX)] := by
    intro c
    unfold primeCheckXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeCheckXBlockWord I cnts).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) =
      cnts.map (fun c => (⟨EventLabel.rd Tid.primeCheckX Loc.xA
        (Val.primeTag Tid.checkX c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckX)) := by
    rw [primeCheckXBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ cnts
  rw [hflat, List.getElem?_map]

/-- `primeCheckX`'s `xA'`-write value at filtered position `j` (offset `0`):
`Val.primeTag Tid.primeCheckX c`. -/
theorem primeCheckXBlockWord_xA'_write_val (I : PCPInstance) (cnts : List (Fin 4)) (j : ℕ) :
    ((primeCheckXBlockWord I cnts).filter (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.wt))[j]? =
      (cnts[j]?).map (fun c => (⟨EventLabel.wt Tid.primeCheckX Loc.xA'
        (Val.primeTag Tid.primeCheckX c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckX)) := by
  have hone : ∀ c : Fin 4, (primeCheckXBlockElems I c).filter
      (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeCheckX Loc.xA' (Val.primeTag Tid.primeCheckX c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX)] := by
    intro c
    unfold primeCheckXBlockElems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeCheckXBlockWord I cnts).filter
      (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.wt) =
      cnts.map (fun c => (⟨EventLabel.wt Tid.primeCheckX Loc.xA'
        (Val.primeTag Tid.primeCheckX c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckX)) := by
    rw [primeCheckXBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ cnts
  rw [hflat, List.getElem?_map]

/-- `checkX`'s `xA'`-read value at filtered position `j`: block 0 has no
`xA'`-read, so position `j` is in block `kws[j]`, with value
`Val.primeTag Tid.primeCheckX kw.1`. -/
theorem checkXBlockWord_xA'_read_val (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) (j : ℕ) :
    ((checkXBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.rd))[j]? =
      (kws[j]?).map (fun kw => (⟨EventLabel.rd Tid.checkX Loc.xA'
        (Val.primeTag Tid.primeCheckX kw.1), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.rd) =
      [] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkXBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.checkX Loc.xA'
        (Val.primeTag Tid.primeCheckX kw.1), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkX Loc.xA' (Val.primeTag Tid.primeCheckX kw.1), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkX)] := by
      intro kw
      unfold checkXBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.nil_append, List.getElem?_map]

/-- Position of offset `p` of `checkX`'s `blockRest` block `n` (`kws[n]`) in
its word: `4 + n * 6 + p` (block 0 has length `4`, each later block `6`). -/
theorem checkXBlockWord_blockRest_pos (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) (n p : ℕ) (kw : Fin 4 × Option I.Γ) (hkw : kws[n]? = some kw)
    (hp : p < 6) :
    (checkXBlockWord I v0 kws)[4 + n * 6 + p]? = (checkXBlockRestElems I kw)[p]? := by
  have heq : checkXBlockWord I v0 kws =
      checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I) := rfl
  have hb0len : (checkXBlock0Elems I v0).length = 4 := rfl
  rw [heq, List.getElem?_append_right (by rw [hb0len]; omega), hb0len]
  have hi : 4 + n * 6 + p - 4 = n * 6 + p := by omega
  rw [hi]
  exact flatMap_uniform_getElem_fwd (checkXBlockRestElems I) 6 (fun _ => rfl) kws n p kw hkw hp

/-! ## Positions of indexed events

`checkX`'s and `primeCheckX`'s `xA`/`xA'` writes and reads, identified with
their positions in `G.threadEvents`, so that `po`-edges between events of
different `(loc, op)` follow from `threadEvents_pairwise_po`. -/

/-- `primeCheckX`'s `n`-th `xA'`-write is at position `n*6` of
`G.threadEvents Tid.primeCheckX`. -/
theorem primeCheckX_xA'_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {cnts : List (Fin 4)}
    (hw2 : G.threadWord Tid.primeCheckX = (primeCheckXBlockWord I cnts).map some)
    (n : ℕ) {cn : Fin 4} (hcn : cnts[n]? = some cn) :
    ∃ hlen : n * 6 < (G.threadEvents Tid.primeCheckX).length,
      G.nthWrite Tid.primeCheckX Loc.xA' n =
        some ((G.threadEvents Tid.primeCheckX)[n * 6]'hlen).1 := by
  have hnlen : n < cnts.length := (List.getElem?_eq_some_iff.mp hcn).1
  have hone_w : ∀ c : Fin 4, (primeCheckXBlockElems I c).filter
      (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeCheckX Loc.xA' (Val.primeTag Tid.primeCheckX c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX)] := by
    intro c
    unfold primeCheckXBlockElems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_w : (((primeCheckXBlockWord I cnts).take (n * 6)).filter
      (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.wt)).length = n := by
    rw [primeCheckXBlockWord_eq_flatMap,
      list_take_flatMap_uniform (primeCheckXBlockElems I) 6 (fun _ => rfl) cnts n (by omega),
      list_filter_flatMap_distrib]
    simp only [hone_w]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeCheckX).length = (primeCheckXBlockWord I cnts).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeCheckXBlockWord I cnts).length = 6 * cnts.length := by
    rw [primeCheckXBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (cnts.map (fun a => (primeCheckXBlockElems I a).length))
        = cnts.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_w : n * 6 < (G.threadEvents Tid.primeCheckX).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_w : (primeCheckXBlockWord I cnts)[n * 6]? =
      some (⟨EventLabel.wt Tid.primeCheckX Loc.xA' (Val.primeTag Tid.primeCheckX cn), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX) := by
    rw [primeCheckXBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeCheckXBlockElems I) 6 (fun _ => rfl) cnts n
      0 cn hcn (by norm_num)
    rw [show n * 6 + 0 = n * 6 from by omega] at hget
    rw [hget]
    unfold primeCheckXBlockElems
    rfl
  refine ⟨hlen_w, ?_⟩
  have hwpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.xA') (op := OpType.wt)
    hw2 hlen_w hlabP_w rfl rfl hcount_w
  rwa [show G.nthEvent Tid.primeCheckX Loc.xA' OpType.wt n = G.nthWrite Tid.primeCheckX Loc.xA' n
    from rfl] at hwpos

/-- `checkX`'s `(j+1)`-th `xA`-write (block `kws[j]`) is at position `4+j*6`
of `G.threadEvents Tid.checkX`. -/
theorem checkX_xA_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : I.Γ} {kws : List (Fin 4 × Option I.Γ)}
    (hw1 : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option I.Γ} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 4 + j * 6 < (G.threadEvents Tid.checkX).length,
      G.nthWrite Tid.checkX Loc.xA (j + 1) =
        some ((G.threadEvents Tid.checkX)[4 + j * 6]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hb0count : ((checkXBlock0Elems I v0).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt)).length = 1 := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rfl
  have hone_ew : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkX Loc.xA (Val.primeTag Tid.checkX (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    intro kw
    unfold checkXBlockRestElems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_ew : (((checkXBlockWord I v0 kws).take (4 + j * 6)).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt)).length = 1 + j := by
    have heq : checkXBlockWord I v0 kws =
        checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I) := rfl
    have hb0len : (checkXBlock0Elems I v0).length = 4 := rfl
    rw [heq, List.take_append, hb0len, Nat.add_sub_cancel_left,
      list_take_flatMap_uniform (checkXBlockRestElems I) 6 (fun _ => rfl) kws j (by omega),
      List.take_of_length_le (hb0len ▸ Nat.le_add_right 4 (j * 6)), List.filter_append,
      List.length_append, hb0count, list_filter_flatMap_distrib]
    congr 1
    simp only [hone_ew]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.checkX).length = (checkXBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_ew : 4 + j * 6 < (G.threadEvents Tid.checkX).length := by
    have hb0len : (checkXBlock0Elems I v0).length = 4 := rfl
    have hbrlen : (kws.flatMap (checkXBlockRestElems I)).length = 6 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (checkXBlockRestElems I a).length))
          = kws.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (checkXBlockWord I v0 kws).length = 4 + 6 * kws.length := by
      show (checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_ew : (checkXBlockWord I v0 kws)[4 + j * 6]? =
      some (⟨EventLabel.wt Tid.checkX Loc.xA (Val.primeTag Tid.checkX (kwj.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
    have hget := checkXBlockWord_blockRest_pos I v0 kws j 0 kwj hkj (by norm_num)
    rw [show 4 + j * 6 + 0 = 4 + j * 6 from by omega] at hget
    rw [hget]
    unfold checkXBlockRestElems
    rfl
  refine ⟨hlen_ew, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.xA) (op := OpType.wt)
    hw1 hlen_ew hlabP_ew rfl rfl hcount_ew
  rwa [show G.nthEvent Tid.checkX Loc.xA OpType.wt (1 + j) = G.nthWrite Tid.checkX Loc.xA (j + 1)
    from by rw [Nat.add_comm]; rfl] at hewpos

/-- `primeCheckX`'s `n`-th `xA`-read is at position `n*6+4` of
`G.threadEvents Tid.primeCheckX`. -/
theorem primeCheckX_xA_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {cnts : List (Fin 4)}
    (hw2 : G.threadWord Tid.primeCheckX = (primeCheckXBlockWord I cnts).map some)
    (n : ℕ) {c0 : Fin 4} (hc0 : cnts[n]? = some c0) :
    ∃ hlen : n * 6 + 4 < (G.threadEvents Tid.primeCheckX).length,
      G.nthRead Tid.primeCheckX Loc.xA n =
        some ((G.threadEvents Tid.primeCheckX)[n * 6 + 4]'hlen).1 := by
  have hnlen : n < cnts.length := (List.getElem?_eq_some_iff.mp hc0).1
  have hsplit := list_take_flatMap_uniform_offset (primeCheckXBlockElems I) 6 (fun _ => rfl)
    cnts n 4 c0 hc0 (by norm_num)
  have hpartial : ((primeCheckXBlockElems I c0).take 4).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) = [] := by
    unfold primeCheckXBlockElems
    rfl
  have hone : ∀ c : Fin 4, (primeCheckXBlockElems I c).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeCheckX Loc.xA (Val.primeTag Tid.checkX c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX)] := by
    intro c
    unfold primeCheckXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((primeCheckXBlockWord I cnts).take (n * 6 + 4)).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd)).length = n := by
    rw [primeCheckXBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeCheckX).length = (primeCheckXBlockWord I cnts).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeCheckXBlockWord I cnts).length = 6 * cnts.length := by
    rw [primeCheckXBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (cnts.map (fun a => (primeCheckXBlockElems I a).length))
        = cnts.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_er : n * 6 + 4 < (G.threadEvents Tid.primeCheckX).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_er : (primeCheckXBlockWord I cnts)[n * 6 + 4]? =
      some (⟨EventLabel.rd Tid.primeCheckX Loc.xA (Val.primeTag Tid.checkX c0), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX) := by
    rw [primeCheckXBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeCheckXBlockElems I) 6 (fun _ => rfl) cnts n
      4 c0 hc0 (by norm_num)
    rw [hget]
    unfold primeCheckXBlockElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.xA) (op := OpType.rd)
    hw2 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.primeCheckX Loc.xA OpType.rd n = G.nthRead Tid.primeCheckX Loc.xA n
    from rfl] at herpos

/-- `checkX`'s `j`-th `xA'`-read (block `kws[j]`; block 0 has none) is at
position `8+j*6` of `G.threadEvents Tid.checkX`. -/
theorem checkX_xA'_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : I.Γ} {kws : List (Fin 4 × Option I.Γ)}
    (hw1 : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option I.Γ} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 8 + j * 6 < (G.threadEvents Tid.checkX).length,
      G.nthRead Tid.checkX Loc.xA' j =
        some ((G.threadEvents Tid.checkX)[8 + j * 6]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hone_er : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkX Loc.xA' (Val.primeTag Tid.primeCheckX kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    intro kw
    unfold checkXBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((checkXBlockWord I v0 kws).take (8 + j * 6)).filter
      (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.rd)).length = j := by
    have heq : checkXBlockWord I v0 kws =
        checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I) := rfl
    have hb0len : (checkXBlock0Elems I v0).length = 4 := rfl
    have hle4 : (checkXBlock0Elems I v0).length ≤ 8 + j * 6 := by rw [hb0len]; omega
    have hb0nil : (checkXBlock0Elems I v0).filter
        (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.rd) = [] := by
      unfold checkXBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hsplit := list_take_flatMap_uniform_offset (checkXBlockRestElems I) 6 (fun _ => rfl)
      kws j 4 kwj hkj (by norm_num)
    have hpartial : ((checkXBlockRestElems I kwj).take 4).filter
        (fun l => l.1.loc = Loc.xA' ∧ l.1.op = OpType.rd) = [] := by
      unfold checkXBlockRestElems
      rfl
    have hsub : 8 + j * 6 - (checkXBlock0Elems I v0).length = j * 6 + 4 := by
      rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle4, hsub, hsplit, List.filter_append,
      List.filter_append, hb0nil, hpartial, List.nil_append, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_er]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.checkX).length = (checkXBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_er : 8 + j * 6 < (G.threadEvents Tid.checkX).length := by
    have hb0len : (checkXBlock0Elems I v0).length = 4 := rfl
    have hbrlen : (kws.flatMap (checkXBlockRestElems I)).length = 6 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (checkXBlockRestElems I a).length))
          = kws.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (checkXBlockWord I v0 kws).length = 4 + 6 * kws.length := by
      show (checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_er : (checkXBlockWord I v0 kws)[8 + j * 6]? =
      some (⟨EventLabel.rd Tid.checkX Loc.xA' (Val.primeTag Tid.primeCheckX kwj.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
    have hget := checkXBlockWord_blockRest_pos I v0 kws j 4 kwj hkj (by norm_num)
    rw [show 4 + j * 6 + 4 = 8 + j * 6 from by omega] at hget
    rw [hget]
    unfold checkXBlockRestElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.xA') (op := OpType.rd)
    hw1 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.checkX Loc.xA' OpType.rd j = G.nthRead Tid.checkX Loc.xA' j
    from rfl] at herpos

/-- Two positions of `G.threadEvents t` in increasing order give
`po`-related events. -/
theorem ExecutionGraph.po_of_threadEvents_pos_lt {D : Domains} (G : ExecutionGraph D) (t : D.Tid)
    {p1 p2 : ℕ} (h1 : p1 < (G.threadEvents t).length) (h2 : p2 < (G.threadEvents t).length)
    (hlt : p1 < p2) :
    G.po ((G.threadEvents t)[p1]'h1).1 ((G.threadEvents t)[p2]'h2).1 :=
  (List.pairwise_iff_getElem.mp (G.threadEvents_pairwise_po t)) p1 p2 h1 h2 hlt

/-- Eq. (16)'s `xA`/`xA'` pair (`CheckX`/`PrimeCheckX`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`checkX_shape_inv`, `primeCheckX_shape_inv`). -/
theorem checkX_primeCheckX_xA_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.primeCheckX Tid.checkX Loc.xA Loc.xA' := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := checkX_run_of_reaches I G hG
  obtain ⟨v0, js, kws, -, -, hkwsval, hσ1⟩ := checkX_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := primeCheckX_run_of_reaches I G hG
  obtain ⟨M, cnts, -, -, hcntsval, hσ2⟩ := primeCheckX_shape_inv I hrun2
  have hw1 : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkX, hσ1]
  have hw2 : G.threadWord Tid.primeCheckX = (primeCheckXBlockWord I cnts).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeCheckX, hσ2]
  -- `checkX`'s `i`-th `xA`-write: value `⟨checkX, (i+1) mod 4⟩`, in block `kws[i-1]` for `i ≥ 1`.
  have hWp : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.checkX Loc.xA i = some w →
      (∃ c : Fin 4, w.val = Val.primeTag Tid.checkX c ∧ c.val = (i + 1) % 4) ∧
      ∀ i', i = i' + 1 → i' < kws.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hw
    rcases i with _ | i'
    · have hf := (checkXBlockWord_xA_write_val0 I v0 kws).symm.trans hf
      refine ⟨⟨1, ?_, rfl⟩, fun i' h => absurd h (by omega)⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
    · have hf := (checkXBlockWord_xA_write_val_succ I v0 kws i').symm.trans hf
      rcases hk : kws[i']? with _ | kw
      · rw [hk] at hf; simp at hf
      · rw [hk] at hf
        have hlt := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨w', hkw⟩ := hkwsval i' hlt
        rw [hk] at hkw
        have hkw1 : kw.1.val = (1 + i') % 4 := by rw [Option.some.inj hkw]
        refine ⟨⟨kw.1 + 1, ?_, ?_⟩, fun j h => by omega⟩
        · rw [Event.val, hlab, ← Option.some.inj hf]
          rfl
        · rw [Fin.val_add, hkw1]; simp; omega
  -- `primeCheckX`'s `j`-th `xA`-read: value `⟨checkX, (j+1) mod 4⟩`, in block `cnts[j]`.
  have hRp : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.primeCheckX Loc.xA j = some r →
      (∃ c : Fin 4, r.val = Val.primeTag Tid.checkX c ∧ c.val = (j + 1) % 4) ∧
      j < cnts.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (primeCheckXBlockWord_xA_read_val I cnts j).symm.trans hf
    rcases hc : cnts[j]? with _ | c
    · rw [hc] at hf; simp at hf
    · rw [hc] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hc).1
      have hcv := hcntsval j hlt
      rw [hc] at hcv
      refine ⟨⟨c, ?_, by rw [Option.some.inj hcv]⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `primeCheckX`'s `i`-th `xA'`-write: value `⟨primeCheckX, (i+1) mod 4⟩`, in block `cnts[i]`.
  have hWq : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.primeCheckX Loc.xA' i = some w →
      (∃ c : Fin 4, w.val = Val.primeTag Tid.primeCheckX c ∧ c.val = (i + 1) % 4) ∧
      i < cnts.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    have hf := (primeCheckXBlockWord_xA'_write_val I cnts i).symm.trans hf
    rcases hc : cnts[i]? with _ | c
    · rw [hc] at hf; simp at hf
    · rw [hc] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hc).1
      have hcv := hcntsval i hlt
      rw [hc] at hcv
      refine ⟨⟨c, ?_, by rw [Option.some.inj hcv]⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `checkX`'s `j`-th `xA'`-read: value `⟨primeCheckX, (j+1) mod 4⟩`, in block `kws[j]`.
  have hRq : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.checkX Loc.xA' j = some r →
      (∃ c : Fin 4, r.val = Val.primeTag Tid.primeCheckX c ∧ c.val = (j + 1) % 4) ∧
      j < kws.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hr
    have hf := (checkXBlockWord_xA'_read_val I v0 kws j).symm.trans hf
    rcases hk : kws[j]? with _ | kw
    · rw [hk] at hf; simp at hf
    · rw [hk] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨w', hkw⟩ := hkwsval j hlt
      rw [hk] at hkw
      have hkw1 : kw.1.val = (1 + j) % 4 := by rw [Option.some.inj hkw]
      refine ⟨⟨kw.1, ?_, by omega⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  have hRpEvent := fun {j : ℕ} {r : Event (domainOf I)}
      (hr : G.nthRead Tid.primeCheckX Loc.xA j = some r) => G.nthEvent_index hr
  have hRqEvent := fun {j : ℕ} {r : Event (domainOf I)}
      (hr : G.nthRead Tid.checkX Loc.xA' j = some r) => G.nthEvent_index hr
  -- Every block index below `cnts.length`/`kws.length` has an entry.
  have hcnt : ∀ {n : ℕ}, n < cnts.length → ∃ c, cnts[n]? = some c :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  have hkw : ∀ {n : ℕ}, n < kws.length → ∃ kw, kws[n]? = some kw :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWp hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRp hr
    rw [hc, hc'] at hv
    injection hv with _ hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWq hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRq hr
    rw [hc, hc'] at hv
    injection hv with _ hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨⟨c, hc, -⟩, -⟩ := hRp hr
    have hwmem := (G.rf_subset hrf).1
    have htid : w.tid = Tid.checkX :=
      G_writer_val_tid I G hG hwmem (G.rf_subset hrf).2.2.1
        (by rw [G.rf_matches hrf, hc]; rfl)
    exact G.exists_nthWrite_of_rf hrf htid (hRpEvent hr).2.2.1
  · intro j w r hr hrf
    obtain ⟨⟨c, hc, -⟩, -⟩ := hRq hr
    have hwmem := (G.rf_subset hrf).1
    have htid : w.tid = Tid.primeCheckX :=
      G_writer_val_tid I G hG hwmem (G.rf_subset hrf).2.2.1
        (by rw [G.rf_matches hrf, hc]; rfl)
    exact G.exists_nthWrite_of_rf hrf htid (hRqEvent hr).2.2.1
  · -- `primeCheckX`: `r(xA)` at `i*6+4` precedes `w(xA')` at `ℓ*6`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨c, hc⟩ := hcnt (hRp hr).2
    obtain ⟨c', hc'⟩ := hcnt (hWq hw).2
    obtain ⟨hlenR, hposR⟩ := primeCheckX_xA_read_nthRead_pos I G hw2 i hc
    obtain ⟨hlenW, hposW⟩ := primeCheckX_xA'_write_nthWrite_pos I G hw2 ℓ hc'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.primeCheckX hlenR hlenW (by omega)
  · -- `checkX`: `r(xA')` at `8+i*6` precedes `w(xA)` at `4+(ℓ-1)*6`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (hRq hr).2
    obtain ⟨kw', hk'⟩ := hkw ((hWp hw).2 ℓ' rfl)
    obtain ⟨hlenR, hposR⟩ := checkX_xA'_read_nthRead_pos I G hw1 i hk
    obtain ⟨hlenW, hposW⟩ := checkX_xA_write_nthWrite_pos I G hw1 ℓ' hk'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.checkX hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    obtain ⟨c, hc⟩ := hcnt (n := i) (by have := (hWq hw).2; omega)
    exact ⟨_, (primeCheckX_xA_read_nthRead_pos I G hw2 i hc).2⟩
  · intro i ℓ w hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (n := i) (by have := (hWp hw).2 ℓ' rfl; omega)
    exact ⟨_, (checkX_xA'_read_nthRead_pos I G hw1 i hk).2⟩

theorem no_skipping_checkX_primeCheckX_xA (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i k : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.checkX Loc.xA i = some ew)
    (her : G.nthRead Tid.primeCheckX Loc.xA k = some er) (hrf : G.rf ew er) :
    i = k :=
  ((checkX_primeCheckX_xA_noSkipPair I G hG).no_skipping hG.1.1 k).1 hew her hrf

theorem no_skipping_checkX_primeCheckX_xA' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (n m : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeCheckX Loc.xA' n = some ew)
    (her : G.nthRead Tid.checkX Loc.xA' m = some er) (hrf : G.rf ew er) :
    n = m :=
  ((checkX_primeCheckX_xA_noSkipPair I G hG).no_skipping hG.1.1 m).2 hew her hrf

/-! ## Eq. (16)'s `yA`/`yA'` pair (mirror of `xA`/`xA'` within `CheckY`/`PrimeCheckY`) -/

/-- `checkY`'s `yA`-write value at filtered position `0` (block 0). -/
theorem checkYBlockWord_yA_write_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((checkYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.checkY Loc.yA (Val.primeTag Tid.checkY 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkY Loc.yA (Val.primeTag Tid.checkY 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `checkY`'s `yA`-write value at filtered position `i + 1` (block `kws[i]`),
in terms of `kws[i].1`. -/
theorem checkYBlockWord_yA_write_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((checkYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.checkY Loc.yA (Val.primeTag Tid.checkY
        (kw.1 + 1)), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkY Loc.yA (Val.primeTag Tid.checkY 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.checkY Loc.yA
        (Val.primeTag Tid.checkY (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.checkY Loc.yA (Val.primeTag Tid.checkY (kw.1 + 1)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkY)] := by
      intro kw
      unfold checkYBlockRestElems
      rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

/-- `primeCheckY`'s `yA`-read value at filtered position `j`:
`Val.primeTag Tid.checkY c` for block `cnts[j] = c`. -/
theorem primeCheckYBlockWord_yA_read_val (I : PCPInstance) (cnts : List (Fin 4)) (j : ℕ) :
    ((primeCheckYBlockWord I cnts).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd))[j]? =
      (cnts[j]?).map (fun c => (⟨EventLabel.rd Tid.primeCheckY Loc.yA
        (Val.primeTag Tid.checkY c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckY)) := by
  have hone : ∀ c : Fin 4, (primeCheckYBlockElems I c).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeCheckY Loc.yA (Val.primeTag Tid.checkY c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY)] := by
    intro c
    unfold primeCheckYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeCheckYBlockWord I cnts).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) =
      cnts.map (fun c => (⟨EventLabel.rd Tid.primeCheckY Loc.yA
        (Val.primeTag Tid.checkY c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckY)) := by
    rw [primeCheckYBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ cnts
  rw [hflat, List.getElem?_map]

/-- `primeCheckY`'s `yA'`-write value at filtered position `j` (offset `0`):
`Val.primeTag Tid.primeCheckY c`. -/
theorem primeCheckYBlockWord_yA'_write_val (I : PCPInstance) (cnts : List (Fin 4)) (j : ℕ) :
    ((primeCheckYBlockWord I cnts).filter (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.wt))[j]? =
      (cnts[j]?).map (fun c => (⟨EventLabel.wt Tid.primeCheckY Loc.yA'
        (Val.primeTag Tid.primeCheckY c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckY)) := by
  have hone : ∀ c : Fin 4, (primeCheckYBlockElems I c).filter
      (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeCheckY Loc.yA' (Val.primeTag Tid.primeCheckY c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY)] := by
    intro c
    unfold primeCheckYBlockElems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeCheckYBlockWord I cnts).filter
      (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.wt) =
      cnts.map (fun c => (⟨EventLabel.wt Tid.primeCheckY Loc.yA'
        (Val.primeTag Tid.primeCheckY c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckY)) := by
    rw [primeCheckYBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ cnts
  rw [hflat, List.getElem?_map]

/-- `checkY`'s `yA'`-read value at filtered position `j`: block 0 has no
`yA'`-read, so position `j` is in block `kws[j]`, with value
`Val.primeTag Tid.primeCheckY kw.1`. -/
theorem checkYBlockWord_yA'_read_val (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (j : ℕ) :
    ((checkYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.rd))[j]? =
      (kws[j]?).map (fun kw => (⟨EventLabel.rd Tid.checkY Loc.yA'
        (Val.primeTag Tid.primeCheckY kw.1), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.rd) =
      [] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.checkY Loc.yA'
        (Val.primeTag Tid.primeCheckY kw.1), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkY Loc.yA' (Val.primeTag Tid.primeCheckY kw.1), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkY)] := by
      intro kw
      unfold checkYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.nil_append, List.getElem?_map]

/-- Position of offset `p` of `checkY`'s `blockRest` block `n` (`kws[n]`) in
its word: `4 + n * 6 + p`. -/
theorem checkYBlockWord_blockRest_pos (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (n p : ℕ) (kw : Fin 4 × Option (Fin I.n)) (hkw : kws[n]? = some kw)
    (hp : p < 6) :
    (checkYBlockWord I v0 kws)[4 + n * 6 + p]? = (checkYBlockRestElems I kw)[p]? := by
  have heq : checkYBlockWord I v0 kws =
      checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I) := rfl
  have hb0len : (checkYBlock0Elems I v0).length = 4 := rfl
  rw [heq, List.getElem?_append_right (by rw [hb0len]; omega), hb0len]
  have hi : 4 + n * 6 + p - 4 = n * 6 + p := by omega
  rw [hi]
  exact flatMap_uniform_getElem_fwd (checkYBlockRestElems I) 6 (fun _ => rfl) kws n p kw hkw hp

/-! ## Positions of indexed events

`checkY`'s and `primeCheckY`'s `yA`/`yA'` writes and reads, identified with
their positions in `G.threadEvents`. -/

/-- `primeCheckY`'s `n`-th `yA'`-write is at position `n*6` of
`G.threadEvents Tid.primeCheckY`. -/
theorem primeCheckY_yA'_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {cnts : List (Fin 4)}
    (hw2 : G.threadWord Tid.primeCheckY = (primeCheckYBlockWord I cnts).map some)
    (n : ℕ) {cn : Fin 4} (hcn : cnts[n]? = some cn) :
    ∃ hlen : n * 6 < (G.threadEvents Tid.primeCheckY).length,
      G.nthWrite Tid.primeCheckY Loc.yA' n =
        some ((G.threadEvents Tid.primeCheckY)[n * 6]'hlen).1 := by
  have hnlen : n < cnts.length := (List.getElem?_eq_some_iff.mp hcn).1
  have hone_w : ∀ c : Fin 4, (primeCheckYBlockElems I c).filter
      (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeCheckY Loc.yA' (Val.primeTag Tid.primeCheckY c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY)] := by
    intro c
    unfold primeCheckYBlockElems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_w : (((primeCheckYBlockWord I cnts).take (n * 6)).filter
      (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.wt)).length = n := by
    rw [primeCheckYBlockWord_eq_flatMap,
      list_take_flatMap_uniform (primeCheckYBlockElems I) 6 (fun _ => rfl) cnts n (by omega),
      list_filter_flatMap_distrib]
    simp only [hone_w]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeCheckY).length = (primeCheckYBlockWord I cnts).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeCheckYBlockWord I cnts).length = 6 * cnts.length := by
    rw [primeCheckYBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (cnts.map (fun a => (primeCheckYBlockElems I a).length))
        = cnts.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_w : n * 6 < (G.threadEvents Tid.primeCheckY).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_w : (primeCheckYBlockWord I cnts)[n * 6]? =
      some (⟨EventLabel.wt Tid.primeCheckY Loc.yA' (Val.primeTag Tid.primeCheckY cn), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY) := by
    rw [primeCheckYBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeCheckYBlockElems I) 6 (fun _ => rfl) cnts n
      0 cn hcn (by norm_num)
    rw [show n * 6 + 0 = n * 6 from by omega] at hget
    rw [hget]
    unfold primeCheckYBlockElems
    rfl
  refine ⟨hlen_w, ?_⟩
  have hwpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.yA') (op := OpType.wt)
    hw2 hlen_w hlabP_w rfl rfl hcount_w
  rwa [show G.nthEvent Tid.primeCheckY Loc.yA' OpType.wt n = G.nthWrite Tid.primeCheckY Loc.yA' n
    from rfl] at hwpos

/-- `checkY`'s `(j+1)`-th `yA`-write (block `kws[j]`) is at position `4+j*6`
of `G.threadEvents Tid.checkY`. -/
theorem checkY_yA_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 4 + j * 6 < (G.threadEvents Tid.checkY).length,
      G.nthWrite Tid.checkY Loc.yA (j + 1) =
        some ((G.threadEvents Tid.checkY)[4 + j * 6]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hb0count : ((checkYBlock0Elems I v0).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt)).length = 1 := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rfl
  have hone_ew : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkY Loc.yA (Val.primeTag Tid.checkY (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    intro kw
    unfold checkYBlockRestElems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_ew : (((checkYBlockWord I v0 kws).take (4 + j * 6)).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt)).length = 1 + j := by
    have heq : checkYBlockWord I v0 kws =
        checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I) := rfl
    have hb0len : (checkYBlock0Elems I v0).length = 4 := rfl
    rw [heq, List.take_append, hb0len, Nat.add_sub_cancel_left,
      list_take_flatMap_uniform (checkYBlockRestElems I) 6 (fun _ => rfl) kws j (by omega),
      List.take_of_length_le (hb0len ▸ Nat.le_add_right 4 (j * 6)), List.filter_append,
      List.length_append, hb0count, list_filter_flatMap_distrib]
    congr 1
    simp only [hone_ew]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.checkY).length = (checkYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_ew : 4 + j * 6 < (G.threadEvents Tid.checkY).length := by
    have hb0len : (checkYBlock0Elems I v0).length = 4 := rfl
    have hbrlen : (kws.flatMap (checkYBlockRestElems I)).length = 6 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (checkYBlockRestElems I a).length))
          = kws.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (checkYBlockWord I v0 kws).length = 4 + 6 * kws.length := by
      show (checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_ew : (checkYBlockWord I v0 kws)[4 + j * 6]? =
      some (⟨EventLabel.wt Tid.checkY Loc.yA (Val.primeTag Tid.checkY (kwj.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
    have hget := checkYBlockWord_blockRest_pos I v0 kws j 0 kwj hkj (by norm_num)
    rw [show 4 + j * 6 + 0 = 4 + j * 6 from by omega] at hget
    rw [hget]
    unfold checkYBlockRestElems
    rfl
  refine ⟨hlen_ew, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.yA) (op := OpType.wt)
    hw1 hlen_ew hlabP_ew rfl rfl hcount_ew
  rwa [show G.nthEvent Tid.checkY Loc.yA OpType.wt (1 + j) = G.nthWrite Tid.checkY Loc.yA (j + 1)
    from by rw [Nat.add_comm]; rfl] at hewpos

/-- `primeCheckY`'s `n`-th `yA`-read is at position `n*6+4` of
`G.threadEvents Tid.primeCheckY`. -/
theorem primeCheckY_yA_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {cnts : List (Fin 4)}
    (hw2 : G.threadWord Tid.primeCheckY = (primeCheckYBlockWord I cnts).map some)
    (n : ℕ) {c0 : Fin 4} (hc0 : cnts[n]? = some c0) :
    ∃ hlen : n * 6 + 4 < (G.threadEvents Tid.primeCheckY).length,
      G.nthRead Tid.primeCheckY Loc.yA n =
        some ((G.threadEvents Tid.primeCheckY)[n * 6 + 4]'hlen).1 := by
  have hnlen : n < cnts.length := (List.getElem?_eq_some_iff.mp hc0).1
  have hsplit := list_take_flatMap_uniform_offset (primeCheckYBlockElems I) 6 (fun _ => rfl)
    cnts n 4 c0 hc0 (by norm_num)
  have hpartial : ((primeCheckYBlockElems I c0).take 4).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) = [] := by
    unfold primeCheckYBlockElems
    rfl
  have hone : ∀ c : Fin 4, (primeCheckYBlockElems I c).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeCheckY Loc.yA (Val.primeTag Tid.checkY c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY)] := by
    intro c
    unfold primeCheckYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((primeCheckYBlockWord I cnts).take (n * 6 + 4)).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd)).length = n := by
    rw [primeCheckYBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeCheckY).length = (primeCheckYBlockWord I cnts).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeCheckYBlockWord I cnts).length = 6 * cnts.length := by
    rw [primeCheckYBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (cnts.map (fun a => (primeCheckYBlockElems I a).length))
        = cnts.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_er : n * 6 + 4 < (G.threadEvents Tid.primeCheckY).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_er : (primeCheckYBlockWord I cnts)[n * 6 + 4]? =
      some (⟨EventLabel.rd Tid.primeCheckY Loc.yA (Val.primeTag Tid.checkY c0), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY) := by
    rw [primeCheckYBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeCheckYBlockElems I) 6 (fun _ => rfl) cnts n
      4 c0 hc0 (by norm_num)
    rw [hget]
    unfold primeCheckYBlockElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.yA) (op := OpType.rd)
    hw2 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.primeCheckY Loc.yA OpType.rd n = G.nthRead Tid.primeCheckY Loc.yA n
    from rfl] at herpos

/-- `checkY`'s `j`-th `yA'`-read (block `kws[j]`; block 0 has none) is at
position `8+j*6` of `G.threadEvents Tid.checkY`. -/
theorem checkY_yA'_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 8 + j * 6 < (G.threadEvents Tid.checkY).length,
      G.nthRead Tid.checkY Loc.yA' j =
        some ((G.threadEvents Tid.checkY)[8 + j * 6]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hone_er : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkY Loc.yA' (Val.primeTag Tid.primeCheckY kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    intro kw
    unfold checkYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((checkYBlockWord I v0 kws).take (8 + j * 6)).filter
      (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.rd)).length = j := by
    have heq : checkYBlockWord I v0 kws =
        checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I) := rfl
    have hb0len : (checkYBlock0Elems I v0).length = 4 := rfl
    have hle4 : (checkYBlock0Elems I v0).length ≤ 8 + j * 6 := by rw [hb0len]; omega
    have hb0nil : (checkYBlock0Elems I v0).filter
        (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.rd) = [] := by
      unfold checkYBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hsplit := list_take_flatMap_uniform_offset (checkYBlockRestElems I) 6 (fun _ => rfl)
      kws j 4 kwj hkj (by norm_num)
    have hpartial : ((checkYBlockRestElems I kwj).take 4).filter
        (fun l => l.1.loc = Loc.yA' ∧ l.1.op = OpType.rd) = [] := by
      unfold checkYBlockRestElems
      rfl
    have hsub : 8 + j * 6 - (checkYBlock0Elems I v0).length = j * 6 + 4 := by
      rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle4, hsub, hsplit, List.filter_append,
      List.filter_append, hb0nil, hpartial, List.nil_append, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_er]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.checkY).length = (checkYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_er : 8 + j * 6 < (G.threadEvents Tid.checkY).length := by
    have hb0len : (checkYBlock0Elems I v0).length = 4 := rfl
    have hbrlen : (kws.flatMap (checkYBlockRestElems I)).length = 6 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (checkYBlockRestElems I a).length))
          = kws.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (checkYBlockWord I v0 kws).length = 4 + 6 * kws.length := by
      show (checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_er : (checkYBlockWord I v0 kws)[8 + j * 6]? =
      some (⟨EventLabel.rd Tid.checkY Loc.yA' (Val.primeTag Tid.primeCheckY kwj.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
    have hget := checkYBlockWord_blockRest_pos I v0 kws j 4 kwj hkj (by norm_num)
    rw [show 4 + j * 6 + 4 = 8 + j * 6 from by omega] at hget
    rw [hget]
    unfold checkYBlockRestElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.yA') (op := OpType.rd)
    hw1 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.checkY Loc.yA' OpType.rd j = G.nthRead Tid.checkY Loc.yA' j
    from rfl] at herpos

/-- Eq. (16)'s `yA`/`yA'` pair (`CheckY`/`PrimeCheckY`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`checkY_shape_inv`, `primeCheckY_shape_inv`). -/
theorem checkY_primeCheckY_yA_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.primeCheckY Tid.checkY Loc.yA Loc.yA' := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := checkY_run_of_reaches I G hG
  obtain ⟨v0, js, kws, -, -, hkwsval, hσ1⟩ := checkY_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := primeCheckY_run_of_reaches I G hG
  obtain ⟨M, cnts, -, -, hcntsval, hσ2⟩ := primeCheckY_shape_inv I hrun2
  have hw1 : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkY, hσ1]
  have hw2 : G.threadWord Tid.primeCheckY = (primeCheckYBlockWord I cnts).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeCheckY, hσ2]
  -- `checkY`'s `i`-th `yA`-write: value `⟨checkY, (i+1) mod 4⟩`, in block `kws[i-1]` for `i ≥ 1`.
  have hWp : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.checkY Loc.yA i = some w →
      (∃ c : Fin 4, w.val = Val.primeTag Tid.checkY c ∧ c.val = (i + 1) % 4) ∧
      ∀ i', i = i' + 1 → i' < kws.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hw
    rcases i with _ | i'
    · have hf := (checkYBlockWord_yA_write_val0 I v0 kws).symm.trans hf
      refine ⟨⟨1, ?_, rfl⟩, fun i' h => absurd h (by omega)⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
    · have hf := (checkYBlockWord_yA_write_val_succ I v0 kws i').symm.trans hf
      rcases hk : kws[i']? with _ | kw
      · rw [hk] at hf; simp at hf
      · rw [hk] at hf
        have hlt := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨w', hkw⟩ := hkwsval i' hlt
        rw [hk] at hkw
        have hkw1 : kw.1.val = (1 + i') % 4 := by rw [Option.some.inj hkw]
        refine ⟨⟨kw.1 + 1, ?_, ?_⟩, fun j h => by omega⟩
        · rw [Event.val, hlab, ← Option.some.inj hf]
          rfl
        · rw [Fin.val_add, hkw1]; simp; omega
  -- `primeCheckY`'s `j`-th `yA`-read: value `⟨checkY, (j+1) mod 4⟩`, in block `cnts[j]`.
  have hRp : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.primeCheckY Loc.yA j = some r →
      (∃ c : Fin 4, r.val = Val.primeTag Tid.checkY c ∧ c.val = (j + 1) % 4) ∧
      j < cnts.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (primeCheckYBlockWord_yA_read_val I cnts j).symm.trans hf
    rcases hc : cnts[j]? with _ | c
    · rw [hc] at hf; simp at hf
    · rw [hc] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hc).1
      have hcv := hcntsval j hlt
      rw [hc] at hcv
      refine ⟨⟨c, ?_, by rw [Option.some.inj hcv]⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `primeCheckY`'s `i`-th `yA'`-write: value `⟨primeCheckY, (i+1) mod 4⟩`, in block `cnts[i]`.
  have hWq : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.primeCheckY Loc.yA' i = some w →
      (∃ c : Fin 4, w.val = Val.primeTag Tid.primeCheckY c ∧ c.val = (i + 1) % 4) ∧
      i < cnts.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    have hf := (primeCheckYBlockWord_yA'_write_val I cnts i).symm.trans hf
    rcases hc : cnts[i]? with _ | c
    · rw [hc] at hf; simp at hf
    · rw [hc] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hc).1
      have hcv := hcntsval i hlt
      rw [hc] at hcv
      refine ⟨⟨c, ?_, by rw [Option.some.inj hcv]⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `checkY`'s `j`-th `yA'`-read: value `⟨primeCheckY, (j+1) mod 4⟩`, in block `kws[j]`.
  have hRq : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.checkY Loc.yA' j = some r →
      (∃ c : Fin 4, r.val = Val.primeTag Tid.primeCheckY c ∧ c.val = (j + 1) % 4) ∧
      j < kws.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hr
    have hf := (checkYBlockWord_yA'_read_val I v0 kws j).symm.trans hf
    rcases hk : kws[j]? with _ | kw
    · rw [hk] at hf; simp at hf
    · rw [hk] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨w', hkw⟩ := hkwsval j hlt
      rw [hk] at hkw
      have hkw1 : kw.1.val = (1 + j) % 4 := by rw [Option.some.inj hkw]
      refine ⟨⟨kw.1, ?_, by omega⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  have hRpEvent := fun {j : ℕ} {r : Event (domainOf I)}
      (hr : G.nthRead Tid.primeCheckY Loc.yA j = some r) => G.nthEvent_index hr
  have hRqEvent := fun {j : ℕ} {r : Event (domainOf I)}
      (hr : G.nthRead Tid.checkY Loc.yA' j = some r) => G.nthEvent_index hr
  -- Every block index below `cnts.length`/`kws.length` has an entry.
  have hcnt : ∀ {n : ℕ}, n < cnts.length → ∃ c, cnts[n]? = some c :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  have hkw : ∀ {n : ℕ}, n < kws.length → ∃ kw, kws[n]? = some kw :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWp hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRp hr
    rw [hc, hc'] at hv
    injection hv with _ hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWq hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRq hr
    rw [hc, hc'] at hv
    injection hv with _ hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨⟨c, hc, -⟩, -⟩ := hRp hr
    have hwmem := (G.rf_subset hrf).1
    have htid : w.tid = Tid.checkY :=
      G_writer_val_tid I G hG hwmem (G.rf_subset hrf).2.2.1
        (by rw [G.rf_matches hrf, hc]; rfl)
    exact G.exists_nthWrite_of_rf hrf htid (hRpEvent hr).2.2.1
  · intro j w r hr hrf
    obtain ⟨⟨c, hc, -⟩, -⟩ := hRq hr
    have hwmem := (G.rf_subset hrf).1
    have htid : w.tid = Tid.primeCheckY :=
      G_writer_val_tid I G hG hwmem (G.rf_subset hrf).2.2.1
        (by rw [G.rf_matches hrf, hc]; rfl)
    exact G.exists_nthWrite_of_rf hrf htid (hRqEvent hr).2.2.1
  · -- `primeCheckY`: `r(yA)` at `i*6+4` precedes `w(yA')` at `ℓ*6`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨c, hc⟩ := hcnt (hRp hr).2
    obtain ⟨c', hc'⟩ := hcnt (hWq hw).2
    obtain ⟨hlenR, hposR⟩ := primeCheckY_yA_read_nthRead_pos I G hw2 i hc
    obtain ⟨hlenW, hposW⟩ := primeCheckY_yA'_write_nthWrite_pos I G hw2 ℓ hc'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.primeCheckY hlenR hlenW (by omega)
  · -- `checkY`: `r(yA')` at `8+i*6` precedes `w(yA)` at `4+(ℓ-1)*6`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (hRq hr).2
    obtain ⟨kw', hk'⟩ := hkw ((hWp hw).2 ℓ' rfl)
    obtain ⟨hlenR, hposR⟩ := checkY_yA'_read_nthRead_pos I G hw1 i hk
    obtain ⟨hlenW, hposW⟩ := checkY_yA_write_nthWrite_pos I G hw1 ℓ' hk'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.checkY hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    obtain ⟨c, hc⟩ := hcnt (n := i) (by have := (hWq hw).2; omega)
    exact ⟨_, (primeCheckY_yA_read_nthRead_pos I G hw2 i hc).2⟩
  · intro i ℓ w hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (n := i) (by have := (hWp hw).2 ℓ' rfl; omega)
    exact ⟨_, (checkY_yA'_read_nthRead_pos I G hw1 i hk).2⟩

theorem no_skipping_checkY_primeCheckY_yA (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i k : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.checkY Loc.yA i = some ew)
    (her : G.nthRead Tid.primeCheckY Loc.yA k = some er) (hrf : G.rf ew er) :
    i = k :=
  ((checkY_primeCheckY_yA_noSkipPair I G hG).no_skipping hG.1.1 k).1 hew her hrf

theorem no_skipping_checkY_primeCheckY_yA' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (n m : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeCheckY Loc.yA' n = some ew)
    (her : G.nthRead Tid.checkY Loc.yA' m = some er) (hrf : G.rf ew er) :
    n = m :=
  ((checkY_primeCheckY_yA_noSkipPair I G hG).no_skipping hG.1.1 m).2 hew her hrf

/-! ## Eq. (16)'s `xB`/`xB'` pair (`CheckX`/`PrimeCheckX`)

`xB`/`xB'` sit one position after `xA`/`xA'` in every block of both threads
(`checkXBlockRestElems`: `w(xA)@0, w(xB)@1, r(xA)@2, r(xB)@3, r(xA')@4,
r(xB')@5`; likewise `primeCheckXBlockElems`), so every position formula of
the `xA`/`xA'` pair shifts by `+1`. -/

theorem checkXBlockWord_xB_write_val0 (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) :
    ((checkXBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.checkX Loc.xB (Val.primeTag Tid.checkX 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkX Loc.xB (Val.primeTag Tid.checkX 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

theorem checkXBlockWord_xB_write_val_succ (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) (i : ℕ) :
    ((checkXBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.checkX Loc.xB (Val.primeTag Tid.checkX
        (kw.1 + 1)), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkX Loc.xB (Val.primeTag Tid.checkX 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkXBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.checkX Loc.xB
        (Val.primeTag Tid.checkX (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.checkX Loc.xB (Val.primeTag Tid.checkX (kw.1 + 1)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkX)] := by
      intro kw
      unfold checkXBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

theorem primeCheckXBlockWord_xB_read_val (I : PCPInstance) (cnts : List (Fin 4)) (j : ℕ) :
    ((primeCheckXBlockWord I cnts).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd))[j]? =
      (cnts[j]?).map (fun c => (⟨EventLabel.rd Tid.primeCheckX Loc.xB
        (Val.primeTag Tid.checkX c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckX)) := by
  have hone : ∀ c : Fin 4, (primeCheckXBlockElems I c).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeCheckX Loc.xB (Val.primeTag Tid.checkX c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX)] := by
    intro c
    unfold primeCheckXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeCheckXBlockWord I cnts).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) =
      cnts.map (fun c => (⟨EventLabel.rd Tid.primeCheckX Loc.xB
        (Val.primeTag Tid.checkX c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckX)) := by
    rw [primeCheckXBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ cnts
  rw [hflat, List.getElem?_map]

theorem primeCheckXBlockWord_xB'_write_val (I : PCPInstance) (cnts : List (Fin 4)) (j : ℕ) :
    ((primeCheckXBlockWord I cnts).filter (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.wt))[j]? =
      (cnts[j]?).map (fun c => (⟨EventLabel.wt Tid.primeCheckX Loc.xB'
        (Val.primeTag Tid.primeCheckX c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckX)) := by
  have hone : ∀ c : Fin 4, (primeCheckXBlockElems I c).filter
      (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeCheckX Loc.xB' (Val.primeTag Tid.primeCheckX c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX)] := by
    intro c
    unfold primeCheckXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeCheckXBlockWord I cnts).filter
      (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.wt) =
      cnts.map (fun c => (⟨EventLabel.wt Tid.primeCheckX Loc.xB'
        (Val.primeTag Tid.primeCheckX c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckX)) := by
    rw [primeCheckXBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ cnts
  rw [hflat, List.getElem?_map]

theorem checkXBlockWord_xB'_read_val (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) (j : ℕ) :
    ((checkXBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.rd))[j]? =
      (kws[j]?).map (fun kw => (⟨EventLabel.rd Tid.checkX Loc.xB'
        (Val.primeTag Tid.primeCheckX kw.1), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.rd) =
      [] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkXBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.checkX Loc.xB'
        (Val.primeTag Tid.primeCheckX kw.1), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkX Loc.xB' (Val.primeTag Tid.primeCheckX kw.1), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkX)] := by
      intro kw
      unfold checkXBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.nil_append, List.getElem?_map]

/-- `primeCheckX`'s `n`-th `xB'`-write is at position `n*6+1`. -/
theorem primeCheckX_xB'_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {cnts : List (Fin 4)}
    (hw2 : G.threadWord Tid.primeCheckX = (primeCheckXBlockWord I cnts).map some)
    (n : ℕ) {cn : Fin 4} (hcn : cnts[n]? = some cn) :
    ∃ hlen : n * 6 + 1 < (G.threadEvents Tid.primeCheckX).length,
      G.nthWrite Tid.primeCheckX Loc.xB' n =
        some ((G.threadEvents Tid.primeCheckX)[n * 6 + 1]'hlen).1 := by
  have hnlen : n < cnts.length := (List.getElem?_eq_some_iff.mp hcn).1
  have hone_w : ∀ c : Fin 4, (primeCheckXBlockElems I c).filter
      (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeCheckX Loc.xB' (Val.primeTag Tid.primeCheckX c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX)] := by
    intro c
    unfold primeCheckXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hsplit := list_take_flatMap_uniform_offset (primeCheckXBlockElems I) 6 (fun _ => rfl)
    cnts n 1 cn hcn (by norm_num)
  have hpartial : ((primeCheckXBlockElems I cn).take 1).filter
      (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.wt) = [] := by
    unfold primeCheckXBlockElems
    rfl
  have hcount_w : (((primeCheckXBlockWord I cnts).take (n * 6 + 1)).filter
      (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.wt)).length = n := by
    rw [primeCheckXBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_w]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeCheckX).length = (primeCheckXBlockWord I cnts).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeCheckXBlockWord I cnts).length = 6 * cnts.length := by
    rw [primeCheckXBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (cnts.map (fun a => (primeCheckXBlockElems I a).length))
        = cnts.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_w : n * 6 + 1 < (G.threadEvents Tid.primeCheckX).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_w : (primeCheckXBlockWord I cnts)[n * 6 + 1]? =
      some (⟨EventLabel.wt Tid.primeCheckX Loc.xB' (Val.primeTag Tid.primeCheckX cn), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX) := by
    rw [primeCheckXBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeCheckXBlockElems I) 6 (fun _ => rfl) cnts n
      1 cn hcn (by norm_num)
    rw [hget]
    unfold primeCheckXBlockElems
    rfl
  refine ⟨hlen_w, ?_⟩
  have hwpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.xB') (op := OpType.wt)
    hw2 hlen_w hlabP_w rfl rfl hcount_w
  rwa [show G.nthEvent Tid.primeCheckX Loc.xB' OpType.wt n = G.nthWrite Tid.primeCheckX Loc.xB' n
    from rfl] at hwpos

/-- `checkX`'s `(j+1)`-th `xB`-write (block `kws[j]`) is at position
`5+j*6`. -/
theorem checkX_xB_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : I.Γ} {kws : List (Fin 4 × Option I.Γ)}
    (hw1 : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option I.Γ} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 5 + j * 6 < (G.threadEvents Tid.checkX).length,
      G.nthWrite Tid.checkX Loc.xB (j + 1) =
        some ((G.threadEvents Tid.checkX)[5 + j * 6]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hb0count : ((checkXBlock0Elems I v0).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt)).length = 1 := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rfl
  have hone_ew : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkX Loc.xB (Val.primeTag Tid.checkX (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    intro kw
    unfold checkXBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have heq : checkXBlockWord I v0 kws =
      checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I) := rfl
  have hb0len : (checkXBlock0Elems I v0).length = 4 := rfl
  have hle4 : (checkXBlock0Elems I v0).length ≤ 5 + j * 6 := by rw [hb0len]; omega
  have hsplit := list_take_flatMap_uniform_offset (checkXBlockRestElems I) 6 (fun _ => rfl)
    kws j 1 kwj hkj (by norm_num)
  have hpartial : ((checkXBlockRestElems I kwj).take 1).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt) = [] := by
    unfold checkXBlockRestElems
    rfl
  have hsub : 5 + j * 6 - (checkXBlock0Elems I v0).length = j * 6 + 1 := by
    rw [hb0len]; omega
  have hcount_ew : (((checkXBlockWord I v0 kws).take (5 + j * 6)).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt)).length = 1 + j := by
    rw [heq, List.take_append, List.take_of_length_le hle4, hsub, hsplit, List.filter_append,
      List.filter_append, List.length_append, List.length_append, hb0count, hpartial]
    simp only [List.filter_nil, List.length_nil, Nat.add_zero, list_filter_flatMap_distrib,
      hone_ew]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.checkX).length = (checkXBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_ew : 5 + j * 6 < (G.threadEvents Tid.checkX).length := by
    have hbrlen : (kws.flatMap (checkXBlockRestElems I)).length = 6 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (checkXBlockRestElems I a).length))
          = kws.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (checkXBlockWord I v0 kws).length = 4 + 6 * kws.length := by
      show (checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_ew : (checkXBlockWord I v0 kws)[5 + j * 6]? =
      some (⟨EventLabel.wt Tid.checkX Loc.xB (Val.primeTag Tid.checkX (kwj.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
    have hget := checkXBlockWord_blockRest_pos I v0 kws j 1 kwj hkj (by norm_num)
    rw [show 4 + j * 6 + 1 = 5 + j * 6 from by omega] at hget
    rw [hget]
    unfold checkXBlockRestElems
    rfl
  refine ⟨hlen_ew, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.xB) (op := OpType.wt)
    hw1 hlen_ew hlabP_ew rfl rfl hcount_ew
  rwa [show G.nthEvent Tid.checkX Loc.xB OpType.wt (1 + j) = G.nthWrite Tid.checkX Loc.xB (j + 1)
    from by rw [Nat.add_comm]; rfl] at hewpos

/-- `primeCheckX`'s `n`-th `xB`-read is at position `n*6+5`. -/
theorem primeCheckX_xB_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {cnts : List (Fin 4)}
    (hw2 : G.threadWord Tid.primeCheckX = (primeCheckXBlockWord I cnts).map some)
    (n : ℕ) {c0 : Fin 4} (hc0 : cnts[n]? = some c0) :
    ∃ hlen : n * 6 + 5 < (G.threadEvents Tid.primeCheckX).length,
      G.nthRead Tid.primeCheckX Loc.xB n =
        some ((G.threadEvents Tid.primeCheckX)[n * 6 + 5]'hlen).1 := by
  have hnlen : n < cnts.length := (List.getElem?_eq_some_iff.mp hc0).1
  have hsplit := list_take_flatMap_uniform_offset (primeCheckXBlockElems I) 6 (fun _ => rfl)
    cnts n 5 c0 hc0 (by norm_num)
  have hpartial : ((primeCheckXBlockElems I c0).take 5).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) = [] := by
    unfold primeCheckXBlockElems
    rfl
  have hone : ∀ c : Fin 4, (primeCheckXBlockElems I c).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeCheckX Loc.xB (Val.primeTag Tid.checkX c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX)] := by
    intro c
    unfold primeCheckXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((primeCheckXBlockWord I cnts).take (n * 6 + 5)).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd)).length = n := by
    rw [primeCheckXBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeCheckX).length = (primeCheckXBlockWord I cnts).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeCheckXBlockWord I cnts).length = 6 * cnts.length := by
    rw [primeCheckXBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (cnts.map (fun a => (primeCheckXBlockElems I a).length))
        = cnts.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_er : n * 6 + 5 < (G.threadEvents Tid.primeCheckX).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_er : (primeCheckXBlockWord I cnts)[n * 6 + 5]? =
      some (⟨EventLabel.rd Tid.primeCheckX Loc.xB (Val.primeTag Tid.checkX c0), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckX) := by
    rw [primeCheckXBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeCheckXBlockElems I) 6 (fun _ => rfl) cnts n
      5 c0 hc0 (by norm_num)
    rw [hget]
    unfold primeCheckXBlockElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.xB) (op := OpType.rd)
    hw2 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.primeCheckX Loc.xB OpType.rd n = G.nthRead Tid.primeCheckX Loc.xB n
    from rfl] at herpos

/-- `checkX`'s `j`-th `xB'`-read (block `kws[j]`) is at position `9+j*6`. -/
theorem checkX_xB'_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : I.Γ} {kws : List (Fin 4 × Option I.Γ)}
    (hw1 : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option I.Γ} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 9 + j * 6 < (G.threadEvents Tid.checkX).length,
      G.nthRead Tid.checkX Loc.xB' j =
        some ((G.threadEvents Tid.checkX)[9 + j * 6]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hone_er : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkX Loc.xB' (Val.primeTag Tid.primeCheckX kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    intro kw
    unfold checkXBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((checkXBlockWord I v0 kws).take (9 + j * 6)).filter
      (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.rd)).length = j := by
    have heq : checkXBlockWord I v0 kws =
        checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I) := rfl
    have hb0len : (checkXBlock0Elems I v0).length = 4 := rfl
    have hle4 : (checkXBlock0Elems I v0).length ≤ 9 + j * 6 := by rw [hb0len]; omega
    have hb0nil : (checkXBlock0Elems I v0).filter
        (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.rd) = [] := by
      unfold checkXBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hsplit := list_take_flatMap_uniform_offset (checkXBlockRestElems I) 6 (fun _ => rfl)
      kws j 5 kwj hkj (by norm_num)
    have hpartial : ((checkXBlockRestElems I kwj).take 5).filter
        (fun l => l.1.loc = Loc.xB' ∧ l.1.op = OpType.rd) = [] := by
      unfold checkXBlockRestElems
      rfl
    have hsub : 9 + j * 6 - (checkXBlock0Elems I v0).length = j * 6 + 5 := by
      rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle4, hsub, hsplit, List.filter_append,
      List.filter_append, hb0nil, hpartial, List.nil_append, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_er]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.checkX).length = (checkXBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_er : 9 + j * 6 < (G.threadEvents Tid.checkX).length := by
    have hb0len : (checkXBlock0Elems I v0).length = 4 := rfl
    have hbrlen : (kws.flatMap (checkXBlockRestElems I)).length = 6 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (checkXBlockRestElems I a).length))
          = kws.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (checkXBlockWord I v0 kws).length = 4 + 6 * kws.length := by
      show (checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_er : (checkXBlockWord I v0 kws)[9 + j * 6]? =
      some (⟨EventLabel.rd Tid.checkX Loc.xB' (Val.primeTag Tid.primeCheckX kwj.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
    have hget := checkXBlockWord_blockRest_pos I v0 kws j 5 kwj hkj (by norm_num)
    rw [show 4 + j * 6 + 5 = 9 + j * 6 from by omega] at hget
    rw [hget]
    unfold checkXBlockRestElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.xB') (op := OpType.rd)
    hw1 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.checkX Loc.xB' OpType.rd j = G.nthRead Tid.checkX Loc.xB' j
    from rfl] at herpos

/-- Eq. (16)'s `xB`/`xB'` pair (`CheckX`/`PrimeCheckX`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`checkX_shape_inv`, `primeCheckX_shape_inv`). -/
theorem checkX_primeCheckX_xB_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.primeCheckX Tid.checkX Loc.xB Loc.xB' := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := checkX_run_of_reaches I G hG
  obtain ⟨v0, js, kws, -, -, hkwsval, hσ1⟩ := checkX_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := primeCheckX_run_of_reaches I G hG
  obtain ⟨M, cnts, -, -, hcntsval, hσ2⟩ := primeCheckX_shape_inv I hrun2
  have hw1 : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkX, hσ1]
  have hw2 : G.threadWord Tid.primeCheckX = (primeCheckXBlockWord I cnts).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeCheckX, hσ2]
  -- `checkX`'s `i`-th `xB`-write: value `⟨checkX, (i+1) mod 4⟩`, in block `kws[i-1]` for `i ≥ 1`.
  have hWp : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.checkX Loc.xB i = some w →
      (∃ c : Fin 4, w.val = Val.primeTag Tid.checkX c ∧ c.val = (i + 1) % 4) ∧
      ∀ i', i = i' + 1 → i' < kws.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hw
    rcases i with _ | i'
    · have hf := (checkXBlockWord_xB_write_val0 I v0 kws).symm.trans hf
      refine ⟨⟨1, ?_, rfl⟩, fun i' h => absurd h (by omega)⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
    · have hf := (checkXBlockWord_xB_write_val_succ I v0 kws i').symm.trans hf
      rcases hk : kws[i']? with _ | kw
      · rw [hk] at hf; simp at hf
      · rw [hk] at hf
        have hlt := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨w', hkw⟩ := hkwsval i' hlt
        rw [hk] at hkw
        have hkw1 : kw.1.val = (1 + i') % 4 := by rw [Option.some.inj hkw]
        refine ⟨⟨kw.1 + 1, ?_, ?_⟩, fun j h => by omega⟩
        · rw [Event.val, hlab, ← Option.some.inj hf]
          rfl
        · rw [Fin.val_add, hkw1]; simp; omega
  -- `primeCheckX`'s `j`-th `xB`-read: value `⟨checkX, (j+1) mod 4⟩`, in block `cnts[j]`.
  have hRp : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.primeCheckX Loc.xB j = some r →
      (∃ c : Fin 4, r.val = Val.primeTag Tid.checkX c ∧ c.val = (j + 1) % 4) ∧
      j < cnts.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (primeCheckXBlockWord_xB_read_val I cnts j).symm.trans hf
    rcases hc : cnts[j]? with _ | c
    · rw [hc] at hf; simp at hf
    · rw [hc] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hc).1
      have hcv := hcntsval j hlt
      rw [hc] at hcv
      refine ⟨⟨c, ?_, by rw [Option.some.inj hcv]⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `primeCheckX`'s `i`-th `xB'`-write: value `⟨primeCheckX, (i+1) mod 4⟩`, in block `cnts[i]`.
  have hWq : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.primeCheckX Loc.xB' i = some w →
      (∃ c : Fin 4, w.val = Val.primeTag Tid.primeCheckX c ∧ c.val = (i + 1) % 4) ∧
      i < cnts.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    have hf := (primeCheckXBlockWord_xB'_write_val I cnts i).symm.trans hf
    rcases hc : cnts[i]? with _ | c
    · rw [hc] at hf; simp at hf
    · rw [hc] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hc).1
      have hcv := hcntsval i hlt
      rw [hc] at hcv
      refine ⟨⟨c, ?_, by rw [Option.some.inj hcv]⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `checkX`'s `j`-th `xB'`-read: value `⟨primeCheckX, (j+1) mod 4⟩`, in block `kws[j]`.
  have hRq : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.checkX Loc.xB' j = some r →
      (∃ c : Fin 4, r.val = Val.primeTag Tid.primeCheckX c ∧ c.val = (j + 1) % 4) ∧
      j < kws.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hr
    have hf := (checkXBlockWord_xB'_read_val I v0 kws j).symm.trans hf
    rcases hk : kws[j]? with _ | kw
    · rw [hk] at hf; simp at hf
    · rw [hk] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨w', hkw⟩ := hkwsval j hlt
      rw [hk] at hkw
      have hkw1 : kw.1.val = (1 + j) % 4 := by rw [Option.some.inj hkw]
      refine ⟨⟨kw.1, ?_, by omega⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  have hRpEvent := fun {j : ℕ} {r : Event (domainOf I)}
      (hr : G.nthRead Tid.primeCheckX Loc.xB j = some r) => G.nthEvent_index hr
  have hRqEvent := fun {j : ℕ} {r : Event (domainOf I)}
      (hr : G.nthRead Tid.checkX Loc.xB' j = some r) => G.nthEvent_index hr
  -- Every block index below `cnts.length`/`kws.length` has an entry.
  have hcnt : ∀ {n : ℕ}, n < cnts.length → ∃ c, cnts[n]? = some c :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  have hkw : ∀ {n : ℕ}, n < kws.length → ∃ kw, kws[n]? = some kw :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWp hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRp hr
    rw [hc, hc'] at hv
    injection hv with _ hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWq hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRq hr
    rw [hc, hc'] at hv
    injection hv with _ hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨⟨c, hc, -⟩, -⟩ := hRp hr
    have hwmem := (G.rf_subset hrf).1
    have htid : w.tid = Tid.checkX :=
      G_writer_val_tid I G hG hwmem (G.rf_subset hrf).2.2.1
        (by rw [G.rf_matches hrf, hc]; rfl)
    exact G.exists_nthWrite_of_rf hrf htid (hRpEvent hr).2.2.1
  · intro j w r hr hrf
    obtain ⟨⟨c, hc, -⟩, -⟩ := hRq hr
    have hwmem := (G.rf_subset hrf).1
    have htid : w.tid = Tid.primeCheckX :=
      G_writer_val_tid I G hG hwmem (G.rf_subset hrf).2.2.1
        (by rw [G.rf_matches hrf, hc]; rfl)
    exact G.exists_nthWrite_of_rf hrf htid (hRqEvent hr).2.2.1
  · -- `primeCheckX`: `r(xB)` at `i*6+5` precedes `w(xB')` at `ℓ*6+1`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨c, hc⟩ := hcnt (hRp hr).2
    obtain ⟨c', hc'⟩ := hcnt (hWq hw).2
    obtain ⟨hlenR, hposR⟩ := primeCheckX_xB_read_nthRead_pos I G hw2 i hc
    obtain ⟨hlenW, hposW⟩ := primeCheckX_xB'_write_nthWrite_pos I G hw2 ℓ hc'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.primeCheckX hlenR hlenW (by omega)
  · -- `checkX`: `r(xB')` at `9+i*6` precedes `w(xB)` at `5+(ℓ-1)*6`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (hRq hr).2
    obtain ⟨kw', hk'⟩ := hkw ((hWp hw).2 ℓ' rfl)
    obtain ⟨hlenR, hposR⟩ := checkX_xB'_read_nthRead_pos I G hw1 i hk
    obtain ⟨hlenW, hposW⟩ := checkX_xB_write_nthWrite_pos I G hw1 ℓ' hk'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.checkX hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    obtain ⟨c, hc⟩ := hcnt (n := i) (by have := (hWq hw).2; omega)
    exact ⟨_, (primeCheckX_xB_read_nthRead_pos I G hw2 i hc).2⟩
  · intro i ℓ w hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (n := i) (by have := (hWp hw).2 ℓ' rfl; omega)
    exact ⟨_, (checkX_xB'_read_nthRead_pos I G hw1 i hk).2⟩

theorem no_skipping_checkX_primeCheckX_xB (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i k : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.checkX Loc.xB i = some ew)
    (her : G.nthRead Tid.primeCheckX Loc.xB k = some er) (hrf : G.rf ew er) :
    i = k :=
  ((checkX_primeCheckX_xB_noSkipPair I G hG).no_skipping hG.1.1 k).1 hew her hrf

theorem no_skipping_checkX_primeCheckX_xB' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (n m : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeCheckX Loc.xB' n = some ew)
    (her : G.nthRead Tid.checkX Loc.xB' m = some er) (hrf : G.rf ew er) :
    n = m :=
  ((checkX_primeCheckX_xB_noSkipPair I G hG).no_skipping hG.1.1 m).2 hew her hrf

theorem checkYBlockWord_yB_write_val0 (I : PCPInstance) (v0 : (Fin I.n))
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((checkYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.checkY Loc.yB (Val.primeTag Tid.checkY 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkY Loc.yB (Val.primeTag Tid.checkY 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

theorem checkYBlockWord_yB_write_val_succ (I : PCPInstance) (v0 : (Fin I.n))
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((checkYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.checkY Loc.yB (Val.primeTag Tid.checkY
        (kw.1 + 1)), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkY Loc.yB (Val.primeTag Tid.checkY 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.checkY Loc.yB
        (Val.primeTag Tid.checkY (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.checkY Loc.yB (Val.primeTag Tid.checkY (kw.1 + 1)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkY)] := by
      intro kw
      unfold checkYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

theorem primeCheckYBlockWord_yB_read_val (I : PCPInstance) (cnts : List (Fin 4)) (j : ℕ) :
    ((primeCheckYBlockWord I cnts).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd))[j]? =
      (cnts[j]?).map (fun c => (⟨EventLabel.rd Tid.primeCheckY Loc.yB
        (Val.primeTag Tid.checkY c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckY)) := by
  have hone : ∀ c : Fin 4, (primeCheckYBlockElems I c).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeCheckY Loc.yB (Val.primeTag Tid.checkY c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY)] := by
    intro c
    unfold primeCheckYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeCheckYBlockWord I cnts).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) =
      cnts.map (fun c => (⟨EventLabel.rd Tid.primeCheckY Loc.yB
        (Val.primeTag Tid.checkY c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckY)) := by
    rw [primeCheckYBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ cnts
  rw [hflat, List.getElem?_map]

theorem primeCheckYBlockWord_yB'_write_val (I : PCPInstance) (cnts : List (Fin 4)) (j : ℕ) :
    ((primeCheckYBlockWord I cnts).filter (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.wt))[j]? =
      (cnts[j]?).map (fun c => (⟨EventLabel.wt Tid.primeCheckY Loc.yB'
        (Val.primeTag Tid.primeCheckY c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckY)) := by
  have hone : ∀ c : Fin 4, (primeCheckYBlockElems I c).filter
      (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeCheckY Loc.yB' (Val.primeTag Tid.primeCheckY c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY)] := by
    intro c
    unfold primeCheckYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeCheckYBlockWord I cnts).filter
      (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.wt) =
      cnts.map (fun c => (⟨EventLabel.wt Tid.primeCheckY Loc.yB'
        (Val.primeTag Tid.primeCheckY c), rfl⟩ : ThreadLabel (domainOf I) Tid.primeCheckY)) := by
    rw [primeCheckYBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ cnts
  rw [hflat, List.getElem?_map]

theorem checkYBlockWord_yB'_read_val (I : PCPInstance) (v0 : (Fin I.n))
    (kws : List (Fin 4 × Option (Fin I.n))) (j : ℕ) :
    ((checkYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.rd))[j]? =
      (kws[j]?).map (fun kw => (⟨EventLabel.rd Tid.checkY Loc.yB'
        (Val.primeTag Tid.primeCheckY kw.1), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.rd) =
      [] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.checkY Loc.yB'
        (Val.primeTag Tid.primeCheckY kw.1), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkY Loc.yB' (Val.primeTag Tid.primeCheckY kw.1), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkY)] := by
      intro kw
      unfold checkYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.nil_append, List.getElem?_map]

/-- `primeCheckY`'s `n`-th `yB'`-write is at position `n*6+1`. -/
theorem primeCheckY_yB'_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {cnts : List (Fin 4)}
    (hw2 : G.threadWord Tid.primeCheckY = (primeCheckYBlockWord I cnts).map some)
    (n : ℕ) {cn : Fin 4} (hcn : cnts[n]? = some cn) :
    ∃ hlen : n * 6 + 1 < (G.threadEvents Tid.primeCheckY).length,
      G.nthWrite Tid.primeCheckY Loc.yB' n =
        some ((G.threadEvents Tid.primeCheckY)[n * 6 + 1]'hlen).1 := by
  have hnlen : n < cnts.length := (List.getElem?_eq_some_iff.mp hcn).1
  have hone_w : ∀ c : Fin 4, (primeCheckYBlockElems I c).filter
      (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeCheckY Loc.yB' (Val.primeTag Tid.primeCheckY c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY)] := by
    intro c
    unfold primeCheckYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hsplit := list_take_flatMap_uniform_offset (primeCheckYBlockElems I) 6 (fun _ => rfl)
    cnts n 1 cn hcn (by norm_num)
  have hpartial : ((primeCheckYBlockElems I cn).take 1).filter
      (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.wt) = [] := by
    unfold primeCheckYBlockElems
    rfl
  have hcount_w : (((primeCheckYBlockWord I cnts).take (n * 6 + 1)).filter
      (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.wt)).length = n := by
    rw [primeCheckYBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_w]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeCheckY).length = (primeCheckYBlockWord I cnts).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeCheckYBlockWord I cnts).length = 6 * cnts.length := by
    rw [primeCheckYBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (cnts.map (fun a => (primeCheckYBlockElems I a).length))
        = cnts.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_w : n * 6 + 1 < (G.threadEvents Tid.primeCheckY).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_w : (primeCheckYBlockWord I cnts)[n * 6 + 1]? =
      some (⟨EventLabel.wt Tid.primeCheckY Loc.yB' (Val.primeTag Tid.primeCheckY cn), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY) := by
    rw [primeCheckYBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeCheckYBlockElems I) 6 (fun _ => rfl) cnts n
      1 cn hcn (by norm_num)
    rw [hget]
    unfold primeCheckYBlockElems
    rfl
  refine ⟨hlen_w, ?_⟩
  have hwpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.yB') (op := OpType.wt)
    hw2 hlen_w hlabP_w rfl rfl hcount_w
  rwa [show G.nthEvent Tid.primeCheckY Loc.yB' OpType.wt n = G.nthWrite Tid.primeCheckY Loc.yB' n
    from rfl] at hwpos

/-- `checkY`'s `(j+1)`-th `yB`-write (block `kws[j]`) is at position
`5+j*6`. -/
theorem checkY_yB_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : (Fin I.n)} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 5 + j * 6 < (G.threadEvents Tid.checkY).length,
      G.nthWrite Tid.checkY Loc.yB (j + 1) =
        some ((G.threadEvents Tid.checkY)[5 + j * 6]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hb0count : ((checkYBlock0Elems I v0).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt)).length = 1 := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rfl
  have hone_ew : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.checkY Loc.yB (Val.primeTag Tid.checkY (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    intro kw
    unfold checkYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have heq : checkYBlockWord I v0 kws =
      checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I) := rfl
  have hb0len : (checkYBlock0Elems I v0).length = 4 := rfl
  have hle4 : (checkYBlock0Elems I v0).length ≤ 5 + j * 6 := by rw [hb0len]; omega
  have hsplit := list_take_flatMap_uniform_offset (checkYBlockRestElems I) 6 (fun _ => rfl)
    kws j 1 kwj hkj (by norm_num)
  have hpartial : ((checkYBlockRestElems I kwj).take 1).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) = [] := by
    unfold checkYBlockRestElems
    rfl
  have hsub : 5 + j * 6 - (checkYBlock0Elems I v0).length = j * 6 + 1 := by
    rw [hb0len]; omega
  have hcount_ew : (((checkYBlockWord I v0 kws).take (5 + j * 6)).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt)).length = 1 + j := by
    rw [heq, List.take_append, List.take_of_length_le hle4, hsub, hsplit, List.filter_append,
      List.filter_append, List.length_append, List.length_append, hb0count, hpartial]
    simp only [List.filter_nil, List.length_nil, Nat.add_zero, list_filter_flatMap_distrib,
      hone_ew]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.checkY).length = (checkYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_ew : 5 + j * 6 < (G.threadEvents Tid.checkY).length := by
    have hbrlen : (kws.flatMap (checkYBlockRestElems I)).length = 6 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (checkYBlockRestElems I a).length))
          = kws.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (checkYBlockWord I v0 kws).length = 4 + 6 * kws.length := by
      show (checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_ew : (checkYBlockWord I v0 kws)[5 + j * 6]? =
      some (⟨EventLabel.wt Tid.checkY Loc.yB (Val.primeTag Tid.checkY (kwj.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
    have hget := checkYBlockWord_blockRest_pos I v0 kws j 1 kwj hkj (by norm_num)
    rw [show 4 + j * 6 + 1 = 5 + j * 6 from by omega] at hget
    rw [hget]
    unfold checkYBlockRestElems
    rfl
  refine ⟨hlen_ew, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.yB) (op := OpType.wt)
    hw1 hlen_ew hlabP_ew rfl rfl hcount_ew
  rwa [show G.nthEvent Tid.checkY Loc.yB OpType.wt (1 + j) = G.nthWrite Tid.checkY Loc.yB (j + 1)
    from by rw [Nat.add_comm]; rfl] at hewpos

/-- `primeCheckY`'s `n`-th `yB`-read is at position `n*6+5`. -/
theorem primeCheckY_yB_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {cnts : List (Fin 4)}
    (hw2 : G.threadWord Tid.primeCheckY = (primeCheckYBlockWord I cnts).map some)
    (n : ℕ) {c0 : Fin 4} (hc0 : cnts[n]? = some c0) :
    ∃ hlen : n * 6 + 5 < (G.threadEvents Tid.primeCheckY).length,
      G.nthRead Tid.primeCheckY Loc.yB n =
        some ((G.threadEvents Tid.primeCheckY)[n * 6 + 5]'hlen).1 := by
  have hnlen : n < cnts.length := (List.getElem?_eq_some_iff.mp hc0).1
  have hsplit := list_take_flatMap_uniform_offset (primeCheckYBlockElems I) 6 (fun _ => rfl)
    cnts n 5 c0 hc0 (by norm_num)
  have hpartial : ((primeCheckYBlockElems I c0).take 5).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) = [] := by
    unfold primeCheckYBlockElems
    rfl
  have hone : ∀ c : Fin 4, (primeCheckYBlockElems I c).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeCheckY Loc.yB (Val.primeTag Tid.checkY c), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY)] := by
    intro c
    unfold primeCheckYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((primeCheckYBlockWord I cnts).take (n * 6 + 5)).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd)).length = n := by
    rw [primeCheckYBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeCheckY).length = (primeCheckYBlockWord I cnts).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeCheckYBlockWord I cnts).length = 6 * cnts.length := by
    rw [primeCheckYBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (cnts.map (fun a => (primeCheckYBlockElems I a).length))
        = cnts.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_er : n * 6 + 5 < (G.threadEvents Tid.primeCheckY).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_er : (primeCheckYBlockWord I cnts)[n * 6 + 5]? =
      some (⟨EventLabel.rd Tid.primeCheckY Loc.yB (Val.primeTag Tid.checkY c0), rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeCheckY) := by
    rw [primeCheckYBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeCheckYBlockElems I) 6 (fun _ => rfl) cnts n
      5 c0 hc0 (by norm_num)
    rw [hget]
    unfold primeCheckYBlockElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.yB) (op := OpType.rd)
    hw2 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.primeCheckY Loc.yB OpType.rd n = G.nthRead Tid.primeCheckY Loc.yB n
    from rfl] at herpos

/-- `checkY`'s `j`-th `yB'`-read (block `kws[j]`) is at position `9+j*6`. -/
theorem checkY_yB'_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : (Fin I.n)} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 9 + j * 6 < (G.threadEvents Tid.checkY).length,
      G.nthRead Tid.checkY Loc.yB' j =
        some ((G.threadEvents Tid.checkY)[9 + j * 6]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hone_er : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkY Loc.yB' (Val.primeTag Tid.primeCheckY kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    intro kw
    unfold checkYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((checkYBlockWord I v0 kws).take (9 + j * 6)).filter
      (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.rd)).length = j := by
    have heq : checkYBlockWord I v0 kws =
        checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I) := rfl
    have hb0len : (checkYBlock0Elems I v0).length = 4 := rfl
    have hle4 : (checkYBlock0Elems I v0).length ≤ 9 + j * 6 := by rw [hb0len]; omega
    have hb0nil : (checkYBlock0Elems I v0).filter
        (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.rd) = [] := by
      unfold checkYBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hsplit := list_take_flatMap_uniform_offset (checkYBlockRestElems I) 6 (fun _ => rfl)
      kws j 5 kwj hkj (by norm_num)
    have hpartial : ((checkYBlockRestElems I kwj).take 5).filter
        (fun l => l.1.loc = Loc.yB' ∧ l.1.op = OpType.rd) = [] := by
      unfold checkYBlockRestElems
      rfl
    have hsub : 9 + j * 6 - (checkYBlock0Elems I v0).length = j * 6 + 5 := by
      rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle4, hsub, hsplit, List.filter_append,
      List.filter_append, hb0nil, hpartial, List.nil_append, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_er]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.checkY).length = (checkYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_er : 9 + j * 6 < (G.threadEvents Tid.checkY).length := by
    have hb0len : (checkYBlock0Elems I v0).length = 4 := rfl
    have hbrlen : (kws.flatMap (checkYBlockRestElems I)).length = 6 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (checkYBlockRestElems I a).length))
          = kws.map (fun _ => 6) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (checkYBlockWord I v0 kws).length = 4 + 6 * kws.length := by
      show (checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_er : (checkYBlockWord I v0 kws)[9 + j * 6]? =
      some (⟨EventLabel.rd Tid.checkY Loc.yB' (Val.primeTag Tid.primeCheckY kwj.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
    have hget := checkYBlockWord_blockRest_pos I v0 kws j 5 kwj hkj (by norm_num)
    rw [show 4 + j * 6 + 5 = 9 + j * 6 from by omega] at hget
    rw [hget]
    unfold checkYBlockRestElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.yB') (op := OpType.rd)
    hw1 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.checkY Loc.yB' OpType.rd j = G.nthRead Tid.checkY Loc.yB' j
    from rfl] at herpos

/-- Eq. (16)'s `yB`/`yB'` pair (`CheckY`/`PrimeCheckY`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`checkY_shape_inv`, `primeCheckY_shape_inv`). -/
theorem checkY_primeCheckY_yB_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.primeCheckY Tid.checkY Loc.yB Loc.yB' := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := checkY_run_of_reaches I G hG
  obtain ⟨v0, js, kws, -, -, hkwsval, hσ1⟩ := checkY_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := primeCheckY_run_of_reaches I G hG
  obtain ⟨M, cnts, -, -, hcntsval, hσ2⟩ := primeCheckY_shape_inv I hrun2
  have hw1 : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkY, hσ1]
  have hw2 : G.threadWord Tid.primeCheckY = (primeCheckYBlockWord I cnts).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeCheckY, hσ2]
  -- `checkY`'s `i`-th `yB`-write: value `⟨checkY, (i+1) mod 4⟩`, in block `kws[i-1]` for `i ≥ 1`.
  have hWp : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.checkY Loc.yB i = some w →
      (∃ c : Fin 4, w.val = Val.primeTag Tid.checkY c ∧ c.val = (i + 1) % 4) ∧
      ∀ i', i = i' + 1 → i' < kws.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hw
    rcases i with _ | i'
    · have hf := (checkYBlockWord_yB_write_val0 I v0 kws).symm.trans hf
      refine ⟨⟨1, ?_, rfl⟩, fun i' h => absurd h (by omega)⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
    · have hf := (checkYBlockWord_yB_write_val_succ I v0 kws i').symm.trans hf
      rcases hk : kws[i']? with _ | kw
      · rw [hk] at hf; simp at hf
      · rw [hk] at hf
        have hlt := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨w', hkw⟩ := hkwsval i' hlt
        rw [hk] at hkw
        have hkw1 : kw.1.val = (1 + i') % 4 := by rw [Option.some.inj hkw]
        refine ⟨⟨kw.1 + 1, ?_, ?_⟩, fun j h => by omega⟩
        · rw [Event.val, hlab, ← Option.some.inj hf]
          rfl
        · rw [Fin.val_add, hkw1]; simp; omega
  -- `primeCheckY`'s `j`-th `yB`-read: value `⟨checkY, (j+1) mod 4⟩`, in block `cnts[j]`.
  have hRp : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.primeCheckY Loc.yB j = some r →
      (∃ c : Fin 4, r.val = Val.primeTag Tid.checkY c ∧ c.val = (j + 1) % 4) ∧
      j < cnts.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (primeCheckYBlockWord_yB_read_val I cnts j).symm.trans hf
    rcases hc : cnts[j]? with _ | c
    · rw [hc] at hf; simp at hf
    · rw [hc] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hc).1
      have hcv := hcntsval j hlt
      rw [hc] at hcv
      refine ⟨⟨c, ?_, by rw [Option.some.inj hcv]⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `primeCheckY`'s `i`-th `yB'`-write: value `⟨primeCheckY, (i+1) mod 4⟩`, in block `cnts[i]`.
  have hWq : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.primeCheckY Loc.yB' i = some w →
      (∃ c : Fin 4, w.val = Val.primeTag Tid.primeCheckY c ∧ c.val = (i + 1) % 4) ∧
      i < cnts.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    have hf := (primeCheckYBlockWord_yB'_write_val I cnts i).symm.trans hf
    rcases hc : cnts[i]? with _ | c
    · rw [hc] at hf; simp at hf
    · rw [hc] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hc).1
      have hcv := hcntsval i hlt
      rw [hc] at hcv
      refine ⟨⟨c, ?_, by rw [Option.some.inj hcv]⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `checkY`'s `j`-th `yB'`-read: value `⟨primeCheckY, (j+1) mod 4⟩`, in block `kws[j]`.
  have hRq : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.checkY Loc.yB' j = some r →
      (∃ c : Fin 4, r.val = Val.primeTag Tid.primeCheckY c ∧ c.val = (j + 1) % 4) ∧
      j < kws.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hr
    have hf := (checkYBlockWord_yB'_read_val I v0 kws j).symm.trans hf
    rcases hk : kws[j]? with _ | kw
    · rw [hk] at hf; simp at hf
    · rw [hk] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨w', hkw⟩ := hkwsval j hlt
      rw [hk] at hkw
      have hkw1 : kw.1.val = (1 + j) % 4 := by rw [Option.some.inj hkw]
      refine ⟨⟨kw.1, ?_, by omega⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  have hRpEvent := fun {j : ℕ} {r : Event (domainOf I)}
      (hr : G.nthRead Tid.primeCheckY Loc.yB j = some r) => G.nthEvent_index hr
  have hRqEvent := fun {j : ℕ} {r : Event (domainOf I)}
      (hr : G.nthRead Tid.checkY Loc.yB' j = some r) => G.nthEvent_index hr
  -- Every block index below `cnts.length`/`kws.length` has an entry.
  have hcnt : ∀ {n : ℕ}, n < cnts.length → ∃ c, cnts[n]? = some c :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  have hkw : ∀ {n : ℕ}, n < kws.length → ∃ kw, kws[n]? = some kw :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWp hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRp hr
    rw [hc, hc'] at hv
    injection hv with _ hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWq hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRq hr
    rw [hc, hc'] at hv
    injection hv with _ hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨⟨c, hc, -⟩, -⟩ := hRp hr
    have hwmem := (G.rf_subset hrf).1
    have htid : w.tid = Tid.checkY :=
      G_writer_val_tid I G hG hwmem (G.rf_subset hrf).2.2.1
        (by rw [G.rf_matches hrf, hc]; rfl)
    exact G.exists_nthWrite_of_rf hrf htid (hRpEvent hr).2.2.1
  · intro j w r hr hrf
    obtain ⟨⟨c, hc, -⟩, -⟩ := hRq hr
    have hwmem := (G.rf_subset hrf).1
    have htid : w.tid = Tid.primeCheckY :=
      G_writer_val_tid I G hG hwmem (G.rf_subset hrf).2.2.1
        (by rw [G.rf_matches hrf, hc]; rfl)
    exact G.exists_nthWrite_of_rf hrf htid (hRqEvent hr).2.2.1
  · -- `primeCheckY`: `r(yB)` at `i*6+5` precedes `w(yB')` at `ℓ*6+1`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨c, hc⟩ := hcnt (hRp hr).2
    obtain ⟨c', hc'⟩ := hcnt (hWq hw).2
    obtain ⟨hlenR, hposR⟩ := primeCheckY_yB_read_nthRead_pos I G hw2 i hc
    obtain ⟨hlenW, hposW⟩ := primeCheckY_yB'_write_nthWrite_pos I G hw2 ℓ hc'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.primeCheckY hlenR hlenW (by omega)
  · -- `checkY`: `r(yB')` at `9+i*6` precedes `w(yB)` at `5+(ℓ-1)*6`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (hRq hr).2
    obtain ⟨kw', hk'⟩ := hkw ((hWp hw).2 ℓ' rfl)
    obtain ⟨hlenR, hposR⟩ := checkY_yB'_read_nthRead_pos I G hw1 i hk
    obtain ⟨hlenW, hposW⟩ := checkY_yB_write_nthWrite_pos I G hw1 ℓ' hk'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.checkY hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    obtain ⟨c, hc⟩ := hcnt (n := i) (by have := (hWq hw).2; omega)
    exact ⟨_, (primeCheckY_yB_read_nthRead_pos I G hw2 i hc).2⟩
  · intro i ℓ w hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (n := i) (by have := (hWp hw).2 ℓ' rfl; omega)
    exact ⟨_, (checkY_yB'_read_nthRead_pos I G hw1 i hk).2⟩

theorem no_skipping_checkY_primeCheckY_yB (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i k : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.checkY Loc.yB i = some ew)
    (her : G.nthRead Tid.primeCheckY Loc.yB k = some er) (hrf : G.rf ew er) :
    i = k :=
  ((checkY_primeCheckY_yB_noSkipPair I G hG).no_skipping hG.1.1 k).1 hew her hrf

theorem no_skipping_checkY_primeCheckY_yB' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (n m : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeCheckY Loc.yB' n = some ew)
    (her : G.nthRead Tid.checkY Loc.yB' m = some er) (hrf : G.rf ew er) :
    n = m :=
  ((checkY_primeCheckY_yB_noSkipPair I G hG).no_skipping hG.1.1 m).2 hew her hrf

/-! ## Eq. (15)'s `zAxx'`/`zAx'x` pair (`GuessAX`/`PrimeAX`): positions

Positions in `guessAX_shape_inv`'s closed form for the nested thread
`GuessAX`, identified in `G` with `ExecutionGraph.nthEvent_eq_of_threadWord_pos`.

**The inner-call index `P`.** Number the inner calls `0, 1, 2, …` across the
whole thread. Call `0`, the thread's first, writes `zAx'x` in the head triple
of `guessAXBlockWord` (`v2`, position `2`) and has no `zAxx'`-read. Calls
`P = 1, …, K0` are the entries `P - 1` of `inner0Rest`, at position `3P`
(`zAx'x`-write at `3P + 1`, `zAxx'`-read at `3P + 2`). So
`G.nthWrite Tid.guessAX Loc.zAx'x i` is call `i`, while
`G.nthRead Tid.guessAX Loc.zAxx' k` is call `k + 1`. -/

/-- The `zAx'x`-write of the thread's first call is at position `2` of
`guessAXBlockWord`. -/
theorem guessAXBlockWord_lead_zAx'x_write_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[2]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) :=
  rfl

/-- The `n`-th entry of `inner0Rest` (call `n + 1`) is at position `3 * n + 3`
of `guessAXBlockWord`. -/
theorem guessAXBlockWord_inner0Rest_pos (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (n p : ℕ) (a : Val I × Val I × Val I) (hva : inner0Rest[n]? = some a) (hp : p < 3) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[3 + n * 3 + p]? =
      (guessAXInnerBlockElems I a)[p]? := by
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
       , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)) := by
    unfold guessAXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)
    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).length = 3 := rfl
  rw [heq, List.getElem?_append_left (by
    rw [List.length_append, hleadlen]
    have hnlen : n < inner0Rest.length := (List.getElem?_eq_some_iff.mp hva).1
    have hlt : n * 3 + p < (inner0Rest.flatMap (guessAXInnerBlockElems I)).length := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat]
      omega
    omega)]
  rw [List.getElem?_append_right (by rw [hleadlen]; omega), hleadlen]
  have hi : 3 + n * 3 + p - 3 = n * 3 + p := by omega
  rw [hi]
  exact flatMap_uniform_getElem_fwd (guessAXInnerBlockElems I) 3 (fun _ => rfl)
    inner0Rest n p a hva hp

/-- Within one outer block `guessAXOuterBlockElems`, event `p` of inner call
`n` is at position `1 + n * 3 + p` (after the leading `zAxy`-write). -/
theorem guessAXOuterBlockElems_inner_pos (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p < 3) :
    (guessAXOuterBlockElems I b vs)[n * 3 + p + 1]? = (guessAXInnerBlockElems I a)[p]? := by
  have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
  have hlt : n * 3 + p < (vs.flatMap (guessAXInnerBlockElems I)).length := by
    rw [List.length_flatMap]
    have heq1 : (vs.map (fun a => (guessAXInnerBlockElems I a).length)) =
        vs.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat]
    have : n + 1 ≤ vs.length := hnlen
    nlinarith
  unfold guessAXOuterBlockElems
  rw [List.getElem?_cons_succ, List.getElem?_append_left hlt]
  exact flatMap_uniform_getElem_fwd (guessAXInnerBlockElems I) 3 (fun _ => rfl) vs n p a hva hp

/-- Position in `guessAXBlockWord` of event `p` of inner call `n` of
`outerRest[m]`: the head triple, `inner0Rest`'s `3 * K0` events, the closing
`ellAyx`-read, the first `m` entries of `outerRest`, then the position within
the block. -/
theorem guessAXBlockWord_outerRest_pos (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (m n p : ℕ) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hmbv : outerRest[m]? = some (b, vs)) (a : Val I × Val I × Val I) (hva : vs[n]? = some a)
    (hp : p < 3) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[4 + K0 * 3 +
      ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length +
      (n * 3 + p + 1)]? = (guessAXInnerBlockElems I a)[p]? := by
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  rw [heq, List.getElem?_append_right (by rw [hleadlen]; omega), hleadlen,
    show 4 + K0 * 3 + ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
      + (n * 3 + p + 1) - (4 + K0 * 3)
      = ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
      + (n * 3 + p + 1) from by omega]
  have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
  have hqlt : n * 3 + p + 1 < (guessAXOuterBlockElems I b vs).length := by
    rw [guessAXOuterBlockElems_length]
    omega
  have hstep := list_take_flatMap_offset_getElem (fun q => guessAXOuterBlockElems I q.1 q.2)
    outerRest m (n * 3 + p + 1) (b, vs) hmbv hqlt
  rw [hstep]
  exact guessAXOuterBlockElems_inner_pos I b vs n p a hva hp

/-- The prefix length in `guessAXBlockWord_outerRest_pos`, in terms of
`nestedOuterStart`. -/
theorem guessAXOuterRest_prefix_length_eq (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (hks : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) (m : ℕ) (hm : m ≤ N + 1) :
    ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
      = nestedOuterStart ks N (m + 1) - nestedOuterStart ks N 1 :=
  guessAXOuterRest_prefix_length I ks N hks outerRest houterLen houter houterLast m hm

/-- `nestedOuterStart ks N 1 = 3 * K0 + 4`, where `K0 := ks[0]`. -/
theorem nestedOuterStart_one (ks : List ℕ) (N K0 : ℕ) (hK0 : ks[0]? = some K0) :
    nestedOuterStart ks N 1 = 3 * K0 + 4 := by
  have h1 : nestedOuterStart ks N 1 = nestedOuterStart ks N 0 + nestedOuterLen ks N 0 :=
    nestedOuterStart_succ ks N 0
  have hlenN : nestedOuterLen ks N 0 = 3 * K0 + 4 := by
    unfold nestedOuterLen
    rw [if_neg (by omega), if_pos rfl]
    have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    rw [hgetD]
  have h0 : nestedOuterStart ks N 0 = 0 := rfl
  rw [h1, hlenN, h0]; omega

/-- For any inner-call index `P < ksPrefix ks (N + 1)`, the `zAx'x`-write of
call `P` is at position `nestedInnerStart ks P + 1` of `guessAXBlockWord`.
With `nestedInnerStart_strictMono`, this compares positions of calls without
knowing in which outer iteration they lie. By `ksPrefix_invert`. -/
theorem guessAXBlockWord_zAx'x_write_nestedInnerPos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    ∃ val, (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · refine ⟨v2, ?_⟩
      rw [show P = 0 from by omega, show nestedInnerStart ks 0 = 1 from rfl]
      exact guessAXBlockWord_lead_zAx'x_write_pos I v1 v2 vB0 inner0Rest outerRest
    · have hks00 : ks[0]'hks0pos = K0 := by
        have h := List.getElem?_eq_getElem (l := ks) hks0pos
        rw [hK0] at h; exact (Option.some.inj h).symm
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      refine ⟨(inner0Rest[n - 1]'hnm1lt).2.1, ?_⟩
      have hpos := guessAXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 1
        (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
      have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
      rw [show n - 1 + 1 = n from by omega] at hns
      rw [heq', hns]
      have hoff : 3 + (n - 1) * 3 + 1 = 3 * n + 1 := by omega
      rwa [hoff] at hpos
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    refine ⟨(vs[n]'hnvs).2.1, ?_⟩
    have hpos := guessAXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 1 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 1
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff]
    exact hpos

/-- The `xA`-write of call `P` is at position `nestedInnerStart ks P` (offset
`0` of each inner call; unlike `zAxx'`, `xA` is also written by call `0`). -/
theorem guessAXBlockWord_xA_write_nestedInnerPos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    ∃ val, (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.xA val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · refine ⟨v1, ?_⟩
      rw [show P = 0 from by omega, show nestedInnerStart ks 0 = 1 from rfl]
      rfl
    · have hks00 : ks[0]'hks0pos = K0 := by
        have h := List.getElem?_eq_getElem (l := ks) hks0pos
        rw [hK0] at h; exact (Option.some.inj h).symm
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      refine ⟨(inner0Rest[n - 1]'hnm1lt).1, ?_⟩
      have hpos := guessAXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 0
        (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
      have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
      rw [show n - 1 + 1 = n from by omega] at hns
      rw [heq', hns]
      have hoff : 3 + (n - 1) * 3 + 0 = 3 * n := by omega
      rwa [hoff] at hpos
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    refine ⟨(vs[n]'hnvs).1, ?_⟩
    have hpos := guessAXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 0 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 0 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff]
    exact hpos

/-- The `xA`-write of the call of the terminating outer iteration
(`P = ksPrefix ks (N + 1)`). -/
theorem guessAXBlockWord_xA_write_terminator_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks (ksPrefix ks (N + 1))]?
      = some (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hpos := guessAXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
    N 0 0 b vs hbvs a hva (by norm_num)
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1))
      = 4 + K0 * 3 + ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 0 + 1) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff]; exact hpos

/-- The `xA`-write of call `P` is at position `nestedInnerStart ks P`, for
`P ≤ ksPrefix ks (N + 1)`. -/
theorem guessAXBlockWord_xA_write_pos_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    ∃ val, (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.xA val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessAXBlockWord_xA_write_nestedInnerPos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    refine ⟨a.1, ?_⟩
    rw [heq]
    exact guessAXBlockWord_xA_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter b vs hbvs hvslen a hva

/-- The number of `xA`-writes within a possibly partial outer block (offset
`0` of each inner call). -/
theorem guessAXOuterBlockElems_xA_take_count (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((guessAXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false)).length
      = n + (if 0 < p then 1 else 0) := by
  have hstep : ((guessAXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) =
      ((vs.flatMap (guessAXInnerBlockElems I)).take (n * 3 + p)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) := by
    unfold guessAXOuterBlockElems
    rw [List.take_succ_cons, List.filter_cons_of_neg (fun h => Bool.noConfusion h),
      List.take_append, List.filter_append]
    have hnil : (([⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).take
          (n * 3 + p - (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hxmem : x ∈ ([⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩] :
          List (ThreadLabel (domainOf I) Tid.guessAX)) := List.mem_of_mem_take hx
      simp only [List.mem_singleton] at hxmem
      subst hxmem
      exact fun h => Bool.noConfusion h
    rw [hnil, List.append_nil]
  rw [hstep]
  exact flatMap_uniform_take_count (guessAXInnerBlockElems I) 3 (fun _ => rfl)
    (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) 0
    (by norm_num)
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun _ => rfl) (fun _ => rfl)
    (fun a q b hq hqb => by
      unfold guessAXInnerBlockElems at hqb
      rcases q with _ | _ | _ | q <;> simp_all only [ne_eq, not_true_eq_false, zero_add, one_ne_zero, not_false_eq_true, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
    vs n a hva p hp

/-- The number of `xA`-writes before an arbitrary position of `outerRest`'s
flatMap. -/
theorem guessAXOuterRest_xA_take_count (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (hks : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (hpredNonBridge :
      ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.xA, OpType.wt => true | _, _ => false) = false)
    (M : ℕ) (hM : M ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hMbv : outerRest[M]? = some (b, vs)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take M).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length +
          (n * 3 + p + 1))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false)).length
      = (ksPrefix ks (M + 1) - ksPrefix ks 1) + (n + (if 0 < p then 1 else 0)) := by
  have hqbound : n * 3 + p + 1 ≤ (guessAXOuterBlockElems I b vs).length := by
    have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
    rw [guessAXOuterBlockElems_length]
    omega
  rw [list_take_flatMap_offset (fun q => guessAXOuterBlockElems I q.1 q.2) outerRest M
    (n * 3 + p + 1) (b, vs) hMbv hqbound, List.filter_append, List.length_append,
    guessAXOuterRest_prefix_matchCount I ks N hks outerRest houter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) 0
      (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessAXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [add_lt_add_iff_right, getElem?_pos, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, Subtype.forall, ne_eq, not_true_eq_false, zero_add, one_ne_zero, not_false_eq_true, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.one_lt_ofNat, List.getElem_cons_succ, List.getElem_cons_zero, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      hpredNonBridge M hM,
    guessAXOuterBlockElems_xA_take_count I b vs n p a hva hp]

/-- The number of `xA`-writes before position `nestedInnerStart ks P` is `P`. -/
theorem guessAXBlockWord_xA_write_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false)).length
      = P := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks00 : ks[0]'hks0pos = K0 := by
    have h := List.getElem?_eq_getElem (l := ks) hks0pos
    rw [hK0] at h; exact (Option.some.inj h).symm
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
       , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)) := by
    unfold guessAXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)
    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] := by
    rfl
  have hinnerflatlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
    rw [List.length_flatMap]
    have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
        inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [show P = 0 from by omega, show nestedInnerStart ks 0 = 1 from rfl]
      rfl
    · have hnstart : nestedInnerStart ks n = 3 * n := by
        have h := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
        rw [show n - 1 + 1 = n from by omega] at h
        omega
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have hva : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      have hcount := flatMap_uniform_take_count (guessAXInnerBlockElems I) 3 (fun _ => rfl)
        (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) 0
        (by norm_num)
        (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessAXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, Nat.right_eq_add, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.length_flatMap, gt_iff_lt, getElem?_eq_some_getElem_iff, ne_eq, not_true_eq_false, one_ne_zero, not_false_eq_true, Nat.one_lt_ofNat, List.getElem_cons_succ, List.getElem_cons_zero, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest (n - 1) (inner0Rest[n - 1]'hnm1lt) hva 0 (by norm_num)
      rw [if_neg (show ¬ (0 : ℕ) < 0 from by omega), Nat.add_zero, Nat.add_zero] at hcount
      rw [heq', hnstart, heq0, show 3 * n = 3 + (n - 1) * 3 from by omega,
        List.take_append_of_le_length (by
          rw [List.length_append, hleadlen, hinnerflatlen]; omega),
        List.take_append, hleadlen,
        show 3 + (n - 1) * 3 - 3 = (n - 1) * 3 from by omega,
        List.take_of_length_le (by rw [hleadlen]; omega),
        List.filter_append, List.length_append, hleadfilter, hcount]
      have hone : List.length
          [ (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ]
          = 1 := rfl
      omega
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      rwa [hgetD0] at hh
    have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n
        = (4 + K0 * 3 - 1) +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 0 + 1))) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff, heq0]
    have hfirstlen : (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
      rw [List.length_append, hleadlen, hinnerflatlen]; omega
    rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length from hfirstlen.symm,
      List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _),
      show (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 0 + 1))) -
          (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length =
          1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 0 + 1)) from by omega,
      List.filter_append, List.length_append]
    have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) =
        [ (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
          inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX)) := by
      rw [List.filter_append, hleadfilter]
      congr 1
      exact guessAXInnerBlockElems_filter I
        (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) 0
        (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessAXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.length_flatMap, gt_iff_lt, Nat.succ_add_sub_one, add_zero, ge_iff_le, List.map_take, ne_eq, not_true_eq_false, one_ne_zero, not_false_eq_true, Nat.one_lt_ofNat, List.getElem_cons_succ, List.getElem_cons_zero, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest
    rw [hleadinnerfilter, List.length_append, List.length_map]
    have hone : List.length
        [ (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ]
        = 1 := rfl
    rw [hone]
    have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.xA, OpType.wt => true | _, _ => false) = false := by
      intro b0 hb0
      have hz : b0.1.loc ≠ Loc.xA := by
        intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.xA ∉ BridgeLoc)
      split
      · exact absurd (by assumption) hz
      · rfl
    have hellalen : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length ≤
        1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 0 + 1)) := by simp
    have hellasub : (1 + (((outerRest.take (m - 1)).flatMap
          (fun q => guessAXOuterBlockElems I q.1 q.2)).length + (n * 3 + 0 + 1))) -
        ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX) ] :
          List (ThreadLabel (domainOf I) Tid.guessAX)).length =
        ((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 0 + 1) := by simp
    rw [show ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 0 + 1))) =
        [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        (outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
          (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 0 + 1)) from by
      rw [List.take_append, List.take_of_length_le hellalen, hellasub],
      List.filter_append]
    have hellafilter : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ]).filter
        (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) = [] :=
      rfl
    rw [hellafilter, List.nil_append, hinner0len]
    have houter' : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
        ks[j + 1]? = some km ∧ vs.length = km + 1 := houter
    have hcountOuter := guessAXOuterRest_xA_take_count I ks N hks outerRest houter'
      hpredNonBridge (m - 1) (by omega) b vs hbvs n 0 (vs[n]'hnvs) hva (by norm_num)
    rw [if_neg (show ¬ (0 : ℕ) < 0 from by omega)] at hcountOuter
    simp only [Nat.add_zero] at hcountOuter
    rw [hmeq] at hcountOuter
    rw [hcountOuter]
    have hksprefM : ksPrefix ks m - ksPrefix ks 1 = ksPrefix ks m - (K0 + 1) := by rw [hks1]
    have hksprefmono : ksPrefix ks 1 ≤ ksPrefix ks m := ksPrefix_mono ks (show (1:ℕ) ≤ m from by omega)
    omega

/-- The `zAxx'`-read of call `P ≥ 1` is at position
`nestedInnerStart ks P + 2` (call `0` has none). -/
theorem guessAXBlockWord_zAxx'_read_nestedInnerPos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P < ksPrefix ks (N + 1)) :
    ∃ val, (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    have hnpos : 0 < n := by omega
    have hks00 : ks[0]'hks0pos = K0 := by
      have h := List.getElem?_eq_getElem (l := ks) hks0pos
      rw [hK0] at h; exact (Option.some.inj h).symm
    have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
    have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
      List.getElem?_eq_getElem hnm1lt
    refine ⟨(inner0Rest[n - 1]'hnm1lt).2.2, ?_⟩
    have hpos := guessAXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 2
      (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
    have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
    rw [show n - 1 + 1 = n from by omega] at hns
    rw [heq', hns]
    have hoff : 3 + (n - 1) * 3 + 2 = 3 * n + 2 := by omega
    rwa [hoff] at hpos
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    refine ⟨(vs[n]'hnvs).2.2, ?_⟩
    have hpos := guessAXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 2 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 2
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff]
    exact hpos

/-! ## `zAxx'`/`zAx'x`: counts

The number of `zAx'x`-writes and `zAxx'`-reads before the positions above, as
`ExecutionGraph.nthEvent_eq_of_threadWord_pos` requires. By `ksPrefix_invert`,
then `flatMap_uniform_take_count` for `inner0Rest` and
`guessAXOuterRest_prefix_matchCount` for whole outer iterations. -/

/-- The number of `zAx'x`-writes within a possibly partial outer block (offset
`1` of each inner call). -/
theorem guessAXOuterBlockElems_zAx'x_take_count (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((guessAXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false)).length
      = n + (if 1 < p then 1 else 0) := by
  have hstep : ((guessAXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) =
      ((vs.flatMap (guessAXInnerBlockElems I)).take (n * 3 + p)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) := by
    unfold guessAXOuterBlockElems
    rw [List.take_succ_cons, List.filter_cons_of_neg (fun h => Bool.noConfusion h),
      List.take_append, List.filter_append]
    have hnil : (([⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).take
          (n * 3 + p - (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hxmem : x ∈ ([⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩] :
          List (ThreadLabel (domainOf I) Tid.guessAX)) := List.mem_of_mem_take hx
      simp only [List.mem_singleton] at hxmem
      subst hxmem
      exact fun h => Bool.noConfusion h
    rw [hnil, List.append_nil]
  rw [hstep]
  exact flatMap_uniform_take_count (guessAXInnerBlockElems I) 3 (fun _ => rfl)
    (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) 1
    (by norm_num)
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun _ => rfl) (fun _ => rfl)
    (fun a q b hq hqb => by
      unfold guessAXInnerBlockElems at hqb
      rcases q with _ | _ | _ | q <;> simp_all only [ne_eq, zero_ne_one, not_false_eq_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.some.injEq, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
    vs n a hva p hp

/-- The number of `zAx'x`-writes before an arbitrary position of `outerRest`'s
flatMap. -/
theorem guessAXOuterRest_zAx'x_take_count (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (hks : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (hpredNonBridge :
      ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) = false)
    (M : ℕ) (hM : M ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hMbv : outerRest[M]? = some (b, vs)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take M).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length +
          (n * 3 + p + 1))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false)).length
      = (ksPrefix ks (M + 1) - ksPrefix ks 1) + (n + (if 1 < p then 1 else 0)) := by
  have hqbound : n * 3 + p + 1 ≤ (guessAXOuterBlockElems I b vs).length := by
    have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
    rw [guessAXOuterBlockElems_length]
    omega
  rw [list_take_flatMap_offset (fun q => guessAXOuterBlockElems I q.1 q.2) outerRest M
    (n * 3 + p + 1) (b, vs) hMbv hqbound, List.filter_append, List.length_append,
    guessAXOuterRest_prefix_matchCount I ks N hks outerRest houter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) 1
      (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessAXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [add_lt_add_iff_right, getElem?_pos, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, Subtype.forall, ne_eq, zero_ne_one, not_false_eq_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, List.getElem_cons_zero, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      hpredNonBridge M hM,
    guessAXOuterBlockElems_zAx'x_take_count I b vs n p a hva hp]

/-- The number of `zAx'x`-writes before position `nestedInnerStart ks P + 1`
is `P`. -/
theorem guessAXBlockWord_zAx'x_write_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false)).length
      = P := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks00 : ks[0]'hks0pos = K0 := by
    have h := List.getElem?_eq_getElem (l := ks) hks0pos
    rw [hK0] at h; exact (Option.some.inj h).symm
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
       , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)) := by
    unfold guessAXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)
    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] := by
    rfl
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [show P = 0 from by omega, show nestedInnerStart ks 0 = 1 from rfl]
      rfl
    · have hnstart : nestedInnerStart ks n = 3 * n := by
        have h := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
        rw [show n - 1 + 1 = n from by omega] at h
        omega
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have hva : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      have hcount := flatMap_uniform_take_count (guessAXInnerBlockElems I) 3 (fun _ => rfl)
        (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) 1
        (by norm_num)
        (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessAXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, Nat.right_eq_add, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, gt_iff_lt, getElem?_eq_some_getElem_iff, ne_eq, zero_ne_one, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest (n - 1) (inner0Rest[n - 1]'hnm1lt) hva 1 (by norm_num)
      rw [if_neg (show ¬ (1 : ℕ) < 1 from by omega)] at hcount
      have hinnerflatlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
        rw [List.length_flatMap]
        have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
            inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
        rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
      rw [heq', hnstart, heq0, show 3 * n + 1 = 3 + ((n - 1) * 3 + 1) from by omega,
        List.take_append_of_le_length (by
          rw [List.length_append, hleadlen, hinnerflatlen]; omega),
        List.take_append, hleadlen,
        show 3 + ((n - 1) * 3 + 1) - 3 = (n - 1) * 3 + 1 from by omega,
        List.take_of_length_le (by rw [hleadlen]; omega),
        List.filter_append, List.length_append, hleadfilter, hcount]
      have hone : List.length
          [ (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ]
          = 1 := rfl
      omega
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      rwa [hgetD0] at hh
    have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 1
        = (4 + K0 * 3 - 1) +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 1 + 1))) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff, heq0]
    have hinnerflatlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
    have hfirstlen : (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
      rw [List.length_append, hleadlen, hinnerflatlen]; omega
    rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length from hfirstlen.symm,
      List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _),
      show (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 1 + 1))) -
          (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length =
          1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 1 + 1)) from by omega,
      List.filter_append, List.length_append]
    have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) =
        [ (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
          inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX)) := by
      rw [List.filter_append, hleadfilter]
      congr 1
      exact guessAXInnerBlockElems_filter I
        (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) 1
        (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessAXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, gt_iff_lt, ge_iff_le, List.length_flatMap, List.map_take, Nat.succ_add_sub_one, ne_eq, zero_ne_one, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest
    rw [hleadinnerfilter, List.length_append, List.length_map]
    have hone : List.length
        [ (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ]
        = 1 := rfl
    rw [hone]
    have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) = false := by
      intro b0 hb0
      have hz : b0.1.loc ≠ Loc.zAx'x := by
        intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.zAx'x ∉ BridgeLoc)
      split
      · exact absurd (by assumption) hz
      · rfl
    have hellalen : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length ≤
        1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1)) := by simp
    have hellasub : (1 + (((outerRest.take (m - 1)).flatMap
          (fun q => guessAXOuterBlockElems I q.1 q.2)).length + (n * 3 + 1 + 1))) -
        ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX) ] :
          List (ThreadLabel (domainOf I) Tid.guessAX)).length =
        ((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1) := by simp
    rw [show ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1))) =
        [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        (outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
          (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 1 + 1)) from by
      rw [List.take_append, List.take_of_length_le hellalen, hellasub],
      List.filter_append]
    have hellafilter : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ]).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) = [] :=
      rfl
    rw [hellafilter, List.length_append, List.length_nil]
    have houtercount := guessAXOuterRest_zAx'x_take_count I ks N hks outerRest houter
      hpredNonBridge (m - 1) (by omega) b vs hbvs n 1 (vs[n]'hnvs) hva (by norm_num)
    rw [if_neg (show ¬ (1 : ℕ) < 1 from by omega), hmeq] at houtercount
    rw [houtercount, hks1]
    have hksmono : ksPrefix ks 1 ≤ ksPrefix ks m := ksPrefix_mono ks (by omega)
    omega

/-- The number of `zAxx'`-reads before position `nestedInnerStart ks P + 2` is
`P - 1`, for `P ≥ 1` (the head triple contains no `zAxx'`-read). -/
theorem guessAXBlockWord_zAxx'_read_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P < ksPrefix ks (N + 1)) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P + 2)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false)).length
      = P - 1 := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks00 : ks[0]'hks0pos = K0 := by
    have h := List.getElem?_eq_getElem (l := ks) hks0pos
    rw [hK0] at h; exact (Option.some.inj h).symm
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
       , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)) := by
    unfold guessAXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)
    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) = [] := by
    rfl
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    have hnpos : 0 < n := by omega
    have hnstart : nestedInnerStart ks n = 3 * n := by
      have h := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
      rw [show n - 1 + 1 = n from by omega] at h
      omega
    have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
    have hva : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
      List.getElem?_eq_getElem hnm1lt
    have hcount := flatMap_uniform_take_count (guessAXInnerBlockElems I) 3 (fun _ => rfl)
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) 2
      (by norm_num)
      (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessAXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, Nat.right_eq_add, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.filter_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true, forall_eq_or_imp, forall_eq, getElem?_eq_some_getElem_iff, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      inner0Rest (n - 1) (inner0Rest[n - 1]'hnm1lt) hva 2 (by norm_num)
    rw [if_neg (show ¬ (2 : ℕ) < 2 from by omega)] at hcount
    have hinnerflatlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
    rw [heq', hnstart, heq0, show 3 * n + 2 = 3 + ((n - 1) * 3 + 2) from by omega,
      List.take_append_of_le_length (by
        rw [List.length_append, hleadlen, hinnerflatlen]; omega),
      List.take_append, hleadlen,
      show 3 + ((n - 1) * 3 + 2) - 3 = (n - 1) * 3 + 2 from by omega,
      List.take_of_length_le (by rw [hleadlen]; omega),
      List.filter_append, List.length_append, hleadfilter, hcount]
    have hnil : ([] : List (ThreadLabel (domainOf I) Tid.guessAX)).length = 0 := rfl
    rw [hnil]
    omega
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      rwa [hgetD0] at hh
    have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 2
        = (4 + K0 * 3 - 1) +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 2 + 1))) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff, heq0]
    have hinnerflatlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
    have hfirstlen : (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
      rw [List.length_append, hleadlen, hinnerflatlen]; omega
    rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length from hfirstlen.symm,
      List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _),
      show (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 2 + 1))) -
          (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I))).length =
          1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 2 + 1)) from by omega,
      List.filter_append, List.length_append]
    have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) =
        [] ++
          inner0Rest.map (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX)) := by
      rw [List.filter_append, hleadfilter]
      congr 1
      exact guessAXInnerBlockElems_filter I
        (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) 2
        (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessAXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.filter_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true, forall_eq_or_imp, forall_eq, gt_iff_lt, ge_iff_le, List.length_flatMap, List.map_take, Nat.succ_add_sub_one, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest
    rw [hleadinnerfilter, List.length_append, List.length_nil, List.length_map]
    have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) = false := by
      intro b0 hb0
      have hz : b0.1.loc ≠ Loc.zAxx' := by
        intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.zAxx' ∉ BridgeLoc)
      split
      · exact absurd (by assumption) hz
      · rfl
    have hellalen : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length ≤
        1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1)) := by simp
    have hellasub : (1 + (((outerRest.take (m - 1)).flatMap
          (fun q => guessAXOuterBlockElems I q.1 q.2)).length + (n * 3 + 2 + 1))) -
        ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX) ] :
          List (ThreadLabel (domainOf I) Tid.guessAX)).length =
        ((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1) := by simp
    rw [show ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1))) =
        [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        (outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
          (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 2 + 1)) from by
      rw [List.take_append, List.take_of_length_le hellalen, hellasub],
      List.filter_append]
    have hellafilter : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ]).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) = [] :=
      rfl
    rw [hellafilter, List.length_append, List.length_nil]
    have houtercount := guessAXOuterRest_zAxx'_take_count I ks N hks outerRest houter
      hpredNonBridge (m - 1) (by omega) b vs hbvs n 2 (vs[n]'hnvs) hva (by norm_num)
    rw [if_neg (show ¬ (2 : ℕ) < 2 from by omega), hmeq] at houtercount
    -- Restate `houtercount` at the predicate written here, so that `rw`
    -- matches it.
    have houtercount2 : (((outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length +
          (n * 3 + 2 + 1))).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false)).length
        = ksPrefix ks m - ksPrefix ks 1 + (n + 0) := houtercount
    rw [houtercount2, hks1]
    have hksmono : ksPrefix ks 1 ≤ ksPrefix ks m := ksPrefix_mono ks (by omega)
    omega

/-! ## `zAxx'`/`zAx'x`: values

The values at call `P`: `(P+1) % 4` for the `zAx'x`-write and `P % 4` for the
`zAxx'`-read, from `guessAX_shape_inv`'s value conjuncts. -/

theorem guessAXBlockWord_zAx'x_write_val (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (hks : ks.length = N + 1)
    (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hv2 : v2 = Val.cnt (1 : Fin 4))
    (hinner0val : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4))
    (houterval : ∀ m, m < N → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix ks' m + n + 1) % 4, by omega⟩ : Fin 4))
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt (⟨(P + 1) % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    obtain rfl : n = P := heq'.symm
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · obtain rfl : n = 0 := hn0
      have hfinEq : (1 : Fin 4) = (⟨(0 + 1) % 4, by omega⟩ : Fin 4) := Fin.ext (by simp)
      have hns0 : nestedInnerStart ks 0 = 1 := rfl
      have hbase := guessAXBlockWord_lead_zAx'x_write_pos I v1 v2 vB0 inner0Rest outerRest
      have hv2full : v2 = Val.cnt (⟨(0 + 1) % 4, by omega⟩ : Fin 4) :=
        hv2.trans (congrArg Val.cnt hfinEq)
      have hgoal := hbase.trans (congrArg (fun x => some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x x,
        rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)) hv2full)
      rw [hns0]
      exact hgoal
    · have hks00 : ks[0]'hks0pos = K0 := by
        have h := List.getElem?_eq_getElem (l := ks) hks0pos
        rw [hK0] at h; exact (Option.some.inj h).symm
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      obtain ⟨e, hae, heval⟩ := hinner0val (n - 1) hnm1lt
      rw [ha] at hae
      have heval' := (Option.some.inj hae) ▸ heval
      have hfinEq : (⟨(1 + (n - 1) + 1) % 4, by omega⟩ : Fin 4) =
          (⟨(n + 1) % 4, by omega⟩ : Fin 4) := Fin.ext (by simp; omega)
      have hpos := guessAXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 1
        (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
      have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
      rw [show n - 1 + 1 = n from by omega] at hns
      have hlab : (guessAXInnerBlockElems I (inner0Rest[n - 1]'hnm1lt))[1]? =
          some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt (⟨(n + 1) % 4, by omega⟩ : Fin 4)),
            rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) := by
        have hlab0 : (guessAXInnerBlockElems I (inner0Rest[n - 1]'hnm1lt))[1]? =
            some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x (inner0Rest[n - 1]'hnm1lt).2.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX) := rfl
        rw [hlab0, heval']
        exact congrArg (fun x => some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt x), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX)) hfinEq
      have hoff : 3 + (n - 1) * 3 + 1 = 3 * n + 1 := by omega
      rw [hoff] at hpos
      rw [hns, hpos, hlab]
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    obtain ⟨b', vs', hbvs', hvalfn⟩ := houterval (m - 1) hjm1
    rw [hbvs] at hbvs'
    have hbveq : (b, vs) = (b', vs') := Option.some.inj hbvs'
    have hvs'eq : vs = vs' := (Prod.mk.injEq _ _ _ _).mp hbveq |>.2
    have hvalfn' := hvs'eq ▸ hvalfn
    obtain ⟨e, hae, heval⟩ := hvalfn' n hnvs
    rw [hva] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hpos := guessAXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 1 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 1
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    have hksrel_cons : ksPrefix ks m = (K0 + 1) + ksPrefix ks' (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [hksrel, ksPrefix_cons]
    have hPeq : P = ksPrefix ks m + n := heq
    have hNatEq : 1 + K0 + ksPrefix ks' (m - 1) + n + 1 = P + 1 := by omega
    have hfinEq : (⟨(1 + K0 + ksPrefix ks' (m - 1) + n + 1) % 4, by omega⟩ : Fin 4) =
        (⟨(P + 1) % 4, by omega⟩ : Fin 4) := Fin.ext (congrArg (· % 4) hNatEq)
    have hlab : (guessAXInnerBlockElems I (vs[n]'hnvs))[1]? =
        some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt (⟨(P + 1) % 4, by omega⟩ : Fin 4)),
          rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) := by
      have hlab0 : (guessAXInnerBlockElems I (vs[n]'hnvs))[1]? =
          some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x (vs[n]'hnvs).2.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX) := rfl
      rw [hlab0, heval']
      exact congrArg (fun x => some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt x), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX)) hfinEq
    have hLHSeq : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
        (guessAXInnerBlockElems I (vs[n]'hnvs))[1]? := by
      rw [heq, hns, hoff]; exact hpos
    exact hLHSeq.trans hlab

/-- The value of the `zAxx'`-read of call `P ≥ 1`. -/
theorem guessAXBlockWord_zAxx'_read_val (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (hks : ks.length = N + 1)
    (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hinner0val : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4))
    (houterval : ∀ m, m < N → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix ks' m + n) % 4, by omega⟩ : Fin 4))
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P < ksPrefix ks (N + 1)) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' (Val.cnt (⟨P % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    have hnpos : 0 < n := by omega
    obtain rfl : n = P := heq'.symm
    have hks00 : ks[0]'hks0pos = K0 := by
      have h := List.getElem?_eq_getElem (l := ks) hks0pos
      rw [hK0] at h; exact (Option.some.inj h).symm
    have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
    have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
      List.getElem?_eq_getElem hnm1lt
    obtain ⟨e, hae, heval⟩ := hinner0val (n - 1) hnm1lt
    rw [ha] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hfinEq : (⟨(1 + (n - 1)) % 4, by omega⟩ : Fin 4) = (⟨n % 4, by omega⟩ : Fin 4) :=
      Fin.ext (by simp; omega)
    have hpos := guessAXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 2
      (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
    have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
    rw [show n - 1 + 1 = n from by omega] at hns
    have hlab : (guessAXInnerBlockElems I (inner0Rest[n - 1]'hnm1lt))[2]? =
        some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' (Val.cnt (⟨n % 4, by omega⟩ : Fin 4)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX) := by
      have hlab0 : (guessAXInnerBlockElems I (inner0Rest[n - 1]'hnm1lt))[2]? =
          some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' (inner0Rest[n - 1]'hnm1lt).2.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX) := rfl
      rw [hlab0, heval']
      exact congrArg (fun x => some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' (Val.cnt x), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX)) hfinEq
    have hoff : 3 + (n - 1) * 3 + 2 = 3 * n + 2 := by omega
    rw [hoff] at hpos
    rw [hns, hpos, hlab]
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    obtain ⟨b', vs', hbvs', hvalfn⟩ := houterval (m - 1) hjm1
    rw [hbvs] at hbvs'
    have hbveq : (b, vs) = (b', vs') := Option.some.inj hbvs'
    have hvs'eq : vs = vs' := (Prod.mk.injEq _ _ _ _).mp hbveq |>.2
    have hvalfn' := hvs'eq ▸ hvalfn
    obtain ⟨e, hae, heval⟩ := hvalfn' n hnvs
    rw [hva] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hpos := guessAXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 2 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 2
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    have hksrel_cons : ksPrefix ks m = (K0 + 1) + ksPrefix ks' (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [hksrel, ksPrefix_cons]
    have hPeq : P = ksPrefix ks m + n := heq
    have hNatEq : 1 + K0 + ksPrefix ks' (m - 1) + n = P := by omega
    have hfinEq : (⟨(1 + K0 + ksPrefix ks' (m - 1) + n) % 4, by omega⟩ : Fin 4) =
        (⟨P % 4, by omega⟩ : Fin 4) := Fin.ext (congrArg (· % 4) hNatEq)
    have hlab : (guessAXInnerBlockElems I (vs[n]'hnvs))[2]? =
        some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' (Val.cnt (⟨P % 4, by omega⟩ : Fin 4)),
          rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) := by
      have hlab0 : (guessAXInnerBlockElems I (vs[n]'hnvs))[2]? =
          some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' (vs[n]'hnvs).2.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX) := rfl
      rw [hlab0, heval']
      exact congrArg (fun x => some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' (Val.cnt x), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX)) hfinEq
    have hLHSeq : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
        (guessAXInnerBlockElems I (vs[n]'hnvs))[2]? := by
      rw [heq, hns, hoff]; exact hpos
    exact hLHSeq.trans hlab

/-! ## `PrimeAX`: values, positions, counts

`primeAXBlockWord I vals = vals.flatMap (primeAXBlockElems I)`, with
`primeAXBlockElems I l = [wt xA' (primeTag primeAX 0), wt zAxx' l, rd zAx'x l]`. -/

/-- `primeAX`'s `zAxx'`-write value at filtered position `j` is `vals[j]`. -/
theorem primeAXBlockWord_zAxx'_write_val (I : PCPInstance) (vals : List (Val I)) (j : ℕ) :
    ((primeAXBlockWord I vals).filter (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.wt))[j]? =
      (vals[j]?).map (fun v => (⟨EventLabel.wt Tid.primeAX Loc.zAxx' v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeAX)) := by
  have hone : ∀ v : Val I, (primeAXBlockElems I v).filter
      (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeAX Loc.zAxx' v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeAX)] := by
    intro v
    unfold primeAXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeAXBlockWord I vals).filter (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.wt) =
      vals.map (fun v => (⟨EventLabel.wt Tid.primeAX Loc.zAxx' v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeAX)) := by
    rw [primeAXBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ vals
  rw [hflat]
  exact List.getElem?_map ..

/-- `primeAX`'s `zAx'x`-read value at filtered position `j` is `vals[j]`. -/
theorem primeAXBlockWord_zAx'x_read_val (I : PCPInstance) (vals : List (Val I)) (j : ℕ) :
    ((primeAXBlockWord I vals).filter (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.rd))[j]? =
      (vals[j]?).map (fun v => (⟨EventLabel.rd Tid.primeAX Loc.zAx'x v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeAX)) := by
  have hone : ∀ v : Val I, (primeAXBlockElems I v).filter
      (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeAX Loc.zAx'x v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeAX)] := by
    intro v
    unfold primeAXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeAXBlockWord I vals).filter (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.rd) =
      vals.map (fun v => (⟨EventLabel.rd Tid.primeAX Loc.zAx'x v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeAX)) := by
    rw [primeAXBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ vals
  rw [hflat]
  exact List.getElem?_map ..

/-- The `match`-based filter of `guessAXBlockWord_zAx'x_write_take_count`
equals the `∧`-predicate filter of
`ExecutionGraph.nthEvent_eq_of_threadWord_pos`. By list induction. -/
theorem guessAX_zAx'x_write_filter_eq {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.guessAX)) :
    w.filter (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.wt) =
    w.filter (fun l => match l.1.loc, l.1.op with
      | Loc.zAx'x, OpType.wt => true | _, _ => false) := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

/-- The `zAxx'`-read counterpart of `guessAX_zAx'x_write_filter_eq`. -/
theorem guessAX_zAxx'_read_filter_eq {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.guessAX)) :
    w.filter (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.rd) =
    w.filter (fun l => match l.1.loc, l.1.op with
      | Loc.zAxx', OpType.rd => true | _, _ => false) := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

/-- The `zAx'x`-write of the terminating outer iteration (`outerRest[N]`,
call `ksPrefix ks (N + 1)`, not covered by
`guessAXBlockWord_zAx'x_write_nestedInnerPos`) is at position
`nestedInnerStart ks (ksPrefix ks (N + 1)) + 1`. -/
theorem guessAXBlockWord_zAx'x_write_terminator_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks (ksPrefix ks (N + 1)) +
      1]? = some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hpos := guessAXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
    N 0 1 b vs hbvs a hva (by norm_num)
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1)) + 1
      = 4 + K0 * 3 + ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 1 + 1) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff]; exact hpos

/-- The count for `guessAXBlockWord_zAx'x_write_terminator_pos`. -/
theorem guessAXBlockWord_zAx'x_write_terminator_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks (ksPrefix ks (N + 1)) + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false)).length
      = ksPrefix ks (N + 1) := by
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
       , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)) := by
    unfold guessAXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)
    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] := by
    rfl
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1)) + 1
      = (4 + K0 * 3 - 1) +
        (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 1 + 1))) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff, heq0]
  have hinnerflatlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
    rw [List.length_flatMap]
    have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
        inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
  have hfirstlen : (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
    rw [List.length_append, hleadlen, hinnerflatlen]; omega
  rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length from hfirstlen.symm,
    List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _),
    show (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length +
        (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 1 + 1))) -
        (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length =
        1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 1 + 1)) from by omega,
    List.filter_append, List.length_append]
  have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX)) := by
    rw [List.filter_append, hleadfilter]
    congr 1
    exact guessAXInnerBlockElems_filter I
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) 1
      (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessAXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, Option.some.injEq, add_lt_add_iff_right, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, ge_iff_le, List.length_flatMap, List.map_take, Nat.succ_add_sub_one, zero_mul, ne_eq, zero_ne_one, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      inner0Rest
  rw [hleadinnerfilter, List.length_append, List.length_map]
  have hone : List.length
      [ (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ]
      = 1 := rfl
  rw [hone]
  have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
      (match b0.1.loc, b0.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) = false := by
    intro b0 hb0
    have hz : b0.1.loc ≠ Loc.zAx'x := by
      intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.zAx'x ∉ BridgeLoc)
    split
    · exact absurd (by assumption) hz
    · rfl
  have hellalen : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ] :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length ≤
      1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 1 + 1)) := by simp
  have hellasub : (1 + (((outerRest.take N).flatMap
        (fun q => guessAXOuterBlockElems I q.1 q.2)).length + (0 * 3 + 1 + 1))) -
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length =
      ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 1 + 1) := by simp
  rw [show ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ] ++
      outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
      (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 1 + 1))) =
      [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
      (outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 1 + 1)) from by
    rw [List.take_append, List.take_of_length_le hellalen, hellasub],
    List.filter_append]
  have hellafilter : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false) = [] :=
    rfl
  rw [hellafilter, List.length_append, List.length_nil]
  have houtercount := guessAXOuterRest_zAx'x_take_count I ks N hks outerRest houter
    hpredNonBridge N (le_refl N) b vs hbvs 0 1 a hva (by norm_num)
  rw [if_neg (show ¬ (1 : ℕ) < 1 from by omega)] at houtercount
  rw [houtercount, hks1]
  have hksmono : ksPrefix ks 1 ≤ ksPrefix ks (N + 1) := ksPrefix_mono ks (by omega)
  omega

/-- The count for `guessAXBlockWord_xA_write_terminator_pos`. -/
theorem guessAXBlockWord_xA_write_terminator_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks (ksPrefix ks (N + 1)))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false)).length
      = ksPrefix ks (N + 1) := by
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
       , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)) := by
    unfold guessAXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)
    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] := by
    rfl
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).length = 3 := rfl
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1))
      = (4 + K0 * 3 - 1) +
        (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 0 + 1))) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff, heq0]
  have hinnerflatlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
    rw [List.length_flatMap]
    have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
        inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
  have hfirstlen : (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
    rw [List.length_append, hleadlen, hinnerflatlen]; omega
  rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length from hfirstlen.symm,
    List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _),
    show (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length +
        (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 0 + 1))) -
        (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length =
        1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 0 + 1)) from by omega,
    List.filter_append, List.length_append]
  have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX)) := by
    rw [List.filter_append, hleadfilter]
    congr 1
    exact guessAXInnerBlockElems_filter I
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) 0
      (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessAXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, Option.some.injEq, add_lt_add_iff_right, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.succ_add_sub_one, zero_mul, add_zero, ge_iff_le, List.length_flatMap, List.map_take, ne_eq, not_true_eq_false, one_ne_zero, not_false_eq_true, Nat.one_lt_ofNat, List.getElem_cons_succ, List.getElem_cons_zero, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      inner0Rest
  rw [hleadinnerfilter, List.length_append, List.length_map]
  have hone : List.length
      [ (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ]
      = 1 := rfl
  rw [hone]
  have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
      (match b0.1.loc, b0.1.op with | Loc.xA, OpType.wt => true | _, _ => false) = false := by
    intro b0 hb0
    have hz : b0.1.loc ≠ Loc.xA := by
      intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.xA ∉ BridgeLoc)
    split
    · exact absurd (by assumption) hz
    · rfl
  have hellalen : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ] :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length ≤
      1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 0 + 1)) := by simp
  have hellasub : (1 + (((outerRest.take N).flatMap
        (fun q => guessAXOuterBlockElems I q.1 q.2)).length + (0 * 3 + 0 + 1))) -
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length =
      ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 0 + 1) := by simp
  rw [show ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ] ++
      outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
      (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 0 + 1))) =
      [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
      (outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 0 + 1)) from by
    rw [List.take_append, List.take_of_length_le hellalen, hellasub],
    List.filter_append]
  have hellafilter : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false) = [] :=
    rfl
  rw [hellafilter, List.length_append, List.length_nil]
  have houtercount := guessAXOuterRest_xA_take_count I ks N hks outerRest houter
    hpredNonBridge N (le_refl N) b vs hbvs 0 0 a hva (by norm_num)
  rw [if_neg (show ¬ (0 : ℕ) < 0 from by omega)] at houtercount
  rw [houtercount, hks1]
  have hksmono : ksPrefix ks 1 ≤ ksPrefix ks (N + 1) := ksPrefix_mono ks (by omega)
  omega

/-- The number of `xA`-writes before position `nestedInnerStart ks P` is `P`,
for `P ≤ ksPrefix ks (N + 1)`. -/
theorem guessAXBlockWord_xA_write_take_count_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false)).length
      = P := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessAXBlockWord_xA_write_take_count I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    rw [heq]
    exact guessAXBlockWord_xA_write_terminator_take_count I v1 v2 vB0 K0 inner0Rest outerRest ks N
      hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva

/-- The value for `guessAXBlockWord_zAx'x_write_terminator_pos`. -/
theorem guessAXBlockWord_zAx'x_write_terminator_val (I : PCPInstance) (_ _ : Val I)
    (_ : Val I × Val I) (K0 : ℕ) (_ : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (_ : ks.length = N + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (_ : outerRest[N]? = some (b, vs)) (_ : vs.length = 1)
    (a : Val I × Val I × Val I) (_ : vs[0]? = some a)
    (haval : a.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix ks' N + 0 + 1) % 4, by omega⟩ : Fin 4)) :
    a.2.1 = Val.cnt (⟨(ksPrefix ks (N + 1) + 1) % 4, by omega⟩ : Fin 4) := by
  have hcons : ksPrefix ks (N + 1) = (K0 + 1) + ksPrefix ks' N := by
    rw [hksrel, ksPrefix_cons]
  have hvaleq : (1 + K0 + ksPrefix ks' N + 0 + 1) % 4 = (ksPrefix ks (N + 1) + 1) % 4 := by
    rw [hcons]; omega
  have hfinEq : (⟨(1 + K0 + ksPrefix ks' N + 0 + 1) % 4, by omega⟩ : Fin 4) =
      (⟨(ksPrefix ks (N + 1) + 1) % 4, by omega⟩ : Fin 4) := Fin.ext hvaleq
  rw [haval]; exact congrArg Val.cnt hfinEq

/-- The `zAxx'`-read of the terminating outer iteration. -/
theorem guessAXBlockWord_zAxx'_read_terminator_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks (ksPrefix ks (N + 1)) +
      2]? = some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hpos := guessAXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
    N 0 2 b vs hbvs a hva (by norm_num)
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1)) + 2
      = 4 + K0 * 3 + ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 2 + 1) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff]; exact hpos

/-- The count for `guessAXBlockWord_zAxx'_read_terminator_pos`. -/
theorem guessAXBlockWord_zAxx'_read_terminator_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks (ksPrefix ks (N + 1)) + 2)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false)).length
      = ksPrefix ks (N + 1) - 1 := by
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
       , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
        outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)) := by
    unfold guessAXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)
    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) = [] := by
    rfl
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hlen := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1)) + 2
      = (4 + K0 * 3 - 1) +
        (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 2 + 1))) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff, heq0]
  have hinnerflatlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
    rw [List.length_flatMap]
    have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
        inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
  have hfirstlen : (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
    rw [List.length_append, hleadlen, hinnerflatlen]; omega
  rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length from hfirstlen.symm,
    List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _),
    show (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length +
        (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 2 + 1))) -
        (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I))).length =
        1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 2 + 1)) from by omega,
    List.filter_append, List.length_append]
  have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX), ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) =
      [] ++
        inner0Rest.map (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX)) := by
    rw [List.filter_append, hleadfilter]
    congr 1
    exact guessAXInnerBlockElems_filter I
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) 2
      (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessAXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, Option.some.injEq, add_lt_add_iff_right, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.filter_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true, forall_eq_or_imp, forall_eq, ge_iff_le, List.length_flatMap, List.map_take, Nat.succ_add_sub_one, zero_mul, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      inner0Rest
  rw [hleadinnerfilter, List.length_append, List.length_nil, List.length_map]
  have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
      (match b0.1.loc, b0.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) = false := by
    intro b0 hb0
    have hz : b0.1.loc ≠ Loc.zAxx' := by
      intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.zAxx' ∉ BridgeLoc)
    split
    · exact absurd (by assumption) hz
    · rfl
  have hellalen : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ] :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length ≤
      1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 2 + 1)) := by simp
  have hellasub : (1 + (((outerRest.take N).flatMap
        (fun q => guessAXOuterBlockElems I q.1 q.2)).length + (0 * 3 + 2 + 1))) -
      ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) ] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length =
      ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 2 + 1) := by simp
  rw [show ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ] ++
      outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
      (1 + (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 2 + 1))) =
      [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) ] ++
      (outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 2 + 1)) from by
    rw [List.take_append, List.take_of_length_le hellalen, hellasub],
    List.filter_append]
  have hellafilter : ([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) = [] :=
    rfl
  rw [hellafilter, List.length_append, List.length_nil]
  have houtercount := guessAXOuterRest_zAxx'_take_count I ks N hks outerRest houter
    hpredNonBridge N (le_refl N) b vs hbvs 0 2 a hva (by norm_num)
  rw [if_neg (show ¬ (2 : ℕ) < 2 from by omega)] at houtercount
  have houtercount2 : (((outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
      (((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length +
        (0 * 3 + 2 + 1))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false)).length
      = ksPrefix ks (N + 1) - ksPrefix ks 1 + (0 + 0) := houtercount
  rw [houtercount2, hks1]
  have hksmono : ksPrefix ks 1 ≤ ksPrefix ks (N + 1) := ksPrefix_mono ks (by omega)
  omega

/-- The value for `guessAXBlockWord_zAxx'_read_terminator_pos`. -/
theorem guessAXBlockWord_zAxx'_read_terminator_val (I : PCPInstance) (_ _ : Val I)
    (_ : Val I × Val I) (K0 : ℕ) (_ : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (_ : ks.length = N + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (_ : outerRest[N]? = some (b, vs)) (_ : vs.length = 1)
    (a : Val I × Val I × Val I) (_ : vs[0]? = some a)
    (haval : a.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix ks' N + 0) % 4, by omega⟩ : Fin 4)) :
    a.2.2 = Val.cnt (⟨(ksPrefix ks (N + 1)) % 4, by omega⟩ : Fin 4) := by
  have hcons : ksPrefix ks (N + 1) = (K0 + 1) + ksPrefix ks' N := by
    rw [hksrel, ksPrefix_cons]
  have hvaleq : (1 + K0 + ksPrefix ks' N + 0) % 4 = (ksPrefix ks (N + 1)) % 4 := by
    rw [hcons]; omega
  have hfinEq : (⟨(1 + K0 + ksPrefix ks' N + 0) % 4, by omega⟩ : Fin 4) =
      (⟨(ksPrefix ks (N + 1)) % 4, by omega⟩ : Fin 4) := Fin.ext hvaleq
  rw [haval]; exact congrArg Val.cnt hfinEq

/-- The `zAx'x`-write of call `P` is at position `nestedInnerStart ks P + 1`,
for `P ≤ ksPrefix ks (N + 1)`. -/
theorem guessAXBlockWord_zAx'x_write_pos_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    ∃ val, (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessAXBlockWord_zAx'x_write_nestedInnerPos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    refine ⟨a.2.1, ?_⟩
    rw [heq]
    exact guessAXBlockWord_zAx'x_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter b vs hbvs hvslen a hva

/-- The `zAxx'`-read of call `P` is at position `nestedInnerStart ks P + 2`,
for `1 ≤ P ≤ ksPrefix ks (N + 1)`. -/
theorem guessAXBlockWord_zAxx'_read_pos_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P ≤ ksPrefix ks (N + 1)) :
    ∃ val, (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessAXBlockWord_zAxx'_read_nestedInnerPos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hP1 hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    refine ⟨a.2.2, ?_⟩
    rw [heq]
    exact guessAXBlockWord_zAxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter b vs hbvs hvslen a hva

/-- The number of `zAx'x`-writes before position `nestedInnerStart ks P + 1`
is `P`, for `P ≤ ksPrefix ks (N + 1)`. -/
theorem guessAXBlockWord_zAx'x_write_take_count_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false)).length
      = P := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessAXBlockWord_zAx'x_write_take_count I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    have h := guessAXBlockWord_zAx'x_write_terminator_take_count I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
    rw [heq]; exact h

/-- The number of `zAxx'`-reads before position `nestedInnerStart ks P + 2` is
`P - 1`, for `1 ≤ P ≤ ksPrefix ks (N + 1)`. -/
theorem guessAXBlockWord_zAxx'_read_take_count_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P ≤ ksPrefix ks (N + 1)) :
    (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P + 2)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false)).length
      = P - 1 := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessAXBlockWord_zAxx'_read_take_count I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hP1 hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    have h := guessAXBlockWord_zAxx'_read_terminator_take_count I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
    rw [heq]; exact h

/-- The value of the `zAx'x`-write of call `P`, for
`P ≤ ksPrefix ks (N + 1)`. -/
theorem guessAXBlockWord_zAx'x_write_val_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (hks : ks.length = N + 1)
    (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hv2 : v2 = Val.cnt (1 : Fin 4))
    (hinner0val : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4))
    (houterval : ∀ m, m < N + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix ks' m + n + 1) % 4, by omega⟩ : Fin 4))
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x (Val.cnt (⟨(P + 1) % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessAXBlockWord_zAx'x_write_val I v1 v2 vB0 K0 inner0Rest outerRest ks ks' N hksrel hks
      hK0 hinner0len houterLen houter houterLast hv2 hinner0val
      (fun m hm => houterval m (by omega)) P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    obtain ⟨b', vs', hbvs', hval⟩ := houterval N (by omega)
    have hbeq : vs' = vs := congrArg Prod.snd (Option.some.inj (hbvs'.symm.trans hbvs))
    rw [hbeq] at hval
    obtain ⟨e, hae, heval⟩ := hval 0 h0
    rw [hva] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hval2 := guessAXBlockWord_zAx'x_write_terminator_val I v1 v2 vB0 K0 inner0Rest outerRest
      ks ks' N hksrel hks b vs hbvs hvslen a hva heval'
    have hpos := guessAXBlockWord_zAx'x_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
    rw [heq, hpos, hval2]

/-- The value of the `zAxx'`-read of call `P`, for
`1 ≤ P ≤ ksPrefix ks (N + 1)`. -/
theorem guessAXBlockWord_zAxx'_read_val_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (hks : ks.length = N + 1)
    (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hinner0val : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4))
    (houterval : ∀ m, m < N + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix ks' m + n) % 4, by omega⟩ : Fin 4))
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P ≤ ksPrefix ks (N + 1)) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' (Val.cnt (⟨P % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessAXBlockWord_zAxx'_read_val I v1 v2 vB0 K0 inner0Rest outerRest ks ks' N hksrel hks
      hK0 hinner0len houterLen houter houterLast hinner0val
      (fun m hm => houterval m (by omega)) P hP1 hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    obtain ⟨b', vs', hbvs', hval⟩ := houterval N (by omega)
    have hbeq : vs' = vs := congrArg Prod.snd (Option.some.inj (hbvs'.symm.trans hbvs))
    rw [hbeq] at hval
    obtain ⟨e, hae, heval⟩ := hval 0 h0
    rw [hva] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hval2 := guessAXBlockWord_zAxx'_read_terminator_val I v1 v2 vB0 K0 inner0Rest outerRest
      ks ks' N hksrel hks b vs hbvs hvslen a hva heval'
    have hpos := guessAXBlockWord_zAxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
    rw [heq, hpos, hval2]

/-- The length of `guessAXBlockWord`:
`nestedInnerStart ks (ksPrefix ks (N + 1)) + 4`. -/
theorem guessAXBlockWord_length (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length =
      nestedInnerStart ks (ksPrefix ks (N + 1)) + 4 := by
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
      , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
      , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessAXInnerBlockElems I)) ++
      [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ] :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hwhole : outerRest.take (N + 1) = outerRest := by
    rw [← houterLen, List.take_length]
  have hlenAll := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    houterLast (N + 1) (by omega)
  rw [hwhole] at hlenAll
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hstartlast : nestedOuterStart ks N (N + 1 + 1) = nestedOuterStart ks N (N + 1) + 5 := by
    rw [nestedOuterStart_succ]
    congr 1
    unfold nestedOuterLen
    rw [if_pos rfl]
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  unfold guessAXBlockWord
  rw [List.length_append, hleadlen, hlenAll]
  omega

/-- The position of the final `ellAyx`-read of `guessAXBlockWord`. -/
theorem guessAXBlockWord_ellAyx_terminator_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (N : ℕ) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[4 + K0 * 3 +
      ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length + 4]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) := by
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  rw [heq, List.getElem?_append_right (by rw [hleadlen]; omega), hleadlen,
    show 4 + K0 * 3 + ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
      + 4 - (4 + K0 * 3) = ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
      + 4 from by omega]
  have hqlt : (4 : ℕ) < (guessAXOuterBlockElems I b vs).length := by
    rw [guessAXOuterBlockElems_length, hvslen]; omega
  have hstep := list_take_flatMap_offset_getElem (fun q => guessAXOuterBlockElems I q.1 q.2)
    outerRest N 4 (b, vs) hbvs hqlt
  rw [hstep, vs.eq_getElem_of_length_eq_one hvslen]
  rfl

/-- `guessAXBlockWord` contains `ksPrefix ks (N + 1) + 1` `xA`-writes. -/
theorem guessAXBlockWord_xA_write_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xA, OpType.wt => true | _, _ => false)).length
      = ksPrefix ks (N + 1) + 1 := by
  obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
  have ha0 : (0 : ℕ) < vs.length := by omega
  obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'ha0, List.getElem?_eq_getElem ha0⟩
  have hlen := guessAXBlockWord_length I v1 v2 vB0 K0 inner0Rest outerRest ks N hks hK0
    hinner0len houterLen houter ⟨b, vs, hbvs, hvslen⟩
  have hcountW := guessAXBlockWord_xA_write_terminator_take_count I v1 v2 vB0 K0 inner0Rest
    outerRest ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposXA := guessAXBlockWord_xA_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposW := guessAXBlockWord_zAx'x_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposR := guessAXBlockWord_zAxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposE := guessAXBlockWord_ellAyx_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len N b vs hbvs hvslen
  set Q := nestedInnerStart ks (ksPrefix ks (N + 1)) with hQdef
  set pred := (fun l : ThreadLabel (domainOf I) Tid.guessAX => match l.1.loc, l.1.op with
    | Loc.xA, OpType.wt => true | _, _ => false) with hpreddef
  have hbridge : Q + 3 = 4 + K0 * 3 +
      ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length + 4 := by
    have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hlenL := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      ⟨b, vs, hbvs, hvslen⟩ N (by omega)
    have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N N
      rwa [hgetD0] at hh
    rw [hQdef, ← hstart, hlenL, hstartm]; omega
  have step0 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1)).filter
      pred).length = (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take Q).filter
      pred).length + 1 := by
    rw [List.take_add_one, hposXA, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step1 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1)).filter
      pred).length = (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1)).filter
      pred).length := by
    rw [List.take_add_one, hposW, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step2 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1)).filter
      pred).length = (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1)).filter
      pred).length := by
    rw [List.take_add_one, hposR, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step3 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (Q + 1 + 1 + 1 + 1)).filter pred).length =
      (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1)).filter
      pred).length := by
    rw [List.take_add_one, show Q + 1 + 1 + 1 = Q + 3 from by omega, hbridge, hposE,
      Option.toList_some, List.filter_append, List.length_append, hpreddef]
    rfl
  have hfull : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1 + 1) =
      guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest := by
    rw [show Q + 1 + 1 + 1 + 1 = (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length from
      by rw [hlen]]
    exact List.take_length
  rw [← hfull]
  omega

/-- `guessAXBlockWord` contains `ksPrefix ks (N + 1) + 1` `zAx'x`-writes. -/
theorem guessAXBlockWord_zAx'x_write_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAx'x, OpType.wt => true | _, _ => false)).length
      = ksPrefix ks (N + 1) + 1 := by
  obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
  have ha0 : (0 : ℕ) < vs.length := by omega
  obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'ha0, List.getElem?_eq_getElem ha0⟩
  have hlen := guessAXBlockWord_length I v1 v2 vB0 K0 inner0Rest outerRest ks N hks hK0
    hinner0len houterLen houter ⟨b, vs, hbvs, hvslen⟩
  have hcountW := guessAXBlockWord_zAx'x_write_terminator_take_count I v1 v2 vB0 K0 inner0Rest
    outerRest ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposW := guessAXBlockWord_zAx'x_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposR := guessAXBlockWord_zAxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposE := guessAXBlockWord_ellAyx_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len N b vs hbvs hvslen
  set Q := nestedInnerStart ks (ksPrefix ks (N + 1)) with hQdef
  set pred := (fun l : ThreadLabel (domainOf I) Tid.guessAX => match l.1.loc, l.1.op with
    | Loc.zAx'x, OpType.wt => true | _, _ => false) with hpreddef
  have hbridge : Q + 3 = 4 + K0 * 3 +
      ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length + 4 := by
    have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hlenL := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      ⟨b, vs, hbvs, hvslen⟩ N (by omega)
    have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N N
      rwa [hgetD0] at hh
    rw [hQdef, ← hstart, hlenL, hstartm]; omega
  have step1 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1)).filter
      pred).length = (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1)).filter
      pred).length + 1 := by
    rw [List.take_add_one, hposW, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step2 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1)).filter
      pred).length = (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1)).filter
      pred).length := by
    rw [List.take_add_one, hposR, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step3 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (Q + 1 + 1 + 1 + 1)).filter pred).length =
      (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1)).filter
      pred).length := by
    rw [List.take_add_one, show Q + 1 + 1 + 1 = Q + 3 from by omega, hbridge, hposE,
      Option.toList_some, List.filter_append, List.length_append, hpreddef]
    rfl
  have hfull : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1 + 1) =
      guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest := by
    rw [show Q + 1 + 1 + 1 + 1 = (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length from
      by rw [hlen]]
    exact List.take_length
  rw [← hfull]
  omega

/-- `guessAXBlockWord` contains `ksPrefix ks (N + 1)` `zAxx'`-reads (call `0`
has none). -/
theorem guessAXBlockWord_zAxx'_read_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false)).length
      = ksPrefix ks (N + 1) := by
  obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
  have ha0 : (0 : ℕ) < vs.length := by omega
  obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'ha0, List.getElem?_eq_getElem ha0⟩
  have hlen := guessAXBlockWord_length I v1 v2 vB0 K0 inner0Rest outerRest ks N hks hK0
    hinner0len houterLen houter ⟨b, vs, hbvs, hvslen⟩
  have hcountR := guessAXBlockWord_zAxx'_read_terminator_take_count I v1 v2 vB0 K0 inner0Rest
    outerRest ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposR := guessAXBlockWord_zAxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposE := guessAXBlockWord_ellAyx_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len N b vs hbvs hvslen
  set Q := nestedInnerStart ks (ksPrefix ks (N + 1)) with hQdef
  set pred := (fun l : ThreadLabel (domainOf I) Tid.guessAX => match l.1.loc, l.1.op with
    | Loc.zAxx', OpType.rd => true | _, _ => false) with hpreddef
  have hbridge : Q + 3 = 4 + K0 * 3 +
      ((outerRest.take N).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length + 4 := by
    have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hlenL := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      ⟨b, vs, hbvs, hvslen⟩ N (by omega)
    have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N N
      rwa [hgetD0] at hh
    rw [hQdef, ← hstart, hlenL, hstartm]; omega
  have step1 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2 + 1)).filter
      pred).length = (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2)).filter
      pred).length + 1 := by
    rw [List.take_add_one, hposR, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step2 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2 + 1 + 1)).filter
      pred).length = (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2 + 1)).filter
      pred).length := by
    rw [List.take_add_one, show Q + 2 + 1 = Q + 3 from by omega, hbridge, hposE, Option.toList_some,
      List.filter_append, List.length_append, hpreddef]
    rfl
  have hfull : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2 + 1 + 1) =
      guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest := by
    rw [show Q + 2 + 1 + 1 = (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length from
      by rw [hlen]]
    exact List.take_length
  have hge1 : 1 ≤ ksPrefix ks (N + 1) := by
    have h := ksPrefix_ge ks (N + 1); omega
  rw [← hfull]
  omega

/-! ## Eq. (15)'s `zAxx'`/`zAx'x` no-skipping pair (`GuessAX`/`PrimeAX`)

`GuessAX` writes `zAx'x` and reads `zAxx'`; `PrimeAX` writes `zAxx'` and reads
`zAx'x`. `GuessAX`'s side goes through the nested-call position layer above
(`nestedInnerStart`); `PrimeAX`'s is a uniform 3-entry block. -/

/-- `PrimeAX`'s `n`-th `zAxx'`-write is at position `n*3+1` of
`G.threadEvents Tid.primeAX`. -/
theorem primeAX_zAxx'_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {vals : List (Val I)}
    (hw2 : G.threadWord Tid.primeAX = (primeAXBlockWord I vals).map some)
    (n : ℕ) {v : Val I} (hv : vals[n]? = some v) :
    ∃ hlen : n * 3 + 1 < (G.threadEvents Tid.primeAX).length,
      G.nthWrite Tid.primeAX Loc.zAxx' n =
        some ((G.threadEvents Tid.primeAX)[n * 3 + 1]'hlen).1 := by
  have hnlen : n < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hsplit := list_take_flatMap_uniform_offset (primeAXBlockElems I) 3 (fun _ => rfl)
    vals n 1 v hv (by norm_num)
  have hpartial : ((primeAXBlockElems I v).take 1).filter
      (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.wt) = [] := by
    unfold primeAXBlockElems
    rfl
  have hone_w : ∀ v' : Val I, (primeAXBlockElems I v').filter
      (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeAX Loc.zAxx' v', rfl⟩ : ThreadLabel (domainOf I) Tid.primeAX)] := by
    intro v'
    unfold primeAXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_w : (((primeAXBlockWord I vals).take (n * 3 + 1)).filter
      (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.wt)).length = n := by
    rw [primeAXBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_w]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeAX).length = (primeAXBlockWord I vals).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeAXBlockWord I vals).length = 3 * vals.length := by
    rw [primeAXBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (vals.map (fun a => (primeAXBlockElems I a).length))
        = vals.map (fun _ => 3) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_w : n * 3 + 1 < (G.threadEvents Tid.primeAX).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_w : (primeAXBlockWord I vals)[n * 3 + 1]? =
      some (⟨EventLabel.wt Tid.primeAX Loc.zAxx' v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeAX) := by
    rw [primeAXBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeAXBlockElems I) 3 (fun _ => rfl) vals n
      1 v hv (by norm_num)
    rw [hget]
    unfold primeAXBlockElems
    rfl
  refine ⟨hlen_w, ?_⟩
  have hwpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zAxx') (op := OpType.wt)
    hw2 hlen_w hlabP_w rfl rfl hcount_w
  rwa [show G.nthEvent Tid.primeAX Loc.zAxx' OpType.wt n = G.nthWrite Tid.primeAX Loc.zAxx' n
    from rfl] at hwpos

/-- `PrimeAX`'s `n`-th `zAx'x`-read is at position `n*3+2` of
`G.threadEvents Tid.primeAX`. -/
theorem primeAX_zAx'x_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {vals : List (Val I)}
    (hw2 : G.threadWord Tid.primeAX = (primeAXBlockWord I vals).map some)
    (n : ℕ) {v : Val I} (hv : vals[n]? = some v) :
    ∃ hlen : n * 3 + 2 < (G.threadEvents Tid.primeAX).length,
      G.nthRead Tid.primeAX Loc.zAx'x n =
        some ((G.threadEvents Tid.primeAX)[n * 3 + 2]'hlen).1 := by
  have hnlen : n < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hsplit := list_take_flatMap_uniform_offset (primeAXBlockElems I) 3 (fun _ => rfl)
    vals n 2 v hv (by norm_num)
  have hpartial : ((primeAXBlockElems I v).take 2).filter
      (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.rd) = [] := by
    unfold primeAXBlockElems
    rfl
  have hone : ∀ v' : Val I, (primeAXBlockElems I v').filter
      (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeAX Loc.zAx'x v', rfl⟩ : ThreadLabel (domainOf I) Tid.primeAX)] := by
    intro v'
    unfold primeAXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((primeAXBlockWord I vals).take (n * 3 + 2)).filter
      (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.rd)).length = n := by
    rw [primeAXBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeAX).length = (primeAXBlockWord I vals).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeAXBlockWord I vals).length = 3 * vals.length := by
    rw [primeAXBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (vals.map (fun a => (primeAXBlockElems I a).length))
        = vals.map (fun _ => 3) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_er : n * 3 + 2 < (G.threadEvents Tid.primeAX).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_er : (primeAXBlockWord I vals)[n * 3 + 2]? =
      some (⟨EventLabel.rd Tid.primeAX Loc.zAx'x v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeAX) := by
    rw [primeAXBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeAXBlockElems I) 3 (fun _ => rfl) vals n
      2 v hv (by norm_num)
    rw [hget]
    unfold primeAXBlockElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zAx'x) (op := OpType.rd)
    hw2 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.primeAX Loc.zAx'x OpType.rd n = G.nthRead Tid.primeAX Loc.zAx'x n
    from rfl] at herpos

/-- Eq. (15)'s `zAxx'`/`zAx'x` pair (`GuessAX`/`PrimeAX`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`guessAX_shape_inv`, `primeAX_shape_inv`). `GuessAX`'s inner calls are
numbered `0, 1, …` across the whole thread (flattened past outer-iteration
boundaries, `ks := K0 :: guessAXJsToKs I js`); call `P` writes `zAx'x` at
`nestedInnerStart ks P + 1`, and every call but the globally-first one reads
`zAxx'` at `nestedInnerStart ks P + 2`, so `GuessAX`'s `j`-th `zAxx'`-read is
call `j + 1`. Both locations have a single writer, so writer identification
is `writerTid_confined`. -/
theorem guessAX_primeAX_zAx_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.guessAX Tid.primeAX Loc.zAxx' Loc.zAx'x := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessAX_run_of_reaches I G hG
  obtain ⟨v0, K0, js, v1, v2, vB0, inner0Rest, outerRest, -, -, hinner0len, houterLen, houter,
    houterLast, hv2, hinner0val, houterval, -, -, -, -, -, -, hσ1⟩ := guessAX_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := primeAX_run_of_reaches I G hG
  obtain ⟨M, vals, -, -, hvalsval, hσ2⟩ := primeAX_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAX, hσ1]
  have hw2 : G.threadWord Tid.primeAX = (primeAXBlockWord I vals).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeAX, hσ2]
  have hks : (K0 :: guessAXJsToKs I js).length = js.length + 1 := by simp [guessAXJsToKs]
  have hK0 : (K0 :: guessAXJsToKs I js)[0]? = some K0 := rfl
  have houter' : ∀ j, j < js.length → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      (K0 :: guessAXJsToKs I js)[j + 1]? = some km ∧ vs.length = km + 1 := by
    intro j hj
    obtain ⟨b, vs, km, hbvs, hksm, hvslen⟩ := houter j hj
    exact ⟨b, vs, km, hbvs, hksm, hvslen⟩
  have hinner0val_write : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4) := fun n hn =>
    let ⟨e, he, _, he1⟩ := hinner0val n hn; ⟨e, he, he1⟩
  have houterval_write : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix (guessAXJsToKs I js) m + n + 1) % 4,
          by omega⟩ : Fin 4) := fun m hm =>
    let ⟨b, vs, hbvs, hval⟩ := houterval m hm
    ⟨b, vs, hbvs, fun n hn => let ⟨e, he, _, he1⟩ := hval n hn; ⟨e, he, he1⟩⟩
  have hinner0val_read : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4) := fun n hn =>
    let ⟨e, he, he2, _⟩ := hinner0val n hn; ⟨e, he, he2⟩
  have houterval_read : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix (guessAXJsToKs I js) m + n) % 4,
          by omega⟩ : Fin 4) := fun m hm =>
    let ⟨b, vs, hbvs, hval⟩ := houterval m hm
    ⟨b, vs, hbvs, fun n hn => let ⟨e, he, he2, _⟩ := hval n hn; ⟨e, he, he2⟩⟩
  set ks := K0 :: guessAXJsToKs I js with hksdef
  set K := ksPrefix ks (js.length + 1) with hKdef
  -- `GuessAX`'s `zAx'x`-writes number `K + 1`, its `zAxx'`-reads `K`.
  have hGWb : ∀ {i : ℕ} {w : Event (domainOf I)},
      G.nthWrite Tid.guessAX Loc.zAx'x i = some w → i ≤ K := by
    intro i w hw
    have hitot : i < (G.opEvents Tid.guessAX Loc.zAx'x OpType.wt).length :=
      (List.getElem?_eq_some_iff.mp hw).1
    have hL := G.opEvents_map_lab_eq_filter_threadLabels Tid.guessAX Loc.zAx'x OpType.wt
    have hLlen := congrArg List.length hL
    rw [List.length_map, List.length_map, hσ1] at hLlen
    have hLlen2 := (guessAX_zAx'x_write_filter_eq (I := I)
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)) ▸ hLlen
    have htot := guessAXBlockWord_zAx'x_write_total_count I v1 v2 vB0 K0 inner0Rest outerRest
      ks js.length hks hK0 hinner0len houterLen houter' houterLast
    omega
  have hGRb : ∀ {j : ℕ} {r : Event (domainOf I)},
      G.nthRead Tid.guessAX Loc.zAxx' j = some r → j + 1 ≤ K := by
    intro j r hr
    have hjtot : j < (G.opEvents Tid.guessAX Loc.zAxx' OpType.rd).length :=
      (List.getElem?_eq_some_iff.mp hr).1
    have hL := G.opEvents_map_lab_eq_filter_threadLabels Tid.guessAX Loc.zAxx' OpType.rd
    have hLlen := congrArg List.length hL
    rw [List.length_map, List.length_map, hσ1] at hLlen
    have hLlen2 := (guessAX_zAxx'_read_filter_eq (I := I)
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)) ▸ hLlen
    have htot := guessAXBlockWord_zAxx'_read_total_count I v1 v2 vB0 K0 inner0Rest outerRest
      ks js.length hks hK0 hinner0len houterLen houter' houterLast
    omega
  -- `GuessAX`'s `i`-th `zAx'x`-write is call `i`, at `nestedInnerStart ks i + 1`.
  have hGW : ∀ i, i ≤ K → ∃ hlen : nestedInnerStart ks i + 1 < (G.threadEvents Tid.guessAX).length,
      G.nthWrite Tid.guessAX Loc.zAx'x i =
        some ((G.threadEvents Tid.guessAX)[nestedInnerStart ks i + 1]'hlen).1 ∧
      ∃ c : Fin 4, ((G.threadEvents Tid.guessAX)[nestedInnerStart ks i + 1]'hlen).1.val =
        Val.cnt c ∧ c.val = (i + 1) % 4 := by
    intro i hi
    have hval := guessAXBlockWord_zAx'x_write_val_full I v1 v2 vB0 K0 inner0Rest outerRest
      ks (guessAXJsToKs I js) js.length rfl hks hK0 hinner0len houterLen
      houter' houterLast hv2 hinner0val_write houterval_write i hi
    obtain ⟨eSub, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 _ _ hval
    have hcountB := guessAXBlockWord_zAx'x_write_take_count_full I v1 v2 vB0 K0 inner0Rest
      outerRest ks js.length hks hK0 hinner0len houterLen houter' houterLast i hi
    have hcount : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks i + 1)).filter
        (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.wt)).length = i := by
      rw [guessAX_zAx'x_write_filter_eq]
      simpa using hcountB
    refine ⟨hlt, G.nthEvent_eq_of_threadWord_pos hw1 hlt hval rfl rfl hcount,
      ⟨(i + 1) % 4, by omega⟩, ?_, rfl⟩
    rw [heq, Event.val, hlab]
    rfl
  -- `GuessAX`'s `j`-th `zAxx'`-read is call `j + 1`, at `nestedInnerStart ks (j + 1) + 2`.
  have hGR : ∀ j, j + 1 ≤ K →
      ∃ hlen : nestedInnerStart ks (j + 1) + 2 < (G.threadEvents Tid.guessAX).length,
      G.nthRead Tid.guessAX Loc.zAxx' j =
        some ((G.threadEvents Tid.guessAX)[nestedInnerStart ks (j + 1) + 2]'hlen).1 ∧
      ∃ c : Fin 4, ((G.threadEvents Tid.guessAX)[nestedInnerStart ks (j + 1) + 2]'hlen).1.val =
        Val.cnt c ∧ c.val = (j + 1) % 4 := by
    intro j hj
    have hval := guessAXBlockWord_zAxx'_read_val_full I v1 v2 vB0 K0 inner0Rest outerRest
      ks (guessAXJsToKs I js) js.length rfl hks hK0 hinner0len houterLen
      houter' houterLast hinner0val_read houterval_read (j + 1) (by omega) hj
    obtain ⟨eSub, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 _ _ hval
    have hcountB := guessAXBlockWord_zAxx'_read_take_count_full I v1 v2 vB0 K0 inner0Rest
      outerRest ks js.length hks hK0 hinner0len houterLen houter' houterLast (j + 1)
      (by omega) hj
    have hcount : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks (j + 1) + 2)).filter
        (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.rd)).length = j := by
      rw [guessAX_zAxx'_read_filter_eq]
      simpa using hcountB
    refine ⟨hlt, G.nthEvent_eq_of_threadWord_pos hw1 hlt hval rfl rfl hcount,
      ⟨(j + 1) % 4, by omega⟩, ?_, rfl⟩
    rw [heq, Event.val, hlab]
    rfl
  -- `primeAX`'s `i`-th `zAxx'`-write and `zAx'x`-read: value `(i+1) mod 4`, in block `vals[i]`.
  have hWp : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.primeAX Loc.zAxx' i = some w →
      (∃ c : Fin 4, w.val = Val.cnt c ∧ c.val = (i + 1) % 4) ∧ i < vals.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    have hf := (primeAXBlockWord_zAxx'_write_val I vals i).symm.trans hf
    rcases hv : vals[i]? with _ | v
    · rw [hv] at hf; exact nomatch hf
    · rw [hv] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hvv := hvalsval i hlt
      rw [hv] at hvv
      refine ⟨⟨⟨(i + 1) % 4, by omega⟩, ?_, rfl⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf, ← Option.some.inj hvv]
      rfl
  have hRq : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.primeAX Loc.zAx'x j = some r →
      (∃ c : Fin 4, r.val = Val.cnt c ∧ c.val = (j + 1) % 4) ∧ j < vals.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (primeAXBlockWord_zAx'x_read_val I vals j).symm.trans hf
    rcases hv : vals[j]? with _ | v
    · rw [hv] at hf; exact nomatch hf
    · rw [hv] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hvv := hvalsval j hlt
      rw [hv] at hvv
      refine ⟨⟨⟨(j + 1) % 4, by omega⟩, ?_, rfl⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf, ← Option.some.inj hvv]
      rfl
  have hval : ∀ {n : ℕ}, n < vals.length → ∃ v, vals[n]? = some v :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWp hw
    obtain ⟨hlen, hpos, c', hc', hc'v⟩ := hGR j (hGRb hr)
    rw [hc, Option.some.inj (hr.symm.trans hpos), hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨hlen, hpos, c, hc, hcv⟩ := hGW i (hGWb hw)
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRq hr
    rw [Option.some.inj (hw.symm.trans hpos), hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.primeAX := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.guessAX := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · -- `guessAX`: `r(zAxx')` of call `i + 1` precedes `w(zAx'x)` of call `ℓ ≥ i + 2`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨hlenR, hposR, -⟩ := hGR i (hGRb hr)
    obtain ⟨hlenW, hposW, -⟩ := hGW ℓ (hGWb hw)
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    have hmono := (nestedInnerStart_strictMono ks).monotone (show i + 2 ≤ ℓ from hiℓ)
    have hstep : nestedInnerStart ks (i + 2) =
        nestedInnerStart ks (i + 1) + (nestedCallLen (i + 1) + nestedGap ks (i + 1)) :=
      nestedInnerStart_succ ks (i + 1)
    have hcall : 2 ≤ nestedCallLen (i + 1) := by unfold nestedCallLen; split <;> omega
    exact G.po_of_threadEvents_pos_lt Tid.guessAX hlenR hlenW (by omega)
  · -- `primeAX`: `r(zAx'x)` at `i*3+2` precedes `w(zAxx')` at `ℓ*3+1`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨v, hv⟩ := hval (hRq hr).2
    obtain ⟨v', hv'⟩ := hval (hWp hw).2
    obtain ⟨hlenR, hposR⟩ := primeAX_zAx'x_read_nthRead_pos I G hw2 i hv
    obtain ⟨hlenW, hposW⟩ := primeAX_zAxx'_write_nthWrite_pos I G hw2 ℓ hv'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.primeAX hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    exact ⟨_, (hGR i (by have := hGWb hw; omega)).2.1⟩
  · intro i ℓ w hw hiℓ
    obtain ⟨v, hv⟩ := hval (n := i) (by have := (hWp hw).2; omega)
    exact ⟨_, (primeAX_zAx'x_read_nthRead_pos I G hw2 i hv).2⟩

theorem no_skipping_guessAX_primeAX_zAxx' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeAX Loc.zAxx' i = some ew)
    (her : G.nthRead Tid.guessAX Loc.zAxx' K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((guessAX_primeAX_zAx_noSkipPair I G hG).no_skipping hG.1.1 K).1 hew her hrf

theorem no_skipping_guessAX_primeAX_zAx'x (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (n K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessAX Loc.zAx'x n = some ew)
    (her : G.nthRead Tid.primeAX Loc.zAx'x K = some er) (hrf : G.rf ew er) :
    n = K :=
  ((guessAX_primeAX_zAx_noSkipPair I G hG).no_skipping hG.1.1 K).2 hew her hrf

/-! ## Eq. (15)'s `zBxx'`/`zBx'x` pair (`GuessBX`/`PrimeBX`): positions

As for `GuessAX`: `G.nthWrite Tid.guessBX Loc.zBx'x i` is inner call `i`, and
`G.nthRead Tid.guessBX Loc.zBxx' k` is inner call `k + 1`. -/

/-- The `zBx'x`-write of the thread's first call is at position `2` of
`guessBXBlockWord`. -/
theorem guessBXBlockWord_lead_zBx'x_write_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[2]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) :=
  rfl

/-- The `n`-th entry of `inner0Rest` (call `n + 1`) is at position `3 * n + 3`
of `guessBXBlockWord`. -/
theorem guessBXBlockWord_inner0Rest_pos (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (n p : ℕ) (a : Val I × Val I × Val I) (hva : inner0Rest[n]? = some a) (hp : p < 3) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[3 + n * 3 + p]? =
      (guessBXInnerBlockElems I a)[p]? := by
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
       , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)) := by
    unfold guessBXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)
    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).length = 3 := rfl
  rw [heq, List.getElem?_append_left (by
    rw [List.length_append, hleadlen]
    have hnlen : n < inner0Rest.length := (List.getElem?_eq_some_iff.mp hva).1
    have hlt : n * 3 + p < (inner0Rest.flatMap (guessBXInnerBlockElems I)).length := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat]
      omega
    omega)]
  rw [List.getElem?_append_right (by rw [hleadlen]; omega), hleadlen]
  have hi : 3 + n * 3 + p - 3 = n * 3 + p := by omega
  rw [hi]
  exact flatMap_uniform_getElem_fwd (guessBXInnerBlockElems I) 3 (fun _ => rfl)
    inner0Rest n p a hva hp

/-- Within one outer block `guessBXOuterBlockElems`, event `p` of inner call
`n` is at position `1 + n * 3 + p`. -/
theorem guessBXOuterBlockElems_inner_pos (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p < 3) :
    (guessBXOuterBlockElems I b vs)[n * 3 + p + 1]? = (guessBXInnerBlockElems I a)[p]? := by
  have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
  have hlt : n * 3 + p < (vs.flatMap (guessBXInnerBlockElems I)).length := by
    rw [List.length_flatMap]
    have heq1 : (vs.map (fun a => (guessBXInnerBlockElems I a).length)) =
        vs.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat]
    have : n + 1 ≤ vs.length := hnlen
    nlinarith
  unfold guessBXOuterBlockElems
  rw [List.getElem?_cons_succ, List.getElem?_append_left hlt]
  exact flatMap_uniform_getElem_fwd (guessBXInnerBlockElems I) 3 (fun _ => rfl) vs n p a hva hp

/-- Position in `guessBXBlockWord` of event `p` of inner call `n` of
`outerRest[m]`. -/
theorem guessBXBlockWord_outerRest_pos (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (m n p : ℕ) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hmbv : outerRest[m]? = some (b, vs)) (a : Val I × Val I × Val I) (hva : vs[n]? = some a)
    (hp : p < 3) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[4 + K0 * 3 +
      ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length +
      (n * 3 + p + 1)]? = (guessBXInnerBlockElems I a)[p]? := by
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  rw [heq, List.getElem?_append_right (by rw [hleadlen]; omega), hleadlen,
    show 4 + K0 * 3 + ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
      + (n * 3 + p + 1) - (4 + K0 * 3)
      = ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
      + (n * 3 + p + 1) from by omega]
  have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
  have hqlt : n * 3 + p + 1 < (guessBXOuterBlockElems I b vs).length := by
    rw [guessBXOuterBlockElems_length]
    omega
  have hstep := list_take_flatMap_offset_getElem (fun q => guessBXOuterBlockElems I q.1 q.2)
    outerRest m (n * 3 + p + 1) (b, vs) hmbv hqlt
  rw [hstep]
  exact guessBXOuterBlockElems_inner_pos I b vs n p a hva hp

/-- The prefix length in `guessBXBlockWord_outerRest_pos`, in terms of
`nestedOuterStart`. -/
theorem guessBXOuterRest_prefix_length_eq (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (hks : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) (m : ℕ) (hm : m ≤ N + 1) :
    ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
      = nestedOuterStart ks N (m + 1) - nestedOuterStart ks N 1 :=
  guessBXOuterRest_prefix_length I ks N hks outerRest houterLen houter houterLast m hm

/-- The `xB`-write of call `P` is at position `nestedInnerStart ks P`. -/
theorem guessBXBlockWord_xB_write_nestedInnerPos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    ∃ val, (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.xB val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · refine ⟨v1, ?_⟩
      rw [show P = 0 from by omega, show nestedInnerStart ks 0 = 1 from rfl]
      rfl
    · have hks00 : ks[0]'hks0pos = K0 := by
        have h := List.getElem?_eq_getElem (l := ks) hks0pos
        rw [hK0] at h; exact (Option.some.inj h).symm
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      refine ⟨(inner0Rest[n - 1]'hnm1lt).1, ?_⟩
      have hpos := guessBXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 0
        (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
      have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
      rw [show n - 1 + 1 = n from by omega] at hns
      rw [heq', hns]
      have hoff : 3 + (n - 1) * 3 + 0 = 3 * n := by omega
      rwa [hoff] at hpos
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    refine ⟨(vs[n]'hnvs).1, ?_⟩
    have hpos := guessBXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 0 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 0 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff]
    exact hpos

/-- The `xB`-write of the call of the terminating outer iteration. -/
theorem guessBXBlockWord_xB_write_terminator_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks (ksPrefix ks (N + 1))]?
      = some (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hpos := guessBXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
    N 0 0 b vs hbvs a hva (by norm_num)
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1))
      = 4 + K0 * 3 + ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 0 + 1) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff]; exact hpos

/-- The `xB`-write of call `P` is at position `nestedInnerStart ks P`, for
`P ≤ ksPrefix ks (N + 1)`. -/
theorem guessBXBlockWord_xB_write_pos_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    ∃ val, (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.xB val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessBXBlockWord_xB_write_nestedInnerPos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    refine ⟨a.1, ?_⟩
    rw [heq]
    exact guessBXBlockWord_xB_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter b vs hbvs hvslen a hva

/-- The number of `xB`-writes within a possibly partial outer block. -/
theorem guessBXOuterBlockElems_xB_take_count (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((guessBXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false)).length
      = n + (if 0 < p then 1 else 0) := by
  have hstep : ((guessBXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) =
      ((vs.flatMap (guessBXInnerBlockElems I)).take (n * 3 + p)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) := by
    unfold guessBXOuterBlockElems
    rw [List.take_succ_cons, List.filter_cons_of_neg (fun h => Bool.noConfusion h),
      List.take_append, List.filter_append]
    have hnil : (([⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).take
          (n * 3 + p - (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hxmem : x ∈ ([⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩] :
          List (ThreadLabel (domainOf I) Tid.guessBX)) := List.mem_of_mem_take hx
      simp only [List.mem_singleton] at hxmem
      subst hxmem
      exact fun h => Bool.noConfusion h
    rw [hnil, List.append_nil]
  rw [hstep]
  exact flatMap_uniform_take_count (guessBXInnerBlockElems I) 3 (fun _ => rfl)
    (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) 0
    (by norm_num)
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun _ => rfl) (fun _ => rfl)
    (fun a q b hq hqb => by
      unfold guessBXInnerBlockElems at hqb
      rcases q with _ | _ | _ | q <;> simp_all only [ne_eq, not_true_eq_false, zero_add, one_ne_zero, not_false_eq_true, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos, List.getElem_cons_succ, List.getElem_cons_zero, Option.some.injEq, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
    vs n a hva p hp

/-- The number of `xB`-writes before an arbitrary position of `outerRest`'s
flatMap. -/
theorem guessBXOuterRest_xB_take_count (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (hks : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (hpredNonBridge :
      ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.xB, OpType.wt => true | _, _ => false) = false)
    (M : ℕ) (hM : M ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hMbv : outerRest[M]? = some (b, vs)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take M).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length +
          (n * 3 + p + 1))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false)).length
      = (ksPrefix ks (M + 1) - ksPrefix ks 1) + (n + (if 0 < p then 1 else 0)) := by
  have hqbound : n * 3 + p + 1 ≤ (guessBXOuterBlockElems I b vs).length := by
    have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
    rw [guessBXOuterBlockElems_length]
    omega
  rw [list_take_flatMap_offset (fun q => guessBXOuterBlockElems I q.1 q.2) outerRest M
    (n * 3 + p + 1) (b, vs) hMbv hqbound, List.filter_append, List.length_append,
    guessBXOuterRest_prefix_matchCount I ks N hks outerRest houter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) 0
      (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessBXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [add_lt_add_iff_right, getElem?_pos, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, Subtype.forall, ne_eq, not_true_eq_false, zero_add, one_ne_zero, not_false_eq_true, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.one_lt_ofNat, List.getElem_cons_succ, List.getElem_cons_zero, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      hpredNonBridge M hM,
    guessBXOuterBlockElems_xB_take_count I b vs n p a hva hp]

/-- The number of `xB`-writes before position `nestedInnerStart ks P` is `P`. -/
theorem guessBXBlockWord_xB_write_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false)).length
      = P := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks00 : ks[0]'hks0pos = K0 := by
    have h := List.getElem?_eq_getElem (l := ks) hks0pos
    rw [hK0] at h; exact (Option.some.inj h).symm
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
       , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)) := by
    unfold guessBXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)
    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] := by
    rfl
  have hinnerflatlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
    rw [List.length_flatMap]
    have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
        inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [show P = 0 from by omega, show nestedInnerStart ks 0 = 1 from rfl]
      rfl
    · have hnstart : nestedInnerStart ks n = 3 * n := by
        have h := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
        rw [show n - 1 + 1 = n from by omega] at h
        omega
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have hva : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      have hcount := flatMap_uniform_take_count (guessBXInnerBlockElems I) 3 (fun _ => rfl)
        (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) 0
        (by norm_num)
        (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessBXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, Nat.right_eq_add, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.length_flatMap, gt_iff_lt, getElem?_eq_some_getElem_iff, ne_eq, not_true_eq_false, one_ne_zero, not_false_eq_true, Nat.one_lt_ofNat, List.getElem_cons_succ, List.getElem_cons_zero, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest (n - 1) (inner0Rest[n - 1]'hnm1lt) hva 0 (by norm_num)
      rw [if_neg (show ¬ (0 : ℕ) < 0 from by omega), Nat.add_zero, Nat.add_zero] at hcount
      rw [heq', hnstart, heq0, show 3 * n = 3 + (n - 1) * 3 from by omega,
        List.take_append_of_le_length (by
          rw [List.length_append, hleadlen, hinnerflatlen]; omega),
        List.take_append, hleadlen,
        show 3 + (n - 1) * 3 - 3 = (n - 1) * 3 from by omega,
        List.take_of_length_le (by rw [hleadlen]; omega),
        List.filter_append, List.length_append, hleadfilter, hcount]
      have hone : List.length
          [ (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ]
          = 1 := rfl
      omega
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      rwa [hgetD0] at hh
    have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n
        = (4 + K0 * 3 - 1) +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 0 + 1))) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff, heq0]
    have hfirstlen : (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
      rw [List.length_append, hleadlen, hinnerflatlen]; omega
    rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length from hfirstlen.symm,
      List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _),
      show (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 0 + 1))) -
          (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length =
          1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 0 + 1)) from by omega,
      List.filter_append, List.length_append]
    have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) =
        [ (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
          inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX)) := by
      rw [List.filter_append, hleadfilter]
      congr 1
      exact guessBXInnerBlockElems_filter I
        (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) 0
        (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessBXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.length_flatMap, gt_iff_lt, Nat.succ_add_sub_one, add_zero, ge_iff_le, List.map_take, ne_eq, not_true_eq_false, one_ne_zero, not_false_eq_true, Nat.one_lt_ofNat, List.getElem_cons_succ, List.getElem_cons_zero, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest
    rw [hleadinnerfilter, List.length_append, List.length_map]
    have hone : List.length
        [ (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ]
        = 1 := rfl
    rw [hone]
    have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.xB, OpType.wt => true | _, _ => false) = false := by
      intro b0 hb0
      have hz : b0.1.loc ≠ Loc.xB := by
        intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.xB ∉ BridgeLoc)
      split
      · exact absurd (by assumption) hz
      · rfl
    have hellalen : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length ≤
        1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 0 + 1)) := by simp
    have hellasub : (1 + (((outerRest.take (m - 1)).flatMap
          (fun q => guessBXOuterBlockElems I q.1 q.2)).length + (n * 3 + 0 + 1))) -
        ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX) ] :
          List (ThreadLabel (domainOf I) Tid.guessBX)).length =
        ((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 0 + 1) := by simp
    rw [show ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 0 + 1))) =
        [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        (outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
          (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 0 + 1)) from by
      rw [List.take_append, List.take_of_length_le hellalen, hellasub],
      List.filter_append]
    have hellafilter : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ]).filter
        (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) = [] :=
      rfl
    rw [hellafilter, List.nil_append, hinner0len]
    have houter' : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
        ks[j + 1]? = some km ∧ vs.length = km + 1 := houter
    have hcountOuter := guessBXOuterRest_xB_take_count I ks N hks outerRest houter'
      hpredNonBridge (m - 1) (by omega) b vs hbvs n 0 (vs[n]'hnvs) hva (by norm_num)
    rw [if_neg (show ¬ (0 : ℕ) < 0 from by omega)] at hcountOuter
    simp only [Nat.add_zero] at hcountOuter
    rw [hmeq] at hcountOuter
    rw [hcountOuter]
    have hksprefM : ksPrefix ks m - ksPrefix ks 1 = ksPrefix ks m - (K0 + 1) := by rw [hks1]
    have hksprefmono : ksPrefix ks 1 ≤ ksPrefix ks m := ksPrefix_mono ks (show (1:ℕ) ≤ m from by omega)
    omega

/-- For any inner-call index `P < ksPrefix ks (N + 1)`, the `zBx'x`-write of
call `P` is at position `nestedInnerStart ks P + 1` of `guessBXBlockWord`. -/
theorem guessBXBlockWord_zBx'x_write_nestedInnerPos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    ∃ val, (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · refine ⟨v2, ?_⟩
      rw [show P = 0 from by omega, show nestedInnerStart ks 0 = 1 from rfl]
      exact guessBXBlockWord_lead_zBx'x_write_pos I v1 v2 vB0 inner0Rest outerRest
    · have hks00 : ks[0]'hks0pos = K0 := by
        have h := List.getElem?_eq_getElem (l := ks) hks0pos
        rw [hK0] at h; exact (Option.some.inj h).symm
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      refine ⟨(inner0Rest[n - 1]'hnm1lt).2.1, ?_⟩
      have hpos := guessBXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 1
        (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
      have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
      rw [show n - 1 + 1 = n from by omega] at hns
      rw [heq', hns]
      have hoff : 3 + (n - 1) * 3 + 1 = 3 * n + 1 := by omega
      rwa [hoff] at hpos
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    refine ⟨(vs[n]'hnvs).2.1, ?_⟩
    have hpos := guessBXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 1 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 1
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff]
    exact hpos

/-- The `zBxx'`-read of call `P ≥ 1` is at position
`nestedInnerStart ks P + 2`. -/
theorem guessBXBlockWord_zBxx'_read_nestedInnerPos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P < ksPrefix ks (N + 1)) :
    ∃ val, (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    have hnpos : 0 < n := by omega
    have hks00 : ks[0]'hks0pos = K0 := by
      have h := List.getElem?_eq_getElem (l := ks) hks0pos
      rw [hK0] at h; exact (Option.some.inj h).symm
    have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
    have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
      List.getElem?_eq_getElem hnm1lt
    refine ⟨(inner0Rest[n - 1]'hnm1lt).2.2, ?_⟩
    have hpos := guessBXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 2
      (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
    have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
    rw [show n - 1 + 1 = n from by omega] at hns
    rw [heq', hns]
    have hoff : 3 + (n - 1) * 3 + 2 = 3 * n + 2 := by omega
    rwa [hoff] at hpos
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    refine ⟨(vs[n]'hnvs).2.2, ?_⟩
    have hpos := guessBXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 2 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 2
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff]
    exact hpos

/-! ## `zBxx'`/`zBx'x`: counts -/

/-- The number of `zBx'x`-writes within a possibly partial outer block. -/
theorem guessBXOuterBlockElems_zBx'x_take_count (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((guessBXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false)).length
      = n + (if 1 < p then 1 else 0) := by
  have hstep : ((guessBXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) =
      ((vs.flatMap (guessBXInnerBlockElems I)).take (n * 3 + p)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) := by
    unfold guessBXOuterBlockElems
    rw [List.take_succ_cons, List.filter_cons_of_neg (fun h => Bool.noConfusion h),
      List.take_append, List.filter_append]
    have hnil : (([⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).take
          (n * 3 + p - (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hxmem : x ∈ ([⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩] :
          List (ThreadLabel (domainOf I) Tid.guessBX)) := List.mem_of_mem_take hx
      simp only [List.mem_singleton] at hxmem
      subst hxmem
      exact fun h => Bool.noConfusion h
    rw [hnil, List.append_nil]
  rw [hstep]
  exact flatMap_uniform_take_count (guessBXInnerBlockElems I) 3 (fun _ => rfl)
    (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) 1
    (by norm_num)
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun _ => rfl) (fun _ => rfl)
    (fun a q b hq hqb => by
      unfold guessBXInnerBlockElems at hqb
      rcases q with _ | _ | _ | q <;> simp_all only [ne_eq, zero_ne_one, not_false_eq_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.some.injEq, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
    vs n a hva p hp

/-- The number of `zBx'x`-writes before an arbitrary position of `outerRest`'s
flatMap. -/
theorem guessBXOuterRest_zBx'x_take_count (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (hks : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (hpredNonBridge :
      ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) = false)
    (M : ℕ) (hM : M ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hMbv : outerRest[M]? = some (b, vs)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take M).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length +
          (n * 3 + p + 1))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false)).length
      = (ksPrefix ks (M + 1) - ksPrefix ks 1) + (n + (if 1 < p then 1 else 0)) := by
  have hqbound : n * 3 + p + 1 ≤ (guessBXOuterBlockElems I b vs).length := by
    have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
    rw [guessBXOuterBlockElems_length]
    omega
  rw [list_take_flatMap_offset (fun q => guessBXOuterBlockElems I q.1 q.2) outerRest M
    (n * 3 + p + 1) (b, vs) hMbv hqbound, List.filter_append, List.length_append,
    guessBXOuterRest_prefix_matchCount I ks N hks outerRest houter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) 1
      (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessBXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [add_lt_add_iff_right, getElem?_pos, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, Subtype.forall, ne_eq, zero_ne_one, not_false_eq_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, List.getElem_cons_zero, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      hpredNonBridge M hM,
    guessBXOuterBlockElems_zBx'x_take_count I b vs n p a hva hp]

/-- The number of `zBx'x`-writes before position `nestedInnerStart ks P + 1`
is `P`. -/
theorem guessBXBlockWord_zBx'x_write_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false)).length
      = P := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks00 : ks[0]'hks0pos = K0 := by
    have h := List.getElem?_eq_getElem (l := ks) hks0pos
    rw [hK0] at h; exact (Option.some.inj h).symm
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
       , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)) := by
    unfold guessBXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)
    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] := by
    rfl
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [show P = 0 from by omega, show nestedInnerStart ks 0 = 1 from rfl]
      rfl
    · have hnstart : nestedInnerStart ks n = 3 * n := by
        have h := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
        rw [show n - 1 + 1 = n from by omega] at h
        omega
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have hva : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      have hcount := flatMap_uniform_take_count (guessBXInnerBlockElems I) 3 (fun _ => rfl)
        (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) 1
        (by norm_num)
        (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessBXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, Nat.right_eq_add, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, gt_iff_lt, getElem?_eq_some_getElem_iff, ne_eq, zero_ne_one, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest (n - 1) (inner0Rest[n - 1]'hnm1lt) hva 1 (by norm_num)
      rw [if_neg (show ¬ (1 : ℕ) < 1 from by omega)] at hcount
      have hinnerflatlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
        rw [List.length_flatMap]
        have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
            inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
        rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
      rw [heq', hnstart, heq0, show 3 * n + 1 = 3 + ((n - 1) * 3 + 1) from by omega,
        List.take_append_of_le_length (by
          rw [List.length_append, hleadlen, hinnerflatlen]; omega),
        List.take_append, hleadlen,
        show 3 + ((n - 1) * 3 + 1) - 3 = (n - 1) * 3 + 1 from by omega,
        List.take_of_length_le (by rw [hleadlen]; omega),
        List.filter_append, List.length_append, hleadfilter, hcount]
      have hone : List.length
          [ (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ]
          = 1 := rfl
      omega
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      rwa [hgetD0] at hh
    have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 1
        = (4 + K0 * 3 - 1) +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 1 + 1))) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff, heq0]
    have hinnerflatlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
    have hfirstlen : (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
      rw [List.length_append, hleadlen, hinnerflatlen]; omega
    rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length from hfirstlen.symm,
      List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _),
      show (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 1 + 1))) -
          (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length =
          1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 1 + 1)) from by omega,
      List.filter_append, List.length_append]
    have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) =
        [ (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
          inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX)) := by
      rw [List.filter_append, hleadfilter]
      congr 1
      exact guessBXInnerBlockElems_filter I
        (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) 1
        (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessBXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, gt_iff_lt, ge_iff_le, List.length_flatMap, List.map_take, Nat.succ_add_sub_one, ne_eq, zero_ne_one, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest
    rw [hleadinnerfilter, List.length_append, List.length_map]
    have hone : List.length
        [ (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ]
        = 1 := rfl
    rw [hone]
    have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) = false := by
      intro b0 hb0
      have hz : b0.1.loc ≠ Loc.zBx'x := by
        intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.zBx'x ∉ BridgeLoc)
      split
      · exact absurd (by assumption) hz
      · rfl
    have hellalen : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length ≤
        1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1)) := by simp
    have hellasub : (1 + (((outerRest.take (m - 1)).flatMap
          (fun q => guessBXOuterBlockElems I q.1 q.2)).length + (n * 3 + 1 + 1))) -
        ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX) ] :
          List (ThreadLabel (domainOf I) Tid.guessBX)).length =
        ((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1) := by simp
    rw [show ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1))) =
        [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        (outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
          (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 1 + 1)) from by
      rw [List.take_append, List.take_of_length_le hellalen, hellasub],
      List.filter_append]
    have hellafilter : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ]).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) = [] :=
      rfl
    rw [hellafilter, List.length_append, List.length_nil]
    have houtercount := guessBXOuterRest_zBx'x_take_count I ks N hks outerRest houter
      hpredNonBridge (m - 1) (by omega) b vs hbvs n 1 (vs[n]'hnvs) hva (by norm_num)
    rw [if_neg (show ¬ (1 : ℕ) < 1 from by omega), hmeq] at houtercount
    rw [houtercount, hks1]
    have hksmono : ksPrefix ks 1 ≤ ksPrefix ks m := ksPrefix_mono ks (by omega)
    omega

/-- The number of `zBxx'`-reads before position `nestedInnerStart ks P + 2` is
`P - 1`, for `P ≥ 1`. -/
theorem guessBXBlockWord_zBxx'_read_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P < ksPrefix ks (N + 1)) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P + 2)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false)).length
      = P - 1 := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks00 : ks[0]'hks0pos = K0 := by
    have h := List.getElem?_eq_getElem (l := ks) hks0pos
    rw [hK0] at h; exact (Option.some.inj h).symm
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
       , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)) := by
    unfold guessBXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)
    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) = [] := by
    rfl
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    have hnpos : 0 < n := by omega
    have hnstart : nestedInnerStart ks n = 3 * n := by
      have h := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
      rw [show n - 1 + 1 = n from by omega] at h
      omega
    have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
    have hva : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
      List.getElem?_eq_getElem hnm1lt
    have hcount := flatMap_uniform_take_count (guessBXInnerBlockElems I) 3 (fun _ => rfl)
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) 2
      (by norm_num)
      (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessBXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, Nat.right_eq_add, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.filter_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true, forall_eq_or_imp, forall_eq, getElem?_eq_some_getElem_iff, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      inner0Rest (n - 1) (inner0Rest[n - 1]'hnm1lt) hva 2 (by norm_num)
    rw [if_neg (show ¬ (2 : ℕ) < 2 from by omega)] at hcount
    have hinnerflatlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
    rw [heq', hnstart, heq0, show 3 * n + 2 = 3 + ((n - 1) * 3 + 2) from by omega,
      List.take_append_of_le_length (by
        rw [List.length_append, hleadlen, hinnerflatlen]; omega),
      List.take_append, hleadlen,
      show 3 + ((n - 1) * 3 + 2) - 3 = (n - 1) * 3 + 2 from by omega,
      List.take_of_length_le (by rw [hleadlen]; omega),
      List.filter_append, List.length_append, hleadfilter, hcount]
    have hnil : ([] : List (ThreadLabel (domainOf I) Tid.guessBX)).length = 0 := rfl
    rw [hnil]
    omega
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      rwa [hgetD0] at hh
    have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 2
        = (4 + K0 * 3 - 1) +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 2 + 1))) := by
      rw [← hstart, hlen, hstartm]; omega
    rw [heq, hns, hoff, heq0]
    have hinnerflatlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
    have hfirstlen : (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
      rw [List.length_append, hleadlen, hinnerflatlen]; omega
    rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length from hfirstlen.symm,
      List.take_append,
      List.take_of_length_le (Nat.le_add_right _ _),
      show (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length +
          (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 2 + 1))) -
          (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I))).length =
          1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 2 + 1)) from by omega,
      List.filter_append, List.length_append]
    have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
        ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) =
        [] ++
          inner0Rest.map (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX)) := by
      rw [List.filter_append, hleadfilter]
      congr 1
      exact guessBXInnerBlockElems_filter I
        (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) 2
        (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX))
        (fun _ => rfl) (fun _ => rfl)
        (fun a q b hq hqb => by
          unfold guessBXInnerBlockElems at hqb
          rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, add_lt_add_iff_right, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.filter_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true, forall_eq_or_imp, forall_eq, gt_iff_lt, ge_iff_le, List.length_flatMap, List.map_take, Nat.succ_add_sub_one, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
        inner0Rest
    rw [hleadinnerfilter, List.length_append, List.length_nil, List.length_map]
    have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) = false := by
      intro b0 hb0
      have hz : b0.1.loc ≠ Loc.zBxx' := by
        intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.zBxx' ∉ BridgeLoc)
      split
      · exact absurd (by assumption) hz
      · rfl
    have hellalen : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length ≤
        1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1)) := by simp
    have hellasub : (1 + (((outerRest.take (m - 1)).flatMap
          (fun q => guessBXOuterBlockElems I q.1 q.2)).length + (n * 3 + 2 + 1))) -
        ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX) ] :
          List (ThreadLabel (domainOf I) Tid.guessBX)).length =
        ((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1) := by simp
    rw [show ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (1 + (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1))) =
        [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        (outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
          (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
            + (n * 3 + 2 + 1)) from by
      rw [List.take_append, List.take_of_length_le hellalen, hellasub],
      List.filter_append]
    have hellafilter : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ]).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) = [] :=
      rfl
    rw [hellafilter, List.length_append, List.length_nil]
    have houtercount := guessBXOuterRest_zBxx'_take_count I ks N hks outerRest houter
      hpredNonBridge (m - 1) (by omega) b vs hbvs n 2 (vs[n]'hnvs) hva (by norm_num)
    rw [if_neg (show ¬ (2 : ℕ) < 2 from by omega), hmeq] at houtercount
    -- Restate `houtercount` at the predicate written here, so that `rw`
    -- matches it.
    have houtercount2 : (((outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length +
          (n * 3 + 2 + 1))).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false)).length
        = ksPrefix ks m - ksPrefix ks 1 + (n + 0) := houtercount
    rw [houtercount2, hks1]
    have hksmono : ksPrefix ks 1 ≤ ksPrefix ks m := ksPrefix_mono ks (by omega)
    omega

/-! ## `zBxx'`/`zBx'x`: values -/

theorem guessBXBlockWord_zBx'x_write_val (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (hks : ks.length = N + 1)
    (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hv2 : v2 = Val.cnt (1 : Fin 4))
    (hinner0val : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4))
    (houterval : ∀ m, m < N → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix ks' m + n + 1) % 4, by omega⟩ : Fin 4))
    (P : ℕ) (hP : P < ksPrefix ks (N + 1)) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt (⟨(P + 1) % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    obtain rfl : n = P := heq'.symm
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · obtain rfl : n = 0 := hn0
      have hfinEq : (1 : Fin 4) = (⟨(0 + 1) % 4, by omega⟩ : Fin 4) := Fin.ext (by simp)
      have hns0 : nestedInnerStart ks 0 = 1 := rfl
      have hbase := guessBXBlockWord_lead_zBx'x_write_pos I v1 v2 vB0 inner0Rest outerRest
      have hv2full : v2 = Val.cnt (⟨(0 + 1) % 4, by omega⟩ : Fin 4) :=
        hv2.trans (congrArg Val.cnt hfinEq)
      have hgoal := hbase.trans (congrArg (fun x => some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x x,
        rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)) hv2full)
      rw [hns0]
      exact hgoal
    · have hks00 : ks[0]'hks0pos = K0 := by
        have h := List.getElem?_eq_getElem (l := ks) hks0pos
        rw [hK0] at h; exact (Option.some.inj h).symm
      have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
      have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
        List.getElem?_eq_getElem hnm1lt
      obtain ⟨e, hae, heval⟩ := hinner0val (n - 1) hnm1lt
      rw [ha] at hae
      have heval' := (Option.some.inj hae) ▸ heval
      have hfinEq : (⟨(1 + (n - 1) + 1) % 4, by omega⟩ : Fin 4) =
          (⟨(n + 1) % 4, by omega⟩ : Fin 4) := Fin.ext (by simp; omega)
      have hpos := guessBXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 1
        (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
      have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
      rw [show n - 1 + 1 = n from by omega] at hns
      have hlab : (guessBXInnerBlockElems I (inner0Rest[n - 1]'hnm1lt))[1]? =
          some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt (⟨(n + 1) % 4, by omega⟩ : Fin 4)),
            rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) := by
        have hlab0 : (guessBXInnerBlockElems I (inner0Rest[n - 1]'hnm1lt))[1]? =
            some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x (inner0Rest[n - 1]'hnm1lt).2.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX) := rfl
        rw [hlab0, heval']
        exact congrArg (fun x => some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt x), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX)) hfinEq
      have hoff : 3 + (n - 1) * 3 + 1 = 3 * n + 1 := by omega
      rw [hoff] at hpos
      rw [hns, hpos, hlab]
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    obtain ⟨b', vs', hbvs', hvalfn⟩ := houterval (m - 1) hjm1
    rw [hbvs] at hbvs'
    have hbveq : (b, vs) = (b', vs') := Option.some.inj hbvs'
    have hvs'eq : vs = vs' := (Prod.mk.injEq _ _ _ _).mp hbveq |>.2
    have hvalfn' := hvs'eq ▸ hvalfn
    obtain ⟨e, hae, heval⟩ := hvalfn' n hnvs
    rw [hva] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hpos := guessBXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 1 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 1
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 1 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    have hksrel_cons : ksPrefix ks m = (K0 + 1) + ksPrefix ks' (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [hksrel, ksPrefix_cons]
    have hPeq : P = ksPrefix ks m + n := heq
    have hNatEq : 1 + K0 + ksPrefix ks' (m - 1) + n + 1 = P + 1 := by omega
    have hfinEq : (⟨(1 + K0 + ksPrefix ks' (m - 1) + n + 1) % 4, by omega⟩ : Fin 4) =
        (⟨(P + 1) % 4, by omega⟩ : Fin 4) := Fin.ext (congrArg (· % 4) hNatEq)
    have hlab : (guessBXInnerBlockElems I (vs[n]'hnvs))[1]? =
        some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt (⟨(P + 1) % 4, by omega⟩ : Fin 4)),
          rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) := by
      have hlab0 : (guessBXInnerBlockElems I (vs[n]'hnvs))[1]? =
          some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x (vs[n]'hnvs).2.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX) := rfl
      rw [hlab0, heval']
      exact congrArg (fun x => some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt x), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX)) hfinEq
    have hLHSeq : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
        (guessBXInnerBlockElems I (vs[n]'hnvs))[1]? := by
      rw [heq, hns, hoff]; exact hpos
    exact hLHSeq.trans hlab

/-- The value of the `zBxx'`-read of call `P ≥ 1`. -/
theorem guessBXBlockWord_zBxx'_read_val (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (hks : ks.length = N + 1)
    (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hinner0val : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4))
    (houterval : ∀ m, m < N → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix ks' m + n) % 4, by omega⟩ : Fin 4))
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P < ksPrefix ks (N + 1)) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' (Val.cnt (⟨P % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  obtain ⟨m, hmlt, km, n, hkm, hnlt, heq⟩ := ksPrefix_invert ks P (by rw [hks]; exact hP)
  have hks0pos : 0 < ks.length := by omega
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have heq' : P = n := by simp only [hm0, ksPrefix] at heq; omega
    have hkm0 : km = K0 := by rw [hm0, hK0] at hkm; exact (Option.some.inj hkm).symm
    rw [hkm0] at hnlt
    have hnpos : 0 < n := by omega
    obtain rfl : n = P := heq'.symm
    have hks00 : ks[0]'hks0pos = K0 := by
      have h := List.getElem?_eq_getElem (l := ks) hks0pos
      rw [hK0] at h; exact (Option.some.inj h).symm
    have hnm1lt : n - 1 < inner0Rest.length := by rw [hinner0len]; omega
    have ha : inner0Rest[n - 1]? = some (inner0Rest[n - 1]'hnm1lt) :=
      List.getElem?_eq_getElem hnm1lt
    obtain ⟨e, hae, heval⟩ := hinner0val (n - 1) hnm1lt
    rw [ha] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hfinEq : (⟨(1 + (n - 1)) % 4, by omega⟩ : Fin 4) = (⟨n % 4, by omega⟩ : Fin 4) :=
      Fin.ext (by simp; omega)
    have hpos := guessBXBlockWord_inner0Rest_pos I v1 v2 vB0 inner0Rest outerRest (n - 1) 2
      (inner0Rest[n - 1]'hnm1lt) ha (by norm_num)
    have hns := nestedInnerStart_inner0Rest ks hks0pos (n - 1) (by rw [hks00]; omega)
    rw [show n - 1 + 1 = n from by omega] at hns
    have hlab : (guessBXInnerBlockElems I (inner0Rest[n - 1]'hnm1lt))[2]? =
        some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' (Val.cnt (⟨n % 4, by omega⟩ : Fin 4)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX) := by
      have hlab0 : (guessBXInnerBlockElems I (inner0Rest[n - 1]'hnm1lt))[2]? =
          some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' (inner0Rest[n - 1]'hnm1lt).2.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX) := rfl
      rw [hlab0, heval']
      exact congrArg (fun x => some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' (Val.cnt x), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX)) hfinEq
    have hoff : 3 + (n - 1) * 3 + 2 = 3 * n + 2 := by omega
    rw [hoff] at hpos
    rw [hns, hpos, hlab]
  · have hjm1 : m - 1 < N := by omega
    obtain ⟨b, vs, km', hbvs, hksm, hvslen⟩ := houter (m - 1) hjm1
    have hmeq : m - 1 + 1 = m := by omega
    have hksm_dep : ks[m - 1 + 1]'(by omega) = km' := by
      have h := List.getElem?_eq_getElem (l := ks) (i := m - 1 + 1) (by omega)
      rw [hksm] at h; exact (Option.some.inj h).symm
    have hkmeq : km' = km := by rw [hmeq] at hksm; rw [hksm] at hkm; exact Option.some.inj hkm
    rw [hkmeq] at hvslen hksm_dep
    have hnvs : n < vs.length := by rw [hvslen]; omega
    have hva : vs[n]? = some (vs[n]'hnvs) := List.getElem?_eq_getElem hnvs
    obtain ⟨b', vs', hbvs', hvalfn⟩ := houterval (m - 1) hjm1
    rw [hbvs] at hbvs'
    have hbveq : (b, vs) = (b', vs') := Option.some.inj hbvs'
    have hvs'eq : vs = vs' := (Prod.mk.injEq _ _ _ _).mp hbveq |>.2
    have hvalfn' := hvs'eq ▸ hvalfn
    obtain ⟨e, hae, heval⟩ := hvalfn' n hnvs
    rw [hva] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hpos := guessBXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
      (m - 1) n 2 b vs hbvs (vs[n]'hnvs) hva (by norm_num)
    have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m - 1) (by omega)
    rw [hmeq] at hlen
    have hstart := nestedOuterStart_succ_eq_innerStart ks N m hks (by omega)
    have hns := nestedInnerStart_outerRest_add ks (m - 1) (by omega) n (by rw [hksm_dep]; omega)
    rw [hmeq] at hns
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N m ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m - 1)
      rw [hmeq] at hh
      have hgetD : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD] at hh
    have hoff : nestedInnerStart ks (ksPrefix ks m) + 3 * n + 2
        = 4 + K0 * 3 +
          ((outerRest.take (m - 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (n * 3 + 2 + 1) := by
      rw [← hstart, hlen, hstartm]; omega
    have hksrel_cons : ksPrefix ks m = (K0 + 1) + ksPrefix ks' (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [hksrel, ksPrefix_cons]
    have hPeq : P = ksPrefix ks m + n := heq
    have hNatEq : 1 + K0 + ksPrefix ks' (m - 1) + n = P := by omega
    have hfinEq : (⟨(1 + K0 + ksPrefix ks' (m - 1) + n) % 4, by omega⟩ : Fin 4) =
        (⟨P % 4, by omega⟩ : Fin 4) := Fin.ext (congrArg (· % 4) hNatEq)
    have hlab : (guessBXInnerBlockElems I (vs[n]'hnvs))[2]? =
        some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' (Val.cnt (⟨P % 4, by omega⟩ : Fin 4)),
          rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) := by
      have hlab0 : (guessBXInnerBlockElems I (vs[n]'hnvs))[2]? =
          some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' (vs[n]'hnvs).2.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX) := rfl
      rw [hlab0, heval']
      exact congrArg (fun x => some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' (Val.cnt x), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX)) hfinEq
    have hLHSeq : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
        (guessBXInnerBlockElems I (vs[n]'hnvs))[2]? := by
      rw [heq, hns, hoff]; exact hpos
    exact hLHSeq.trans hlab

/-! ## `PrimeBX`: values, positions, counts

`primeBXBlockElems I l = [wt xB' (primeTag primeBX 0), wt zBxx' l, rd zBx'x l]`. -/

/-- `primeBX`'s `zBxx'`-write value at filtered position `j` is `vals[j]`. -/
theorem primeBXBlockWord_zBxx'_write_val (I : PCPInstance) (vals : List (Val I)) (j : ℕ) :
    ((primeBXBlockWord I vals).filter (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.wt))[j]? =
      (vals[j]?).map (fun v => (⟨EventLabel.wt Tid.primeBX Loc.zBxx' v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeBX)) := by
  have hone : ∀ v : Val I, (primeBXBlockElems I v).filter
      (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeBX Loc.zBxx' v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeBX)] := by
    intro v
    unfold primeBXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeBXBlockWord I vals).filter (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.wt) =
      vals.map (fun v => (⟨EventLabel.wt Tid.primeBX Loc.zBxx' v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeBX)) := by
    rw [primeBXBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ vals
  rw [hflat]
  exact List.getElem?_map ..

/-- `primeBX`'s `zBx'x`-read value at filtered position `j` is `vals[j]`. -/
theorem primeBXBlockWord_zBx'x_read_val (I : PCPInstance) (vals : List (Val I)) (j : ℕ) :
    ((primeBXBlockWord I vals).filter (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.rd))[j]? =
      (vals[j]?).map (fun v => (⟨EventLabel.rd Tid.primeBX Loc.zBx'x v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeBX)) := by
  have hone : ∀ v : Val I, (primeBXBlockElems I v).filter
      (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeBX Loc.zBx'x v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeBX)] := by
    intro v
    unfold primeBXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeBXBlockWord I vals).filter (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.rd) =
      vals.map (fun v => (⟨EventLabel.rd Tid.primeBX Loc.zBx'x v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeBX)) := by
    rw [primeBXBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ vals
  rw [hflat]
  exact List.getElem?_map ..

/-- The `match`-based filter of `guessBXBlockWord_zBx'x_write_take_count`
equals the `∧`-predicate filter. By list induction. -/
theorem guessBX_zBx'x_write_filter_eq {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.guessBX)) :
    w.filter (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.wt) =
    w.filter (fun l => match l.1.loc, l.1.op with
      | Loc.zBx'x, OpType.wt => true | _, _ => false) := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

/-- The `zBxx'`-read counterpart of `guessBX_zBx'x_write_filter_eq`. -/
theorem guessBX_zBxx'_read_filter_eq {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.guessBX)) :
    w.filter (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.rd) =
    w.filter (fun l => match l.1.loc, l.1.op with
      | Loc.zBxx', OpType.rd => true | _, _ => false) := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

/-- The `zBx'x`-write of the terminating outer iteration. -/
theorem guessBXBlockWord_zBx'x_write_terminator_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks (ksPrefix ks (N + 1)) +
      1]? = some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hpos := guessBXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
    N 0 1 b vs hbvs a hva (by norm_num)
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1)) + 1
      = 4 + K0 * 3 + ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 1 + 1) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff]; exact hpos

/-- The count for `guessBXBlockWord_zBx'x_write_terminator_pos`. -/
theorem guessBXBlockWord_zBx'x_write_terminator_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks (ksPrefix ks (N + 1)) + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false)).length
      = ksPrefix ks (N + 1) := by
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
       , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)) := by
    unfold guessBXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)
    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] := by
    rfl
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1)) + 1
      = (4 + K0 * 3 - 1) +
        (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 1 + 1))) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff, heq0]
  have hinnerflatlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
    rw [List.length_flatMap]
    have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
        inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
  have hfirstlen : (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
    rw [List.length_append, hleadlen, hinnerflatlen]; omega
  rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length from hfirstlen.symm,
    List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _),
    show (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length +
        (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 1 + 1))) -
        (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length =
        1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 1 + 1)) from by omega,
    List.filter_append, List.length_append]
  have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX)) := by
    rw [List.filter_append, hleadfilter]
    congr 1
    exact guessBXInnerBlockElems_filter I
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) 1
      (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessBXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, Option.some.injEq, add_lt_add_iff_right, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, ge_iff_le, List.length_flatMap, List.map_take, Nat.succ_add_sub_one, zero_mul, ne_eq, zero_ne_one, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, not_true_eq_false, OfNat.ofNat_ne_one, Nat.lt_add_one, List.getElem_cons_succ, Nat.add_eq_right, Nat.add_eq_zero_iff, one_ne_zero, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      inner0Rest
  rw [hleadinnerfilter, List.length_append, List.length_map]
  have hone : List.length
      [ (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ]
      = 1 := rfl
  rw [hone]
  have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
      (match b0.1.loc, b0.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) = false := by
    intro b0 hb0
    have hz : b0.1.loc ≠ Loc.zBx'x := by
      intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.zBx'x ∉ BridgeLoc)
    split
    · exact absurd (by assumption) hz
    · rfl
  have hellalen : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ] :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length ≤
      1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 1 + 1)) := by simp
  have hellasub : (1 + (((outerRest.take N).flatMap
        (fun q => guessBXOuterBlockElems I q.1 q.2)).length + (0 * 3 + 1 + 1))) -
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length =
      ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 1 + 1) := by simp
  rw [show ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ] ++
      outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
      (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 1 + 1))) =
      [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
      (outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 1 + 1)) from by
    rw [List.take_append, List.take_of_length_le hellalen, hellasub],
    List.filter_append]
  have hellafilter : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false) = [] :=
    rfl
  rw [hellafilter, List.length_append, List.length_nil]
  have houtercount := guessBXOuterRest_zBx'x_take_count I ks N hks outerRest houter
    hpredNonBridge N (le_refl N) b vs hbvs 0 1 a hva (by norm_num)
  rw [if_neg (show ¬ (1 : ℕ) < 1 from by omega)] at houtercount
  rw [houtercount, hks1]
  have hksmono : ksPrefix ks 1 ≤ ksPrefix ks (N + 1) := ksPrefix_mono ks (by omega)
  omega

/-- The count for `guessBXBlockWord_xB_write_terminator_pos`. -/
theorem guessBXBlockWord_xB_write_terminator_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks (ksPrefix ks (N + 1)))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false)).length
      = ksPrefix ks (N + 1) := by
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
       , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)) := by
    unfold guessBXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)
    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] := by
    rfl
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).length = 3 := rfl
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1))
      = (4 + K0 * 3 - 1) +
        (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 0 + 1))) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff, heq0]
  have hinnerflatlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
    rw [List.length_flatMap]
    have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
        inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
  have hfirstlen : (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
    rw [List.length_append, hleadlen, hinnerflatlen]; omega
  rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length from hfirstlen.symm,
    List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _),
    show (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length +
        (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 0 + 1))) -
        (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length =
        1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 0 + 1)) from by omega,
    List.filter_append, List.length_append]
  have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) =
      [ (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX)) := by
    rw [List.filter_append, hleadfilter]
    congr 1
    exact guessBXInnerBlockElems_filter I
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) 0
      (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessBXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, Option.some.injEq, add_lt_add_iff_right, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.succ_add_sub_one, zero_mul, add_zero, ge_iff_le, List.length_flatMap, List.map_take, ne_eq, not_true_eq_false, one_ne_zero, not_false_eq_true, Nat.one_lt_ofNat, List.getElem_cons_succ, List.getElem_cons_zero, OfNat.ofNat_ne_zero, Nat.lt_add_one, Nat.add_eq_zero_iff, and_false, and_self, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      inner0Rest
  rw [hleadinnerfilter, List.length_append, List.length_map]
  have hone : List.length
      [ (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ]
      = 1 := rfl
  rw [hone]
  have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
      (match b0.1.loc, b0.1.op with | Loc.xB, OpType.wt => true | _, _ => false) = false := by
    intro b0 hb0
    have hz : b0.1.loc ≠ Loc.xB := by
      intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.xB ∉ BridgeLoc)
    split
    · exact absurd (by assumption) hz
    · rfl
  have hellalen : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ] :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length ≤
      1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 0 + 1)) := by simp
  have hellasub : (1 + (((outerRest.take N).flatMap
        (fun q => guessBXOuterBlockElems I q.1 q.2)).length + (0 * 3 + 0 + 1))) -
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length =
      ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 0 + 1) := by simp
  rw [show ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ] ++
      outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
      (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 0 + 1))) =
      [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
      (outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 0 + 1)) from by
    rw [List.take_append, List.take_of_length_le hellalen, hellasub],
    List.filter_append]
  have hellafilter : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false) = [] :=
    rfl
  rw [hellafilter, List.length_append, List.length_nil]
  have houtercount := guessBXOuterRest_xB_take_count I ks N hks outerRest houter
    hpredNonBridge N (le_refl N) b vs hbvs 0 0 a hva (by norm_num)
  rw [if_neg (show ¬ (0 : ℕ) < 0 from by omega)] at houtercount
  rw [houtercount, hks1]
  have hksmono : ksPrefix ks 1 ≤ ksPrefix ks (N + 1) := ksPrefix_mono ks (by omega)
  omega

/-- The number of `xB`-writes before position `nestedInnerStart ks P` is `P`,
for `P ≤ ksPrefix ks (N + 1)`. -/
theorem guessBXBlockWord_xB_write_take_count_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false)).length
      = P := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessBXBlockWord_xB_write_take_count I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    rw [heq]
    exact guessBXBlockWord_xB_write_terminator_take_count I v1 v2 vB0 K0 inner0Rest outerRest ks N
      hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva

/-- The value for `guessBXBlockWord_zBx'x_write_terminator_pos`. -/
theorem guessBXBlockWord_zBx'x_write_terminator_val (I : PCPInstance) (_ _ : Val I)
    (_ : Val I × Val I) (K0 : ℕ) (_ : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (_ : ks.length = N + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (_ : outerRest[N]? = some (b, vs)) (_ : vs.length = 1)
    (a : Val I × Val I × Val I) (_ : vs[0]? = some a)
    (haval : a.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix ks' N + 0 + 1) % 4, by omega⟩ : Fin 4)) :
    a.2.1 = Val.cnt (⟨(ksPrefix ks (N + 1) + 1) % 4, by omega⟩ : Fin 4) := by
  have hcons : ksPrefix ks (N + 1) = (K0 + 1) + ksPrefix ks' N := by
    rw [hksrel, ksPrefix_cons]
  have hvaleq : (1 + K0 + ksPrefix ks' N + 0 + 1) % 4 = (ksPrefix ks (N + 1) + 1) % 4 := by
    rw [hcons]; omega
  have hfinEq : (⟨(1 + K0 + ksPrefix ks' N + 0 + 1) % 4, by omega⟩ : Fin 4) =
      (⟨(ksPrefix ks (N + 1) + 1) % 4, by omega⟩ : Fin 4) := Fin.ext hvaleq
  rw [haval]; exact congrArg Val.cnt hfinEq

/-- The `zBxx'`-read of the terminating outer iteration. -/
theorem guessBXBlockWord_zBxx'_read_terminator_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks (ksPrefix ks (N + 1)) +
      2]? = some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hpos := guessBXBlockWord_outerRest_pos I v1 v2 vB0 K0 inner0Rest outerRest hinner0len
    N 0 2 b vs hbvs a hva (by norm_num)
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1)) + 2
      = 4 + K0 * 3 + ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 2 + 1) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff]; exact hpos

/-- The count for `guessBXBlockWord_zBxx'_read_terminator_pos`. -/
theorem guessBXBlockWord_zBxx'_read_terminator_take_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1)
    (a : Val I × Val I × Val I) (hva : vs[0]? = some a) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks (ksPrefix ks (N + 1)) + 2)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false)).length
      = ksPrefix ks (N + 1) - 1 := by
  have hks0pos : 0 < ks.length := by omega
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hks1 : ksPrefix ks 1 = K0 + 1 := by
    show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
    rw [hgetD0, show ksPrefix ks 0 = 0 from rfl]; omega
  have heq0 : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
       , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
       , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)) ++
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
        outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)) := by
    unfold guessBXBlockWord
    rw [List.append_assoc, List.append_assoc]
  have hleadlen : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).length = 3 := rfl
  have hleadfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)
    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) = [] := by
    rfl
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  have hlen := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    (⟨b, vs, hbvs, hvslen⟩) N (by omega)
  have hoff : nestedInnerStart ks (ksPrefix ks (N + 1)) + 2
      = (4 + K0 * 3 - 1) +
        (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 2 + 1))) := by
    rw [← hstart, hlen, hstartm]; omega
  rw [hoff, heq0]
  have hinnerflatlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
    rw [List.length_flatMap]
    have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
        inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, hinner0len, Nat.mul_comm]
  have hfirstlen : (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length = 4 + K0 * 3 - 1 := by
    rw [List.length_append, hleadlen, hinnerflatlen]; omega
  rw [show (4 + K0 * 3 - 1 : ℕ) = (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length from hfirstlen.symm,
    List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _),
    show (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length +
        (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 2 + 1))) -
        (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I))).length =
        1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 2 + 1)) from by omega,
    List.filter_append, List.length_append]
  have hleadinnerfilter : ([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX), ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩,
      ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) =
      [] ++
        inner0Rest.map (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX)) := by
    rw [List.filter_append, hleadfilter]
    congr 1
    exact guessBXInnerBlockElems_filter I
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) 2
      (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessBXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, Option.some.injEq, add_lt_add_iff_right, exists_and_left, ↓existsAndEq, true_and, Prod.exists, lt_add_iff_pos_right, List.getD_eq_getElem?_getD, Option.getD_some, List.cons_append, List.nil_append, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, List.filter_eq_nil_iff, List.mem_cons, List.not_mem_nil, or_false, Bool.not_eq_true, forall_eq_or_imp, forall_eq, ge_iff_le, List.length_flatMap, List.map_take, Nat.succ_add_sub_one, zero_mul, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, Nat.ofNat_pos, List.getElem_cons_zero, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      inner0Rest
  rw [hleadinnerfilter, List.length_append, List.length_nil, List.length_map]
  have hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
      (match b0.1.loc, b0.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) = false := by
    intro b0 hb0
    have hz : b0.1.loc ≠ Loc.zBxx' := by
      intro h; rw [h] at hb0; exact absurd hb0 (by decide : Loc.zBxx' ∉ BridgeLoc)
    split
    · exact absurd (by assumption) hz
    · rfl
  have hellalen : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ] :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length ≤
      1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 2 + 1)) := by simp
  have hellasub : (1 + (((outerRest.take N).flatMap
        (fun q => guessBXOuterBlockElems I q.1 q.2)).length + (0 * 3 + 2 + 1))) -
      ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) ] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length =
      ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 2 + 1) := by simp
  rw [show ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ] ++
      outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
      (1 + (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (0 * 3 + 2 + 1))) =
      [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) ] ++
      (outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
          + (0 * 3 + 2 + 1)) from by
    rw [List.take_append, List.take_of_length_le hellalen, hellasub],
    List.filter_append]
  have hellafilter : ([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) ]).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) = [] :=
    rfl
  rw [hellafilter, List.length_append, List.length_nil]
  have houtercount := guessBXOuterRest_zBxx'_take_count I ks N hks outerRest houter
    hpredNonBridge N (le_refl N) b vs hbvs 0 2 a hva (by norm_num)
  rw [if_neg (show ¬ (2 : ℕ) < 2 from by omega)] at houtercount
  have houtercount2 : (((outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
      (((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length +
        (0 * 3 + 2 + 1))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false)).length
      = ksPrefix ks (N + 1) - ksPrefix ks 1 + (0 + 0) := houtercount
  rw [houtercount2, hks1]
  have hksmono : ksPrefix ks 1 ≤ ksPrefix ks (N + 1) := ksPrefix_mono ks (by omega)
  omega

/-- The value for `guessBXBlockWord_zBxx'_read_terminator_pos`. -/
theorem guessBXBlockWord_zBxx'_read_terminator_val (I : PCPInstance) (_ _ : Val I)
    (_ : Val I × Val I) (K0 : ℕ) (_ : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (_ : ks.length = N + 1)
    (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (_ : outerRest[N]? = some (b, vs)) (_ : vs.length = 1)
    (a : Val I × Val I × Val I) (_ : vs[0]? = some a)
    (haval : a.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix ks' N + 0) % 4, by omega⟩ : Fin 4)) :
    a.2.2 = Val.cnt (⟨(ksPrefix ks (N + 1)) % 4, by omega⟩ : Fin 4) := by
  have hcons : ksPrefix ks (N + 1) = (K0 + 1) + ksPrefix ks' N := by
    rw [hksrel, ksPrefix_cons]
  have hvaleq : (1 + K0 + ksPrefix ks' N + 0) % 4 = (ksPrefix ks (N + 1)) % 4 := by
    rw [hcons]; omega
  have hfinEq : (⟨(1 + K0 + ksPrefix ks' N + 0) % 4, by omega⟩ : Fin 4) =
      (⟨(ksPrefix ks (N + 1)) % 4, by omega⟩ : Fin 4) := Fin.ext hvaleq
  rw [haval]; exact congrArg Val.cnt hfinEq

/-- The `zBx'x`-write of call `P` is at position `nestedInnerStart ks P + 1`,
for `P ≤ ksPrefix ks (N + 1)`. -/
theorem guessBXBlockWord_zBx'x_write_pos_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    ∃ val, (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessBXBlockWord_zBx'x_write_nestedInnerPos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    refine ⟨a.2.1, ?_⟩
    rw [heq]
    exact guessBXBlockWord_zBx'x_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter b vs hbvs hvslen a hva

/-- The `zBxx'`-read of call `P` is at position `nestedInnerStart ks P + 2`,
for `1 ≤ P ≤ ksPrefix ks (N + 1)`. -/
theorem guessBXBlockWord_zBxx'_read_pos_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P ≤ ksPrefix ks (N + 1)) :
    ∃ val, (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' val, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessBXBlockWord_zBxx'_read_nestedInnerPos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hP1 hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    refine ⟨a.2.2, ?_⟩
    rw [heq]
    exact guessBXBlockWord_zBxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter b vs hbvs hvslen a hva

/-- The number of `zBx'x`-writes before position `nestedInnerStart ks P + 1`
is `P`, for `P ≤ ksPrefix ks (N + 1)`. -/
theorem guessBXBlockWord_zBx'x_write_take_count_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false)).length
      = P := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessBXBlockWord_zBx'x_write_take_count I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    have h := guessBXBlockWord_zBx'x_write_terminator_take_count I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
    rw [heq]; exact h

/-- The number of `zBxx'`-reads before position `nestedInnerStart ks P + 2` is
`P - 1`, for `1 ≤ P ≤ ksPrefix ks (N + 1)`. -/
theorem guessBXBlockWord_zBxx'_read_take_count_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P ≤ ksPrefix ks (N + 1)) :
    (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedInnerStart ks P + 2)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false)).length
      = P - 1 := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessBXBlockWord_zBxx'_read_take_count I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
      hK0 hinner0len houterLen houter houterLast P hP1 hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    have h := guessBXBlockWord_zBxx'_read_terminator_take_count I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
    rw [heq]; exact h

/-- The value of the `zBx'x`-write of call `P`, for
`P ≤ ksPrefix ks (N + 1)`. -/
theorem guessBXBlockWord_zBx'x_write_val_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (hks : ks.length = N + 1)
    (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hv2 : v2 = Val.cnt (1 : Fin 4))
    (hinner0val : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4))
    (houterval : ∀ m, m < N + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix ks' m + n + 1) % 4, by omega⟩ : Fin 4))
    (P : ℕ) (hP : P ≤ ksPrefix ks (N + 1)) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 1]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x (Val.cnt (⟨(P + 1) % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessBXBlockWord_zBx'x_write_val I v1 v2 vB0 K0 inner0Rest outerRest ks ks' N hksrel hks
      hK0 hinner0len houterLen houter houterLast hv2 hinner0val
      (fun m hm => houterval m (by omega)) P hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    obtain ⟨b', vs', hbvs', hval⟩ := houterval N (by omega)
    have hbeq : vs' = vs := congrArg Prod.snd (Option.some.inj (hbvs'.symm.trans hbvs))
    rw [hbeq] at hval
    obtain ⟨e, hae, heval⟩ := hval 0 h0
    rw [hva] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hval2 := guessBXBlockWord_zBx'x_write_terminator_val I v1 v2 vB0 K0 inner0Rest outerRest
      ks ks' N hksrel hks b vs hbvs hvslen a hva heval'
    have hpos := guessBXBlockWord_zBx'x_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
    rw [heq, hpos, hval2]

/-- The value of the `zBxx'`-read of call `P`, for
`1 ≤ P ≤ ksPrefix ks (N + 1)`. -/
theorem guessBXBlockWord_zBxx'_read_val_full (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks ks' : List ℕ) (N : ℕ) (hksrel : ks = K0 :: ks') (hks : ks.length = N + 1)
    (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hinner0val : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4))
    (houterval : ∀ m, m < N + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix ks' m + n) % 4, by omega⟩ : Fin 4))
    (P : ℕ) (hP1 : 1 ≤ P) (hP : P ≤ ksPrefix ks (N + 1)) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedInnerStart ks P + 2]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' (Val.cnt (⟨P % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  rcases hP.lt_or_eq with hlt | heq
  · exact guessBXBlockWord_zBxx'_read_val I v1 v2 vB0 K0 inner0Rest outerRest ks ks' N hksrel hks
      hK0 hinner0len houterLen houter houterLast hinner0val
      (fun m hm => houterval m (by omega)) P hP1 hlt
  · obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
    have h0 : (0 : ℕ) < vs.length := by omega
    obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'h0, List.getElem?_eq_getElem h0⟩
    obtain ⟨b', vs', hbvs', hval⟩ := houterval N (by omega)
    have hbeq : vs' = vs := congrArg Prod.snd (Option.some.inj (hbvs'.symm.trans hbvs))
    rw [hbeq] at hval
    obtain ⟨e, hae, heval⟩ := hval 0 h0
    rw [hva] at hae
    have heval' := (Option.some.inj hae) ▸ heval
    have hval2 := guessBXBlockWord_zBxx'_read_terminator_val I v1 v2 vB0 K0 inner0Rest outerRest
      ks ks' N hksrel hks b vs hbvs hvslen a hva heval'
    have hpos := guessBXBlockWord_zBxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
    rw [heq, hpos, hval2]

/-- The length of `guessBXBlockWord`:
`nestedInnerStart ks (ksPrefix ks (N + 1)) + 4`. -/
theorem guessBXBlockWord_length (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length =
      nestedInnerStart ks (ksPrefix ks (N + 1)) + 4 := by
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
      , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
      , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
      inner0Rest.flatMap (guessBXInnerBlockElems I)) ++
      [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ] :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hwhole : outerRest.take (N + 1) = outerRest := by
    rw [← houterLen, List.take_length]
  have hlenAll := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
    houterLast (N + 1) (by omega)
  rw [hwhole] at hlenAll
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hstartlast : nestedOuterStart ks N (N + 1 + 1) = nestedOuterStart ks N (N + 1) + 5 := by
    rw [nestedOuterStart_succ]
    congr 1
    unfold nestedOuterLen
    rw [if_pos rfl]
  have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
  have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
  have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N N
    rwa [hgetD0] at hh
  unfold guessBXBlockWord
  rw [List.length_append, hleadlen, hlenAll]
  omega

/-- The position of the final `ellByx`-read of `guessBXBlockWord`. -/
theorem guessBXBlockWord_ellByx_terminator_pos (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (N : ℕ) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hbvs : outerRest[N]? = some (b, vs)) (hvslen : vs.length = 1) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[4 + K0 * 3 +
      ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length + 4]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) := by
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  rw [heq, List.getElem?_append_right (by rw [hleadlen]; omega), hleadlen,
    show 4 + K0 * 3 + ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
      + 4 - (4 + K0 * 3) = ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
      + 4 from by omega]
  have hqlt : (4 : ℕ) < (guessBXOuterBlockElems I b vs).length := by
    rw [guessBXOuterBlockElems_length, hvslen]; omega
  have hstep := list_take_flatMap_offset_getElem (fun q => guessBXOuterBlockElems I q.1 q.2)
    outerRest N 4 (b, vs) hbvs hqlt
  rw [hstep, vs.eq_getElem_of_length_eq_one hvslen]
  rfl

/-- `guessBXBlockWord` contains `ksPrefix ks (N + 1) + 1` `zBx'x`-writes. -/
theorem guessBXBlockWord_zBx'x_write_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBx'x, OpType.wt => true | _, _ => false)).length
      = ksPrefix ks (N + 1) + 1 := by
  obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
  have ha0 : (0 : ℕ) < vs.length := by omega
  obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'ha0, List.getElem?_eq_getElem ha0⟩
  have hlen := guessBXBlockWord_length I v1 v2 vB0 K0 inner0Rest outerRest ks N hks hK0
    hinner0len houterLen houter ⟨b, vs, hbvs, hvslen⟩
  have hcountW := guessBXBlockWord_zBx'x_write_terminator_take_count I v1 v2 vB0 K0 inner0Rest
    outerRest ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposW := guessBXBlockWord_zBx'x_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposR := guessBXBlockWord_zBxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposE := guessBXBlockWord_ellByx_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len N b vs hbvs hvslen
  set Q := nestedInnerStart ks (ksPrefix ks (N + 1)) with hQdef
  set pred := (fun l : ThreadLabel (domainOf I) Tid.guessBX => match l.1.loc, l.1.op with
    | Loc.zBx'x, OpType.wt => true | _, _ => false) with hpreddef
  have hbridge : Q + 3 = 4 + K0 * 3 +
      ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length + 4 := by
    have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hlenL := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      ⟨b, vs, hbvs, hvslen⟩ N (by omega)
    have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N N
      rwa [hgetD0] at hh
    rw [hQdef, ← hstart, hlenL, hstartm]; omega
  have step1 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1)).filter
      pred).length = (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1)).filter
      pred).length + 1 := by
    rw [List.take_add_one, hposW, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step2 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1)).filter
      pred).length = (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1)).filter
      pred).length := by
    rw [List.take_add_one, hposR, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step3 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (Q + 1 + 1 + 1 + 1)).filter pred).length =
      (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1)).filter
      pred).length := by
    rw [List.take_add_one, show Q + 1 + 1 + 1 = Q + 3 from by omega, hbridge, hposE,
      Option.toList_some, List.filter_append, List.length_append, hpreddef]
    rfl
  have hfull : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1 + 1) =
      guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest := by
    rw [show Q + 1 + 1 + 1 + 1 = (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length from
      by rw [hlen]]
    exact List.take_length
  rw [← hfull]
  omega

/-- `guessBXBlockWord` contains `ksPrefix ks (N + 1) + 1` `xB`-writes. -/
theorem guessBXBlockWord_xB_write_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => match l.1.loc, l.1.op with | Loc.xB, OpType.wt => true | _, _ => false)).length
      = ksPrefix ks (N + 1) + 1 := by
  obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
  have ha0 : (0 : ℕ) < vs.length := by omega
  obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'ha0, List.getElem?_eq_getElem ha0⟩
  have hlen := guessBXBlockWord_length I v1 v2 vB0 K0 inner0Rest outerRest ks N hks hK0
    hinner0len houterLen houter ⟨b, vs, hbvs, hvslen⟩
  have hcountW := guessBXBlockWord_xB_write_terminator_take_count I v1 v2 vB0 K0 inner0Rest
    outerRest ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposXA := guessBXBlockWord_xB_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposW := guessBXBlockWord_zBx'x_write_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposR := guessBXBlockWord_zBxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposE := guessBXBlockWord_ellByx_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len N b vs hbvs hvslen
  set Q := nestedInnerStart ks (ksPrefix ks (N + 1)) with hQdef
  set pred := (fun l : ThreadLabel (domainOf I) Tid.guessBX => match l.1.loc, l.1.op with
    | Loc.xB, OpType.wt => true | _, _ => false) with hpreddef
  have hbridge : Q + 3 = 4 + K0 * 3 +
      ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length + 4 := by
    have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hlenL := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      ⟨b, vs, hbvs, hvslen⟩ N (by omega)
    have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N N
      rwa [hgetD0] at hh
    rw [hQdef, ← hstart, hlenL, hstartm]; omega
  have step0 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1)).filter
      pred).length = (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take Q).filter
      pred).length + 1 := by
    rw [List.take_add_one, hposXA, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step1 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1)).filter
      pred).length = (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1)).filter
      pred).length := by
    rw [List.take_add_one, hposW, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step2 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1)).filter
      pred).length = (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1)).filter
      pred).length := by
    rw [List.take_add_one, hposR, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step3 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (Q + 1 + 1 + 1 + 1)).filter pred).length =
      (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1)).filter
      pred).length := by
    rw [List.take_add_one, show Q + 1 + 1 + 1 = Q + 3 from by omega, hbridge, hposE,
      Option.toList_some, List.filter_append, List.length_append, hpreddef]
    rfl
  have hfull : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 1 + 1 + 1 + 1) =
      guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest := by
    rw [show Q + 1 + 1 + 1 + 1 = (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length from
      by rw [hlen]]
    exact List.take_length
  rw [← hfull]
  omega
/-- `guessBXBlockWord` contains `ksPrefix ks (N + 1)` `zBxx'`-reads. -/
theorem guessBXBlockWord_zBxx'_read_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false)).length
      = ksPrefix ks (N + 1) := by
  obtain ⟨b, vs, hbvs, hvslen⟩ := houterLast
  have ha0 : (0 : ℕ) < vs.length := by omega
  obtain ⟨a, hva⟩ : ∃ a, vs[0]? = some a := ⟨vs[0]'ha0, List.getElem?_eq_getElem ha0⟩
  have hlen := guessBXBlockWord_length I v1 v2 vB0 K0 inner0Rest outerRest ks N hks hK0
    hinner0len houterLen houter ⟨b, vs, hbvs, hvslen⟩
  have hcountR := guessBXBlockWord_zBxx'_read_terminator_take_count I v1 v2 vB0 K0 inner0Rest
    outerRest ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposR := guessBXBlockWord_zBxx'_read_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    ks N hks hK0 hinner0len houterLen houter b vs hbvs hvslen a hva
  have hposE := guessBXBlockWord_ellByx_terminator_pos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len N b vs hbvs hvslen
  set Q := nestedInnerStart ks (ksPrefix ks (N + 1)) with hQdef
  set pred := (fun l : ThreadLabel (domainOf I) Tid.guessBX => match l.1.loc, l.1.op with
    | Loc.zBxx', OpType.rd => true | _, _ => false) with hpreddef
  have hbridge : Q + 3 = 4 + K0 * 3 +
      ((outerRest.take N).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length + 4 := by
    have hstart := nestedOuterStart_succ_eq_innerStart ks N (N + 1) hks (le_refl (N + 1))
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hlenL := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      ⟨b, vs, hbvs, hvslen⟩ N (by omega)
    have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    have hge : nestedOuterStart ks N (N + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N N
      rwa [hgetD0] at hh
    rw [hQdef, ← hstart, hlenL, hstartm]; omega
  have step1 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2 + 1)).filter
      pred).length = (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2)).filter
      pred).length + 1 := by
    rw [List.take_add_one, hposR, Option.toList_some, List.filter_append, List.length_append,
      hpreddef]
    rfl
  have step2 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2 + 1 + 1)).filter
      pred).length = (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2 + 1)).filter
      pred).length := by
    rw [List.take_add_one, show Q + 2 + 1 = Q + 3 from by omega, hbridge, hposE, Option.toList_some,
      List.filter_append, List.length_append, hpreddef]
    rfl
  have hfull : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (Q + 2 + 1 + 1) =
      guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest := by
    rw [show Q + 2 + 1 + 1 = (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length from
      by rw [hlen]]
    exact List.take_length
  have hge1 : 1 ≤ ksPrefix ks (N + 1) := by
    have h := ksPrefix_ge ks (N + 1); omega
  rw [← hfull]
  omega

/-! ## Eq. (15)'s `zBxx'`/`zBx'x` no-skipping pair (`GuessBX`/`PrimeBX`)

`GuessBX` writes `zBx'x` and reads `zBxx'`; `PrimeBX` writes `zBxx'` and reads
`zBx'x`. `GuessBX`'s side goes through the nested-call position layer above
(`nestedInnerStart`); `PrimeBX`'s is a uniform 3-entry block. -/

/-- `PrimeBX`'s `n`-th `zBxx'`-write is at position `n*3+1` of
`G.threadEvents Tid.primeBX`. -/
theorem primeBX_zBxx'_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {vals : List (Val I)}
    (hw2 : G.threadWord Tid.primeBX = (primeBXBlockWord I vals).map some)
    (n : ℕ) {v : Val I} (hv : vals[n]? = some v) :
    ∃ hlen : n * 3 + 1 < (G.threadEvents Tid.primeBX).length,
      G.nthWrite Tid.primeBX Loc.zBxx' n =
        some ((G.threadEvents Tid.primeBX)[n * 3 + 1]'hlen).1 := by
  have hnlen : n < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hsplit := list_take_flatMap_uniform_offset (primeBXBlockElems I) 3 (fun _ => rfl)
    vals n 1 v hv (by norm_num)
  have hpartial : ((primeBXBlockElems I v).take 1).filter
      (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.wt) = [] := by
    unfold primeBXBlockElems
    rfl
  have hone_w : ∀ v' : Val I, (primeBXBlockElems I v').filter
      (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeBX Loc.zBxx' v', rfl⟩ : ThreadLabel (domainOf I) Tid.primeBX)] := by
    intro v'
    unfold primeBXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_w : (((primeBXBlockWord I vals).take (n * 3 + 1)).filter
      (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.wt)).length = n := by
    rw [primeBXBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_w]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeBX).length = (primeBXBlockWord I vals).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeBXBlockWord I vals).length = 3 * vals.length := by
    rw [primeBXBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (vals.map (fun a => (primeBXBlockElems I a).length))
        = vals.map (fun _ => 3) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_w : n * 3 + 1 < (G.threadEvents Tid.primeBX).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_w : (primeBXBlockWord I vals)[n * 3 + 1]? =
      some (⟨EventLabel.wt Tid.primeBX Loc.zBxx' v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeBX) := by
    rw [primeBXBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeBXBlockElems I) 3 (fun _ => rfl) vals n
      1 v hv (by norm_num)
    rw [hget]
    unfold primeBXBlockElems
    rfl
  refine ⟨hlen_w, ?_⟩
  have hwpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zBxx') (op := OpType.wt)
    hw2 hlen_w hlabP_w rfl rfl hcount_w
  rwa [show G.nthEvent Tid.primeBX Loc.zBxx' OpType.wt n = G.nthWrite Tid.primeBX Loc.zBxx' n
    from rfl] at hwpos

/-- `PrimeBX`'s `n`-th `zBx'x`-read is at position `n*3+2` of
`G.threadEvents Tid.primeBX`. -/
theorem primeBX_zBx'x_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {vals : List (Val I)}
    (hw2 : G.threadWord Tid.primeBX = (primeBXBlockWord I vals).map some)
    (n : ℕ) {v : Val I} (hv : vals[n]? = some v) :
    ∃ hlen : n * 3 + 2 < (G.threadEvents Tid.primeBX).length,
      G.nthRead Tid.primeBX Loc.zBx'x n =
        some ((G.threadEvents Tid.primeBX)[n * 3 + 2]'hlen).1 := by
  have hnlen : n < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hsplit := list_take_flatMap_uniform_offset (primeBXBlockElems I) 3 (fun _ => rfl)
    vals n 2 v hv (by norm_num)
  have hpartial : ((primeBXBlockElems I v).take 2).filter
      (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.rd) = [] := by
    unfold primeBXBlockElems
    rfl
  have hone : ∀ v' : Val I, (primeBXBlockElems I v').filter
      (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeBX Loc.zBx'x v', rfl⟩ : ThreadLabel (domainOf I) Tid.primeBX)] := by
    intro v'
    unfold primeBXBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((primeBXBlockWord I vals).take (n * 3 + 2)).filter
      (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.rd)).length = n := by
    rw [primeBXBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeBX).length = (primeBXBlockWord I vals).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeBXBlockWord I vals).length = 3 * vals.length := by
    rw [primeBXBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (vals.map (fun a => (primeBXBlockElems I a).length))
        = vals.map (fun _ => 3) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_er : n * 3 + 2 < (G.threadEvents Tid.primeBX).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_er : (primeBXBlockWord I vals)[n * 3 + 2]? =
      some (⟨EventLabel.rd Tid.primeBX Loc.zBx'x v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeBX) := by
    rw [primeBXBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeBXBlockElems I) 3 (fun _ => rfl) vals n
      2 v hv (by norm_num)
    rw [hget]
    unfold primeBXBlockElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zBx'x) (op := OpType.rd)
    hw2 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.primeBX Loc.zBx'x OpType.rd n = G.nthRead Tid.primeBX Loc.zBx'x n
    from rfl] at herpos

/-- Eq. (15)'s `zBxx'`/`zBx'x` pair (`GuessBX`/`PrimeBX`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`guessBX_shape_inv`, `primeBX_shape_inv`). `GuessBX`'s inner calls are
numbered `0, 1, …` across the whole thread (flattened past outer-iteration
boundaries, `ks := K0 :: guessBXJsToKs I js`); call `P` writes `zBx'x` at
`nestedInnerStart ks P + 1`, and every call but the globally-first one reads
`zBxx'` at `nestedInnerStart ks P + 2`, so `GuessBX`'s `j`-th `zBxx'`-read is
call `j + 1`. Both locations have a single writer, so writer identification
is `writerTid_confined`. -/
theorem guessBX_primeBX_zBx_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.guessBX Tid.primeBX Loc.zBxx' Loc.zBx'x := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessBX_run_of_reaches I G hG
  obtain ⟨v0, K0, js, v1, v2, vB0, inner0Rest, outerRest, -, -, hinner0len, houterLen, houter,
    houterLast, hv2, hinner0val, houterval, -, -, -, -, -, -, hσ1⟩ := guessBX_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := primeBX_run_of_reaches I G hG
  obtain ⟨M, vals, -, -, hvalsval, hσ2⟩ := primeBX_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBX, hσ1]
  have hw2 : G.threadWord Tid.primeBX = (primeBXBlockWord I vals).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeBX, hσ2]
  have hks : (K0 :: guessBXJsToKs I js).length = js.length + 1 := by simp [guessBXJsToKs]
  have hK0 : (K0 :: guessBXJsToKs I js)[0]? = some K0 := rfl
  have houter' : ∀ j, j < js.length → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      (K0 :: guessBXJsToKs I js)[j + 1]? = some km ∧ vs.length = km + 1 := by
    intro j hj
    obtain ⟨b, vs, km, hbvs, hksm, hvslen⟩ := houter j hj
    exact ⟨b, vs, km, hbvs, hksm, hvslen⟩
  have hinner0val_write : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4) := fun n hn =>
    let ⟨e, he, _, he1⟩ := hinner0val n hn; ⟨e, he, he1⟩
  have houterval_write : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix (guessBXJsToKs I js) m + n + 1) % 4,
          by omega⟩ : Fin 4) := fun m hm =>
    let ⟨b, vs, hbvs, hval⟩ := houterval m hm
    ⟨b, vs, hbvs, fun n hn => let ⟨e, he, _, he1⟩ := hval n hn; ⟨e, he, he1⟩⟩
  have hinner0val_read : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4) := fun n hn =>
    let ⟨e, he, he2, _⟩ := hinner0val n hn; ⟨e, he, he2⟩
  have houterval_read : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix (guessBXJsToKs I js) m + n) % 4,
          by omega⟩ : Fin 4) := fun m hm =>
    let ⟨b, vs, hbvs, hval⟩ := houterval m hm
    ⟨b, vs, hbvs, fun n hn => let ⟨e, he, he2, _⟩ := hval n hn; ⟨e, he, he2⟩⟩
  set ks := K0 :: guessBXJsToKs I js with hksdef
  set K := ksPrefix ks (js.length + 1) with hKdef
  -- `GuessBX`'s `zBx'x`-writes number `K + 1`, its `zBxx'`-reads `K`.
  have hGWb : ∀ {i : ℕ} {w : Event (domainOf I)},
      G.nthWrite Tid.guessBX Loc.zBx'x i = some w → i ≤ K := by
    intro i w hw
    have hitot : i < (G.opEvents Tid.guessBX Loc.zBx'x OpType.wt).length :=
      (List.getElem?_eq_some_iff.mp hw).1
    have hL := G.opEvents_map_lab_eq_filter_threadLabels Tid.guessBX Loc.zBx'x OpType.wt
    have hLlen := congrArg List.length hL
    rw [List.length_map, List.length_map, hσ1] at hLlen
    have hLlen2 := (guessBX_zBx'x_write_filter_eq (I := I)
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)) ▸ hLlen
    have htot := guessBXBlockWord_zBx'x_write_total_count I v1 v2 vB0 K0 inner0Rest outerRest
      ks js.length hks hK0 hinner0len houterLen houter' houterLast
    omega
  have hGRb : ∀ {j : ℕ} {r : Event (domainOf I)},
      G.nthRead Tid.guessBX Loc.zBxx' j = some r → j + 1 ≤ K := by
    intro j r hr
    have hjtot : j < (G.opEvents Tid.guessBX Loc.zBxx' OpType.rd).length :=
      (List.getElem?_eq_some_iff.mp hr).1
    have hL := G.opEvents_map_lab_eq_filter_threadLabels Tid.guessBX Loc.zBxx' OpType.rd
    have hLlen := congrArg List.length hL
    rw [List.length_map, List.length_map, hσ1] at hLlen
    have hLlen2 := (guessBX_zBxx'_read_filter_eq (I := I)
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)) ▸ hLlen
    have htot := guessBXBlockWord_zBxx'_read_total_count I v1 v2 vB0 K0 inner0Rest outerRest
      ks js.length hks hK0 hinner0len houterLen houter' houterLast
    omega
  -- `GuessBX`'s `i`-th `zBx'x`-write is call `i`, at `nestedInnerStart ks i + 1`.
  have hGW : ∀ i, i ≤ K → ∃ hlen : nestedInnerStart ks i + 1 < (G.threadEvents Tid.guessBX).length,
      G.nthWrite Tid.guessBX Loc.zBx'x i =
        some ((G.threadEvents Tid.guessBX)[nestedInnerStart ks i + 1]'hlen).1 ∧
      ∃ c : Fin 4, ((G.threadEvents Tid.guessBX)[nestedInnerStart ks i + 1]'hlen).1.val =
        Val.cnt c ∧ c.val = (i + 1) % 4 := by
    intro i hi
    have hval := guessBXBlockWord_zBx'x_write_val_full I v1 v2 vB0 K0 inner0Rest outerRest
      ks (guessBXJsToKs I js) js.length rfl hks hK0 hinner0len houterLen
      houter' houterLast hv2 hinner0val_write houterval_write i hi
    obtain ⟨eSub, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 _ _ hval
    have hcountB := guessBXBlockWord_zBx'x_write_take_count_full I v1 v2 vB0 K0 inner0Rest
      outerRest ks js.length hks hK0 hinner0len houterLen houter' houterLast i hi
    have hcount : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks i + 1)).filter
        (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.wt)).length = i := by
      rw [guessBX_zBx'x_write_filter_eq]
      simpa using hcountB
    refine ⟨hlt, G.nthEvent_eq_of_threadWord_pos hw1 hlt hval rfl rfl hcount,
      ⟨(i + 1) % 4, by omega⟩, ?_, rfl⟩
    rw [heq, Event.val, hlab]
    rfl
  -- `GuessBX`'s `j`-th `zBxx'`-read is call `j + 1`, at `nestedInnerStart ks (j + 1) + 2`.
  have hGR : ∀ j, j + 1 ≤ K →
      ∃ hlen : nestedInnerStart ks (j + 1) + 2 < (G.threadEvents Tid.guessBX).length,
      G.nthRead Tid.guessBX Loc.zBxx' j =
        some ((G.threadEvents Tid.guessBX)[nestedInnerStart ks (j + 1) + 2]'hlen).1 ∧
      ∃ c : Fin 4, ((G.threadEvents Tid.guessBX)[nestedInnerStart ks (j + 1) + 2]'hlen).1.val =
        Val.cnt c ∧ c.val = (j + 1) % 4 := by
    intro j hj
    have hval := guessBXBlockWord_zBxx'_read_val_full I v1 v2 vB0 K0 inner0Rest outerRest
      ks (guessBXJsToKs I js) js.length rfl hks hK0 hinner0len houterLen
      houter' houterLast hinner0val_read houterval_read (j + 1) (by omega) hj
    obtain ⟨eSub, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 _ _ hval
    have hcountB := guessBXBlockWord_zBxx'_read_take_count_full I v1 v2 vB0 K0 inner0Rest
      outerRest ks js.length hks hK0 hinner0len houterLen houter' houterLast (j + 1)
      (by omega) hj
    have hcount : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks (j + 1) + 2)).filter
        (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.rd)).length = j := by
      rw [guessBX_zBxx'_read_filter_eq]
      simpa using hcountB
    refine ⟨hlt, G.nthEvent_eq_of_threadWord_pos hw1 hlt hval rfl rfl hcount,
      ⟨(j + 1) % 4, by omega⟩, ?_, rfl⟩
    rw [heq, Event.val, hlab]
    rfl
  -- `primeBX`'s `i`-th `zBxx'`-write and `zBx'x`-read: value `(i+1) mod 4`, in block `vals[i]`.
  have hWp : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.primeBX Loc.zBxx' i = some w →
      (∃ c : Fin 4, w.val = Val.cnt c ∧ c.val = (i + 1) % 4) ∧ i < vals.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    have hf := (primeBXBlockWord_zBxx'_write_val I vals i).symm.trans hf
    rcases hv : vals[i]? with _ | v
    · rw [hv] at hf; exact nomatch hf
    · rw [hv] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hvv := hvalsval i hlt
      rw [hv] at hvv
      refine ⟨⟨⟨(i + 1) % 4, by omega⟩, ?_, rfl⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf, ← Option.some.inj hvv]
      rfl
  have hRq : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.primeBX Loc.zBx'x j = some r →
      (∃ c : Fin 4, r.val = Val.cnt c ∧ c.val = (j + 1) % 4) ∧ j < vals.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (primeBXBlockWord_zBx'x_read_val I vals j).symm.trans hf
    rcases hv : vals[j]? with _ | v
    · rw [hv] at hf; exact nomatch hf
    · rw [hv] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hvv := hvalsval j hlt
      rw [hv] at hvv
      refine ⟨⟨⟨(j + 1) % 4, by omega⟩, ?_, rfl⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf, ← Option.some.inj hvv]
      rfl
  have hval : ∀ {n : ℕ}, n < vals.length → ∃ v, vals[n]? = some v :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWp hw
    obtain ⟨hlen, hpos, c', hc', hc'v⟩ := hGR j (hGRb hr)
    rw [hc, Option.some.inj (hr.symm.trans hpos), hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨hlen, hpos, c, hc, hcv⟩ := hGW i (hGWb hw)
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRq hr
    rw [Option.some.inj (hw.symm.trans hpos), hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.primeBX := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.guessBX := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · -- `guessBX`: `r(zBxx')` of call `i + 1` precedes `w(zBx'x)` of call `ℓ ≥ i + 2`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨hlenR, hposR, -⟩ := hGR i (hGRb hr)
    obtain ⟨hlenW, hposW, -⟩ := hGW ℓ (hGWb hw)
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    have hmono := (nestedInnerStart_strictMono ks).monotone (show i + 2 ≤ ℓ from hiℓ)
    have hstep : nestedInnerStart ks (i + 2) =
        nestedInnerStart ks (i + 1) + (nestedCallLen (i + 1) + nestedGap ks (i + 1)) :=
      nestedInnerStart_succ ks (i + 1)
    have hcall : 2 ≤ nestedCallLen (i + 1) := by unfold nestedCallLen; split <;> omega
    exact G.po_of_threadEvents_pos_lt Tid.guessBX hlenR hlenW (by omega)
  · -- `primeBX`: `r(zBx'x)` at `i*3+2` precedes `w(zBxx')` at `ℓ*3+1`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨v, hv⟩ := hval (hRq hr).2
    obtain ⟨v', hv'⟩ := hval (hWp hw).2
    obtain ⟨hlenR, hposR⟩ := primeBX_zBx'x_read_nthRead_pos I G hw2 i hv
    obtain ⟨hlenW, hposW⟩ := primeBX_zBxx'_write_nthWrite_pos I G hw2 ℓ hv'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.primeBX hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    exact ⟨_, (hGR i (by have := hGWb hw; omega)).2.1⟩
  · intro i ℓ w hw hiℓ
    obtain ⟨v, hv⟩ := hval (n := i) (by have := (hWp hw).2; omega)
    exact ⟨_, (primeBX_zBx'x_read_nthRead_pos I G hw2 i hv).2⟩

theorem no_skipping_guessBX_primeBX_zBxx' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeBX Loc.zBxx' i = some ew)
    (her : G.nthRead Tid.guessBX Loc.zBxx' K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((guessBX_primeBX_zBx_noSkipPair I G hG).no_skipping hG.1.1 K).1 hew her hrf

theorem no_skipping_guessBX_primeBX_zBx'x (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (n K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessBX Loc.zBx'x n = some ew)
    (her : G.nthRead Tid.primeBX Loc.zBx'x K = some er) (hrf : G.rf ew er) :
    n = K :=
  ((guessBX_primeBX_zBx_noSkipPair I G hG).no_skipping hG.1.1 K).2 hew her hrf

/-! ## Eq. (15)'s `zAyy'`/`zAy'y` pair (`GuessAY`/`PrimeAY`)

`GuessAY` has a single loop: block 0 (length 3) is
`[w(yA), w(ellAyx), w(zAy'y)]`, and every later block (length 5) is
`[w(yA), w(ellAyx), w(zAy'y), r(zAxy), r(zAyy')]`; block 0 has neither
read. `PrimeAY` is uniform: `primeAYBlockElems l =
[w(yA', primeTag 0), w(zAyy', l), r(zAy'y, l)]`. Both locations carry
untagged `Val.cnt` values, so writers are identified by
`writerTid_confined`. -/

/-- `GuessAY`'s `zAy'y`-write value at filtered index `0` (block 0): `1`. -/
theorem guessAYBlockWord_zAy'y_write_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((guessAYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.guessAY Loc.zAy'y (Val.cnt 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY) := by
  unfold guessAYBlockWord
  rw [List.filter_append]
  have hb0 : (guessAYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAY Loc.zAy'y (Val.cnt 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `GuessAY`'s `zAy'y`-write value at filtered index `i + 1` (block
`kws[i]`), in terms of `kws[i].1`. -/
theorem guessAYBlockWord_zAy'y_write_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((guessAYBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.guessAY Loc.zAy'y (Val.cnt (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
  unfold guessAYBlockWord
  rw [List.filter_append]
  have hb0 : (guessAYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAY Loc.zAy'y (Val.cnt 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessAYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.guessAY Loc.zAy'y (Val.cnt (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.guessAY Loc.zAy'y (Val.cnt (kw.1 + 1)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAY)] := by
      intro kw
      unfold guessAYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

/-- `GuessAY`'s `zAyy'`-read value at filtered index `k`: block 0 has none,
so this is block `kws[k]`, with value `Val.cnt kw.1`. -/
theorem guessAYBlockWord_zAyy'_read_val (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (k : ℕ) :
    ((guessAYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.rd))[k]? =
      (kws[k]?).map (fun kw => (⟨EventLabel.rd Tid.guessAY Loc.zAyy' (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
  unfold guessAYBlockWord
  rw [List.filter_append]
  have hb0 : (guessAYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.rd) =
      [] := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessAYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.guessAY Loc.zAyy' (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.guessAY Loc.zAyy' (Val.cnt kw.1), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAY)] := by
      intro kw
      unfold guessAYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.nil_append, List.getElem?_map]

/-- `PrimeAY`'s `zAyy'`-write value at filtered position `j` is `vals[j]`. -/
theorem primeAYBlockWord_zAyy'_write_val (I : PCPInstance) (vals : List (Val I)) (j : ℕ) :
    ((primeAYBlockWord I vals).filter (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.wt))[j]? =
      (vals[j]?).map (fun v => (⟨EventLabel.wt Tid.primeAY Loc.zAyy' v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeAY)) := by
  have hone : ∀ v : Val I, (primeAYBlockElems I v).filter
      (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeAY Loc.zAyy' v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeAY)] := by
    intro v
    unfold primeAYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeAYBlockWord I vals).filter (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.wt) =
      vals.map (fun v => (⟨EventLabel.wt Tid.primeAY Loc.zAyy' v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeAY)) := by
    rw [primeAYBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ vals
  rw [hflat]
  exact List.getElem?_map ..

/-- `PrimeAY`'s `zAy'y`-read value at filtered position `j` is `vals[j]`. -/
theorem primeAYBlockWord_zAy'y_read_val (I : PCPInstance) (vals : List (Val I)) (j : ℕ) :
    ((primeAYBlockWord I vals).filter (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.rd))[j]? =
      (vals[j]?).map (fun v => (⟨EventLabel.rd Tid.primeAY Loc.zAy'y v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeAY)) := by
  have hone : ∀ v : Val I, (primeAYBlockElems I v).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeAY Loc.zAy'y v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeAY)] := by
    intro v
    unfold primeAYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeAYBlockWord I vals).filter (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.rd) =
      vals.map (fun v => (⟨EventLabel.rd Tid.primeAY Loc.zAy'y v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeAY)) := by
    rw [primeAYBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ vals
  rw [hflat]
  exact List.getElem?_map ..

/-- Position of offset `p` of `GuessAY`'s block `n + 1` (`kws[n]`):
`3 + n * 5 + p`. -/
theorem guessAYBlockWord_blockRest_pos (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (n p : ℕ) (kw : Fin 4 × Option (Fin I.n))
    (hkw : kws[n]? = some kw) (hp : p < 5) :
    (guessAYBlockWord I v0 kws)[3 + n * 5 + p]? = (guessAYBlockRestElems I kw)[p]? := by
  have heq : guessAYBlockWord I v0 kws =
      guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I) := rfl
  have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
  rw [heq, List.getElem?_append_right (by rw [hb0len]; omega), hb0len]
  have hi : 3 + n * 5 + p - 3 = n * 5 + p := by omega
  rw [hi]
  exact flatMap_uniform_getElem_fwd (guessAYBlockRestElems I) 5 (fun _ => rfl) kws n p kw hkw hp

/-- `GuessAY`'s `yA`-write value at filtered index `0` (block 0). -/
theorem guessAYBlockWord_yA_write_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((guessAYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.guessAY Loc.yA (Val.yTag (Tid.guessAY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY) := by
  unfold guessAYBlockWord
  rw [List.filter_append]
  have hb0 : (guessAYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAY Loc.yA (Val.yTag (Tid.guessAY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `GuessAY`'s `yA`-write value at filtered index `i + 1` (block
`kws[i]`). -/
theorem guessAYBlockWord_yA_write_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((guessAYBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.guessAY Loc.yA (Val.yTag (Tid.guessAY, false) kw.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
  unfold guessAYBlockWord
  rw [List.filter_append]
  have hb0 : (guessAYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAY Loc.yA (Val.yTag (Tid.guessAY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessAYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.guessAY Loc.yA (Val.yTag (Tid.guessAY, false) kw.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.guessAY Loc.yA (Val.yTag (Tid.guessAY, false) kw.2), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAY)] := by
      intro kw
      unfold guessAYBlockRestElems
      rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

/-- `PrimeAY`'s `n`-th `zAyy'`-write is at position `n*3+1` of
`G.threadEvents Tid.primeAY`. -/
theorem primeAY_zAyy'_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {vals : List (Val I)}
    (hw2 : G.threadWord Tid.primeAY = (primeAYBlockWord I vals).map some)
    (n : ℕ) {v : Val I} (hv : vals[n]? = some v) :
    ∃ hlen : n * 3 + 1 < (G.threadEvents Tid.primeAY).length,
      G.nthWrite Tid.primeAY Loc.zAyy' n =
        some ((G.threadEvents Tid.primeAY)[n * 3 + 1]'hlen).1 := by
  have hnlen : n < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hsplit := list_take_flatMap_uniform_offset (primeAYBlockElems I) 3 (fun _ => rfl)
    vals n 1 v hv (by norm_num)
  have hpartial : ((primeAYBlockElems I v).take 1).filter
      (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.wt) = [] := by
    unfold primeAYBlockElems
    rfl
  have hone_w : ∀ v' : Val I, (primeAYBlockElems I v').filter
      (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeAY Loc.zAyy' v', rfl⟩ : ThreadLabel (domainOf I) Tid.primeAY)] := by
    intro v'
    unfold primeAYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_w : (((primeAYBlockWord I vals).take (n * 3 + 1)).filter
      (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.wt)).length = n := by
    rw [primeAYBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_w]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeAY).length = (primeAYBlockWord I vals).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeAYBlockWord I vals).length = 3 * vals.length := by
    rw [primeAYBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (vals.map (fun a => (primeAYBlockElems I a).length))
        = vals.map (fun _ => 3) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_w : n * 3 + 1 < (G.threadEvents Tid.primeAY).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_w : (primeAYBlockWord I vals)[n * 3 + 1]? =
      some (⟨EventLabel.wt Tid.primeAY Loc.zAyy' v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeAY) := by
    rw [primeAYBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeAYBlockElems I) 3 (fun _ => rfl) vals n
      1 v hv (by norm_num)
    rw [hget]
    unfold primeAYBlockElems
    rfl
  refine ⟨hlen_w, ?_⟩
  have hwpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zAyy') (op := OpType.wt)
    hw2 hlen_w hlabP_w rfl rfl hcount_w
  rwa [show G.nthEvent Tid.primeAY Loc.zAyy' OpType.wt n = G.nthWrite Tid.primeAY Loc.zAyy' n
    from rfl] at hwpos

/-- `PrimeAY`'s `n`-th `zAy'y`-read is at position `n*3+2` of
`G.threadEvents Tid.primeAY`. -/
theorem primeAY_zAy'y_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {vals : List (Val I)}
    (hw2 : G.threadWord Tid.primeAY = (primeAYBlockWord I vals).map some)
    (n : ℕ) {v : Val I} (hv : vals[n]? = some v) :
    ∃ hlen : n * 3 + 2 < (G.threadEvents Tid.primeAY).length,
      G.nthRead Tid.primeAY Loc.zAy'y n =
        some ((G.threadEvents Tid.primeAY)[n * 3 + 2]'hlen).1 := by
  have hnlen : n < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hsplit := list_take_flatMap_uniform_offset (primeAYBlockElems I) 3 (fun _ => rfl)
    vals n 2 v hv (by norm_num)
  have hpartial : ((primeAYBlockElems I v).take 2).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.rd) = [] := by
    unfold primeAYBlockElems
    rfl
  have hone : ∀ v' : Val I, (primeAYBlockElems I v').filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeAY Loc.zAy'y v', rfl⟩ : ThreadLabel (domainOf I) Tid.primeAY)] := by
    intro v'
    unfold primeAYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((primeAYBlockWord I vals).take (n * 3 + 2)).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.rd)).length = n := by
    rw [primeAYBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeAY).length = (primeAYBlockWord I vals).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeAYBlockWord I vals).length = 3 * vals.length := by
    rw [primeAYBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (vals.map (fun a => (primeAYBlockElems I a).length))
        = vals.map (fun _ => 3) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_er : n * 3 + 2 < (G.threadEvents Tid.primeAY).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_er : (primeAYBlockWord I vals)[n * 3 + 2]? =
      some (⟨EventLabel.rd Tid.primeAY Loc.zAy'y v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeAY) := by
    rw [primeAYBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeAYBlockElems I) 3 (fun _ => rfl) vals n
      2 v hv (by norm_num)
    rw [hget]
    unfold primeAYBlockElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zAy'y) (op := OpType.rd)
    hw2 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.primeAY Loc.zAy'y OpType.rd n = G.nthRead Tid.primeAY Loc.zAy'y n
    from rfl] at herpos

/-- `GuessAY`'s `j`-th `zAyy'`-read (block `kws[j]`) is at position `7+j*5`
of `G.threadEvents Tid.guessAY`. -/
theorem guessAY_zAyy'_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.guessAY = (guessAYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 7 + j * 5 < (G.threadEvents Tid.guessAY).length,
      G.nthRead Tid.guessAY Loc.zAyy' j =
        some ((G.threadEvents Tid.guessAY)[7 + j * 5]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hone_er : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessAY Loc.zAyy' (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    intro kw
    unfold guessAYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((guessAYBlockWord I v0 kws).take (7 + j * 5)).filter
      (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.rd)).length = j := by
    have heq : guessAYBlockWord I v0 kws =
        guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I) := rfl
    have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
    have hle3 : (guessAYBlock0Elems I v0).length ≤ 7 + j * 5 := by rw [hb0len]; omega
    have hb0nil : (guessAYBlock0Elems I v0).filter
        (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.rd) = [] := by
      unfold guessAYBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hsplit := list_take_flatMap_uniform_offset (guessAYBlockRestElems I) 5 (fun _ => rfl)
      kws j 4 kwj hkj (by norm_num)
    have hpartial : ((guessAYBlockRestElems I kwj).take 4).filter
        (fun l => l.1.loc = Loc.zAyy' ∧ l.1.op = OpType.rd) = [] := by
      unfold guessAYBlockRestElems
      rfl
    have hsub : 7 + j * 5 - (guessAYBlock0Elems I v0).length = j * 5 + 4 := by
      rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle3, hsub, hsplit, List.filter_append,
      List.filter_append, hb0nil, hpartial, List.nil_append, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_er]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.guessAY).length = (guessAYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_er : 7 + j * 5 < (G.threadEvents Tid.guessAY).length := by
    have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
    have hbrlen : (kws.flatMap (guessAYBlockRestElems I)).length = 5 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (guessAYBlockRestElems I a).length))
          = kws.map (fun _ => 5) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (guessAYBlockWord I v0 kws).length = 3 + 5 * kws.length := by
      show (guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_er : (guessAYBlockWord I v0 kws)[7 + j * 5]? =
      some (⟨EventLabel.rd Tid.guessAY Loc.zAyy' (Val.cnt kwj.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY) := by
    have hget := guessAYBlockWord_blockRest_pos I v0 kws j 4 kwj hkj (by norm_num)
    rw [show 3 + j * 5 + 4 = 7 + j * 5 from by omega] at hget
    rw [hget]
    unfold guessAYBlockRestElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zAyy') (op := OpType.rd)
    hw1 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.guessAY Loc.zAyy' OpType.rd j = G.nthRead Tid.guessAY Loc.zAyy' j
    from rfl] at herpos

/-- `GuessAY`'s `(j+1)`-th `zAy'y`-write (block `kws[j]`) is at position
`3+j*5+2` of `G.threadEvents Tid.guessAY`. -/
theorem guessAY_zAy'y_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.guessAY = (guessAYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 3 + j * 5 + 2 < (G.threadEvents Tid.guessAY).length,
      G.nthWrite Tid.guessAY Loc.zAy'y (j + 1) =
        some ((G.threadEvents Tid.guessAY)[3 + j * 5 + 2]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hb0count : ((guessAYBlock0Elems I v0).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt)).length = 1 := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rfl
  have hone_ew : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAY Loc.zAy'y (Val.cnt (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    intro kw
    unfold guessAYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hpartial0 : ((guessAYBlockRestElems I kwj).take 2).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt) = [] := by
    unfold guessAYBlockRestElems
    rfl
  have hcount_ew : (((guessAYBlockWord I v0 kws).take (3 + j * 5 + 2)).filter
      (fun l => l.1.loc = Loc.zAy'y ∧ l.1.op = OpType.wt)).length = 1 + j := by
    have heq : guessAYBlockWord I v0 kws =
        guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I) := rfl
    have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
    have hsub : 3 + j * 5 + 2 - 3 = j * 5 + 2 := by omega
    have hle : (guessAYBlock0Elems I v0).length ≤ 3 + j * 5 + 2 := by rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle, hb0len, hsub,
      list_take_flatMap_uniform_offset (guessAYBlockRestElems I) 5 (fun _ => rfl) kws j 2 kwj hkj
        (by norm_num)]
    simp only [List.filter_append, List.length_append, hb0count, hpartial0, List.filter_nil,
      List.length_nil, Nat.add_zero]
    rw [list_filter_flatMap_distrib]
    simp only [hone_ew]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.guessAY).length = (guessAYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_ew : 3 + j * 5 + 2 < (G.threadEvents Tid.guessAY).length := by
    have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
    have hbrlen : (kws.flatMap (guessAYBlockRestElems I)).length = 5 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (guessAYBlockRestElems I a).length))
          = kws.map (fun _ => 5) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (guessAYBlockWord I v0 kws).length = 3 + 5 * kws.length := by
      show (guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_ew : (guessAYBlockWord I v0 kws)[3 + j * 5 + 2]? =
      some (⟨EventLabel.wt Tid.guessAY Loc.zAy'y (Val.cnt (kwj.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY) := by
    have hget := guessAYBlockWord_blockRest_pos I v0 kws j 2 kwj hkj (by norm_num)
    rw [hget]
    unfold guessAYBlockRestElems
    rfl
  refine ⟨hlen_ew, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zAy'y) (op := OpType.wt)
    hw1 hlen_ew hlabP_ew rfl rfl hcount_ew
  rwa [show G.nthEvent Tid.guessAY Loc.zAy'y OpType.wt (1 + j) = G.nthWrite Tid.guessAY Loc.zAy'y
    (j + 1) from by rw [Nat.add_comm]; rfl] at hewpos

/-- Eq. (15)'s `zAyy'`/`zAy'y` pair (`GuessAY`/`PrimeAY`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`guessAY_shape_inv`, `primeAY_shape_inv`). `GuessAY` skips its first
`zAyy'`-read, so its `j`-th `zAyy'`-read sits in iteration `j + 1`; both
locations have a single writer, so writer identification is
`writerTid_confined`. -/
theorem guessAY_primeAY_zAy_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.guessAY Tid.primeAY Loc.zAyy' Loc.zAy'y := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessAY_run_of_reaches I G hG
  obtain ⟨v0, js, kws, -, -, hkwsval, hσ1⟩ := guessAY_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := primeAY_run_of_reaches I G hG
  obtain ⟨M, vals, -, -, hvalsval, hσ2⟩ := primeAY_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessAY = (guessAYBlockWord I v0 kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAY, hσ1]
  have hw2 : G.threadWord Tid.primeAY = (primeAYBlockWord I vals).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeAY, hσ2]
  -- `primeAY`'s `i`-th `zAyy'`-write: value `(i+1) mod 4`, in block `vals[i]`.
  have hWp : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.primeAY Loc.zAyy' i = some w →
      (∃ c : Fin 4, w.val = Val.cnt c ∧ c.val = (i + 1) % 4) ∧ i < vals.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    have hf := (primeAYBlockWord_zAyy'_write_val I vals i).symm.trans hf
    rcases hv : vals[i]? with _ | v
    · rw [hv] at hf; exact nomatch hf
    · rw [hv] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hvv := hvalsval i hlt
      rw [hv] at hvv
      refine ⟨⟨⟨(i + 1) % 4, by omega⟩, ?_, rfl⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf, ← Option.some.inj hvv]
      rfl
  -- `guessAY`'s `j`-th `zAyy'`-read: value `(j+1) mod 4`, in block `kws[j]`.
  have hRp : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.guessAY Loc.zAyy' j = some r →
      (∃ c : Fin 4, r.val = Val.cnt c ∧ c.val = (j + 1) % 4) ∧ j < kws.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hr
    have hf := (guessAYBlockWord_zAyy'_read_val I v0 kws j).symm.trans hf
    rcases hk : kws[j]? with _ | kw
    · rw [hk] at hf; simp at hf
    · rw [hk] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨w', hkw⟩ := hkwsval j hlt
      rw [hk] at hkw
      have hkw1 : kw.1.val = (1 + j) % 4 := by rw [Option.some.inj hkw]
      refine ⟨⟨kw.1, ?_, by omega⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `guessAY`'s `i`-th `zAy'y`-write: value `(i+1) mod 4`, in block `kws[i-1]` for `i ≥ 1`.
  have hWq : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.guessAY Loc.zAy'y i = some w →
      (∃ c : Fin 4, w.val = Val.cnt c ∧ c.val = (i + 1) % 4) ∧
      ∀ i', i = i' + 1 → i' < kws.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hw
    rcases i with _ | i'
    · have hf := (guessAYBlockWord_zAy'y_write_val0 I v0 kws).symm.trans hf
      refine ⟨⟨1, ?_, rfl⟩, fun i' h => absurd h (by omega)⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
    · have hf := (guessAYBlockWord_zAy'y_write_val_succ I v0 kws i').symm.trans hf
      rcases hk : kws[i']? with _ | kw
      · rw [hk] at hf; simp at hf
      · rw [hk] at hf
        have hlt := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨w', hkw⟩ := hkwsval i' hlt
        rw [hk] at hkw
        have hkw1 : kw.1.val = (1 + i') % 4 := by rw [Option.some.inj hkw]
        refine ⟨⟨kw.1 + 1, ?_, ?_⟩, fun j h => by omega⟩
        · rw [Event.val, hlab, ← Option.some.inj hf]
          rfl
        · rw [Fin.val_add, hkw1]; simp; omega
  -- `primeAY`'s `j`-th `zAy'y`-read: value `(j+1) mod 4`, in block `vals[j]`.
  have hRq : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.primeAY Loc.zAy'y j = some r →
      (∃ c : Fin 4, r.val = Val.cnt c ∧ c.val = (j + 1) % 4) ∧ j < vals.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (primeAYBlockWord_zAy'y_read_val I vals j).symm.trans hf
    rcases hv : vals[j]? with _ | v
    · rw [hv] at hf; exact nomatch hf
    · rw [hv] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hvv := hvalsval j hlt
      rw [hv] at hvv
      refine ⟨⟨⟨(j + 1) % 4, by omega⟩, ?_, rfl⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf, ← Option.some.inj hvv]
      rfl
  have hval : ∀ {n : ℕ}, n < vals.length → ∃ v, vals[n]? = some v :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  have hkw : ∀ {n : ℕ}, n < kws.length → ∃ kw, kws[n]? = some kw :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWp hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRp hr
    rw [hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWq hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRq hr
    rw [hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.primeAY := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.guessAY := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · -- `guessAY`: `r(zAyy')` at `7+i*5` precedes `w(zAy'y)` at `5+(ℓ-1)*5`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (hRp hr).2
    obtain ⟨kw', hk'⟩ := hkw ((hWq hw).2 ℓ' rfl)
    obtain ⟨hlenR, hposR⟩ := guessAY_zAyy'_read_nthRead_pos I G hw1 i hk
    obtain ⟨hlenW, hposW⟩ := guessAY_zAy'y_write_nthWrite_pos I G hw1 ℓ' hk'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.guessAY hlenR hlenW (by omega)
  · -- `primeAY`: `r(zAy'y)` at `i*3+2` precedes `w(zAyy')` at `ℓ*3+1`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨v, hv⟩ := hval (hRq hr).2
    obtain ⟨v', hv'⟩ := hval (hWp hw).2
    obtain ⟨hlenR, hposR⟩ := primeAY_zAy'y_read_nthRead_pos I G hw2 i hv
    obtain ⟨hlenW, hposW⟩ := primeAY_zAyy'_write_nthWrite_pos I G hw2 ℓ hv'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.primeAY hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (n := i) (by have := (hWq hw).2 ℓ' rfl; omega)
    exact ⟨_, (guessAY_zAyy'_read_nthRead_pos I G hw1 i hk).2⟩
  · intro i ℓ w hw hiℓ
    obtain ⟨v, hv⟩ := hval (n := i) (by have := (hWp hw).2; omega)
    exact ⟨_, (primeAY_zAy'y_read_nthRead_pos I G hw2 i hv).2⟩

theorem no_skipping_guessAY_primeAY_zAyy' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeAY Loc.zAyy' i = some ew)
    (her : G.nthRead Tid.guessAY Loc.zAyy' K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((guessAY_primeAY_zAy_noSkipPair I G hG).no_skipping hG.1.1 K).1 hew her hrf

theorem no_skipping_guessAY_primeAY_zAy'y (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (n K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessAY Loc.zAy'y n = some ew)
    (her : G.nthRead Tid.primeAY Loc.zAy'y K = some er) (hrf : G.rf ew er) :
    n = K :=
  ((guessAY_primeAY_zAy_noSkipPair I G hG).no_skipping hG.1.1 K).2 hew her hrf

/-! ## Eq. (15)'s `zByy'`/`zBy'y` pair (`GuessBY`/`PrimeBY`)

As for `zAyy'`/`zAy'y`. -/
theorem guessBYBlockWord_zBy'y_write_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((guessBYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.guessBY Loc.zBy'y (Val.cnt 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY) := by
  unfold guessBYBlockWord
  rw [List.filter_append]
  have hb0 : (guessBYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBY Loc.zBy'y (Val.cnt 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `GuessBY`'s `zBy'y`-write value at filtered index `i + 1` (block
`kws[i]`). -/
theorem guessBYBlockWord_zBy'y_write_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((guessBYBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.guessBY Loc.zBy'y (Val.cnt (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
  unfold guessBYBlockWord
  rw [List.filter_append]
  have hb0 : (guessBYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBY Loc.zBy'y (Val.cnt 1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessBYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.guessBY Loc.zBy'y (Val.cnt (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.guessBY Loc.zBy'y (Val.cnt (kw.1 + 1)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBY)] := by
      intro kw
      unfold guessBYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

/-- `GuessBY`'s `zByy'`-read value at filtered index `k` (block `kws[k]`). -/
theorem guessBYBlockWord_zByy'_read_val (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (k : ℕ) :
    ((guessBYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.rd))[k]? =
      (kws[k]?).map (fun kw => (⟨EventLabel.rd Tid.guessBY Loc.zByy' (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
  unfold guessBYBlockWord
  rw [List.filter_append]
  have hb0 : (guessBYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.rd) =
      [] := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessBYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.guessBY Loc.zByy' (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.guessBY Loc.zByy' (Val.cnt kw.1), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBY)] := by
      intro kw
      unfold guessBYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.nil_append, List.getElem?_map]

/-- `PrimeBY`'s `zByy'`-write value at filtered position `j` is `vals[j]`. -/
theorem primeBYBlockWord_zByy'_write_val (I : PCPInstance) (vals : List (Val I)) (j : ℕ) :
    ((primeBYBlockWord I vals).filter (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.wt))[j]? =
      (vals[j]?).map (fun v => (⟨EventLabel.wt Tid.primeBY Loc.zByy' v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeBY)) := by
  have hone : ∀ v : Val I, (primeBYBlockElems I v).filter
      (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeBY Loc.zByy' v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeBY)] := by
    intro v
    unfold primeBYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeBYBlockWord I vals).filter (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.wt) =
      vals.map (fun v => (⟨EventLabel.wt Tid.primeBY Loc.zByy' v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeBY)) := by
    rw [primeBYBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ vals
  rw [hflat]
  exact List.getElem?_map ..

/-- `PrimeBY`'s `zBy'y`-read value at filtered position `j` is `vals[j]`. -/
theorem primeBYBlockWord_zBy'y_read_val (I : PCPInstance) (vals : List (Val I)) (j : ℕ) :
    ((primeBYBlockWord I vals).filter (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.rd))[j]? =
      (vals[j]?).map (fun v => (⟨EventLabel.rd Tid.primeBY Loc.zBy'y v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeBY)) := by
  have hone : ∀ v : Val I, (primeBYBlockElems I v).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeBY Loc.zBy'y v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeBY)] := by
    intro v
    unfold primeBYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflat : (primeBYBlockWord I vals).filter (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.rd) =
      vals.map (fun v => (⟨EventLabel.rd Tid.primeBY Loc.zBy'y v, rfl⟩ :
        ThreadLabel (domainOf I) Tid.primeBY)) := by
    rw [primeBYBlockWord_eq_flatMap, list_filter_flatMap_distrib]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ vals
  rw [hflat]
  exact List.getElem?_map ..

/-- Position of offset `p` of `GuessBY`'s block `n + 1` (`kws[n]`):
`3 + n * 5 + p`. -/
theorem guessBYBlockWord_blockRest_pos (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (n p : ℕ) (kw : Fin 4 × Option (Fin I.n))
    (hkw : kws[n]? = some kw) (hp : p < 5) :
    (guessBYBlockWord I v0 kws)[3 + n * 5 + p]? = (guessBYBlockRestElems I kw)[p]? := by
  have heq : guessBYBlockWord I v0 kws =
      guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I) := rfl
  have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
  rw [heq, List.getElem?_append_right (by rw [hb0len]; omega), hb0len]
  have hi : 3 + n * 5 + p - 3 = n * 5 + p := by omega
  rw [hi]
  exact flatMap_uniform_getElem_fwd (guessBYBlockRestElems I) 5 (fun _ => rfl) kws n p kw hkw hp

/-- `PrimeBY`'s `n`-th `zByy'`-write is at position `n*3+1` of
`G.threadEvents Tid.primeBY`. -/
theorem primeBY_zByy'_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {vals : List (Val I)}
    (hw2 : G.threadWord Tid.primeBY = (primeBYBlockWord I vals).map some)
    (n : ℕ) {v : Val I} (hv : vals[n]? = some v) :
    ∃ hlen : n * 3 + 1 < (G.threadEvents Tid.primeBY).length,
      G.nthWrite Tid.primeBY Loc.zByy' n =
        some ((G.threadEvents Tid.primeBY)[n * 3 + 1]'hlen).1 := by
  have hnlen : n < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hsplit := list_take_flatMap_uniform_offset (primeBYBlockElems I) 3 (fun _ => rfl)
    vals n 1 v hv (by norm_num)
  have hpartial : ((primeBYBlockElems I v).take 1).filter
      (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.wt) = [] := by
    unfold primeBYBlockElems
    rfl
  have hone_w : ∀ v' : Val I, (primeBYBlockElems I v').filter
      (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.primeBY Loc.zByy' v', rfl⟩ : ThreadLabel (domainOf I) Tid.primeBY)] := by
    intro v'
    unfold primeBYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_w : (((primeBYBlockWord I vals).take (n * 3 + 1)).filter
      (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.wt)).length = n := by
    rw [primeBYBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_w]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeBY).length = (primeBYBlockWord I vals).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeBYBlockWord I vals).length = 3 * vals.length := by
    rw [primeBYBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (vals.map (fun a => (primeBYBlockElems I a).length))
        = vals.map (fun _ => 3) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_w : n * 3 + 1 < (G.threadEvents Tid.primeBY).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_w : (primeBYBlockWord I vals)[n * 3 + 1]? =
      some (⟨EventLabel.wt Tid.primeBY Loc.zByy' v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeBY) := by
    rw [primeBYBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeBYBlockElems I) 3 (fun _ => rfl) vals n
      1 v hv (by norm_num)
    rw [hget]
    unfold primeBYBlockElems
    rfl
  refine ⟨hlen_w, ?_⟩
  have hwpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zByy') (op := OpType.wt)
    hw2 hlen_w hlabP_w rfl rfl hcount_w
  rwa [show G.nthEvent Tid.primeBY Loc.zByy' OpType.wt n = G.nthWrite Tid.primeBY Loc.zByy' n
    from rfl] at hwpos

/-- `PrimeBY`'s `n`-th `zBy'y`-read is at position `n*3+2` of
`G.threadEvents Tid.primeBY`. -/
theorem primeBY_zBy'y_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {vals : List (Val I)}
    (hw2 : G.threadWord Tid.primeBY = (primeBYBlockWord I vals).map some)
    (n : ℕ) {v : Val I} (hv : vals[n]? = some v) :
    ∃ hlen : n * 3 + 2 < (G.threadEvents Tid.primeBY).length,
      G.nthRead Tid.primeBY Loc.zBy'y n =
        some ((G.threadEvents Tid.primeBY)[n * 3 + 2]'hlen).1 := by
  have hnlen : n < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hsplit := list_take_flatMap_uniform_offset (primeBYBlockElems I) 3 (fun _ => rfl)
    vals n 2 v hv (by norm_num)
  have hpartial : ((primeBYBlockElems I v).take 2).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.rd) = [] := by
    unfold primeBYBlockElems
    rfl
  have hone : ∀ v' : Val I, (primeBYBlockElems I v').filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.primeBY Loc.zBy'y v', rfl⟩ : ThreadLabel (domainOf I) Tid.primeBY)] := by
    intro v'
    unfold primeBYBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((primeBYBlockWord I vals).take (n * 3 + 2)).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.rd)).length = n := by
    rw [primeBYBlockWord_eq_flatMap, hsplit, List.filter_append, hpartial, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq2 : (G.threadEvents Tid.primeBY).length = (primeBYBlockWord I vals).length := by
    have hlc := congrArg List.length hw2
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenw2 : (primeBYBlockWord I vals).length = 3 * vals.length := by
    rw [primeBYBlockWord_eq_flatMap, List.length_flatMap]
    have heq1 : (vals.map (fun a => (primeBYBlockElems I a).length))
        = vals.map (fun _ => 3) := List.map_congr_left (fun a _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hlen_er : n * 3 + 2 < (G.threadEvents Tid.primeBY).length := by
    rw [hlenEq2, hlenw2]
    nlinarith [hnlen]
  have hlabP_er : (primeBYBlockWord I vals)[n * 3 + 2]? =
      some (⟨EventLabel.rd Tid.primeBY Loc.zBy'y v, rfl⟩ : ThreadLabel (domainOf I) Tid.primeBY) := by
    rw [primeBYBlockWord_eq_flatMap]
    have hget := flatMap_uniform_getElem_fwd (primeBYBlockElems I) 3 (fun _ => rfl) vals n
      2 v hv (by norm_num)
    rw [hget]
    unfold primeBYBlockElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zBy'y) (op := OpType.rd)
    hw2 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.primeBY Loc.zBy'y OpType.rd n = G.nthRead Tid.primeBY Loc.zBy'y n
    from rfl] at herpos

/-- `GuessBY`'s `j`-th `zByy'`-read (block `kws[j]`) is at position `7+j*5`
of `G.threadEvents Tid.guessBY`. -/
theorem guessBY_zByy'_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.guessBY = (guessBYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 7 + j * 5 < (G.threadEvents Tid.guessBY).length,
      G.nthRead Tid.guessBY Loc.zByy' j =
        some ((G.threadEvents Tid.guessBY)[7 + j * 5]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hone_er : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessBY Loc.zByy' (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    intro kw
    unfold guessBYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((guessBYBlockWord I v0 kws).take (7 + j * 5)).filter
      (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.rd)).length = j := by
    have heq : guessBYBlockWord I v0 kws =
        guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I) := rfl
    have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
    have hle3 : (guessBYBlock0Elems I v0).length ≤ 7 + j * 5 := by rw [hb0len]; omega
    have hb0nil : (guessBYBlock0Elems I v0).filter
        (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.rd) = [] := by
      unfold guessBYBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hsplit := list_take_flatMap_uniform_offset (guessBYBlockRestElems I) 5 (fun _ => rfl)
      kws j 4 kwj hkj (by norm_num)
    have hpartial : ((guessBYBlockRestElems I kwj).take 4).filter
        (fun l => l.1.loc = Loc.zByy' ∧ l.1.op = OpType.rd) = [] := by
      unfold guessBYBlockRestElems
      rfl
    have hsub : 7 + j * 5 - (guessBYBlock0Elems I v0).length = j * 5 + 4 := by
      rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle3, hsub, hsplit, List.filter_append,
      List.filter_append, hb0nil, hpartial, List.nil_append, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_er]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.guessBY).length = (guessBYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_er : 7 + j * 5 < (G.threadEvents Tid.guessBY).length := by
    have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
    have hbrlen : (kws.flatMap (guessBYBlockRestElems I)).length = 5 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (guessBYBlockRestElems I a).length))
          = kws.map (fun _ => 5) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (guessBYBlockWord I v0 kws).length = 3 + 5 * kws.length := by
      show (guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_er : (guessBYBlockWord I v0 kws)[7 + j * 5]? =
      some (⟨EventLabel.rd Tid.guessBY Loc.zByy' (Val.cnt kwj.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY) := by
    have hget := guessBYBlockWord_blockRest_pos I v0 kws j 4 kwj hkj (by norm_num)
    rw [show 3 + j * 5 + 4 = 7 + j * 5 from by omega] at hget
    rw [hget]
    unfold guessBYBlockRestElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zByy') (op := OpType.rd)
    hw1 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.guessBY Loc.zByy' OpType.rd j = G.nthRead Tid.guessBY Loc.zByy' j
    from rfl] at herpos

/-- `GuessBY`'s `(j+1)`-th `zBy'y`-write (block `kws[j]`) is at position
`3+j*5+2` of `G.threadEvents Tid.guessBY`. -/
theorem guessBY_zBy'y_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.guessBY = (guessBYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 3 + j * 5 + 2 < (G.threadEvents Tid.guessBY).length,
      G.nthWrite Tid.guessBY Loc.zBy'y (j + 1) =
        some ((G.threadEvents Tid.guessBY)[3 + j * 5 + 2]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hb0count : ((guessBYBlock0Elems I v0).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt)).length = 1 := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rfl
  have hone_ew : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBY Loc.zBy'y (Val.cnt (kw.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    intro kw
    unfold guessBYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hpartial0 : ((guessBYBlockRestElems I kwj).take 2).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt) = [] := by
    unfold guessBYBlockRestElems
    rfl
  have hcount_ew : (((guessBYBlockWord I v0 kws).take (3 + j * 5 + 2)).filter
      (fun l => l.1.loc = Loc.zBy'y ∧ l.1.op = OpType.wt)).length = 1 + j := by
    have heq : guessBYBlockWord I v0 kws =
        guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I) := rfl
    have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
    have hsub : 3 + j * 5 + 2 - 3 = j * 5 + 2 := by omega
    have hle : (guessBYBlock0Elems I v0).length ≤ 3 + j * 5 + 2 := by rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle, hb0len, hsub,
      list_take_flatMap_uniform_offset (guessBYBlockRestElems I) 5 (fun _ => rfl) kws j 2 kwj hkj
        (by norm_num)]
    simp only [List.filter_append, List.length_append, hb0count, hpartial0, List.filter_nil,
      List.length_nil, Nat.add_zero]
    rw [list_filter_flatMap_distrib]
    simp only [hone_ew]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.guessBY).length = (guessBYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_ew : 3 + j * 5 + 2 < (G.threadEvents Tid.guessBY).length := by
    have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
    have hbrlen : (kws.flatMap (guessBYBlockRestElems I)).length = 5 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (guessBYBlockRestElems I a).length))
          = kws.map (fun _ => 5) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (guessBYBlockWord I v0 kws).length = 3 + 5 * kws.length := by
      show (guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_ew : (guessBYBlockWord I v0 kws)[3 + j * 5 + 2]? =
      some (⟨EventLabel.wt Tid.guessBY Loc.zBy'y (Val.cnt (kwj.1 + 1)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY) := by
    have hget := guessBYBlockWord_blockRest_pos I v0 kws j 2 kwj hkj (by norm_num)
    rw [hget]
    unfold guessBYBlockRestElems
    rfl
  refine ⟨hlen_ew, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zBy'y) (op := OpType.wt)
    hw1 hlen_ew hlabP_ew rfl rfl hcount_ew
  rwa [show G.nthEvent Tid.guessBY Loc.zBy'y OpType.wt (1 + j) = G.nthWrite Tid.guessBY Loc.zBy'y
    (j + 1) from by rw [Nat.add_comm]; rfl] at hewpos

/-- Eq. (15)'s `zByy'`/`zBy'y` pair (`GuessBY`/`PrimeBY`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`guessBY_shape_inv`, `primeBY_shape_inv`). `GuessBY` skips its first
`zByy'`-read, so its `j`-th `zByy'`-read sits in iteration `j + 1`; both
locations have a single writer, so writer identification is
`writerTid_confined`. -/
theorem guessBY_primeBY_zBy_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.guessBY Tid.primeBY Loc.zByy' Loc.zBy'y := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessBY_run_of_reaches I G hG
  obtain ⟨v0, js, kws, -, -, hkwsval, hσ1⟩ := guessBY_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := primeBY_run_of_reaches I G hG
  obtain ⟨M, vals, -, -, hvalsval, hσ2⟩ := primeBY_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessBY = (guessBYBlockWord I v0 kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBY, hσ1]
  have hw2 : G.threadWord Tid.primeBY = (primeBYBlockWord I vals).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeBY, hσ2]
  -- `primeBY`'s `i`-th `zByy'`-write: value `(i+1) mod 4`, in block `vals[i]`.
  have hWp : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.primeBY Loc.zByy' i = some w →
      (∃ c : Fin 4, w.val = Val.cnt c ∧ c.val = (i + 1) % 4) ∧ i < vals.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    have hf := (primeBYBlockWord_zByy'_write_val I vals i).symm.trans hf
    rcases hv : vals[i]? with _ | v
    · rw [hv] at hf; exact nomatch hf
    · rw [hv] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hvv := hvalsval i hlt
      rw [hv] at hvv
      refine ⟨⟨⟨(i + 1) % 4, by omega⟩, ?_, rfl⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf, ← Option.some.inj hvv]
      rfl
  -- `guessBY`'s `j`-th `zByy'`-read: value `(j+1) mod 4`, in block `kws[j]`.
  have hRp : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.guessBY Loc.zByy' j = some r →
      (∃ c : Fin 4, r.val = Val.cnt c ∧ c.val = (j + 1) % 4) ∧ j < kws.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hr
    have hf := (guessBYBlockWord_zByy'_read_val I v0 kws j).symm.trans hf
    rcases hk : kws[j]? with _ | kw
    · rw [hk] at hf; simp at hf
    · rw [hk] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨w', hkw⟩ := hkwsval j hlt
      rw [hk] at hkw
      have hkw1 : kw.1.val = (1 + j) % 4 := by rw [Option.some.inj hkw]
      refine ⟨⟨kw.1, ?_, by omega⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `guessBY`'s `i`-th `zBy'y`-write: value `(i+1) mod 4`, in block `kws[i-1]` for `i ≥ 1`.
  have hWq : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.guessBY Loc.zBy'y i = some w →
      (∃ c : Fin 4, w.val = Val.cnt c ∧ c.val = (i + 1) % 4) ∧
      ∀ i', i = i' + 1 → i' < kws.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw1 hw
    rcases i with _ | i'
    · have hf := (guessBYBlockWord_zBy'y_write_val0 I v0 kws).symm.trans hf
      refine ⟨⟨1, ?_, rfl⟩, fun i' h => absurd h (by omega)⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
    · have hf := (guessBYBlockWord_zBy'y_write_val_succ I v0 kws i').symm.trans hf
      rcases hk : kws[i']? with _ | kw
      · rw [hk] at hf; simp at hf
      · rw [hk] at hf
        have hlt := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨w', hkw⟩ := hkwsval i' hlt
        rw [hk] at hkw
        have hkw1 : kw.1.val = (1 + i') % 4 := by rw [Option.some.inj hkw]
        refine ⟨⟨kw.1 + 1, ?_, ?_⟩, fun j h => by omega⟩
        · rw [Event.val, hlab, ← Option.some.inj hf]
          rfl
        · rw [Fin.val_add, hkw1]; simp; omega
  -- `primeBY`'s `j`-th `zBy'y`-read: value `(j+1) mod 4`, in block `vals[j]`.
  have hRq : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.primeBY Loc.zBy'y j = some r →
      (∃ c : Fin 4, r.val = Val.cnt c ∧ c.val = (j + 1) % 4) ∧ j < vals.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (primeBYBlockWord_zBy'y_read_val I vals j).symm.trans hf
    rcases hv : vals[j]? with _ | v
    · rw [hv] at hf; exact nomatch hf
    · rw [hv] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hv).1
      have hvv := hvalsval j hlt
      rw [hv] at hvv
      refine ⟨⟨⟨(j + 1) % 4, by omega⟩, ?_, rfl⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf, ← Option.some.inj hvv]
      rfl
  have hval : ∀ {n : ℕ}, n < vals.length → ∃ v, vals[n]? = some v :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  have hkw : ∀ {n : ℕ}, n < kws.length → ∃ kw, kws[n]? = some kw :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWp hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRp hr
    rw [hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨⟨c, hc, hcv⟩, -⟩ := hWq hw
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRq hr
    rw [hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.primeBY := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.guessBY := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · -- `guessBY`: `r(zByy')` at `7+i*5` precedes `w(zBy'y)` at `5+(ℓ-1)*5`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (hRp hr).2
    obtain ⟨kw', hk'⟩ := hkw ((hWq hw).2 ℓ' rfl)
    obtain ⟨hlenR, hposR⟩ := guessBY_zByy'_read_nthRead_pos I G hw1 i hk
    obtain ⟨hlenW, hposW⟩ := guessBY_zBy'y_write_nthWrite_pos I G hw1 ℓ' hk'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.guessBY hlenR hlenW (by omega)
  · -- `primeBY`: `r(zBy'y)` at `i*3+2` precedes `w(zByy')` at `ℓ*3+1`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨v, hv⟩ := hval (hRq hr).2
    obtain ⟨v', hv'⟩ := hval (hWp hw).2
    obtain ⟨hlenR, hposR⟩ := primeBY_zBy'y_read_nthRead_pos I G hw2 i hv
    obtain ⟨hlenW, hposW⟩ := primeBY_zByy'_write_nthWrite_pos I G hw2 ℓ hv'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.primeBY hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (n := i) (by have := (hWq hw).2 ℓ' rfl; omega)
    exact ⟨_, (guessBY_zByy'_read_nthRead_pos I G hw1 i hk).2⟩
  · intro i ℓ w hw hiℓ
    obtain ⟨v, hv⟩ := hval (n := i) (by have := (hWp hw).2; omega)
    exact ⟨_, (primeBY_zBy'y_read_nthRead_pos I G hw2 i hv).2⟩

theorem no_skipping_guessBY_primeBY_zByy' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeBY Loc.zByy' i = some ew)
    (her : G.nthRead Tid.guessBY Loc.zByy' K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((guessBY_primeBY_zBy_noSkipPair I G hG).no_skipping hG.1.1 K).1 hew her hrf

theorem no_skipping_guessBY_primeBY_zBy'y (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (n K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessBY Loc.zBy'y n = some ew)
    (her : G.nthRead Tid.primeBY Loc.zBy'y K = some er) (hrf : G.rf ew er) :
    n = K :=
  ((guessBY_primeBY_zBy_noSkipPair I G hG).no_skipping hG.1.1 K).2 hew her hrf

/-! ## Eq. (15)'s bridge pair `zAxy`/`ellAyx` (`GuessAX`/`GuessAY`)

`z_α^{x,y}` (`z_α^{x,y}`, `Loc.zAxy`) and `ℓ_α^{y,x}` (`ℓ_α^{y,x}`, `Loc.ellAyx`)
are two bridge locations.

`GuessAX` writes `zAxy` at the start and reads `ellAyx` at the end of each
outer iteration, so positions are given by `nestedOuterStart`: the
`ellAyx`-read of outer iteration `m + 1` is at
`nestedOuterStart ks N (m + 2) - 1`, for every `m ≤ N` including the
terminating iteration.

`GuessAY` writes `ellAyx` in every iteration, with the same counter as
`zAy'y`, and reads `zAxy` from block 1 on (block 0 has no reads); the value it
expects at `zAxy` is `Val.cnt kw.1`, as for `zAyy'`. -/

/-- The `zAxy`-write is the only `(zAxy, wt)` event of an outer block
`guessAXOuterBlockElems`, at its head. -/
theorem guessAXOuterBlockElems_zAxy_write_filter (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) :
    (guessAXOuterBlockElems I b vs).filter (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
  have hinner_nil : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) = [] := by
    intro a
    unfold guessAXInnerBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflatnil : ∀ l : List (Val I × Val I × Val I),
      l.flatMap (fun (_ : Val I × Val I × Val I) =>
        ([] : List (ThreadLabel (domainOf I) Tid.guessAX))) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons _ t ih => simp [List.flatMap_cons, ih]
  have htail_nil : (vs.flatMap (guessAXInnerBlockElems I) ++
      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)]).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) = [] := by
    rw [List.filter_append, list_filter_flatMap_distrib]
    simp only [hinner_nil]
    rw [hflatnil vs, List.nil_append]
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  unfold guessAXOuterBlockElems
  rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), htail_nil]

/-- The `ellAyx`-read is the only `(ellAyx, rd)` event of an outer block
`guessAXOuterBlockElems`, at its end. -/
theorem guessAXOuterBlockElems_ellAyx_read_filter (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) :
    (guessAXOuterBlockElems I b vs).filter (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
  have hinner_nil : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) = [] := by
    intro a
    unfold guessAXInnerBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflatnil : ∀ l : List (Val I × Val I × Val I),
      l.flatMap (fun (_ : Val I × Val I × Val I) =>
        ([] : List (ThreadLabel (domainOf I) Tid.guessAX))) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons _ t ih => simp [List.flatMap_cons, ih]
  unfold guessAXOuterBlockElems
  rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_append,
    list_filter_flatMap_distrib]
  simp only [hinner_nil]
  rw [hflatnil vs, List.nil_append,
    List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]

/-- The `zAxy`-write of outer iteration `0` is at position `0` of
`guessAXBlockWord`. -/
theorem guessAXBlockWord_zAxy_write_pos0 (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[0]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) :=
  rfl

/-- The `ellAyx`-read of outer iteration `0` is at position `3 + K0 * 3` of
`guessAXBlockWord`. -/
theorem guessAXBlockWord_ellAyx_read_pos0 (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I)) (hinner0len : inner0Rest.length = K0)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[3 + K0 * 3]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) := by
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I)) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 3 + K0 * 3 := by
    rw [List.length_append]
    have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
  have hfulllen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
    rw [List.length_append, hleadlen, List.length_singleton]; omega
  rw [heq, List.getElem?_append_left (by rw [hfulllen]; omega),
    List.getElem?_append_right (by rw [hleadlen]), hleadlen, Nat.sub_self]
  rfl

/-- The `zAxy`-write of outer iteration `m + 1` (`outerRest[m]`) is at
position `nestedOuterStart ks N (m + 1)`. -/
theorem guessAXBlockWord_zAxy_write_outerPos (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hmbv : outerRest[m]? = some (b, vs)) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N (m + 1)]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) := by
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hlenL := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter houterLast
    m (by omega)
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hge : nestedOuterStart ks N (m + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N m
    have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    rwa [hgetD0] at hh
  have hposeq : nestedOuterStart ks N (m + 1) = 4 + K0 * 3 +
      ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length := by
    rw [hlenL, hstartm]; omega
  rw [heq, hposeq, List.getElem?_append_right (by omega), hleadlen,
    show 4 + K0 * 3 + ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
      - (4 + K0 * 3) = ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
      + 0 from by omega]
  have hqlt : (0 : ℕ) < (guessAXOuterBlockElems I b vs).length := by
    rw [guessAXOuterBlockElems_length]; omega
  rw [list_take_flatMap_offset_getElem (fun q => guessAXOuterBlockElems I q.1 q.2) outerRest m 0
    (b, vs) hmbv hqlt]
  rfl

/-- The `ellAyx`-read of outer iteration `m + 1` (`outerRest[m]`) is at
position `nestedOuterStart ks N (m + 2) - 1`, for every `m ≤ N`. -/
theorem guessAXBlockWord_ellAyx_read_outerPos (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hmbv : outerRest[m]? = some (b, vs)) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N (m + 2) - 1]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) := by
  have hstart := guessAXBlockWord_zAxy_write_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len ks N hks hK0 houterLen houter houterLast m hm b vs hmbv
  have hlen : (guessAXOuterBlockElems I b vs).length = 3 * vs.length + 2 :=
    guessAXOuterBlockElems_length I b vs
  have hvslen : vs.length = if m = N then 1 else (ks[m + 1]?).getD 0 + 1 := by
    by_cases hmN : m = N
    · subst hmN
      obtain ⟨b', vs', hbv', hvl'⟩ := houterLast
      rw [hbv'] at hmbv
      have heq2 : vs' = vs := congrArg Prod.snd (Option.some.inj hmbv)
      rw [if_pos rfl, ← heq2]; exact hvl'
    · obtain ⟨b', vs', km, hbv', hks', hvl'⟩ := houter m (by omega)
      rw [hbv'] at hmbv
      have heq2 : vs' = vs := congrArg Prod.snd (Option.some.inj hmbv)
      rw [if_neg hmN, ← heq2, hvl', hks']
      rfl
  have hstep : nestedOuterStart ks N (m + 2) = nestedOuterStart ks N (m + 1) +
      nestedOuterLen ks N (m + 1) := nestedOuterStart_succ ks N (m + 1)
  have hnol : nestedOuterLen ks N (m + 1) = 3 * vs.length + 2 := by
    unfold nestedOuterLen
    by_cases hmN : m = N
    · subst hmN
      rw [if_pos rfl]
      rw [if_pos rfl] at hvslen
      omega
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [if_neg hmN] at hvslen
      have hgd : ks.getD (m + 1) 0 = (ks[m + 1]?).getD 0 := rfl
      omega
  have hlastpos : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N (m + 1) +
      (3 * vs.length + 2 - 1)]? = (guessAXOuterBlockElems I b vs)[3 * vs.length + 2 - 1]? := by
    have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
        (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessAXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
        outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
    have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessAXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
      rw [List.length_append, List.length_append]
      have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
        rw [List.length_flatMap]
        have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
            inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
        rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
      simp only [List.length_cons, List.length_nil, hinner]
      omega
    have hlenL := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter houterLast
      m (by omega)
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N (m + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N m
      have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD0] at hh
    have hposeq : nestedOuterStart ks N (m + 1) = 4 + K0 * 3 +
        ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length := by
      rw [hlenL, hstartm]; omega
    rw [heq, hposeq, List.getElem?_append_right (by omega), hleadlen,
      show 4 + K0 * 3 + ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (3 * vs.length + 2 - 1) - (4 + K0 * 3)
        = ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        + (3 * vs.length + 2 - 1) from by omega]
    have hqlt : 3 * vs.length + 2 - 1 < (guessAXOuterBlockElems I b vs).length := by
      rw [guessAXOuterBlockElems_length]; omega
    exact list_take_flatMap_offset_getElem (fun q => guessAXOuterBlockElems I q.1 q.2) outerRest m
      (3 * vs.length + 2 - 1) (b, vs) hmbv hqlt
  have hidx : nestedOuterStart ks N (m + 2) - 1 =
      nestedOuterStart ks N (m + 1) + (3 * vs.length + 2 - 1) := by
    rw [hstep, hnol]; omega
  rw [hidx, hlastpos]
  have hidx2 : 3 * vs.length + 2 - 1 = 3 * vs.length + 1 := by omega
  rw [hidx2]
  unfold guessAXOuterBlockElems
  rw [show (3 * vs.length + 1 : ℕ) = (3 * vs.length) + 1 from rfl, List.getElem?_cons_succ]
  have hflen : (vs.flatMap (guessAXInnerBlockElems I)).length = 3 * vs.length := by
    rw [List.length_flatMap]
    have heq1 : (vs.map (fun a => (guessAXInnerBlockElems I a).length)) = vs.map (fun _ => 3) :=
      List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  rw [List.getElem?_append_right (by omega), hflen, Nat.sub_self]
  rfl

/-- `GuessAY`'s `ellAyx`-write value at filtered index `0` (block 0). -/
theorem guessAYBlockWord_ellAyx_write_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((guessAYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.guessAY Loc.ellAyx (Val.cntAux 1 (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY) := by
  unfold guessAYBlockWord
  rw [List.filter_append]
  have hb0 : (guessAYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAY Loc.ellAyx (Val.cntAux 1 (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `GuessAY`'s `ellAyx`-write value at filtered index `i + 1` (block
`kws[i]`). -/
theorem guessAYBlockWord_ellAyx_write_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((guessAYBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.guessAY Loc.ellAyx (Val.cntAux (kw.1 + 1) kw.2),
        rfl⟩ : ThreadLabel (domainOf I) Tid.guessAY)) := by
  unfold guessAYBlockWord
  rw [List.filter_append]
  have hb0 : (guessAYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAY Loc.ellAyx (Val.cntAux 1 (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessAYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.guessAY Loc.ellAyx (Val.cntAux (kw.1 + 1) kw.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.guessAY Loc.ellAyx (Val.cntAux (kw.1 + 1) kw.2), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAY)] := by
      intro kw
      unfold guessAYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

/-- `GuessAY`'s `zAxy`-read value at filtered index `k` (block `kws[k]`;
block 0 has none). -/
theorem guessAYBlockWord_zAxy_read_val (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (k : ℕ) :
    ((guessAYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.rd))[k]? =
      (kws[k]?).map (fun kw => (⟨EventLabel.rd Tid.guessAY Loc.zAxy (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
  unfold guessAYBlockWord
  rw [List.filter_append]
  have hb0 : (guessAYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.rd) =
      [] := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessAYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.guessAY Loc.zAxy (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.guessAY Loc.zAxy (Val.cnt kw.1), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAY)] := by
      intro kw
      unfold guessAYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.nil_append, List.getElem?_map]

/-- `GuessAY`'s `(j + 1)`-th `ellAyx`-write (block `kws[j]`) is at position
`3 + j * 5 + 1` of `G.threadEvents Tid.guessAY`. -/
theorem guessAY_ellAyx_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.guessAY = (guessAYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 3 + j * 5 + 1 < (G.threadEvents Tid.guessAY).length,
      G.nthWrite Tid.guessAY Loc.ellAyx (j + 1) =
        some ((G.threadEvents Tid.guessAY)[3 + j * 5 + 1]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hb0count : ((guessAYBlock0Elems I v0).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt)).length = 1 := by
    unfold guessAYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rfl
  have hone_ew : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAY Loc.ellAyx (Val.cntAux (kw.1 + 1) kw.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    intro kw
    unfold guessAYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hpartial0 : ((guessAYBlockRestElems I kwj).take 1).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt) = [] := by
    unfold guessAYBlockRestElems
    rfl
  have hcount_ew : (((guessAYBlockWord I v0 kws).take (3 + j * 5 + 1)).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.wt)).length = 1 + j := by
    have heq : guessAYBlockWord I v0 kws =
        guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I) := rfl
    have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
    have hsub : 3 + j * 5 + 1 - 3 = j * 5 + 1 := by omega
    have hle : (guessAYBlock0Elems I v0).length ≤ 3 + j * 5 + 1 := by rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle, hb0len, hsub,
      list_take_flatMap_uniform_offset (guessAYBlockRestElems I) 5 (fun _ => rfl) kws j 1 kwj hkj
        (by norm_num)]
    simp only [List.filter_append, List.length_append, hb0count, hpartial0, List.filter_nil,
      List.length_nil, Nat.add_zero]
    rw [list_filter_flatMap_distrib]
    simp only [hone_ew]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.guessAY).length = (guessAYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_ew : 3 + j * 5 + 1 < (G.threadEvents Tid.guessAY).length := by
    have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
    have hbrlen : (kws.flatMap (guessAYBlockRestElems I)).length = 5 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (guessAYBlockRestElems I a).length))
          = kws.map (fun _ => 5) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (guessAYBlockWord I v0 kws).length = 3 + 5 * kws.length := by
      show (guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_ew : (guessAYBlockWord I v0 kws)[3 + j * 5 + 1]? =
      some (⟨EventLabel.wt Tid.guessAY Loc.ellAyx (Val.cntAux (kwj.1 + 1) kwj.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY) := by
    have hget := guessAYBlockWord_blockRest_pos I v0 kws j 1 kwj hkj (by norm_num)
    rw [hget]
    unfold guessAYBlockRestElems
    rfl
  refine ⟨hlen_ew, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.ellAyx) (op := OpType.wt)
    hw1 hlen_ew hlabP_ew rfl rfl hcount_ew
  rwa [show G.nthEvent Tid.guessAY Loc.ellAyx OpType.wt (1 + j) = G.nthWrite Tid.guessAY Loc.ellAyx
    (j + 1) from by rw [Nat.add_comm]; rfl] at hewpos

/-- `GuessAY`'s `j`-th `zAxy`-read (block `kws[j]`) is at position
`3 + j * 5 + 3` of `G.threadEvents Tid.guessAY`. -/
theorem guessAY_zAxy_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.guessAY = (guessAYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 3 + j * 5 + 3 < (G.threadEvents Tid.guessAY).length,
      G.nthRead Tid.guessAY Loc.zAxy j =
        some ((G.threadEvents Tid.guessAY)[3 + j * 5 + 3]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hone_er : ∀ kw : Fin 4 × Option (Fin I.n), (guessAYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessAY Loc.zAxy (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY)] := by
    intro kw
    unfold guessAYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((guessAYBlockWord I v0 kws).take (3 + j * 5 + 3)).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.rd)).length = j := by
    have heq : guessAYBlockWord I v0 kws =
        guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I) := rfl
    have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
    have hle3 : (guessAYBlock0Elems I v0).length ≤ 3 + j * 5 + 3 := by rw [hb0len]; omega
    have hb0nil : (guessAYBlock0Elems I v0).filter
        (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.rd) = [] := by
      unfold guessAYBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hsplit := list_take_flatMap_uniform_offset (guessAYBlockRestElems I) 5 (fun _ => rfl)
      kws j 3 kwj hkj (by norm_num)
    have hpartial : ((guessAYBlockRestElems I kwj).take 3).filter
        (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.rd) = [] := by
      unfold guessAYBlockRestElems
      rfl
    have hsub : 3 + j * 5 + 3 - (guessAYBlock0Elems I v0).length = j * 5 + 3 := by
      rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle3, hsub, hsplit, List.filter_append,
      List.filter_append, hb0nil, hpartial, List.nil_append, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_er]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.guessAY).length = (guessAYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_er : 3 + j * 5 + 3 < (G.threadEvents Tid.guessAY).length := by
    have hb0len : (guessAYBlock0Elems I v0).length = 3 := rfl
    have hbrlen : (kws.flatMap (guessAYBlockRestElems I)).length = 5 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (guessAYBlockRestElems I a).length))
          = kws.map (fun _ => 5) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (guessAYBlockWord I v0 kws).length = 3 + 5 * kws.length := by
      show (guessAYBlock0Elems I v0 ++ kws.flatMap (guessAYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_er : (guessAYBlockWord I v0 kws)[3 + j * 5 + 3]? =
      some (⟨EventLabel.rd Tid.guessAY Loc.zAxy (Val.cnt kwj.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAY) := by
    have hget := guessAYBlockWord_blockRest_pos I v0 kws j 3 kwj hkj (by norm_num)
    rw [hget]
    unfold guessAYBlockRestElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zAxy) (op := OpType.rd)
    hw1 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.guessAY Loc.zAxy OpType.rd j = G.nthRead Tid.guessAY Loc.zAxy j
    from rfl] at herpos

/-- The first `m` blocks of `outerRest` contain `m` `zAxy`-writes. -/
theorem guessAXOuterRest_zAxy_write_take_count (I : PCPInstance)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    ∀ m, m ≤ outerRest.length →
      (((outerRest.take m).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)).filter
        (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt)).length = m := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
      have hmlen : m ≤ outerRest.length := by omega
      have ihm := ih hmlen
      have hmlt : m < outerRest.length := by omega
      have hget : outerRest[m]? = some (outerRest[m]'hmlt) := List.getElem?_eq_getElem hmlt
      rw [List.take_add_one, hget]
      simp only [Option.toList_some, List.flatMap_append, List.filter_append, List.length_append]
      rw [ihm]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [guessAXOuterBlockElems_zAxy_write_filter I (outerRest[m]'hmlt).1 (outerRest[m]'hmlt).2]
      rfl

/-- The first `m` blocks of `outerRest` contain `m` `ellAyx`-reads. -/
theorem guessAXOuterRest_ellAyx_read_take_count (I : PCPInstance)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    ∀ m, m ≤ outerRest.length →
      (((outerRest.take m).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)).filter
        (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd)).length = m := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
      have hmlen : m ≤ outerRest.length := by omega
      have ihm := ih hmlen
      have hmlt : m < outerRest.length := by omega
      have hget : outerRest[m]? = some (outerRest[m]'hmlt) := List.getElem?_eq_getElem hmlt
      rw [List.take_add_one, hget]
      simp only [Option.toList_some, List.flatMap_append, List.filter_append, List.length_append]
      rw [ihm]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [guessAXOuterBlockElems_ellAyx_read_filter I (outerRest[m]'hmlt).1 (outerRest[m]'hmlt).2]
      rfl

/-- `GuessAX`'s `0`-th `zAxy`-write is at position `0` of
`G.threadEvents Tid.guessAX`. -/
theorem guessAX_zAxy_write_nthWrite_pos0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some) :
    ∃ hlen : (0 : ℕ) < (G.threadEvents Tid.guessAX).length,
      G.nthWrite Tid.guessAX Loc.zAxy 0 =
        some ((G.threadEvents Tid.guessAX)[(0 : ℕ)]'hlen).1 := by
  have hlabP0 := guessAXBlockWord_zAxy_write_pos0 I v1 v2 vB0 inner0Rest outerRest
  have hlenEq : (G.threadEvents Tid.guessAX).length =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen0 : (0 : ℕ) < (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hne : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest ≠ [] := by
      intro hcontra
      rw [hcontra] at hlabP0
      simp at hlabP0
    exact List.length_pos_of_ne_nil hne
  have hlen : (0 : ℕ) < (G.threadEvents Tid.guessAX).length := by rw [hlenEq]; exact hlen0
  refine ⟨hlen, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zAxy) (op := OpType.wt) (i := 0)
    hw1 hlen hlabP0 rfl rfl (by simp)
  rwa [show G.nthEvent Tid.guessAX Loc.zAxy OpType.wt 0 = G.nthWrite Tid.guessAX Loc.zAxy 0
    from rfl] at hewpos

/-- `GuessAX`'s `(m + 1)`-th `zAxy`-write is at position
`nestedOuterStart ks N (m + 1)` of `G.threadEvents Tid.guessAX`. -/
theorem guessAX_zAxy_write_nthWrite_pos_outer (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) {b : Val I × Val I} {vs : List (Val I × Val I × Val I)}
    (hmbv : outerRest[m]? = some (b, vs)) :
    ∃ hlen : nestedOuterStart ks N (m + 1) < (G.threadEvents Tid.guessAX).length,
      G.nthWrite Tid.guessAX Loc.zAxy (m + 1) =
        some ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N (m + 1)]'hlen).1 := by
  have hlabPm := guessAXBlockWord_zAxy_write_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len ks N hks hK0 houterLen houter houterLast m hm b vs hmbv
  have hlenEq : (G.threadEvents Tid.guessAX).length =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenP : nestedOuterStart ks N (m + 1) <
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length :=
    (List.getElem?_eq_some_iff.mp hlabPm).1
  have hlen : nestedOuterStart ks N (m + 1) < (G.threadEvents Tid.guessAX).length := by
    rw [hlenEq]; exact hlenP
  refine ⟨hlen, ?_⟩
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hposeq : nestedOuterStart ks N (m + 1) = 4 + K0 * 3 +
      ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length := by
    have hlenL := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast m (by omega)
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N (m + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N m
      have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD0] at hh
    rw [hlenL, hstartm]; omega
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hlead_filter : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) = [] := by
      intro a
      unfold guessAXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessAX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    have htail_nil : ((inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
        List (ThreadLabel (domainOf I) Tid.guessAX)).filter
        (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) = [] := by
      rw [List.filter_append, list_filter_flatMap_distrib]
      simp only [hinner_nil]
      rw [hflatnil inner0Rest, List.nil_append]
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), htail_nil]
  have hcount : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedOuterStart ks N (m + 1))).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt)).length = m + 1 := by
    have hle1 : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessAXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length ≤
        4 + K0 * 3 + ((outerRest.take m).flatMap
          (fun q => guessAXOuterBlockElems I q.1 q.2)).length := by
      rw [hleadlen]; omega
    have hmlt : m < outerRest.length := by omega
    have htakeeq : (outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length) =
        (outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2) := by
      have hget : outerRest[m]? = some (outerRest[m]'hmlt) := List.getElem?_eq_getElem hmlt
      have h := list_take_flatMap_offset (fun q => guessAXOuterBlockElems I q.1 q.2) outerRest m 0
        (outerRest[m]'hmlt) hget (Nat.zero_le _)
      simpa using h
    rw [heq, hposeq, List.take_append, List.take_of_length_le hle1, hleadlen,
      show 4 + K0 * 3 + ((outerRest.take m).flatMap
          (fun q => guessAXOuterBlockElems I q.1 q.2)).length - (4 + K0 * 3)
        = ((outerRest.take m).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        from by omega,
      htakeeq, List.filter_append, List.length_append, hlead_filter,
      guessAXOuterRest_zAxy_write_take_count I outerRest m (by omega), List.length_singleton]
    omega
  exact G.nthEvent_eq_of_threadWord_pos (x := Loc.zAxy) (op := OpType.wt) hw1 hlen hlabPm rfl rfl
    hcount

/-- `GuessAX`'s `0`-th `ellAyx`-read is at position `3 + K0 * 3` of
`G.threadEvents Tid.guessAX`. -/
theorem guessAX_ellAyx_read_nthRead_pos0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some) :
    ∃ hlen : 3 + K0 * 3 < (G.threadEvents Tid.guessAX).length,
      G.nthRead Tid.guessAX Loc.ellAyx 0 =
        some ((G.threadEvents Tid.guessAX)[3 + K0 * 3]'hlen).1 := by
  have hlabP0 := guessAXBlockWord_ellAyx_read_pos0 I v1 v2 vB0 K0 inner0Rest hinner0len outerRest
  have hlenEq : (G.threadEvents Tid.guessAX).length =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenP : 3 + K0 * 3 < (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length :=
    (List.getElem?_eq_some_iff.mp hlabP0).1
  have hlen : 3 + K0 * 3 < (G.threadEvents Tid.guessAX).length := by rw [hlenEq]; exact hlenP
  refine ⟨hlen, ?_⟩
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hlead_filter_ellAyx : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) = [] := by
      intro a
      unfold guessAXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessAX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_append, list_filter_flatMap_distrib]
    simp only [hinner_nil]
    rw [hflatnil inner0Rest, List.nil_append,
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hstep : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (3 + K0 * 3 + 1) =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (3 + K0 * 3) ++
        [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
    rw [List.take_add_one, hlabP0]; rfl
  have hcount1 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (3 + K0 * 3 + 1)).filter (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd)).length = 1 := by
    have h4 : (3 : ℕ) + K0 * 3 + 1 = 4 + K0 * 3 := by omega
    rw [h4, heq, List.take_append_of_le_length (le_of_eq hleadlen.symm),
      List.take_of_length_le (le_of_eq hleadlen), hlead_filter_ellAyx, List.length_singleton]
  have hcount0 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (3 + K0 * 3)).filter (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd)).length = 0 := by
    have h := hcount1
    rw [hstep, List.filter_append, List.length_append] at h
    have hone : (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX)]) :
        List (ThreadLabel (domainOf I) Tid.guessAX)).filter
        (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
      rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rw [hone, List.length_singleton] at h
    omega
  exact G.nthEvent_eq_of_threadWord_pos (x := Loc.ellAyx) (op := OpType.rd) (i := 0)
    hw1 hlen hlabP0 rfl rfl hcount0

/-- `GuessAX`'s `(m + 1)`-th `ellAyx`-read is at position
`nestedOuterStart ks N (m + 2) - 1` of `G.threadEvents Tid.guessAX`. -/
theorem guessAX_ellAyx_read_nthRead_pos_outer (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) {b : Val I × Val I} {vs : List (Val I × Val I × Val I)}
    (hmbv : outerRest[m]? = some (b, vs)) :
    ∃ hlen : nestedOuterStart ks N (m + 2) - 1 < (G.threadEvents Tid.guessAX).length,
      G.nthRead Tid.guessAX Loc.ellAyx (m + 1) =
        some ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N (m + 2) - 1]'hlen).1 := by
  have hlabPm := guessAXBlockWord_ellAyx_read_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len ks N hks hK0 houterLen houter houterLast m hm b vs hmbv
  have hlenEq : (G.threadEvents Tid.guessAX).length =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenP : nestedOuterStart ks N (m + 2) - 1 <
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length :=
    (List.getElem?_eq_some_iff.mp hlabPm).1
  have hlen : nestedOuterStart ks N (m + 2) - 1 < (G.threadEvents Tid.guessAX).length := by
    rw [hlenEq]; exact hlenP
  refine ⟨hlen, ?_⟩
  have hge2 : nestedOuterStart ks N (m + 2) ≥ 1 := by
    have hh := nestedOuterStart_ge ks N (m + 1)
    rw [show m + 1 + 1 = m + 2 from by omega] at hh
    omega
  have hstepidx : nestedOuterStart ks N (m + 2) - 1 + 1 = nestedOuterStart ks N (m + 2) := by omega
  have hstep : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedOuterStart ks N (m + 2) - 1 + 1) =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedOuterStart ks N (m + 2) - 1) ++
      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
    rw [List.take_add_one, hlabPm]; rfl
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessAXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hlead_filter_ellAyx : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) = [] := by
      intro a
      unfold guessAXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessAX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_append, list_filter_flatMap_distrib]
    simp only [hinner_nil]
    rw [hflatnil inner0Rest, List.nil_append,
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hposeq1 : nestedOuterStart ks N (m + 2) = 4 + K0 * 3 +
      ((outerRest.take (m + 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length := by
    have hlenL := guessAXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m + 1) (by omega)
    rw [show m + 1 + 1 = m + 2 from by omega] at hlenL
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N (m + 2) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m + 1)
      have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rw [hgetD0, show m + 1 + 1 = m + 2 from by omega] at hh
      exact hh
    rw [hlenL, hstartm]; omega
  have hle1 : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).length ≤
      4 + K0 * 3 + ((outerRest.take (m + 1)).flatMap
        (fun q => guessAXOuterBlockElems I q.1 q.2)).length := by
    rw [hleadlen]; omega
  have htakeeq : (outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
      (((outerRest.take (m + 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length) =
      (outerRest.take (m + 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2) := by
    have hsplit : outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2) =
        (outerRest.take (m + 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2) ++
        (outerRest.drop (m + 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2) := by
      conv_lhs => rw [← List.take_append_drop (m + 1) outerRest]
      rw [List.flatMap_append]
    rw [hsplit, List.take_append_of_le_length (le_refl _), List.take_of_length_le (le_refl _)]
  have hcount1 : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedOuterStart ks N (m + 2))).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd)).length = m + 2 := by
    rw [heq, hposeq1, List.take_append, List.take_of_length_le hle1, hleadlen,
      show 4 + K0 * 3 + ((outerRest.take (m + 1)).flatMap
          (fun q => guessAXOuterBlockElems I q.1 q.2)).length - (4 + K0 * 3)
        = ((outerRest.take (m + 1)).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length
        from by omega,
      htakeeq, List.filter_append, List.length_append, hlead_filter_ellAyx,
      guessAXOuterRest_ellAyx_read_take_count I outerRest (m + 1) (by omega), List.length_singleton]
    omega
  have hcount : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedOuterStart ks N (m + 2) - 1)).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd)).length = m + 1 := by
    have h := hcount1
    rw [← hstepidx, hstep, List.filter_append, List.length_append] at h
    have hone : (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX)]) :
        List (ThreadLabel (domainOf I) Tid.guessAX)).filter
        (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
      rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rw [hone, List.length_singleton] at h
    omega
  exact G.nthEvent_eq_of_threadWord_pos (x := Loc.ellAyx) (op := OpType.rd) (i := m + 1)
    hw1 hlen hlabPm rfl rfl hcount

/-- `guessAXBlockWord` contains `outerRest.length + 1` `zAxy`-writes. -/
theorem guessAXBlockWord_zAxy_write_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (_ : inner0Rest.length = K0) :
    ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt)).length = outerRest.length + 1 := by
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hlead_filter : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).filter
      (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) = [] := by
      intro a
      unfold guessAXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessAX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    have htail_nil : ((inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
        List (ThreadLabel (domainOf I) Tid.guessAX)).filter
        (fun l => l.1.loc = Loc.zAxy ∧ l.1.op = OpType.wt) = [] := by
      rw [List.filter_append, list_filter_flatMap_distrib]
      simp only [hinner_nil]
      rw [hflatnil inner0Rest, List.nil_append]
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), htail_nil]
  rw [heq, List.filter_append, List.length_append, hlead_filter, List.length_singleton]
  conv_lhs => rw [show outerRest = outerRest.take outerRest.length from
    (List.take_of_length_le (le_refl _)).symm]
  rw [guessAXOuterRest_zAxy_write_take_count I outerRest outerRest.length (le_refl _)]
  omega

/-- `guessAXBlockWord` contains `outerRest.length + 1` `ellAyx`-reads. -/
theorem guessAXBlockWord_ellAyx_read_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (_ : inner0Rest.length = K0) :
    ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd)).length = outerRest.length + 1 := by
  have heq : guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)) := rfl
  have hlead_filter_ellAyx : (([ ⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessAXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessAX)).filter
      (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.ellAyx ∧ l.1.op = OpType.rd) = [] := by
      intro a
      unfold guessAXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessAX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_append, list_filter_flatMap_distrib]
    simp only [hinner_nil]
    rw [hflatnil inner0Rest, List.nil_append,
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [heq, List.filter_append, List.length_append, hlead_filter_ellAyx, List.length_singleton]
  conv_lhs => rw [show outerRest = outerRest.take outerRest.length from
    (List.take_of_length_le (le_refl _)).symm]
  rw [guessAXOuterRest_ellAyx_read_take_count I outerRest outerRest.length (le_refl _)]
  omega

/-- `nestedOuterStart ks N` is strictly monotone (`nestedOuterLen` is
positive). -/
theorem nestedOuterStart_strictMono (ks : List ℕ) (N : ℕ) : StrictMono (nestedOuterStart ks N) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hpos : nestedOuterLen ks N n ≥ 1 := by unfold nestedOuterLen; split_ifs <;> omega
  have hsucc := nestedOuterStart_succ ks N n
  omega

/-- `GuessAX`'s `j`-th `zAxy`-write is at position `nestedOuterStart ks N j`
of `G.threadEvents Tid.guessAX`. -/
theorem guessAX_zAxy_write_nthWrite_pos_full (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (j : ℕ) (hj : j ≤ N + 1) :
    ∃ hlen : nestedOuterStart ks N j < (G.threadEvents Tid.guessAX).length,
      G.nthWrite Tid.guessAX Loc.zAxy j =
        some ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N j]'hlen).1 := by
  rcases j with _ | m
  · have h0 : nestedOuterStart ks N 0 = 0 := rfl
    rw [h0]
    exact guessAX_zAxy_write_nthWrite_pos0 I G hw1
  · have hmlen : m ≤ N := by omega
    obtain ⟨b, vs, hbv⟩ : ∃ b vs, outerRest[m]? = some (b, vs) := by
      by_cases hmN : m = N
      · subst hmN; obtain ⟨b, vs, hbv, -⟩ := houterLast; exact ⟨b, vs, hbv⟩
      · obtain ⟨b, vs, km, hbv, -, -⟩ := houter m (by omega); exact ⟨b, vs, hbv⟩
    exact guessAX_zAxy_write_nthWrite_pos_outer I G hinner0len hw1 hks hK0 houterLen houter
      houterLast m hmlen hbv

/-- `GuessAX`'s `j`-th `ellAyx`-read is at position
`nestedOuterStart ks N (j + 1) - 1` of `G.threadEvents Tid.guessAX`. -/
theorem guessAX_ellAyx_read_nthRead_pos_full (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (j : ℕ) (hj : j ≤ N + 1) :
    ∃ hlen : nestedOuterStart ks N (j + 1) - 1 < (G.threadEvents Tid.guessAX).length,
      G.nthRead Tid.guessAX Loc.ellAyx j =
        some ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N (j + 1) - 1]'hlen).1 := by
  rcases j with _ | m
  · have h1 := nestedOuterStart_one ks N K0 hK0
    have heq : nestedOuterStart ks N (0 + 1) - 1 = 3 + K0 * 3 := by
      rw [Nat.zero_add]; omega
    rw [heq]
    exact guessAX_ellAyx_read_nthRead_pos0 I G hinner0len hw1
  · have hmlen : m ≤ N := by omega
    obtain ⟨b, vs, hbv⟩ : ∃ b vs, outerRest[m]? = some (b, vs) := by
      by_cases hmN : m = N
      · subst hmN; obtain ⟨b, vs, hbv, -⟩ := houterLast; exact ⟨b, vs, hbv⟩
      · obtain ⟨b, vs, km, hbv, -, -⟩ := houter m (by omega); exact ⟨b, vs, hbv⟩
    exact guessAX_ellAyx_read_nthRead_pos_outer I G hinner0len hw1 hks hK0 houterLen houter
      houterLast m hmlen hbv

/-- `GuessAX`'s `j`-th `zAxy`-write is at position `nestedOuterStart ks N j`
of its word, with value `(1 + j) % 4`. -/
theorem guessAXBlockWord_zAxy_write_val_full (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hvB01 : vB0.1 = Val.cnt (1 : Fin 4))
    (houterval1 : ∀ m, m < N + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      b.1 = Val.cnt (⟨(2 + m) % 4, by omega⟩ : Fin 4))
    (j : ℕ) (hj : j ≤ N + 1) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N j]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAxy (Val.cnt (⟨(1 + j) % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX) := by
  rcases j with _ | m
  · have h0 : nestedOuterStart ks N 0 = 0 := rfl
    rw [h0]
    have hlab := guessAXBlockWord_zAxy_write_pos0 I v1 v2 vB0 inner0Rest outerRest
    have hnat0 : (1 : ℕ) = (1 + 0) % 4 := by omega
    have hveq : (Val.cnt (1 : Fin 4) : Val I) = Val.cnt (⟨(1 + 0) % 4, by omega⟩ : Fin 4) := by
      congr 1
    rw [hlab, hvB01, hveq]
  · have hmlt : m ≤ N := by omega
    obtain ⟨b, vs, hbv⟩ : ∃ b vs, outerRest[m]? = some (b, vs) := by
      by_cases hmN : m = N
      · subst hmN; obtain ⟨b, vs, hbv, -⟩ := houterLast; exact ⟨b, vs, hbv⟩
      · obtain ⟨b, vs, km, hbv, -, -⟩ := houter m (by omega); exact ⟨b, vs, hbv⟩
    obtain ⟨b', vs', hbv', hbval1⟩ := houterval1 m (by omega)
    have hbeq : b' = b := congrArg Prod.fst (Option.some.inj (hbv'.symm.trans hbv))
    rw [hbeq] at hbval1
    have hlab := guessAXBlockWord_zAxy_write_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len ks N hks hK0 houterLen houter houterLast m hmlt b vs hbv
    have hnatm : (2 + m) % 4 = (1 + (m + 1)) % 4 := by omega
    have hveq : b.1 = Val.cnt (⟨(1 + (m + 1)) % 4, by omega⟩ : Fin 4) := by
      rw [hbval1]; congr 1; exact Fin.ext hnatm
    rw [hlab, hveq]

/-- `GuessAX`'s `j`-th `ellAyx`-read is at position
`nestedOuterStart ks N (j + 1) - 1` of its word, with counter `(1 + j) % 4`. -/
theorem guessAXBlockWord_ellAyx_read_val_full (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (v0 : Fin I.n) (hvB02 : vB0.2 = Val.cntAux (1 : Fin 4) (some v0))
    (houterval2 : ∀ m, m < N + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∃ aux, b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) aux)
    (j : ℕ) (hj : j ≤ N + 1) :
    ∃ aux, (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N (j + 1) - 1]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.ellAyx (Val.cntAux (⟨(1 + j) % 4, by omega⟩ : Fin 4) aux),
        rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) := by
  rcases j with _ | m
  · refine ⟨some v0, ?_⟩
    have heq : nestedOuterStart ks N (0 + 1) - 1 = 3 + K0 * 3 := by
      have h1 := nestedOuterStart_one ks N K0 hK0
      simp only [Nat.zero_add]
      omega
    rw [heq]
    have hlab := guessAXBlockWord_ellAyx_read_pos0 I v1 v2 vB0 K0 inner0Rest hinner0len outerRest
    have hnat0 : (1 : ℕ) = (1 + 0) % 4 := by omega
    have hveq : (Val.cntAux (1 : Fin 4) (some v0) : Val I) =
        Val.cntAux (⟨(1 + 0) % 4, by omega⟩ : Fin 4) (some v0) := by
      congr 1
    rw [hlab, hvB02, hveq]
  · have hmlt : m ≤ N := by omega
    obtain ⟨b, vs, hbv⟩ : ∃ b vs, outerRest[m]? = some (b, vs) := by
      by_cases hmN : m = N
      · subst hmN; obtain ⟨b, vs, hbv, -⟩ := houterLast; exact ⟨b, vs, hbv⟩
      · obtain ⟨b, vs, km, hbv, -, -⟩ := houter m (by omega); exact ⟨b, vs, hbv⟩
    obtain ⟨b', vs', hbv', aux, hbval2⟩ := houterval2 m (by omega)
    have hbeq : b' = b := congrArg Prod.fst (Option.some.inj (hbv'.symm.trans hbv))
    rw [hbeq] at hbval2
    refine ⟨aux, ?_⟩
    have hlab := guessAXBlockWord_ellAyx_read_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len ks N hks hK0 houterLen houter houterLast m hmlt b vs hbv
    have hnatm : (2 + m) % 4 = (1 + (m + 1)) % 4 := by omega
    have hveq : b.2 = Val.cntAux (⟨(1 + (m + 1)) % 4, by omega⟩ : Fin 4) aux := by
      rw [hbval2]; congr 1; exact Fin.ext hnatm
    rw [hlab, hveq]

/-- Eq. (15)'s bridge pair `zAxy`/`ellAyx` (`GuessAX`/`GuessAY`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`guessAX_shape_inv`, `guessAY_shape_inv`). `GuessAX` writes `zAxy` at the
head and reads `ellAyx` at the tail of each outer iteration (positions
`nestedOuterStart ks N j` and `nestedOuterStart ks N (j + 1) - 1`);
`GuessAY` writes `ellAyx` in every iteration and skips its first
`zAxy`-read, so its `j`-th `zAxy`-read sits in iteration `j + 1`. Both
locations have a single writer, so writer identification is
`writerTid_confined`. -/
theorem guessAX_guessAY_zAxy_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.guessAY Tid.guessAX Loc.zAxy Loc.ellAyx := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessAX_run_of_reaches I G hG
  obtain ⟨v0, K0, js, v1, v2, vB0, inner0Rest, outerRest, -, -, hinner0len, houterLen, houter,
    houterLast, -, -, -, hvB01, hvB02, houterval2, -, -, -, hσ1⟩ :=
    guessAX_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := guessAY_run_of_reaches I G hG
  obtain ⟨v0', js', kws, -, -, hkwsval, hσ2⟩ := guessAY_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAX, hσ1]
  have hw2 : G.threadWord Tid.guessAY = (guessAYBlockWord I v0' kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAY, hσ2]
  have hks : (K0 :: guessAXJsToKs I js).length = js.length + 1 := by simp [guessAXJsToKs]
  have hK0 : (K0 :: guessAXJsToKs I js)[0]? = some K0 := rfl
  have houter' : ∀ j, j < js.length → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      (K0 :: guessAXJsToKs I js)[j + 1]? = some km ∧ vs.length = km + 1 := by
    intro j hj
    obtain ⟨b, vs, km, hbvs, hksm, hvslen⟩ := houter j hj
    exact ⟨b, vs, km, hbvs, hksm, hvslen⟩
  have houterval1' : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      b.1 = Val.cnt (⟨(2 + m) % 4, by omega⟩ : Fin 4) := by
    intro m hm
    obtain ⟨b, vs, hbv, hb1, -, -⟩ := houterval2 m hm
    exact ⟨b, vs, hbv, hb1⟩
  have houterval2' : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∃ aux, b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) aux := by
    intro m hm
    obtain ⟨b, vs, hbv, -, hbaux3, hbaux4⟩ := houterval2 m hm
    by_cases hmlt : m < js.length
    · obtain ⟨w, -, hb2⟩ := hbaux3 hmlt
      exact ⟨b, vs, hbv, some w, hb2⟩
    · exact ⟨b, vs, hbv, none, hbaux4 (by omega)⟩
  set ks := K0 :: guessAXJsToKs I js with hksdef
  set N := js.length with hNdef
  -- `GuessAX` has `N + 2` outer iterations, so `N + 2` `zAxy`-writes and `ellAyx`-reads.
  have hBW : ∀ {j : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.guessAX Loc.zAxy j = some w →
      j ≤ N + 1 := by
    intro j w hw
    have hjtot : j < (G.opEvents Tid.guessAX Loc.zAxy OpType.wt).length :=
      (List.getElem?_eq_some_iff.mp hw).1
    have h1 := congrArg List.length
      (G.opEvents_map_lab_eq_filter_threadLabels Tid.guessAX Loc.zAxy OpType.wt)
    rw [List.length_map, List.length_map, G.threadLabels_eq_of_threadWord hw1] at h1
    have htc := guessAXBlockWord_zAxy_write_total_count I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len
    have htot := h1.trans htc
    omega
  have hBR : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.guessAX Loc.ellAyx j = some r →
      j ≤ N + 1 := by
    intro j r hr
    have hjtot : j < (G.opEvents Tid.guessAX Loc.ellAyx OpType.rd).length :=
      (List.getElem?_eq_some_iff.mp hr).1
    have h1 := congrArg List.length
      (G.opEvents_map_lab_eq_filter_threadLabels Tid.guessAX Loc.ellAyx OpType.rd)
    rw [List.length_map, List.length_map, G.threadLabels_eq_of_threadWord hw1] at h1
    have htc := guessAXBlockWord_ellAyx_read_total_count I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len
    have htot := h1.trans htc
    omega
  -- `GuessAX`'s `j`-th `zAxy`-write: at `nestedOuterStart ks N j`, value `(j+1) mod 4`.
  have hWp : ∀ j, j ≤ N + 1 →
      ∃ hlen : nestedOuterStart ks N j < (G.threadEvents Tid.guessAX).length,
      G.nthWrite Tid.guessAX Loc.zAxy j =
        some ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N j]'hlen).1 ∧
      ∃ c : Fin 4, ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N j]'hlen).1.val =
        Val.cnt c ∧ c.val = (j + 1) % 4 := by
    intro j hj
    obtain ⟨hlen, hpos⟩ := guessAX_zAxy_write_nthWrite_pos_full I G hinner0len hw1 hks hK0
      houterLen houter' houterLast j hj
    have hval := guessAXBlockWord_zAxy_write_val_full I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len ks N hks hK0 houterLen houter' houterLast hvB01 houterval1' j hj
    obtain ⟨eSub, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 _ _ hval
    refine ⟨hlen, hpos, ⟨(1 + j) % 4, by omega⟩, ?_, by simp only; omega⟩
    rw [show ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N j]'hlen) = eSub from heq,
      Event.val, hlab]
    rfl
  -- `GuessAX`'s `j`-th `ellAyx`-read: at `nestedOuterStart ks N (j + 1) - 1`, value `⟨(j+1) mod 4, _⟩`.
  have hRq : ∀ j, j ≤ N + 1 →
      ∃ hlen : nestedOuterStart ks N (j + 1) - 1 < (G.threadEvents Tid.guessAX).length,
      G.nthRead Tid.guessAX Loc.ellAyx j =
        some ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N (j + 1) - 1]'hlen).1 ∧
      ∃ (c : Fin 4) (aux : Option (Fin I.n)),
        ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N (j + 1) - 1]'hlen).1.val =
        Val.cntAux c aux ∧ c.val = (j + 1) % 4 := by
    intro j hj
    obtain ⟨hlen, hpos⟩ := guessAX_ellAyx_read_nthRead_pos_full I G hinner0len hw1 hks hK0
      houterLen houter' houterLast j hj
    obtain ⟨aux, hval⟩ := guessAXBlockWord_ellAyx_read_val_full I v1 v2 vB0 K0 inner0Rest
      outerRest hinner0len ks N hks hK0 houterLen houter' houterLast v0 hvB02 houterval2' j hj
    obtain ⟨eSub, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 _ _ hval
    refine ⟨hlen, hpos, ⟨(1 + j) % 4, by omega⟩, aux, ?_, by simp only; omega⟩
    rw [show ((G.threadEvents Tid.guessAX)[nestedOuterStart ks N (j + 1) - 1]'hlen) = eSub
      from heq, Event.val, hlab]
    rfl
  -- `GuessAY`'s `j`-th `zAxy`-read: value `(j+1) mod 4`, in block `kws[j]`.
  have hRp : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.guessAY Loc.zAxy j = some r →
      (∃ c : Fin 4, r.val = Val.cnt c ∧ c.val = (j + 1) % 4) ∧ j < kws.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (guessAYBlockWord_zAxy_read_val I v0' kws j).symm.trans hf
    rcases hk : kws[j]? with _ | kw
    · rw [hk] at hf; simp at hf
    · rw [hk] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨w', hkw⟩ := hkwsval j hlt
      rw [hk] at hkw
      have hkw1 : kw.1.val = (1 + j) % 4 := by rw [Option.some.inj hkw]
      refine ⟨⟨kw.1, ?_, by omega⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `GuessAY`'s `i`-th `ellAyx`-write: value `⟨(i+1) mod 4, _⟩`, in block `kws[i-1]` for `i ≥ 1`.
  have hWq : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.guessAY Loc.ellAyx i = some w →
      (∃ (c : Fin 4) (aux : Option (Fin I.n)), w.val = Val.cntAux c aux ∧ c.val = (i + 1) % 4) ∧
      ∀ i', i = i' + 1 → i' < kws.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    rcases i with _ | i'
    · have hf := (guessAYBlockWord_ellAyx_write_val0 I v0' kws).symm.trans hf
      refine ⟨⟨1, some v0', ?_, rfl⟩, fun i' h => absurd h (by omega)⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
    · have hf := (guessAYBlockWord_ellAyx_write_val_succ I v0' kws i').symm.trans hf
      rcases hk : kws[i']? with _ | kw
      · rw [hk] at hf; simp at hf
      · rw [hk] at hf
        have hlt := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨w', hkw⟩ := hkwsval i' hlt
        rw [hk] at hkw
        have hkw1 : kw.1.val = (1 + i') % 4 := by rw [Option.some.inj hkw]
        refine ⟨⟨kw.1 + 1, kw.2, ?_, ?_⟩, fun j h => by omega⟩
        · rw [Event.val, hlab, ← Option.some.inj hf]
          rfl
        · rw [Fin.val_add, hkw1]; simp; omega
  have hkw : ∀ {n : ℕ}, n < kws.length → ∃ kw, kws[n]? = some kw :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨hlen, hpos, c, hc, hcv⟩ := hWp i (hBW hw)
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRp hr
    rw [Option.some.inj (hw.symm.trans hpos), hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨⟨c, a, hc, hcv⟩, -⟩ := hWq hw
    obtain ⟨hlen, hpos, c', a', hc', hc'v⟩ := hRq j (hBR hr)
    rw [Option.some.inj (hr.symm.trans hpos), hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.guessAX := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.guessAY := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · -- `guessAY`: `r(zAxy)` at `6+i*5` precedes `w(ellAyx)` at `4+(ℓ-1)*5`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (hRp hr).2
    obtain ⟨kw', hk'⟩ := hkw ((hWq hw).2 ℓ' rfl)
    obtain ⟨hlenR, hposR⟩ := guessAY_zAxy_read_nthRead_pos I G hw2 i hk
    obtain ⟨hlenW, hposW⟩ := guessAY_ellAyx_write_nthWrite_pos I G hw2 ℓ' hk'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.guessAY hlenR hlenW (by omega)
  · -- `guessAX`: the `ellAyx`-read ending outer iteration `i` precedes iteration `ℓ`'s `zAxy`-write.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨hlenR, hposR, -⟩ := hRq i (hBR hr)
    obtain ⟨hlenW, hposW, -⟩ := hWp ℓ (hBW hw)
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    have hmono := nestedOuterStart_strictMono ks N (show i + 1 < ℓ by omega)
    exact G.po_of_threadEvents_pos_lt Tid.guessAX hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (n := i) (by have := (hWq hw).2 ℓ' rfl; omega)
    exact ⟨_, (guessAY_zAxy_read_nthRead_pos I G hw2 i hk).2⟩
  · intro i ℓ w hw hiℓ
    exact ⟨_, (hRq i (by have := hBW hw; omega)).2.1⟩

theorem no_skipping_guessAX_guessAY_zAxy (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessAX Loc.zAxy i = some ew)
    (her : G.nthRead Tid.guessAY Loc.zAxy K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((guessAX_guessAY_zAxy_noSkipPair I G hG).no_skipping hG.1.1 K).1 hew her hrf

theorem no_skipping_guessAX_guessAY_ellAyx (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessAY Loc.ellAyx i = some ew)
    (her : G.nthRead Tid.guessAX Loc.ellAyx K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((guessAX_guessAY_zAxy_noSkipPair I G hG).no_skipping hG.1.1 K).2 hew her hrf

theorem guessBXOuterBlockElems_zBxy_write_filter (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) :
    (guessBXOuterBlockElems I b vs).filter (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
  have hinner_nil : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) = [] := by
    intro a
    unfold guessBXInnerBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflatnil : ∀ l : List (Val I × Val I × Val I),
      l.flatMap (fun (_ : Val I × Val I × Val I) =>
        ([] : List (ThreadLabel (domainOf I) Tid.guessBX))) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons _ t ih => simp [List.flatMap_cons, ih]
  have htail_nil : (vs.flatMap (guessBXInnerBlockElems I) ++
      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)]).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) = [] := by
    rw [List.filter_append, list_filter_flatMap_distrib]
    simp only [hinner_nil]
    rw [hflatnil vs, List.nil_append]
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  unfold guessBXOuterBlockElems
  rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), htail_nil]

/-- The `ellByx`-read is the only `(ellByx, rd)` event of an outer block
`guessBXOuterBlockElems`, at its end. -/
theorem guessBXOuterBlockElems_ellByx_read_filter (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) :
    (guessBXOuterBlockElems I b vs).filter (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
  have hinner_nil : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) = [] := by
    intro a
    unfold guessBXInnerBlockElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hflatnil : ∀ l : List (Val I × Val I × Val I),
      l.flatMap (fun (_ : Val I × Val I × Val I) =>
        ([] : List (ThreadLabel (domainOf I) Tid.guessBX))) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons _ t ih => simp [List.flatMap_cons, ih]
  unfold guessBXOuterBlockElems
  rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_append,
    list_filter_flatMap_distrib]
  simp only [hinner_nil]
  rw [hflatnil vs, List.nil_append,
    List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]

/-- The `zBxy`-write of outer iteration `0` is at position `0` of
`guessBXBlockWord`. -/
theorem guessBXBlockWord_zBxy_write_pos0 (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[0]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) :=
  rfl

/-- The `ellByx`-read of outer iteration `0` is at position `3 + K0 * 3` of
`guessBXBlockWord`. -/
theorem guessBXBlockWord_ellByx_read_pos0 (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I)) (hinner0len : inner0Rest.length = K0)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[3 + K0 * 3]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) := by
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I)) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 3 + K0 * 3 := by
    rw [List.length_append]
    have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
  have hfulllen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
    rw [List.length_append, hleadlen, List.length_singleton]; omega
  rw [heq, List.getElem?_append_left (by rw [hfulllen]; omega),
    List.getElem?_append_right (by rw [hleadlen]), hleadlen, Nat.sub_self]
  rfl

/-- The `zBxy`-write of outer iteration `m + 1` is at position
`nestedOuterStart ks N (m + 1)`. -/
theorem guessBXBlockWord_zBxy_write_outerPos (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hmbv : outerRest[m]? = some (b, vs)) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N (m + 1)]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) := by
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hlenL := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter houterLast
    m (by omega)
  have hstartm := nestedOuterStart_one ks N K0 hK0
  have hge : nestedOuterStart ks N (m + 1) ≥ 3 * K0 + 4 := by
    have hh := nestedOuterStart_ge ks N m
    have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
    rwa [hgetD0] at hh
  have hposeq : nestedOuterStart ks N (m + 1) = 4 + K0 * 3 +
      ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length := by
    rw [hlenL, hstartm]; omega
  rw [heq, hposeq, List.getElem?_append_right (by omega), hleadlen,
    show 4 + K0 * 3 + ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
      - (4 + K0 * 3) = ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
      + 0 from by omega]
  have hqlt : (0 : ℕ) < (guessBXOuterBlockElems I b vs).length := by
    rw [guessBXOuterBlockElems_length]; omega
  rw [list_take_flatMap_offset_getElem (fun q => guessBXOuterBlockElems I q.1 q.2) outerRest m 0
    (b, vs) hmbv hqlt]
  rfl

/-- The `ellByx`-read of outer iteration `m + 1` is at position
`nestedOuterStart ks N (m + 2) - 1`, for every `m ≤ N`. -/
theorem guessBXBlockWord_ellByx_read_outerPos (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hmbv : outerRest[m]? = some (b, vs)) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N (m + 2) - 1]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) := by
  have hstart := guessBXBlockWord_zBxy_write_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len ks N hks hK0 houterLen houter houterLast m hm b vs hmbv
  have hlen : (guessBXOuterBlockElems I b vs).length = 3 * vs.length + 2 :=
    guessBXOuterBlockElems_length I b vs
  have hvslen : vs.length = if m = N then 1 else (ks[m + 1]?).getD 0 + 1 := by
    by_cases hmN : m = N
    · subst hmN
      obtain ⟨b', vs', hbv', hvl'⟩ := houterLast
      rw [hbv'] at hmbv
      have heq2 : vs' = vs := congrArg Prod.snd (Option.some.inj hmbv)
      rw [if_pos rfl, ← heq2]; exact hvl'
    · obtain ⟨b', vs', km, hbv', hks', hvl'⟩ := houter m (by omega)
      rw [hbv'] at hmbv
      have heq2 : vs' = vs := congrArg Prod.snd (Option.some.inj hmbv)
      rw [if_neg hmN, ← heq2, hvl', hks']
      rfl
  have hstep : nestedOuterStart ks N (m + 2) = nestedOuterStart ks N (m + 1) +
      nestedOuterLen ks N (m + 1) := nestedOuterStart_succ ks N (m + 1)
  have hnol : nestedOuterLen ks N (m + 1) = 3 * vs.length + 2 := by
    unfold nestedOuterLen
    by_cases hmN : m = N
    · subst hmN
      rw [if_pos rfl]
      rw [if_pos rfl] at hvslen
      omega
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [if_neg hmN] at hvslen
      have hgd : ks.getD (m + 1) 0 = (ks[m + 1]?).getD 0 := rfl
      omega
  have hlastpos : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N (m + 1) +
      (3 * vs.length + 2 - 1)]? = (guessBXOuterBlockElems I b vs)[3 * vs.length + 2 - 1]? := by
    have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
        (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessBXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
        outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
    have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessBXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
      rw [List.length_append, List.length_append]
      have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
        rw [List.length_flatMap]
        have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
            inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
        rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
      simp only [List.length_cons, List.length_nil, hinner]
      omega
    have hlenL := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter houterLast
      m (by omega)
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N (m + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N m
      have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD0] at hh
    have hposeq : nestedOuterStart ks N (m + 1) = 4 + K0 * 3 +
        ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length := by
      rw [hlenL, hstartm]; omega
    rw [heq, hposeq, List.getElem?_append_right (by omega), hleadlen,
      show 4 + K0 * 3 + ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (3 * vs.length + 2 - 1) - (4 + K0 * 3)
        = ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        + (3 * vs.length + 2 - 1) from by omega]
    have hqlt : 3 * vs.length + 2 - 1 < (guessBXOuterBlockElems I b vs).length := by
      rw [guessBXOuterBlockElems_length]; omega
    exact list_take_flatMap_offset_getElem (fun q => guessBXOuterBlockElems I q.1 q.2) outerRest m
      (3 * vs.length + 2 - 1) (b, vs) hmbv hqlt
  have hidx : nestedOuterStart ks N (m + 2) - 1 =
      nestedOuterStart ks N (m + 1) + (3 * vs.length + 2 - 1) := by
    rw [hstep, hnol]; omega
  rw [hidx, hlastpos]
  have hidx2 : 3 * vs.length + 2 - 1 = 3 * vs.length + 1 := by omega
  rw [hidx2]
  unfold guessBXOuterBlockElems
  rw [show (3 * vs.length + 1 : ℕ) = (3 * vs.length) + 1 from rfl, List.getElem?_cons_succ]
  have hflen : (vs.flatMap (guessBXInnerBlockElems I)).length = 3 * vs.length := by
    rw [List.length_flatMap]
    have heq1 : (vs.map (fun a => (guessBXInnerBlockElems I a).length)) = vs.map (fun _ => 3) :=
      List.map_congr_left (fun _ _ => rfl)
    rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
  rw [List.getElem?_append_right (by omega), hflen, Nat.sub_self]
  rfl

/-- `GuessBY`'s `ellByx`-write value at filtered index `0` (block 0). -/
theorem guessBYBlockWord_ellByx_write_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((guessBYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.guessBY Loc.ellByx (Val.cntAux 1 (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY) := by
  unfold guessBYBlockWord
  rw [List.filter_append]
  have hb0 : (guessBYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBY Loc.ellByx (Val.cntAux 1 (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `GuessBY`'s `ellByx`-write value at filtered index `i + 1` (block
`kws[i]`). -/
theorem guessBYBlockWord_ellByx_write_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((guessBYBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.guessBY Loc.ellByx (Val.cntAux (kw.1 + 1) kw.2),
        rfl⟩ : ThreadLabel (domainOf I) Tid.guessBY)) := by
  unfold guessBYBlockWord
  rw [List.filter_append]
  have hb0 : (guessBYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBY Loc.ellByx (Val.cntAux 1 (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessBYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.guessBY Loc.ellByx (Val.cntAux (kw.1 + 1) kw.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.guessBY Loc.ellByx (Val.cntAux (kw.1 + 1) kw.2), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBY)] := by
      intro kw
      unfold guessBYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

/-- `GuessBY`'s `zBxy`-read value at filtered index `k` (block `kws[k]`;
block 0 has none). -/
theorem guessBYBlockWord_zBxy_read_val (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (k : ℕ) :
    ((guessBYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.rd))[k]? =
      (kws[k]?).map (fun kw => (⟨EventLabel.rd Tid.guessBY Loc.zBxy (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
  unfold guessBYBlockWord
  rw [List.filter_append]
  have hb0 : (guessBYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.rd) =
      [] := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessBYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.guessBY Loc.zBxy (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.guessBY Loc.zBxy (Val.cnt kw.1), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBY)] := by
      intro kw
      unfold guessBYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.nil_append, List.getElem?_map]

/-- `GuessBY`'s `(j + 1)`-th `ellByx`-write (block `kws[j]`) is at position
`3 + j * 5 + 1` of `G.threadEvents Tid.guessBY`. -/
theorem guessBY_ellByx_write_nthWrite_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.guessBY = (guessBYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 3 + j * 5 + 1 < (G.threadEvents Tid.guessBY).length,
      G.nthWrite Tid.guessBY Loc.ellByx (j + 1) =
        some ((G.threadEvents Tid.guessBY)[3 + j * 5 + 1]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hb0count : ((guessBYBlock0Elems I v0).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt)).length = 1 := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rfl
  have hone_ew : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBY Loc.ellByx (Val.cntAux (kw.1 + 1) kw.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    intro kw
    unfold guessBYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hpartial0 : ((guessBYBlockRestElems I kwj).take 1).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt) = [] := by
    unfold guessBYBlockRestElems
    rfl
  have hcount_ew : (((guessBYBlockWord I v0 kws).take (3 + j * 5 + 1)).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.wt)).length = 1 + j := by
    have heq : guessBYBlockWord I v0 kws =
        guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I) := rfl
    have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
    have hsub : 3 + j * 5 + 1 - 3 = j * 5 + 1 := by omega
    have hle : (guessBYBlock0Elems I v0).length ≤ 3 + j * 5 + 1 := by rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle, hb0len, hsub,
      list_take_flatMap_uniform_offset (guessBYBlockRestElems I) 5 (fun _ => rfl) kws j 1 kwj hkj
        (by norm_num)]
    simp only [List.filter_append, List.length_append, hb0count, hpartial0, List.filter_nil,
      List.length_nil, Nat.add_zero]
    rw [list_filter_flatMap_distrib]
    simp only [hone_ew]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.guessBY).length = (guessBYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_ew : 3 + j * 5 + 1 < (G.threadEvents Tid.guessBY).length := by
    have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
    have hbrlen : (kws.flatMap (guessBYBlockRestElems I)).length = 5 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (guessBYBlockRestElems I a).length))
          = kws.map (fun _ => 5) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (guessBYBlockWord I v0 kws).length = 3 + 5 * kws.length := by
      show (guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_ew : (guessBYBlockWord I v0 kws)[3 + j * 5 + 1]? =
      some (⟨EventLabel.wt Tid.guessBY Loc.ellByx (Val.cntAux (kwj.1 + 1) kwj.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY) := by
    have hget := guessBYBlockWord_blockRest_pos I v0 kws j 1 kwj hkj (by norm_num)
    rw [hget]
    unfold guessBYBlockRestElems
    rfl
  refine ⟨hlen_ew, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.ellByx) (op := OpType.wt)
    hw1 hlen_ew hlabP_ew rfl rfl hcount_ew
  rwa [show G.nthEvent Tid.guessBY Loc.ellByx OpType.wt (1 + j) = G.nthWrite Tid.guessBY Loc.ellByx
    (j + 1) from by rw [Nat.add_comm]; rfl] at hewpos

/-- `GuessBY`'s `j`-th `zBxy`-read (block `kws[j]`) is at position
`3 + j * 5 + 3` of `G.threadEvents Tid.guessBY`. -/
theorem guessBY_zBxy_read_nthRead_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw1 : G.threadWord Tid.guessBY = (guessBYBlockWord I v0 kws).map some)
    (j : ℕ) {kwj : Fin 4 × Option (Fin I.n)} (hkj : kws[j]? = some kwj) :
    ∃ hlen : 3 + j * 5 + 3 < (G.threadEvents Tid.guessBY).length,
      G.nthRead Tid.guessBY Loc.zBxy j =
        some ((G.threadEvents Tid.guessBY)[3 + j * 5 + 3]'hlen).1 := by
  have hjlen : j < kws.length := (List.getElem?_eq_some_iff.mp hkj).1
  have hone_er : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessBY Loc.zBxy (Val.cnt kw.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    intro kw
    unfold guessBYBlockRestElems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hcount_er : (((guessBYBlockWord I v0 kws).take (3 + j * 5 + 3)).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.rd)).length = j := by
    have heq : guessBYBlockWord I v0 kws =
        guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I) := rfl
    have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
    have hle3 : (guessBYBlock0Elems I v0).length ≤ 3 + j * 5 + 3 := by rw [hb0len]; omega
    have hb0nil : (guessBYBlock0Elems I v0).filter
        (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.rd) = [] := by
      unfold guessBYBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hsplit := list_take_flatMap_uniform_offset (guessBYBlockRestElems I) 5 (fun _ => rfl)
      kws j 3 kwj hkj (by norm_num)
    have hpartial : ((guessBYBlockRestElems I kwj).take 3).filter
        (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.rd) = [] := by
      unfold guessBYBlockRestElems
      rfl
    have hsub : 3 + j * 5 + 3 - (guessBYBlock0Elems I v0).length = j * 5 + 3 := by
      rw [hb0len]; omega
    rw [heq, List.take_append, List.take_of_length_le hle3, hsub, hsplit, List.filter_append,
      List.filter_append, hb0nil, hpartial, List.nil_append, List.append_nil,
      list_filter_flatMap_distrib]
    simp only [hone_er]
    rw [list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hlenEq1 : (G.threadEvents Tid.guessBY).length = (guessBYBlockWord I v0 kws).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen_er : 3 + j * 5 + 3 < (G.threadEvents Tid.guessBY).length := by
    have hb0len : (guessBYBlock0Elems I v0).length = 3 := rfl
    have hbrlen : (kws.flatMap (guessBYBlockRestElems I)).length = 5 * kws.length := by
      rw [List.length_flatMap]
      have heq1 : (kws.map (fun a => (guessBYBlockRestElems I a).length))
          = kws.map (fun _ => 5) := List.map_congr_left (fun a _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, Nat.mul_comm]
    have hwlen : (guessBYBlockWord I v0 kws).length = 3 + 5 * kws.length := by
      show (guessBYBlock0Elems I v0 ++ kws.flatMap (guessBYBlockRestElems I)).length = _
      rw [List.length_append, hb0len, hbrlen]
    rw [hlenEq1, hwlen]
    nlinarith [hjlen]
  have hlabP_er : (guessBYBlockWord I v0 kws)[3 + j * 5 + 3]? =
      some (⟨EventLabel.rd Tid.guessBY Loc.zBxy (Val.cnt kwj.1), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY) := by
    have hget := guessBYBlockWord_blockRest_pos I v0 kws j 3 kwj hkj (by norm_num)
    rw [hget]
    unfold guessBYBlockRestElems
    rfl
  refine ⟨hlen_er, ?_⟩
  have herpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zBxy) (op := OpType.rd)
    hw1 hlen_er hlabP_er rfl rfl hcount_er
  rwa [show G.nthEvent Tid.guessBY Loc.zBxy OpType.rd j = G.nthRead Tid.guessBY Loc.zBxy j
    from rfl] at herpos

/-- The first `m` blocks of `outerRest` contain `m` `zBxy`-writes. -/
theorem guessBXOuterRest_zBxy_write_take_count (I : PCPInstance)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    ∀ m, m ≤ outerRest.length →
      (((outerRest.take m).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)).filter
        (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt)).length = m := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
      have hmlen : m ≤ outerRest.length := by omega
      have ihm := ih hmlen
      have hmlt : m < outerRest.length := by omega
      have hget : outerRest[m]? = some (outerRest[m]'hmlt) := List.getElem?_eq_getElem hmlt
      rw [List.take_add_one, hget]
      simp only [Option.toList_some, List.flatMap_append, List.filter_append, List.length_append]
      rw [ihm]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [guessBXOuterBlockElems_zBxy_write_filter I (outerRest[m]'hmlt).1 (outerRest[m]'hmlt).2]
      rfl

/-- The first `m` blocks of `outerRest` contain `m` `ellByx`-reads. -/
theorem guessBXOuterRest_ellByx_read_take_count (I : PCPInstance)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    ∀ m, m ≤ outerRest.length →
      (((outerRest.take m).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)).filter
        (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd)).length = m := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
      have hmlen : m ≤ outerRest.length := by omega
      have ihm := ih hmlen
      have hmlt : m < outerRest.length := by omega
      have hget : outerRest[m]? = some (outerRest[m]'hmlt) := List.getElem?_eq_getElem hmlt
      rw [List.take_add_one, hget]
      simp only [Option.toList_some, List.flatMap_append, List.filter_append, List.length_append]
      rw [ihm]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [guessBXOuterBlockElems_ellByx_read_filter I (outerRest[m]'hmlt).1 (outerRest[m]'hmlt).2]
      rfl

/-- `GuessBX`'s `0`-th `zBxy`-write is at position `0` of
`G.threadEvents Tid.guessBX`. -/
theorem guessBX_zBxy_write_nthWrite_pos0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some) :
    ∃ hlen : (0 : ℕ) < (G.threadEvents Tid.guessBX).length,
      G.nthWrite Tid.guessBX Loc.zBxy 0 =
        some ((G.threadEvents Tid.guessBX)[(0 : ℕ)]'hlen).1 := by
  have hlabP0 := guessBXBlockWord_zBxy_write_pos0 I v1 v2 vB0 inner0Rest outerRest
  have hlenEq : (G.threadEvents Tid.guessBX).length =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlen0 : (0 : ℕ) < (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hne : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest ≠ [] := by
      intro hcontra
      rw [hcontra] at hlabP0
      simp at hlabP0
    exact List.length_pos_of_ne_nil hne
  have hlen : (0 : ℕ) < (G.threadEvents Tid.guessBX).length := by rw [hlenEq]; exact hlen0
  refine ⟨hlen, ?_⟩
  have hewpos := G.nthEvent_eq_of_threadWord_pos (x := Loc.zBxy) (op := OpType.wt) (i := 0)
    hw1 hlen hlabP0 rfl rfl (by simp)
  rwa [show G.nthEvent Tid.guessBX Loc.zBxy OpType.wt 0 = G.nthWrite Tid.guessBX Loc.zBxy 0
    from rfl] at hewpos

/-- `GuessBX`'s `(m + 1)`-th `zBxy`-write is at position
`nestedOuterStart ks N (m + 1)` of `G.threadEvents Tid.guessBX`. -/
theorem guessBX_zBxy_write_nthWrite_pos_outer (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) {b : Val I × Val I} {vs : List (Val I × Val I × Val I)}
    (hmbv : outerRest[m]? = some (b, vs)) :
    ∃ hlen : nestedOuterStart ks N (m + 1) < (G.threadEvents Tid.guessBX).length,
      G.nthWrite Tid.guessBX Loc.zBxy (m + 1) =
        some ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N (m + 1)]'hlen).1 := by
  have hlabPm := guessBXBlockWord_zBxy_write_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len ks N hks hK0 houterLen houter houterLast m hm b vs hmbv
  have hlenEq : (G.threadEvents Tid.guessBX).length =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenP : nestedOuterStart ks N (m + 1) <
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length :=
    (List.getElem?_eq_some_iff.mp hlabPm).1
  have hlen : nestedOuterStart ks N (m + 1) < (G.threadEvents Tid.guessBX).length := by
    rw [hlenEq]; exact hlenP
  refine ⟨hlen, ?_⟩
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hposeq : nestedOuterStart ks N (m + 1) = 4 + K0 * 3 +
      ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length := by
    have hlenL := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast m (by omega)
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N (m + 1) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N m
      have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rwa [hgetD0] at hh
    rw [hlenL, hstartm]; omega
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hlead_filter : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) = [] := by
      intro a
      unfold guessBXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessBX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    have htail_nil : ((inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
        List (ThreadLabel (domainOf I) Tid.guessBX)).filter
        (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) = [] := by
      rw [List.filter_append, list_filter_flatMap_distrib]
      simp only [hinner_nil]
      rw [hflatnil inner0Rest, List.nil_append]
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), htail_nil]
  have hcount : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedOuterStart ks N (m + 1))).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt)).length = m + 1 := by
    have hle1 : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessBXInnerBlockElems I) ++
          [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length ≤
        4 + K0 * 3 + ((outerRest.take m).flatMap
          (fun q => guessBXOuterBlockElems I q.1 q.2)).length := by
      rw [hleadlen]; omega
    have hmlt : m < outerRest.length := by omega
    have htakeeq : (outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length) =
        (outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2) := by
      have hget : outerRest[m]? = some (outerRest[m]'hmlt) := List.getElem?_eq_getElem hmlt
      have h := list_take_flatMap_offset (fun q => guessBXOuterBlockElems I q.1 q.2) outerRest m 0
        (outerRest[m]'hmlt) hget (Nat.zero_le _)
      simpa using h
    rw [heq, hposeq, List.take_append, List.take_of_length_le hle1, hleadlen,
      show 4 + K0 * 3 + ((outerRest.take m).flatMap
          (fun q => guessBXOuterBlockElems I q.1 q.2)).length - (4 + K0 * 3)
        = ((outerRest.take m).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        from by omega,
      htakeeq, List.filter_append, List.length_append, hlead_filter,
      guessBXOuterRest_zBxy_write_take_count I outerRest m (by omega), List.length_singleton]
    omega
  exact G.nthEvent_eq_of_threadWord_pos (x := Loc.zBxy) (op := OpType.wt) hw1 hlen hlabPm rfl rfl
    hcount

/-- `GuessBX`'s `0`-th `ellByx`-read is at position `3 + K0 * 3` of
`G.threadEvents Tid.guessBX`. -/
theorem guessBX_ellByx_read_nthRead_pos0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some) :
    ∃ hlen : 3 + K0 * 3 < (G.threadEvents Tid.guessBX).length,
      G.nthRead Tid.guessBX Loc.ellByx 0 =
        some ((G.threadEvents Tid.guessBX)[3 + K0 * 3]'hlen).1 := by
  have hlabP0 := guessBXBlockWord_ellByx_read_pos0 I v1 v2 vB0 K0 inner0Rest hinner0len outerRest
  have hlenEq : (G.threadEvents Tid.guessBX).length =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenP : 3 + K0 * 3 < (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length :=
    (List.getElem?_eq_some_iff.mp hlabP0).1
  have hlen : 3 + K0 * 3 < (G.threadEvents Tid.guessBX).length := by rw [hlenEq]; exact hlenP
  refine ⟨hlen, ?_⟩
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hlead_filter_ellByx : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) = [] := by
      intro a
      unfold guessBXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessBX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_append, list_filter_flatMap_distrib]
    simp only [hinner_nil]
    rw [hflatnil inner0Rest, List.nil_append,
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hstep : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (3 + K0 * 3 + 1) =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take (3 + K0 * 3) ++
        [(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
    rw [List.take_add_one, hlabP0]; rfl
  have hcount1 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (3 + K0 * 3 + 1)).filter (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd)).length = 1 := by
    have h4 : (3 : ℕ) + K0 * 3 + 1 = 4 + K0 * 3 := by omega
    rw [h4, heq, List.take_append_of_le_length (le_of_eq hleadlen.symm),
      List.take_of_length_le (le_of_eq hleadlen), hlead_filter_ellByx, List.length_singleton]
  have hcount0 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (3 + K0 * 3)).filter (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd)).length = 0 := by
    have h := hcount1
    rw [hstep, List.filter_append, List.length_append] at h
    have hone : (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX)]) :
        List (ThreadLabel (domainOf I) Tid.guessBX)).filter
        (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
      rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rw [hone, List.length_singleton] at h
    omega
  exact G.nthEvent_eq_of_threadWord_pos (x := Loc.ellByx) (op := OpType.rd) (i := 0)
    hw1 hlen hlabP0 rfl rfl hcount0

/-- `GuessBX`'s `(m + 1)`-th `ellByx`-read is at position
`nestedOuterStart ks N (m + 2) - 1` of `G.threadEvents Tid.guessBX`. -/
theorem guessBX_ellByx_read_nthRead_pos_outer (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) {b : Val I × Val I} {vs : List (Val I × Val I × Val I)}
    (hmbv : outerRest[m]? = some (b, vs)) :
    ∃ hlen : nestedOuterStart ks N (m + 2) - 1 < (G.threadEvents Tid.guessBX).length,
      G.nthRead Tid.guessBX Loc.ellByx (m + 1) =
        some ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N (m + 2) - 1]'hlen).1 := by
  have hlabPm := guessBXBlockWord_ellByx_read_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len ks N hks hK0 houterLen houter houterLast m hm b vs hmbv
  have hlenEq : (G.threadEvents Tid.guessBX).length =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  have hlenP : nestedOuterStart ks N (m + 2) - 1 <
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length :=
    (List.getElem?_eq_some_iff.mp hlabPm).1
  have hlen : nestedOuterStart ks N (m + 2) - 1 < (G.threadEvents Tid.guessBX).length := by
    rw [hlenEq]; exact hlenP
  refine ⟨hlen, ?_⟩
  have hge2 : nestedOuterStart ks N (m + 2) ≥ 1 := by
    have hh := nestedOuterStart_ge ks N (m + 1)
    rw [show m + 1 + 1 = m + 2 from by omega] at hh
    omega
  have hstepidx : nestedOuterStart ks N (m + 2) - 1 + 1 = nestedOuterStart ks N (m + 2) := by omega
  have hstep : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedOuterStart ks N (m + 2) - 1 + 1) =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedOuterStart ks N (m + 2) - 1) ++
      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
    rw [List.take_add_one, hlabPm]; rfl
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hleadlen : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length = 4 + K0 * 3 := by
    rw [List.length_append, List.length_append]
    have hinner : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = K0 * 3 := by
      rw [List.length_flatMap]
      have heq1 : (inner0Rest.map (fun a => (guessBXInnerBlockElems I a).length)) =
          inner0Rest.map (fun _ => 3) := List.map_congr_left (fun _ _ => rfl)
      rw [heq1, List.map_const', List.sum_const_nat, hinner0len]
    simp only [List.length_cons, List.length_nil, hinner]
    omega
  have hlead_filter_ellByx : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) = [] := by
      intro a
      unfold guessBXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessBX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_append, list_filter_flatMap_distrib]
    simp only [hinner_nil]
    rw [hflatnil inner0Rest, List.nil_append,
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hposeq1 : nestedOuterStart ks N (m + 2) = 4 + K0 * 3 +
      ((outerRest.take (m + 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length := by
    have hlenL := guessBXOuterRest_prefix_length_eq I ks N hks outerRest houterLen houter
      houterLast (m + 1) (by omega)
    rw [show m + 1 + 1 = m + 2 from by omega] at hlenL
    have hstartm := nestedOuterStart_one ks N K0 hK0
    have hge : nestedOuterStart ks N (m + 2) ≥ 3 * K0 + 4 := by
      have hh := nestedOuterStart_ge ks N (m + 1)
      have hgetD0 : ks.getD 0 0 = K0 := by show (ks[0]?).getD 0 = K0; rw [hK0]; rfl
      rw [hgetD0, show m + 1 + 1 = m + 2 from by omega] at hh
      exact hh
    rw [hlenL, hstartm]; omega
  have hle1 : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).length ≤
      4 + K0 * 3 + ((outerRest.take (m + 1)).flatMap
        (fun q => guessBXOuterBlockElems I q.1 q.2)).length := by
    rw [hleadlen]; omega
  have htakeeq : (outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
      (((outerRest.take (m + 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length) =
      (outerRest.take (m + 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2) := by
    have hsplit : outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2) =
        (outerRest.take (m + 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2) ++
        (outerRest.drop (m + 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2) := by
      conv_lhs => rw [← List.take_append_drop (m + 1) outerRest]
      rw [List.flatMap_append]
    rw [hsplit, List.take_append_of_le_length (le_refl _), List.take_of_length_le (le_refl _)]
  have hcount1 : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedOuterStart ks N (m + 2))).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd)).length = m + 2 := by
    rw [heq, hposeq1, List.take_append, List.take_of_length_le hle1, hleadlen,
      show 4 + K0 * 3 + ((outerRest.take (m + 1)).flatMap
          (fun q => guessBXOuterBlockElems I q.1 q.2)).length - (4 + K0 * 3)
        = ((outerRest.take (m + 1)).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length
        from by omega,
      htakeeq, List.filter_append, List.length_append, hlead_filter_ellByx,
      guessBXOuterRest_ellByx_read_take_count I outerRest (m + 1) (by omega), List.length_singleton]
    omega
  have hcount : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
      (nestedOuterStart ks N (m + 2) - 1)).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd)).length = m + 1 := by
    have h := hcount1
    rw [← hstepidx, hstep, List.filter_append, List.length_append] at h
    have hone : (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX)]) :
        List (ThreadLabel (domainOf I) Tid.guessBX)).filter
        (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
      rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rw [hone, List.length_singleton] at h
    omega
  exact G.nthEvent_eq_of_threadWord_pos (x := Loc.ellByx) (op := OpType.rd) (i := m + 1)
    hw1 hlen hlabPm rfl rfl hcount

/-- `guessBXBlockWord` contains `outerRest.length + 1` `zBxy`-writes. -/
theorem guessBXBlockWord_zBxy_write_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (_ : inner0Rest.length = K0) :
    ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt)).length = outerRest.length + 1 := by
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hlead_filter : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).filter
      (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) = [] := by
      intro a
      unfold guessBXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessBX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    have htail_nil : ((inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
        List (ThreadLabel (domainOf I) Tid.guessBX)).filter
        (fun l => l.1.loc = Loc.zBxy ∧ l.1.op = OpType.wt) = [] := by
      rw [List.filter_append, list_filter_flatMap_distrib]
      simp only [hinner_nil]
      rw [hflatnil inner0Rest, List.nil_append]
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), htail_nil]
  rw [heq, List.filter_append, List.length_append, hlead_filter, List.length_singleton]
  conv_lhs => rw [show outerRest = outerRest.take outerRest.length from
    (List.take_of_length_le (le_refl _)).symm]
  rw [guessBXOuterRest_zBxy_write_take_count I outerRest outerRest.length (le_refl _)]
  omega

/-- `guessBXBlockWord` contains `outerRest.length + 1` `ellByx`-reads. -/
theorem guessBXBlockWord_ellByx_read_total_count (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (_ : inner0Rest.length = K0) :
    ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd)).length = outerRest.length + 1 := by
  have heq : guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest =
      (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) ++
      outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)) := rfl
  have hlead_filter_ellByx : (([ ⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
        , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
        inner0Rest.flatMap (guessBXInnerBlockElems I) ++
        [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]) :
      List (ThreadLabel (domainOf I) Tid.guessBX)).filter
      (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] := by
    have hinner_nil : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a).filter
        (fun l => l.1.loc = Loc.ellByx ∧ l.1.op = OpType.rd) = [] := by
      intro a
      unfold guessBXInnerBlockElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    have hflatnil : ∀ l : List (Val I × Val I × Val I),
        l.flatMap (fun (_ : Val I × Val I × Val I) =>
          ([] : List (ThreadLabel (domainOf I) Tid.guessBX))) = [] := by
      intro l
      induction l with
      | nil => rfl
      | cons _ t ih => simp [List.flatMap_cons, ih]
    simp only [List.cons_append, List.nil_append]
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_append, list_filter_flatMap_distrib]
    simp only [hinner_nil]
    rw [hflatnil inner0Rest, List.nil_append,
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [heq, List.filter_append, List.length_append, hlead_filter_ellByx, List.length_singleton]
  conv_lhs => rw [show outerRest = outerRest.take outerRest.length from
    (List.take_of_length_le (le_refl _)).symm]
  rw [guessBXOuterRest_ellByx_read_take_count I outerRest outerRest.length (le_refl _)]
  omega

/-- `GuessBX`'s `j`-th `zBxy`-write is at position `nestedOuterStart ks N j`
of `G.threadEvents Tid.guessBX`. -/
theorem guessBX_zBxy_write_nthWrite_pos_full (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (j : ℕ) (hj : j ≤ N + 1) :
    ∃ hlen : nestedOuterStart ks N j < (G.threadEvents Tid.guessBX).length,
      G.nthWrite Tid.guessBX Loc.zBxy j =
        some ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N j]'hlen).1 := by
  rcases j with _ | m
  · have h0 : nestedOuterStart ks N 0 = 0 := rfl
    rw [h0]
    exact guessBX_zBxy_write_nthWrite_pos0 I G hw1
  · have hmlen : m ≤ N := by omega
    obtain ⟨b, vs, hbv⟩ : ∃ b vs, outerRest[m]? = some (b, vs) := by
      by_cases hmN : m = N
      · subst hmN; obtain ⟨b, vs, hbv, -⟩ := houterLast; exact ⟨b, vs, hbv⟩
      · obtain ⟨b, vs, km, hbv, -, -⟩ := houter m (by omega); exact ⟨b, vs, hbv⟩
    exact guessBX_zBxy_write_nthWrite_pos_outer I G hinner0len hw1 hks hK0 houterLen houter
      houterLast m hmlen hbv

/-- `GuessBX`'s `j`-th `ellByx`-read is at position
`nestedOuterStart ks N (j + 1) - 1` of `G.threadEvents Tid.guessBX`. -/
theorem guessBX_ellByx_read_nthRead_pos_full (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (j : ℕ) (hj : j ≤ N + 1) :
    ∃ hlen : nestedOuterStart ks N (j + 1) - 1 < (G.threadEvents Tid.guessBX).length,
      G.nthRead Tid.guessBX Loc.ellByx j =
        some ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N (j + 1) - 1]'hlen).1 := by
  rcases j with _ | m
  · have h1 := nestedOuterStart_one ks N K0 hK0
    have heq : nestedOuterStart ks N (0 + 1) - 1 = 3 + K0 * 3 := by
      rw [Nat.zero_add]; omega
    rw [heq]
    exact guessBX_ellByx_read_nthRead_pos0 I G hinner0len hw1
  · have hmlen : m ≤ N := by omega
    obtain ⟨b, vs, hbv⟩ : ∃ b vs, outerRest[m]? = some (b, vs) := by
      by_cases hmN : m = N
      · subst hmN; obtain ⟨b, vs, hbv, -⟩ := houterLast; exact ⟨b, vs, hbv⟩
      · obtain ⟨b, vs, km, hbv, -, -⟩ := houter m (by omega); exact ⟨b, vs, hbv⟩
    exact guessBX_ellByx_read_nthRead_pos_outer I G hinner0len hw1 hks hK0 houterLen houter
      houterLast m hmlen hbv

/-- `GuessBX`'s `j`-th `zBxy`-write is at position `nestedOuterStart ks N j`
of its word, with value `(1 + j) % 4`. -/
theorem guessBXBlockWord_zBxy_write_val_full (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (hvB01 : vB0.1 = Val.cnt (1 : Fin 4))
    (houterval1 : ∀ m, m < N + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      b.1 = Val.cnt (⟨(2 + m) % 4, by omega⟩ : Fin 4))
    (j : ℕ) (hj : j ≤ N + 1) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N j]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBxy (Val.cnt (⟨(1 + j) % 4, by omega⟩ : Fin 4)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX) := by
  rcases j with _ | m
  · have h0 : nestedOuterStart ks N 0 = 0 := rfl
    rw [h0]
    have hlab := guessBXBlockWord_zBxy_write_pos0 I v1 v2 vB0 inner0Rest outerRest
    have hnat0 : (1 : ℕ) = (1 + 0) % 4 := by omega
    have hveq : (Val.cnt (1 : Fin 4) : Val I) = Val.cnt (⟨(1 + 0) % 4, by omega⟩ : Fin 4) := by
      congr 1
    rw [hlab, hvB01, hveq]
  · have hmlt : m ≤ N := by omega
    obtain ⟨b, vs, hbv⟩ : ∃ b vs, outerRest[m]? = some (b, vs) := by
      by_cases hmN : m = N
      · subst hmN; obtain ⟨b, vs, hbv, -⟩ := houterLast; exact ⟨b, vs, hbv⟩
      · obtain ⟨b, vs, km, hbv, -, -⟩ := houter m (by omega); exact ⟨b, vs, hbv⟩
    obtain ⟨b', vs', hbv', hbval1⟩ := houterval1 m (by omega)
    have hbeq : b' = b := congrArg Prod.fst (Option.some.inj (hbv'.symm.trans hbv))
    rw [hbeq] at hbval1
    have hlab := guessBXBlockWord_zBxy_write_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len ks N hks hK0 houterLen houter houterLast m hmlt b vs hbv
    have hnatm : (2 + m) % 4 = (1 + (m + 1)) % 4 := by omega
    have hveq : b.1 = Val.cnt (⟨(1 + (m + 1)) % 4, by omega⟩ : Fin 4) := by
      rw [hbval1]; congr 1; exact Fin.ext hnatm
    rw [hlab, hveq]

/-- `GuessBX`'s `j`-th `ellByx`-read is at position
`nestedOuterStart ks N (j + 1) - 1` of its word, with counter
`(1 + j) % 4`. -/
theorem guessBXBlockWord_ellByx_read_val_full (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (K0 : ℕ) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0len : inner0Rest.length = K0)
    (ks : List ℕ) (N : ℕ) (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (v0 : Fin I.n) (hvB02 : vB0.2 = Val.cntAux (1 : Fin 4) (some v0))
    (houterval2 : ∀ m, m < N + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∃ aux, b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) aux)
    (j : ℕ) (hj : j ≤ N + 1) :
    ∃ aux, (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[nestedOuterStart ks N (j + 1) - 1]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.ellByx (Val.cntAux (⟨(1 + j) % 4, by omega⟩ : Fin 4) aux),
        rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) := by
  rcases j with _ | m
  · refine ⟨some v0, ?_⟩
    have heq : nestedOuterStart ks N (0 + 1) - 1 = 3 + K0 * 3 := by
      have h1 := nestedOuterStart_one ks N K0 hK0
      simp only [Nat.zero_add]
      omega
    rw [heq]
    have hlab := guessBXBlockWord_ellByx_read_pos0 I v1 v2 vB0 K0 inner0Rest hinner0len outerRest
    have hnat0 : (1 : ℕ) = (1 + 0) % 4 := by omega
    have hveq : (Val.cntAux (1 : Fin 4) (some v0) : Val I) =
        Val.cntAux (⟨(1 + 0) % 4, by omega⟩ : Fin 4) (some v0) := by
      congr 1
    rw [hlab, hvB02, hveq]
  · have hmlt : m ≤ N := by omega
    obtain ⟨b, vs, hbv⟩ : ∃ b vs, outerRest[m]? = some (b, vs) := by
      by_cases hmN : m = N
      · subst hmN; obtain ⟨b, vs, hbv, -⟩ := houterLast; exact ⟨b, vs, hbv⟩
      · obtain ⟨b, vs, km, hbv, -, -⟩ := houter m (by omega); exact ⟨b, vs, hbv⟩
    obtain ⟨b', vs', hbv', aux, hbval2⟩ := houterval2 m (by omega)
    have hbeq : b' = b := congrArg Prod.fst (Option.some.inj (hbv'.symm.trans hbv))
    rw [hbeq] at hbval2
    refine ⟨aux, ?_⟩
    have hlab := guessBXBlockWord_ellByx_read_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len ks N hks hK0 houterLen houter houterLast m hmlt b vs hbv
    have hnatm : (2 + m) % 4 = (1 + (m + 1)) % 4 := by omega
    have hveq : b.2 = Val.cntAux (⟨(1 + (m + 1)) % 4, by omega⟩ : Fin 4) aux := by
      rw [hbval2]; congr 1; exact Fin.ext hnatm
    rw [hlab, hveq]

/-- Eq. (15)'s bridge pair `zBxy`/`ellByx` (`GuessBX`/`GuessBY`) satisfies
`NoSkipPair`'s hypotheses, read off the two threads' own closed forms
(`guessBX_shape_inv`, `guessBY_shape_inv`). `GuessBX` writes `zBxy` at the
head and reads `ellByx` at the tail of each outer iteration (positions
`nestedOuterStart ks N j` and `nestedOuterStart ks N (j + 1) - 1`);
`GuessBY` writes `ellByx` in every iteration and skips its first
`zBxy`-read, so its `j`-th `zBxy`-read sits in iteration `j + 1`. Both
locations have a single writer, so writer identification is
`writerTid_confined`. -/
theorem guessBX_guessBY_zBxy_noSkipPair (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.NoSkipPair Tid.guessBY Tid.guessBX Loc.zBxy Loc.ellByx := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessBX_run_of_reaches I G hG
  obtain ⟨v0, K0, js, v1, v2, vB0, inner0Rest, outerRest, -, -, hinner0len, houterLen, houter,
    houterLast, -, -, -, hvB01, hvB02, houterval2, -, -, -, hσ1⟩ :=
    guessBX_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := guessBY_run_of_reaches I G hG
  obtain ⟨v0', js', kws, -, -, hkwsval, hσ2⟩ := guessBY_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBX, hσ1]
  have hw2 : G.threadWord Tid.guessBY = (guessBYBlockWord I v0' kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBY, hσ2]
  have hks : (K0 :: guessBXJsToKs I js).length = js.length + 1 := by simp [guessBXJsToKs]
  have hK0 : (K0 :: guessBXJsToKs I js)[0]? = some K0 := rfl
  have houter' : ∀ j, j < js.length → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      (K0 :: guessBXJsToKs I js)[j + 1]? = some km ∧ vs.length = km + 1 := by
    intro j hj
    obtain ⟨b, vs, km, hbvs, hksm, hvslen⟩ := houter j hj
    exact ⟨b, vs, km, hbvs, hksm, hvslen⟩
  have houterval1' : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      b.1 = Val.cnt (⟨(2 + m) % 4, by omega⟩ : Fin 4) := by
    intro m hm
    obtain ⟨b, vs, hbv, hb1, -, -⟩ := houterval2 m hm
    exact ⟨b, vs, hbv, hb1⟩
  have houterval2' : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∃ aux, b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) aux := by
    intro m hm
    obtain ⟨b, vs, hbv, -, hbaux3, hbaux4⟩ := houterval2 m hm
    by_cases hmlt : m < js.length
    · obtain ⟨w, -, hb2⟩ := hbaux3 hmlt
      exact ⟨b, vs, hbv, some w, hb2⟩
    · exact ⟨b, vs, hbv, none, hbaux4 (by omega)⟩
  set ks := K0 :: guessBXJsToKs I js with hksdef
  set N := js.length with hNdef
  -- `GuessBX` has `N + 2` outer iterations, so `N + 2` `zBxy`-writes and `ellByx`-reads.
  have hBW : ∀ {j : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.guessBX Loc.zBxy j = some w →
      j ≤ N + 1 := by
    intro j w hw
    have hjtot : j < (G.opEvents Tid.guessBX Loc.zBxy OpType.wt).length :=
      (List.getElem?_eq_some_iff.mp hw).1
    have h1 := congrArg List.length
      (G.opEvents_map_lab_eq_filter_threadLabels Tid.guessBX Loc.zBxy OpType.wt)
    rw [List.length_map, List.length_map, G.threadLabels_eq_of_threadWord hw1] at h1
    have htc := guessBXBlockWord_zBxy_write_total_count I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len
    have htot := h1.trans htc
    omega
  have hBR : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.guessBX Loc.ellByx j = some r →
      j ≤ N + 1 := by
    intro j r hr
    have hjtot : j < (G.opEvents Tid.guessBX Loc.ellByx OpType.rd).length :=
      (List.getElem?_eq_some_iff.mp hr).1
    have h1 := congrArg List.length
      (G.opEvents_map_lab_eq_filter_threadLabels Tid.guessBX Loc.ellByx OpType.rd)
    rw [List.length_map, List.length_map, G.threadLabels_eq_of_threadWord hw1] at h1
    have htc := guessBXBlockWord_ellByx_read_total_count I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len
    have htot := h1.trans htc
    omega
  -- `GuessBX`'s `j`-th `zBxy`-write: at `nestedOuterStart ks N j`, value `(j+1) mod 4`.
  have hWp : ∀ j, j ≤ N + 1 →
      ∃ hlen : nestedOuterStart ks N j < (G.threadEvents Tid.guessBX).length,
      G.nthWrite Tid.guessBX Loc.zBxy j =
        some ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N j]'hlen).1 ∧
      ∃ c : Fin 4, ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N j]'hlen).1.val =
        Val.cnt c ∧ c.val = (j + 1) % 4 := by
    intro j hj
    obtain ⟨hlen, hpos⟩ := guessBX_zBxy_write_nthWrite_pos_full I G hinner0len hw1 hks hK0
      houterLen houter' houterLast j hj
    have hval := guessBXBlockWord_zBxy_write_val_full I v1 v2 vB0 K0 inner0Rest outerRest
      hinner0len ks N hks hK0 houterLen houter' houterLast hvB01 houterval1' j hj
    obtain ⟨eSub, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 _ _ hval
    refine ⟨hlen, hpos, ⟨(1 + j) % 4, by omega⟩, ?_, by simp only; omega⟩
    rw [show ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N j]'hlen) = eSub from heq,
      Event.val, hlab]
    rfl
  -- `GuessBX`'s `j`-th `ellByx`-read: at `nestedOuterStart ks N (j + 1) - 1`, value `⟨(j+1) mod 4, _⟩`.
  have hRq : ∀ j, j ≤ N + 1 →
      ∃ hlen : nestedOuterStart ks N (j + 1) - 1 < (G.threadEvents Tid.guessBX).length,
      G.nthRead Tid.guessBX Loc.ellByx j =
        some ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N (j + 1) - 1]'hlen).1 ∧
      ∃ (c : Fin 4) (aux : Option (Fin I.n)),
        ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N (j + 1) - 1]'hlen).1.val =
        Val.cntAux c aux ∧ c.val = (j + 1) % 4 := by
    intro j hj
    obtain ⟨hlen, hpos⟩ := guessBX_ellByx_read_nthRead_pos_full I G hinner0len hw1 hks hK0
      houterLen houter' houterLast j hj
    obtain ⟨aux, hval⟩ := guessBXBlockWord_ellByx_read_val_full I v1 v2 vB0 K0 inner0Rest
      outerRest hinner0len ks N hks hK0 houterLen houter' houterLast v0 hvB02 houterval2' j hj
    obtain ⟨eSub, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 _ _ hval
    refine ⟨hlen, hpos, ⟨(1 + j) % 4, by omega⟩, aux, ?_, by simp only; omega⟩
    rw [show ((G.threadEvents Tid.guessBX)[nestedOuterStart ks N (j + 1) - 1]'hlen) = eSub
      from heq, Event.val, hlab]
    rfl
  -- `GuessBY`'s `j`-th `zBxy`-read: value `(j+1) mod 4`, in block `kws[j]`.
  have hRp : ∀ {j : ℕ} {r : Event (domainOf I)}, G.nthRead Tid.guessBY Loc.zBxy j = some r →
      (∃ c : Fin 4, r.val = Val.cnt c ∧ c.val = (j + 1) % 4) ∧ j < kws.length := by
    intro j r hr
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hr
    have hf := (guessBYBlockWord_zBxy_read_val I v0' kws j).symm.trans hf
    rcases hk : kws[j]? with _ | kw
    · rw [hk] at hf; simp at hf
    · rw [hk] at hf
      have hlt := (List.getElem?_eq_some_iff.mp hk).1
      obtain ⟨w', hkw⟩ := hkwsval j hlt
      rw [hk] at hkw
      have hkw1 : kw.1.val = (1 + j) % 4 := by rw [Option.some.inj hkw]
      refine ⟨⟨kw.1, ?_, by omega⟩, hlt⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
  -- `GuessBY`'s `i`-th `ellByx`-write: value `⟨(i+1) mod 4, _⟩`, in block `kws[i-1]` for `i ≥ 1`.
  have hWq : ∀ {i : ℕ} {w : Event (domainOf I)}, G.nthWrite Tid.guessBY Loc.ellByx i = some w →
      (∃ (c : Fin 4) (aux : Option (Fin I.n)), w.val = Val.cntAux c aux ∧ c.val = (i + 1) % 4) ∧
      ∀ i', i = i' + 1 → i' < kws.length := by
    intro i w hw
    obtain ⟨lab, hf, hlab⟩ := G.exists_filter_of_nthEvent hw2 hw
    rcases i with _ | i'
    · have hf := (guessBYBlockWord_ellByx_write_val0 I v0' kws).symm.trans hf
      refine ⟨⟨1, some v0', ?_, rfl⟩, fun i' h => absurd h (by omega)⟩
      rw [Event.val, hlab, ← Option.some.inj hf]
      rfl
    · have hf := (guessBYBlockWord_ellByx_write_val_succ I v0' kws i').symm.trans hf
      rcases hk : kws[i']? with _ | kw
      · rw [hk] at hf; simp at hf
      · rw [hk] at hf
        have hlt := (List.getElem?_eq_some_iff.mp hk).1
        obtain ⟨w', hkw⟩ := hkwsval i' hlt
        rw [hk] at hkw
        have hkw1 : kw.1.val = (1 + i') % 4 := by rw [Option.some.inj hkw]
        refine ⟨⟨kw.1 + 1, kw.2, ?_, ?_⟩, fun j h => by omega⟩
        · rw [Event.val, hlab, ← Option.some.inj hf]
          rfl
        · rw [Fin.val_add, hkw1]; simp; omega
  have hkw : ∀ {n : ℕ}, n < kws.length → ∃ kw, kws[n]? = some kw :=
    fun hn => ⟨_, List.getElem?_eq_getElem hn⟩
  refine
    { match_p := ?_, match_q := ?_, writer_p := ?_, writer_q := ?_,
      po_A := ?_, po_B := ?_, ex_A := ?_, ex_B := ?_ }
  · intro i j w r hw hr hv
    obtain ⟨hlen, hpos, c, hc, hcv⟩ := hWp i (hBW hw)
    obtain ⟨⟨c', hc', hc'v⟩, -⟩ := hRp hr
    rw [Option.some.inj (hw.symm.trans hpos), hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro i j w r hw hr hv
    obtain ⟨⟨c, a, hc, hcv⟩, -⟩ := hWq hw
    obtain ⟨hlen, hpos, c', a', hc', hc'v⟩ := hRq j (hBR hr)
    rw [Option.some.inj (hr.symm.trans hpos), hc, hc'] at hv
    injection hv with hcc
    rw [hcc] at hcv
    omega
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.guessBX := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · intro j w r hr hrf
    obtain ⟨hwmem, -, hwwt, -, hwloc⟩ := G.rf_subset hrf
    have hrloc := (G.nthEvent_index hr).2.2.1
    have htid : w.tid = Tid.guessBY := by
      have h := writerTid_confined I G hG hwmem hwwt
      rw [hwloc, hrloc] at h
      exact Finset.mem_singleton.mp h
    exact G.exists_nthWrite_of_rf hrf htid hrloc
  · -- `guessBY`: `r(zBxy)` at `6+i*5` precedes `w(ellByx)` at `4+(ℓ-1)*5`.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (hRp hr).2
    obtain ⟨kw', hk'⟩ := hkw ((hWq hw).2 ℓ' rfl)
    obtain ⟨hlenR, hposR⟩ := guessBY_zBxy_read_nthRead_pos I G hw2 i hk
    obtain ⟨hlenW, hposW⟩ := guessBY_ellByx_write_nthWrite_pos I G hw2 ℓ' hk'
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    exact G.po_of_threadEvents_pos_lt Tid.guessBY hlenR hlenW (by omega)
  · -- `guessBX`: the `ellByx`-read ending outer iteration `i` precedes iteration `ℓ`'s `zBxy`-write.
    intro i ℓ r w hr hw hiℓ
    obtain ⟨hlenR, hposR, -⟩ := hRq i (hBR hr)
    obtain ⟨hlenW, hposW, -⟩ := hWp ℓ (hBW hw)
    rw [Option.some.inj (hr.symm.trans hposR), Option.some.inj (hw.symm.trans hposW)]
    have hmono := nestedOuterStart_strictMono ks N (show i + 1 < ℓ by omega)
    exact G.po_of_threadEvents_pos_lt Tid.guessBX hlenR hlenW (by omega)
  · intro i ℓ w hw hiℓ
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    obtain ⟨kw, hk⟩ := hkw (n := i) (by have := (hWq hw).2 ℓ' rfl; omega)
    exact ⟨_, (guessBY_zBxy_read_nthRead_pos I G hw2 i hk).2⟩
  · intro i ℓ w hw hiℓ
    exact ⟨_, (hRq i (by have := hBW hw; omega)).2.1⟩

theorem no_skipping_guessBX_guessBY_zBxy (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessBX Loc.zBxy i = some ew)
    (her : G.nthRead Tid.guessBY Loc.zBxy K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((guessBX_guessBY_zBxy_noSkipPair I G hG).no_skipping hG.1.1 K).1 hew her hrf

theorem no_skipping_guessBX_guessBY_ellByx (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessBY Loc.ellByx i = some ew)
    (her : G.nthRead Tid.guessBX Loc.ellByx K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((guessBX_guessBY_zBxy_noSkipPair I G hG).no_skipping hG.1.1 K).2 hew her hrf

/-! ## Eq. (17): the base cases

For each pair of Eq. (17), the base case of its first family (Appendix B):
the checker's first read on `x_α` (resp. `x_β`, `y_α`, `y_β`) expects a value
tagged with the guesser and the `First()` flag set, which only the guesser's
first write on that location carries. The locations have two writers each
(the guesser and the checker), and these edges differ from those of Eq. (16)
on the same locations. -/

/-- The `guessAXXAWritePred` filter equals the `∧`-predicate filter. -/
theorem guessAX_xA_write_filter_eq {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.guessAX)) :
    w.filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt) =
    w.filter (guessAXXAWritePred I) := by
  unfold guessAXXAWritePred xAWritePredCore
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

/-- The `checkXXAReadPred` filter equals the `∧`-predicate filter. -/
theorem checkX_xA_read_filter_eq {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.checkX)) :
    w.filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) =
    w.filter (checkXXAReadPred I) := by
  unfold checkXXAReadPred xAReadPredCore
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

/-- Eq. (17), base case, first direction: `CheckX`'s `0`-th
`xA`-read reads from `GuessAX`'s `0`-th `xA`-write. As in Appendix B, by
values alone: the read expects a value tagged `(Tid.guessAX, true)` (the
`First()` flag), which `GuessAX` writes only in its `0`-th write (`v1`); all
later writes are tagged `(Tid.guessAX, false)`. -/
theorem guessBX_xB_write_filter_eq {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.guessBX)) :
    w.filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt) =
    w.filter (guessBXXBWritePred I) := by
  unfold guessBXXBWritePred xBWritePredCore
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

theorem checkX_xB_read_filter_eq {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.checkX)) :
    w.filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) =
    w.filter (checkXXBReadPred I) := by
  unfold checkXXBReadPred xBReadPredCore
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

theorem no_skipping_guessAX_checkX_xA_base (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessAX Loc.xA i = some ew)
    (her : G.nthRead Tid.checkX Loc.xA 0 = some er) (hrf : G.rf ew er) :
    i = 0 := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessAX_run_of_reaches I G hG
  obtain ⟨v0G, K0, js, v1, v2, vB0, inner0Rest, outerRest, hα, hs1, hinner0len, houterlen,
    hpreOuter, hlastOuter, hv2, hinner0val, houterval, hvB01, hvB02, hbridgeval, hv1xA,
    hinner0valxA, houtervalxA, hσ1⟩ := guessAX_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := checkX_run_of_reaches I G hG
  obtain ⟨v0, js2, kws, hs2, hkwslen, hkwsval, hσ2⟩ := checkX_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAX, hσ1]
  have hw2 : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkX, hσ2]
  -- `er`'s value: `checkX`'s 0th `xA`-read, block0's singleton match.
  have her_eq := G.nthEvent_lab_of_threadWord hw2 Loc.xA OpType.rd 0
  rw [show G.nthEvent Tid.checkX Loc.xA OpType.rd 0 = G.nthRead Tid.checkX Loc.xA 0
    from rfl, her] at her_eq
  have hb0val : ((checkXBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd))[0]? =
      some (⟨EventLabel.rd Tid.checkX Loc.xA (Val.xTag (Tid.guessAX, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
    rw [checkX_xA_read_filter_eq]
    have heq : checkXBlockWord I v0 kws =
        checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I) := rfl
    rw [heq, List.filter_append, checkXBlock0Elems_xA_read_filter]
    rfl
  have her_eq := hb0val ▸ her_eq
  have herval : er.val = Val.xTag (Tid.guessAX, true) (some v0) := by
    simp only [Option.map_some, Option.some.injEq] at her_eq
    rw [Event.val, her_eq]; rfl
  have hvaleq : ew.val = Val.xTag (Tid.guessAX, true) (some v0) := by
    rw [← herval]; exact G.rf_matches hrf
  -- `ew`'s value: `guessAX`'s `i`-th `xA`-write.
  have hew_eq := G.nthEvent_lab_of_threadWord hw1 Loc.xA OpType.wt i
  rw [show G.nthEvent Tid.guessAX Loc.xA OpType.wt i = G.nthWrite Tid.guessAX Loc.xA i
    from rfl, hew] at hew_eq
  have hfilteq := guessAX_xA_write_filter_eq
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
  have hew_eq := hfilteq ▸ hew_eq
  have hew_eq := (guessAXBlockWord_xA_filter_eq I v1 v2 vB0 inner0Rest outerRest) ▸ hew_eq
  rw [List.append_assoc] at hew_eq
  cases i with
  | zero =>
      simp only [List.getElem?_append_left (by simp : (0 : ℕ) < ([_] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).length), List.getElem?_cons_zero] at hew_eq
      rfl
  | succ j =>
      exfalso
      set REST : List (ThreadLabel (domainOf I) Tid.guessAX) :=
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX)) ++
        outerRest.flatMap (fun p => p.2.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX))) with hRESTdef
      have hget : REST[j]?.map Subtype.val = some ew.lab := by
        rw [hRESTdef]
        rw [show ([(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX)] ++
            (inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX)) ++
            outerRest.flatMap (fun p => p.2.map (fun a =>
              (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessAX)))))[j + 1]? =
            (inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX)) ++
            outerRest.flatMap (fun p => p.2.map (fun a =>
              (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessAX))))[j + 1 - 1]?
          from List.getElem?_append_right (by simp)] at hew_eq
        simpa using hew_eq.symm
      obtain ⟨x, hxeq, hxval⟩ := Option.map_eq_some_iff.mp hget
      obtain ⟨hjlt, hjget⟩ := List.getElem?_eq_some_iff.mp hxeq
      have hxmem : x ∈ REST := hjget ▸ List.getElem_mem hjlt
      rw [hRESTdef, List.mem_append] at hxmem
      have hewlabeq : x.1 = ew.lab := hxval
      have htagfalse : ∃ letter, ew.lab = EventLabel.wt Tid.guessAX Loc.xA
          (Val.xTag (Tid.guessAX, false) letter) := by
        rcases hxmem with hxmem | hxmem
        · rw [List.mem_map] at hxmem
          obtain ⟨e, hemem, hfe⟩ := hxmem
          obtain ⟨n, hnlt, hne⟩ := List.getElem_of_mem hemem
          obtain ⟨e', jf, he'eq, _, he'val⟩ := hinner0valxA n hnlt
          have hee' : e = e' := by
            have := List.getElem?_eq_getElem hnlt
            rw [hne] at this
            rw [this] at he'eq
            exact Option.some.inj he'eq
          refine ⟨GuessAX.jthLetter I (some v0G) jf, ?_⟩
          rw [← hewlabeq, ← hfe, hee', he'val]
        · rw [List.mem_flatMap] at hxmem
          obtain ⟨p, hpmem, hxinp⟩ := hxmem
          obtain ⟨m, hmlt, hpe⟩ := List.getElem_of_mem hpmem
          obtain ⟨b, vs, hbvseq, hcaselt, hcaseeq⟩ := houtervalxA m (houterlen ▸ hmlt)
          have hpbvs : p = (b, vs) := by
            have := List.getElem?_eq_getElem hmlt
            rw [hpe] at this
            rw [this] at hbvseq
            exact Option.some.inj hbvseq
          rw [hpbvs] at hxinp
          rw [List.mem_map] at hxinp
          obtain ⟨a, hamem, hfa⟩ := hxinp
          obtain ⟨n, hnlt, hna⟩ := List.getElem_of_mem hamem
          rcases Nat.lt_or_ge m js.length with hmjs | hmjs
          · obtain ⟨w, hwjs, hforall⟩ := hcaselt hmjs
            obtain ⟨a', jf, ha'eq, _, ha'val⟩ := hforall n hnlt
            have haa' : a = a' := by
              have := List.getElem?_eq_getElem hnlt
              rw [hna] at this
              rw [this] at ha'eq
              exact Option.some.inj ha'eq
            refine ⟨GuessAX.jthLetter I (some w) jf, ?_⟩
            rw [← hewlabeq, ← hfa, haa', ha'val]
          · have hmeq : m = js.length := by omega
            have hforall := hcaseeq hmeq n hnlt
            obtain ⟨a', jf, ha'eq, _, ha'val⟩ := hforall
            have haa' : a = a' := by
              have := List.getElem?_eq_getElem hnlt
              rw [hna] at this
              rw [this] at ha'eq
              exact Option.some.inj ha'eq
            refine ⟨GuessAX.jthLetter I none jf, ?_⟩
            rw [← hewlabeq, ← hfa, haa', ha'val]
      obtain ⟨letter, hewlab⟩ := htagfalse
      have hewval : ew.val = Val.xTag (Tid.guessAX, false) letter := by
        rw [Event.val, hewlab]; rfl
      rw [hewval] at hvaleq
      injection hvaleq with h1 h2
      injection h1 with _ h1b
      exact absurd h1b (by decide)

/-- The `β` counterpart of `no_skipping_guessAX_checkX_xA_base`: `CheckX`'s
`0`-th `xB`-read reads from `GuessBX`'s `0`-th `xB`-write. -/
theorem no_skipping_guessBX_checkX_xB_base (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessBX Loc.xB i = some ew)
    (her : G.nthRead Tid.checkX Loc.xB 0 = some er) (hrf : G.rf ew er) :
    i = 0 := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessBX_run_of_reaches I G hG
  obtain ⟨v0G, K0, js, v1, v2, vB0, inner0Rest, outerRest, hα, hs1, hinner0len, houterlen,
    hpreOuter, hlastOuter, hv2, hinner0val, houterval, hvB01, hvB02, hbridgeval, hv1xB,
    hinner0valxB, houtervalxB, hσ1⟩ := guessBX_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := checkX_run_of_reaches I G hG
  obtain ⟨v0, js2, kws, hs2, hkwslen, hkwsval, hσ2⟩ := checkX_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBX, hσ1]
  have hw2 : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkX, hσ2]
  -- `er`'s value: `checkX`'s 0th `xB`-read, block0's singleton match.
  have her_eq := G.nthEvent_lab_of_threadWord hw2 Loc.xB OpType.rd 0
  rw [show G.nthEvent Tid.checkX Loc.xB OpType.rd 0 = G.nthRead Tid.checkX Loc.xB 0
    from rfl, her] at her_eq
  have hb0val : ((checkXBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd))[0]? =
      some (⟨EventLabel.rd Tid.checkX Loc.xB (Val.xTag (Tid.guessBX, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
    rw [checkX_xB_read_filter_eq]
    have heq : checkXBlockWord I v0 kws =
        checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I) := rfl
    rw [heq, List.filter_append, checkXBlock0Elems_xB_read_filter]
    rfl
  have her_eq := hb0val ▸ her_eq
  have herval : er.val = Val.xTag (Tid.guessBX, true) (some v0) := by
    simp only [Option.map_some, Option.some.injEq] at her_eq
    rw [Event.val, her_eq]; rfl
  have hvaleq : ew.val = Val.xTag (Tid.guessBX, true) (some v0) := by
    rw [← herval]; exact G.rf_matches hrf
  -- `ew`'s value: `guessBX`'s `i`-th `xB`-write.
  have hew_eq := G.nthEvent_lab_of_threadWord hw1 Loc.xB OpType.wt i
  rw [show G.nthEvent Tid.guessBX Loc.xB OpType.wt i = G.nthWrite Tid.guessBX Loc.xB i
    from rfl, hew] at hew_eq
  have hfilteq := guessBX_xB_write_filter_eq
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
  have hew_eq := hfilteq ▸ hew_eq
  have hew_eq := (guessBXBlockWord_xB_filter_eq I v1 v2 vB0 inner0Rest outerRest) ▸ hew_eq
  rw [List.append_assoc] at hew_eq
  cases i with
  | zero =>
      simp only [List.getElem?_append_left (by simp : (0 : ℕ) < ([_] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).length), List.getElem?_cons_zero] at hew_eq
      rfl
  | succ j =>
      exfalso
      set REST : List (ThreadLabel (domainOf I) Tid.guessBX) :=
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX)) ++
        outerRest.flatMap (fun p => p.2.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX))) with hRESTdef
      have hget : REST[j]?.map Subtype.val = some ew.lab := by
        rw [hRESTdef]
        rw [show ([(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX)] ++
            (inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX)) ++
            outerRest.flatMap (fun p => p.2.map (fun a =>
              (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessBX)))))[j + 1]? =
            (inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX)) ++
            outerRest.flatMap (fun p => p.2.map (fun a =>
              (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessBX))))[j + 1 - 1]?
          from List.getElem?_append_right (by simp)] at hew_eq
        simpa using hew_eq.symm
      obtain ⟨x, hxeq, hxval⟩ := Option.map_eq_some_iff.mp hget
      obtain ⟨hjlt, hjget⟩ := List.getElem?_eq_some_iff.mp hxeq
      have hxmem : x ∈ REST := hjget ▸ List.getElem_mem hjlt
      rw [hRESTdef, List.mem_append] at hxmem
      have hewlabeq : x.1 = ew.lab := hxval
      have htagfalse : ∃ letter, ew.lab = EventLabel.wt Tid.guessBX Loc.xB
          (Val.xTag (Tid.guessBX, false) letter) := by
        rcases hxmem with hxmem | hxmem
        · rw [List.mem_map] at hxmem
          obtain ⟨e, hemem, hfe⟩ := hxmem
          obtain ⟨n, hnlt, hne⟩ := List.getElem_of_mem hemem
          obtain ⟨e', jf, he'eq, _, he'val⟩ := hinner0valxB n hnlt
          have hee' : e = e' := by
            have := List.getElem?_eq_getElem hnlt
            rw [hne] at this
            rw [this] at he'eq
            exact Option.some.inj he'eq
          refine ⟨GuessBX.jthLetter I (some v0G) jf, ?_⟩
          rw [← hewlabeq, ← hfe, hee', he'val]
        · rw [List.mem_flatMap] at hxmem
          obtain ⟨p, hpmem, hxinp⟩ := hxmem
          obtain ⟨m, hmlt, hpe⟩ := List.getElem_of_mem hpmem
          obtain ⟨b, vs, hbvseq, hcaselt, hcaseeq⟩ := houtervalxB m (houterlen ▸ hmlt)
          have hpbvs : p = (b, vs) := by
            have := List.getElem?_eq_getElem hmlt
            rw [hpe] at this
            rw [this] at hbvseq
            exact Option.some.inj hbvseq
          rw [hpbvs] at hxinp
          rw [List.mem_map] at hxinp
          obtain ⟨a, hamem, hfa⟩ := hxinp
          obtain ⟨n, hnlt, hna⟩ := List.getElem_of_mem hamem
          rcases Nat.lt_or_ge m js.length with hmjs | hmjs
          · obtain ⟨w, hwjs, hforall⟩ := hcaselt hmjs
            obtain ⟨a', jf, ha'eq, _, ha'val⟩ := hforall n hnlt
            have haa' : a = a' := by
              have := List.getElem?_eq_getElem hnlt
              rw [hna] at this
              rw [this] at ha'eq
              exact Option.some.inj ha'eq
            refine ⟨GuessBX.jthLetter I (some w) jf, ?_⟩
            rw [← hewlabeq, ← hfa, haa', ha'val]
          · have hmeq : m = js.length := by omega
            have hforall := hcaseeq hmeq n hnlt
            obtain ⟨a', jf, ha'eq, _, ha'val⟩ := hforall
            have haa' : a = a' := by
              have := List.getElem?_eq_getElem hnlt
              rw [hna] at this
              rw [this] at ha'eq
              exact Option.some.inj ha'eq
            refine ⟨GuessBX.jthLetter I none jf, ?_⟩
            rw [← hewlabeq, ← hfa, haa', ha'val]
      obtain ⟨letter, hewlab⟩ := htagfalse
      have hewval : ew.val = Val.xTag (Tid.guessBX, false) letter := by
        rw [Event.val, hewlab]; rfl
      rw [hewval] at hvaleq
      injection hvaleq with h1 h2
      injection h1 with _ h1b
      exact absurd h1b (by decide)

/-- The `y`-`α` counterpart of `no_skipping_guessAX_checkX_xA_base`: `CheckY`'s
`0`-th `yA`-read reads from `GuessAY`'s `0`-th `yA`-write, by values alone
(`guessAYBlockWord_yA_write_val0`/`_val_succ`). -/
theorem no_skipping_guessAY_checkY_yA_base (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessAY Loc.yA i = some ew)
    (her : G.nthRead Tid.checkY Loc.yA 0 = some er) (hrf : G.rf ew er) :
    i = 0 := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessAY_run_of_reaches I G hG
  obtain ⟨v0G, js1, kws1, hs1, hkwslen1, hkwsval1, hσ1⟩ := guessAY_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := checkY_run_of_reaches I G hG
  obtain ⟨v0, js2, kws2, hs2, hkwslen2, hkwsval2, hσ2⟩ := checkY_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessAY = (guessAYBlockWord I v0G kws1).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAY, hσ1]
  have hw2 : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws2).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkY, hσ2]
  -- `er`'s value: `checkY`'s 0th `yA`-read, block0's leading (offset-2) match.
  have her_eq := G.nthEvent_lab_of_threadWord hw2 Loc.yA OpType.rd 0
  rw [show G.nthEvent Tid.checkY Loc.yA OpType.rd 0 = G.nthRead Tid.checkY Loc.yA 0
    from rfl, her] at her_eq
  have hb0val : ((checkYBlockWord I v0 kws2).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd))[0]? =
      some (⟨EventLabel.rd Tid.checkY Loc.yA (Val.yTag (Tid.guessAY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
    have heq : checkYBlockWord I v0 kws2 =
        checkYBlock0Elems I v0 ++ kws2.flatMap (checkYBlockRestElems I) := rfl
    rw [heq, List.filter_append]
    have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkY Loc.yA (Val.yTag (Tid.guessAY, true) (some v0)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkY)] := by
      unfold checkYBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rw [hb0, List.getElem?_append_left (by simp)]
    rfl
  have her_eq := hb0val ▸ her_eq
  have herval : er.val = Val.yTag (Tid.guessAY, true) (some v0) := by
    simp only [Option.map_some, Option.some.injEq] at her_eq
    rw [Event.val, her_eq]; rfl
  have hvaleq : ew.val = Val.yTag (Tid.guessAY, true) (some v0) := by
    rw [← herval]; exact G.rf_matches hrf
  -- `ew`'s value: `guessAY`'s `i`-th `yA`-write.
  have hew_eq := G.nthEvent_lab_of_threadWord hw1 Loc.yA OpType.wt i
  rw [show G.nthEvent Tid.guessAY Loc.yA OpType.wt i = G.nthWrite Tid.guessAY Loc.yA i
    from rfl, hew] at hew_eq
  cases i with
  | zero =>
      have h0 := guessAYBlockWord_yA_write_val0 I v0G kws1
      have hew_eq := h0 ▸ hew_eq
      simp only [Option.map_some, Option.some.injEq] at hew_eq
      rfl
  | succ j =>
      exfalso
      have hjopt := guessAYBlockWord_yA_write_val_succ I v0G kws1 j
      have hew_eq := hjopt ▸ hew_eq
      rcases hjw : kws1[j]? with _ | kw
      · rw [hjw] at hew_eq; simp at hew_eq
      · rw [hjw] at hew_eq
        simp only [Option.map_some, Option.some.injEq] at hew_eq
        have hewval : ew.val = Val.yTag (Tid.guessAY, false) kw.2 := by
          have h := congrArg EventLabel.val hew_eq
          simpa [Event.val, EventLabel.val] using h
        rw [hewval] at hvaleq
        injection hvaleq with h1 h2
        injection h1 with _ h1b
        exact absurd h1b (by decide)

/-- The `β` counterpart of `guessAX_xA_write_filter_eq'`. -/
theorem guessBX_xB_write_filter_eq' {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.guessBX)) :
    w.filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt) =
    w.filter (fun l => match l.1.loc, l.1.op with
      | Loc.xB, OpType.wt => true | _, _ => false) := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

/-- The `match`-based `xA`-write filter of
`guessAXBlockWord_xA_write_total_count` equals the `∧`-predicate filter. By
list induction. -/
theorem guessAX_xA_write_filter_eq' {I : PCPInstance}
    (w : List (ThreadLabel (domainOf I) Tid.guessAX)) :
    w.filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt) =
    w.filter (fun l => match l.1.loc, l.1.op with
      | Loc.xA, OpType.wt => true | _, _ => false) := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter_cons]
    cases hloc : a.1.loc <;> cases hop : a.1.op <;> simp [hloc, hop, ih]

/-- `GuessBY`'s `yB`-write value at filtered index `0` (block 0). -/
theorem guessBYBlockWord_yB_write_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((guessBYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt))[0]? =
      some (⟨EventLabel.wt Tid.guessBY Loc.yB (Val.yTag (Tid.guessBY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY) := by
  unfold guessBYBlockWord
  rw [List.filter_append]
  have hb0 : (guessBYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBY Loc.yB (Val.yTag (Tid.guessBY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `GuessBY`'s `yB`-write value at filtered index `i + 1` (block `kws[i]`). -/
theorem guessBYBlockWord_yB_write_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((guessBYBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.wt Tid.guessBY Loc.yB (Val.yTag (Tid.guessBY, false) kw.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
  unfold guessBYBlockWord
  rw [List.filter_append]
  have hb0 : (guessBYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
      [(⟨EventLabel.wt Tid.guessBY Loc.yB (Val.yTag (Tid.guessBY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)] := by
    unfold guessBYBlock0Elems
    rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (guessBYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
      kws.map (fun kw => (⟨EventLabel.wt Tid.guessBY Loc.yB (Val.yTag (Tid.guessBY, false) kw.2), rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (guessBYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.wt) =
        [(⟨EventLabel.wt Tid.guessBY Loc.yB (Val.yTag (Tid.guessBY, false) kw.2), rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBY)] := by
      intro kw
      unfold guessBYBlockRestElems
      rw [List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr, List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_singleton, Nat.add_sub_cancel]

/-- The `y`-`β` counterpart of `no_skipping_guessAY_checkY_yA_base`:
`CheckY`'s `0`-th `yB`-read (position `3` of block 0) reads from `GuessBY`'s
`0`-th `yB`-write. -/
theorem no_skipping_guessBY_checkY_yB_base (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessBY Loc.yB i = some ew)
    (her : G.nthRead Tid.checkY Loc.yB 0 = some er) (hrf : G.rf ew er) :
    i = 0 := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessBY_run_of_reaches I G hG
  obtain ⟨v0G, js1, kws1, hs1, hkwslen1, hkwsval1, hσ1⟩ := guessBY_shape_inv I hrun1
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := checkY_run_of_reaches I G hG
  obtain ⟨v0, js2, kws2, hs2, hkwslen2, hkwsval2, hσ2⟩ := checkY_shape_inv I hrun2
  have hw1 : G.threadWord Tid.guessBY = (guessBYBlockWord I v0G kws1).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBY, hσ1]
  have hw2 : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws2).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkY, hσ2]
  -- `er`'s value: `checkY`'s 0th `yB`-read, block0's offset-3 match.
  have her_eq := G.nthEvent_lab_of_threadWord hw2 Loc.yB OpType.rd 0
  rw [show G.nthEvent Tid.checkY Loc.yB OpType.rd 0 = G.nthRead Tid.checkY Loc.yB 0
    from rfl, her] at her_eq
  have hb0val : ((checkYBlockWord I v0 kws2).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd))[0]? =
      some (⟨EventLabel.rd Tid.checkY Loc.yB (Val.yTag (Tid.guessBY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
    have heq : checkYBlockWord I v0 kws2 =
        checkYBlock0Elems I v0 ++ kws2.flatMap (checkYBlockRestElems I) := rfl
    rw [heq, List.filter_append]
    have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkY Loc.yB (Val.yTag (Tid.guessBY, true) (some v0)), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkY)] := by
      unfold checkYBlock0Elems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    rw [hb0, List.getElem?_append_left (by simp)]
    rfl
  have her_eq := hb0val ▸ her_eq
  have herval : er.val = Val.yTag (Tid.guessBY, true) (some v0) := by
    simp only [Option.map_some, Option.some.injEq] at her_eq
    rw [Event.val, her_eq]; rfl
  have hvaleq : ew.val = Val.yTag (Tid.guessBY, true) (some v0) := by
    rw [← herval]; exact G.rf_matches hrf
  -- `ew`'s value: `guessBY`'s `i`-th `yB`-write.
  have hew_eq := G.nthEvent_lab_of_threadWord hw1 Loc.yB OpType.wt i
  rw [show G.nthEvent Tid.guessBY Loc.yB OpType.wt i = G.nthWrite Tid.guessBY Loc.yB i
    from rfl, hew] at hew_eq
  cases i with
  | zero =>
      have h0 := guessBYBlockWord_yB_write_val0 I v0G kws1
      have hew_eq := h0 ▸ hew_eq
      simp only [Option.map_some, Option.some.injEq] at hew_eq
      rfl
  | succ j =>
      exfalso
      have hjopt := guessBYBlockWord_yB_write_val_succ I v0G kws1 j
      have hew_eq := hjopt ▸ hew_eq
      rcases hjw : kws1[j]? with _ | kw
      · rw [hjw] at hew_eq; simp at hew_eq
      · rw [hjw] at hew_eq
        simp only [Option.map_some, Option.some.injEq] at hew_eq
        have hewval : ew.val = Val.yTag (Tid.guessBY, false) kw.2 := by
          have h := congrArg EventLabel.val hew_eq
          simpa [Event.val, EventLabel.val] using h
        rw [hewval] at hvaleq
        injection hvaleq with h1 h2
        injection h1 with _ h1b
        exact absurd h1b (by decide)

/-! ## Who writes what a read reads -/

/-- On a location with a single writer `tw` (`writerTids x = {tw}`), every
write is `tw`'s. -/
theorem writer_of_single_writer (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) {tw tr : Tid} {x : Loc}
    (hx : writerTids x = {tw}) {i : ℕ} {er w : Event (domainOf I)}
    (her : G.nthRead tr x i = some er) (hrf : G.rf w er) : w.tid = tw := by
  obtain ⟨hmem, -, hwt, -, hwloc⟩ := G.rf_subset hrf
  obtain ⟨-, -, hloc, -⟩ := G.nthEvent_index her
  have h := writerTid_confined I G hG hmem hwt
  rw [hwloc, hloc, hx] at h
  exact Finset.mem_singleton.mp h

/-- If every read node of `tr`'s program on `x` expects a value tagged with
`tw`, then every write read by `tr` on `x` is `tw`'s. -/
theorem writer_of_read_tag {I : PCPInstance} {V : Vocabulary (domainOf I)} {tr tw : Tid}
    {C_t : Command (domainOf I) V} {φ₀ : V.Store} (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    (hex : ∃ (s : List V.LVal) (cLast : Config (domainOf I) V) (φ' : V.Store),
      Command.Run tr s (C_t, φ₀) (G.threadLabels tr) cLast [] (Command.term, φ'))
    {x : Loc} (htag : ∀ (e : V.VExpr) (φ : V.Store), Command.HasRead x e C_t →
      (V.evalV e φ).writerTid = some tw)
    {i : ℕ} {er w : Event (domainOf I)}
    (her : G.nthRead tr x i = some er) (hrf : G.rf w er) : w.tid = tw := by
  obtain ⟨s, cLast, φ', hrun⟩ := hex
  obtain ⟨-, htid, hloc, hop⟩ := G.nthEvent_index her
  have hmem := (G.mem_opEvents_iff.mp (List.mem_of_getElem? her)).1
  have hlab := G.mem_threadLabels_of_mem_Events hmem htid
  obtain ⟨e, hhr, φ, hval⟩ := hrun.read_hasRead _ hlab hop
  have hval' : er.val = V.evalV e φ := hval
  have hhr' : Command.HasRead er.loc e C_t := hhr
  have hhr'' : Command.HasRead x e C_t := hloc ▸ hhr'
  obtain ⟨hwmem, -, hwt, -, -⟩ := G.rf_subset hrf
  apply G_writer_val_tid I G hG hwmem hwt
  rw [G.rf_matches hrf, hval']
  exact htag e φ hhr''

/-- The read nodes of `CheckX`'s program: on `x_α`/`x_β` it expects `g_α^x`'s
resp. `g_β^x`'s tag, on `x'_α`/`x'_β` the tag of `c^{x'}`. -/
theorem CheckX.hasRead_writerTid (I : PCPInstance) {u : Loc} {e : CheckX.VExpr}
    (h : Command.HasRead u e (CheckX.program I)) (φ : CheckX.Vars → CheckX.Vals I) :
    (u = Loc.xA → (CheckX.evalV I e φ).writerTid = some Tid.guessAX) ∧
    (u = Loc.xB → (CheckX.evalV I e φ).writerTid = some Tid.guessBX) ∧
    (u = Loc.xA' → (CheckX.evalV I e φ).writerTid = some Tid.primeCheckX) ∧
    (u = Loc.xB' → (CheckX.evalV I e φ).writerTid = some Tid.primeCheckX) := by
  unfold CheckX.program CheckX.body Command.firstIt at h
  simp only [Command.HasRead, false_or, or_false] at h
  cases e <;> simp_all only [reduceCtorEq, and_false, or_self, or_false, Val.writerTid, evalV, imp_self, Option.some.injEq, and_self, false_or, imp_false, implies_true, and_true]
  all_goals (rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)

/-- The read nodes of `PrimeCheckX`'s program: on `x'_α`/`x'_β` it expects
`g_α^{x'}`'s resp. `g_β^{x'}`'s tag, on `x_α`/`x_β` the tag of `c^x`. -/
theorem PrimeCheckX.hasRead_writerTid (I : PCPInstance) {u : Loc} {e : PrimeCheckX.VExpr}
    (h : Command.HasRead u e (PrimeCheckX.program I)) (φ : PrimeCheckX.Vars → PrimeCheckX.Vals) :
    (u = Loc.xA' → (PrimeCheckX.evalV I e φ).writerTid = some Tid.primeAX) ∧
    (u = Loc.xB' → (PrimeCheckX.evalV I e φ).writerTid = some Tid.primeBX) ∧
    (u = Loc.xA → (PrimeCheckX.evalV I e φ).writerTid = some Tid.checkX) ∧
    (u = Loc.xB → (PrimeCheckX.evalV I e φ).writerTid = some Tid.checkX) := by
  unfold PrimeCheckX.program Command.whileNdet PrimeCheckX.body at h
  simp only [Command.HasRead, false_or, or_false] at h
  cases e <;> simp_all only [reduceCtorEq, and_false, or_self, or_false, Val.writerTid, evalV, Fin.isValue, imp_self, Option.some.injEq, and_self, false_or, imp_false, implies_true, and_true]
  all_goals (rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)

/-- The read nodes of `CheckY`'s program, as `CheckX.hasRead_writerTid`. -/
theorem CheckY.hasRead_writerTid (I : PCPInstance) {u : Loc} {e : CheckY.VExpr}
    (h : Command.HasRead u e (CheckY.program I)) (φ : CheckY.Vars → CheckY.Vals I) :
    (u = Loc.yA → (CheckY.evalV I e φ).writerTid = some Tid.guessAY) ∧
    (u = Loc.yB → (CheckY.evalV I e φ).writerTid = some Tid.guessBY) ∧
    (u = Loc.yA' → (CheckY.evalV I e φ).writerTid = some Tid.primeCheckY) ∧
    (u = Loc.yB' → (CheckY.evalV I e φ).writerTid = some Tid.primeCheckY) := by
  unfold CheckY.program CheckY.body Command.firstIt at h
  simp only [Command.HasRead, false_or, or_false] at h
  cases e <;> simp_all only [reduceCtorEq, and_false, or_self, or_false, Val.writerTid, evalV, imp_self, Option.some.injEq, and_self, false_or, imp_false, implies_true, and_true]
  all_goals (rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)

/-- The read nodes of `PrimeCheckY`'s program, as `PrimeCheckX.hasRead_writerTid`. -/
theorem PrimeCheckY.hasRead_writerTid (I : PCPInstance) {u : Loc} {e : PrimeCheckY.VExpr}
    (h : Command.HasRead u e (PrimeCheckY.program I)) (φ : PrimeCheckY.Vars → PrimeCheckY.Vals) :
    (u = Loc.yA' → (PrimeCheckY.evalV I e φ).writerTid = some Tid.primeAY) ∧
    (u = Loc.yB' → (PrimeCheckY.evalV I e φ).writerTid = some Tid.primeBY) ∧
    (u = Loc.yA → (PrimeCheckY.evalV I e φ).writerTid = some Tid.checkY) ∧
    (u = Loc.yB → (PrimeCheckY.evalV I e φ).writerTid = some Tid.checkY) := by
  unfold PrimeCheckY.program Command.whileNdet PrimeCheckY.body at h
  simp only [Command.HasRead, false_or, or_false] at h
  cases e <;> simp_all only [reduceCtorEq, and_false, or_self, or_false, Val.writerTid, evalV, Fin.isValue, imp_self, Option.some.injEq, and_self, false_or, imp_false, implies_true, and_true]
  all_goals (rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)

/-! ## Eq. (17): the four pairs, by the shared argument

Each pair of Eq. (17) satisfies `ExecutionGraph.CrossPair`
(`Soundness/NoSkippingPair.lean`): the tags and Eq. (15)/(16) supply its
first fields, the closed-form words of the four threads (`*_shape_inv`) the
facts "by the construction". -/

/-! ### `g_α^x`, `g_α^{x'}`, `c^x`, `c^{x'}` on `x_α`, `x'_α` -/

/-- `GuessAX`'s writes on `x_α` and `z_α^{x',x}` and reads on `z_α^{x,x'}`, at
their positions `nestedInnerStart ks P (+1, +2)`. -/
theorem guessAX_xA_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ} {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hw1 : G.threadWord Tid.guessAX = (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0) (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    (∀ {j : ℕ} {e : Event (domainOf I)}, G.nthWrite Tid.guessAX Loc.xA j = some e →
      j ≤ ksPrefix ks (N + 1)) ∧
    (∀ {j : ℕ}, j ≤ ksPrefix ks (N + 1) →
      ∃ hP : nestedInnerStart ks j < (G.threadEvents Tid.guessAX).length,
        G.nthWrite Tid.guessAX Loc.xA j =
          some ((G.threadEvents Tid.guessAX)[nestedInnerStart ks j]'hP).1) ∧
    (∀ {j : ℕ}, j ≤ ksPrefix ks (N + 1) →
      ∃ hP : nestedInnerStart ks j + 1 < (G.threadEvents Tid.guessAX).length,
        G.nthWrite Tid.guessAX Loc.zAx'x j =
          some ((G.threadEvents Tid.guessAX)[nestedInnerStart ks j + 1]'hP).1) ∧
    (∀ {m : ℕ}, m + 1 ≤ ksPrefix ks (N + 1) →
      ∃ hP : nestedInnerStart ks (m + 1) + 2 < (G.threadEvents Tid.guessAX).length,
        G.nthRead Tid.guessAX Loc.zAxx' m =
          some ((G.threadEvents Tid.guessAX)[nestedInnerStart ks (m + 1) + 2]'hP).1) := by
  have hthreadlen : (G.threadEvents Tid.guessAX).length =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  refine ⟨fun {j e} he => ?_, fun {j} hj => ?_, fun {j} hj => ?_, fun {m} hm => ?_⟩
  · have htotcount : (G.opEvents Tid.guessAX Loc.xA OpType.wt).length =
        ksPrefix ks (N + 1) + 1 := by
      have hL := G.opEvents_map_lab_eq_filter_threadLabels Tid.guessAX Loc.xA OpType.wt
      have hLlen := congrArg List.length hL
      rw [List.length_map, List.length_map, G.threadLabels_eq_of_threadWord hw1] at hLlen
      have hbridge := guessAX_xA_write_filter_eq'
        (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
      have hLlen2 := hbridge ▸ hLlen
      rw [hLlen2]
      exact guessAXBlockWord_xA_write_total_count I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
        hK0 hinner0len houterLen houter houterLast
    have := (List.getElem?_eq_some_iff.mp he).1
    omega
  · obtain ⟨val, hval⟩ := guessAXBlockWord_xA_write_pos_full I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter houterLast j hj
    have hlen : nestedInnerStart ks j < (G.threadEvents Tid.guessAX).length := by
      rw [hthreadlen]; exact (List.getElem?_eq_some_iff.mp hval).1
    have hcount : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks j)).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.wt)).length
        = j := by
      rw [guessAX_xA_write_filter_eq']
      exact guessAXBlockWord_xA_write_take_count_full I v1 v2 vB0 K0 inner0Rest outerRest ks N
        hks hK0 hinner0len houterLen houter houterLast j hj
    exact ⟨hlen, G.nthEvent_eq_of_threadWord_pos hw1 hlen hval rfl rfl hcount⟩
  · obtain ⟨val, hval⟩ := guessAXBlockWord_zAx'x_write_pos_full I v1 v2 vB0 K0 inner0Rest
      outerRest ks N hks hK0 hinner0len houterLen houter houterLast j hj
    have hlen : nestedInnerStart ks j + 1 < (G.threadEvents Tid.guessAX).length := by
      rw [hthreadlen]; exact (List.getElem?_eq_some_iff.mp hval).1
    have hcount : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks j + 1)).filter
        (fun l => l.1.loc = Loc.zAx'x ∧ l.1.op = OpType.wt)).length = j := by
      rw [guessAX_zAx'x_write_filter_eq]
      exact guessAXBlockWord_zAx'x_write_take_count_full I v1 v2 vB0 K0 inner0Rest outerRest ks N
        hks hK0 hinner0len houterLen houter houterLast j hj
    exact ⟨hlen, G.nthEvent_eq_of_threadWord_pos hw1 hlen hval rfl rfl hcount⟩
  · obtain ⟨val, hval⟩ := guessAXBlockWord_zAxx'_read_pos_full I v1 v2 vB0 K0 inner0Rest
      outerRest ks N hks hK0 hinner0len houterLen houter houterLast (m + 1) (by omega) hm
    have hlen : nestedInnerStart ks (m + 1) + 2 < (G.threadEvents Tid.guessAX).length := by
      rw [hthreadlen]; exact (List.getElem?_eq_some_iff.mp hval).1
    have hcount : (((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks (m + 1) + 2)).filter
        (fun l => l.1.loc = Loc.zAxx' ∧ l.1.op = OpType.rd)).length = m := by
      rw [guessAX_zAxx'_read_filter_eq, guessAXBlockWord_zAxx'_read_take_count_full I v1 v2 vB0 K0
        inner0Rest outerRest ks N hks hK0 hinner0len houterLen houter houterLast (m + 1)
        (by omega) hm]
      rfl
    exact ⟨hlen, G.nthEvent_eq_of_threadWord_pos hw1 hlen hval rfl rfl hcount⟩

/-- Eq. (17), first pair (`g_α^x`, `g_α^{x'}`, `c^x`, `c^{x'}` on `x_α`, `x'_α`): the facts
`ExecutionGraph.CrossPair` asks for, from the four threads' closed forms. -/
theorem crossPair_xA (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.CrossPair Tid.guessAX Tid.primeAX Tid.checkX Tid.primeCheckX
      Loc.xA Loc.xA' Loc.zAxx' Loc.zAx'x := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessAX_run_of_reaches I G hG
  obtain ⟨v0G, K0, js, v1, v2, vB0, inner0Rest, outerRest, -, -, hinner0len, houterLen, houter,
    houterLast, -, -, -, -, -, -, -, -, -, hσ1⟩ := guessAX_shape_inv I hrun1
  have hcX := checkX_run_of_reaches I G hG
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := hcX
  obtain ⟨v0, js2, kws, -, -, -, hσ2⟩ := checkX_shape_inv I hrun2
  obtain ⟨s3, cLast3, φ3, hrun3⟩ := primeAX_run_of_reaches I G hG
  obtain ⟨M, vals, -, -, -, hσ3⟩ := primeAX_shape_inv I hrun3
  obtain ⟨s4, cLast4, φ4, hrun4⟩ := primeCheckX_run_of_reaches I G hG
  obtain ⟨N, cnts, -, -, -, hσ4⟩ := primeCheckX_shape_inv I hrun4
  have hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAX, hσ1]
  have hw2 : G.threadWord Tid.checkX =
      (checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkX, hσ2]; rfl
  have hw3 : G.threadWord Tid.primeAX = ([] ++ vals.flatMap (primeAXBlockElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeAX, hσ3]; rfl
  have hw4 : G.threadWord Tid.primeCheckX =
      ([] ++ cnts.flatMap (primeCheckXBlockElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeCheckX, hσ4]; rfl
  have hks : (K0 :: guessAXJsToKs I js).length = js.length + 1 := by simp [guessAXJsToKs]
  obtain ⟨gW, gWpos, gZ'pos, gZpos⟩ := guessAX_xA_pos I G hw1 hks rfl hinner0len houterLen houter
    houterLast
  -- `CheckX`: block 0 (`w(x_α)`, `w(x_β)`, `r(x_α)`, `r(x_β)`), then six-event blocks.
  have cW := G.nthEvent_of_uniform (x := Loc.xA) (op := OpType.wt) hw2 (n := 6) (p0 := 0)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have cR := G.nthEvent_of_uniform (x := Loc.xA) (op := OpType.rd) hw2 (n := 6) (p0 := 2)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have cR' := G.nthEvent_of_uniform (x := Loc.xA') (op := OpType.rd) hw2 (n := 6) (p0 := 4)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have cW0 := G.nthEvent_of_threadWord_pos (x := Loc.xA) (op := OpType.wt) (i := 0) (P := 0) hw2
    rfl rfl rfl rfl
  have cR0 := G.nthEvent_of_threadWord_pos (x := Loc.xA) (op := OpType.rd) (i := 0) (P := 2) hw2
    rfl rfl rfl rfl
  have hb0 : (checkXBlock0Elems I v0).length = 4 := rfl
  -- `PrimeCheckX`: six-event blocks (`w(x'_α)`, `w(x'_β)`, `r(x'_α)`, `r(x'_β)`, `r(x_α)`, `r(x_β)`).
  have qW := G.nthEvent_of_uniform (x := Loc.xA') (op := OpType.wt) hw4 (n := 6) (p0 := 0)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have qR := G.nthEvent_of_uniform (x := Loc.xA') (op := OpType.rd) hw4 (n := 6) (p0 := 2)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have qRA := G.nthEvent_of_uniform (x := Loc.xA) (op := OpType.rd) hw4 (n := 6) (p0 := 4)
    (c := 0) (by omega) (fun _ => rfl) rfl
  -- `PrimeAX`: three-event blocks (`w(x'_α)`, `w(z_α^{x,x'})`, `r(z_α^{x',x})`).
  have pW := G.nthEvent_of_uniform (x := Loc.xA') (op := OpType.wt) hw3 (n := 3) (p0 := 0)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have pZ := G.nthEvent_of_uniform (x := Loc.zAxx') (op := OpType.wt) hw3 (n := 3) (p0 := 1)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have pR := G.nthEvent_of_uniform (x := Loc.zAx'x) (op := OpType.rd) hw3 (n := 3) (p0 := 2)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have get : ∀ {β : Type} {L : List β} {j : ℕ}, j < L.length → ∃ a, L[j]? = some a :=
    fun h => ⟨_, List.getElem?_eq_getElem h⟩
  exact {
    tag_ca := fun her hrf => writer_of_read_tag G hG (checkX_run_of_reaches I G hG)
      (fun e φ h => (CheckX.hasRead_writerTid I h φ).1 rfl) her hrf
    tag_qa' := fun her hrf => writer_of_read_tag G hG (primeCheckX_run_of_reaches I G hG)
      (fun e φ h => (PrimeCheckX.hasRead_writerTid I h φ).1 rfl) her hrf
    hgc := by intro h; cases h
    hpq := by intro h; cases h
    base := fun hew her hrf => no_skipping_guessAX_checkX_xA_base I G hG _ hew her hrf
    rs_qa := G.readsFromSameIndex_of
      (writer_of_read_tag G hG (primeCheckX_run_of_reaches I G hG)
        (fun e φ h => (PrimeCheckX.hasRead_writerTid I h φ).2.2.1 rfl))
      (fun hew her hrf => no_skipping_checkX_primeCheckX_xA I G hG _ _ hew her hrf)
    rs_ca' := G.readsFromSameIndex_of
      (writer_of_read_tag G hG (checkX_run_of_reaches I G hG)
        (fun e φ h => (CheckX.hasRead_writerTid I h φ).2.2.1 rfl))
      (fun hew her hrf => no_skipping_checkX_primeCheckX_xA' I G hG _ _ hew her hrf)
    rs_gz := G.readsFromSameIndex_of (writer_of_single_writer I G hG rfl)
      (fun hew her hrf => no_skipping_guessAX_primeAX_zAxx' I G hG _ _ hew her hrf)
    rs_pz' := G.readsFromSameIndex_of (writer_of_single_writer I G hG rfl)
      (fun hew her hrf => no_skipping_guessAX_primeAX_zAx'x I G hG _ _ hew her hrf)
    c_wr := by
      intro k r hr
      rcases k with _ | j
      · obtain ⟨hP0, h0⟩ := cW0
        exact ⟨_, h0, G.po_of_pos ⟨hP0, rfl⟩ (G.eq_of_nthEvent_pos hr cR0) (by omega)⟩
      · obtain ⟨a, ha⟩ := get (cR.1 hr)
        obtain ⟨hPw, hw⟩ := cW.2 ha
        exact ⟨_, hw, G.po_of_pos ⟨hPw, rfl⟩ (G.eq_of_nthEvent_pos hr (cR.2 ha)) (by omega)⟩
    c_ex := by
      intro k w hw
      rcases k with _ | j
      · exact ⟨_, cR0.2⟩
      · obtain ⟨a, ha⟩ := get (cW.1 hw)
        exact ⟨_, (cR.2 ha).2⟩
    c_rw := by
      intro j k r w hr hw hjk
      rcases k with _ | m
      · omega
      obtain ⟨a, ha⟩ := get (cW.1 hw)
      have hwp := G.eq_of_nthEvent_pos hw (cW.2 ha)
      rcases j with _ | n
      · exact G.po_of_pos (G.eq_of_nthEvent_pos hr cR0) hwp (by omega)
      · obtain ⟨b, hb⟩ := get (cR.1 hr)
        exact G.po_of_pos (G.eq_of_nthEvent_pos hr (cR.2 hb)) hwp (by omega)
    c_rr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (cR.1 hr)
      obtain ⟨hP, h⟩ := cR'.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hr (cR.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    q_wr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (qR.1 hr)
      obtain ⟨hP, h⟩ := qW.2 ha
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hr (qR.2 ha)) (by omega)⟩
    q_ex := by
      intro k w hw
      obtain ⟨a, ha⟩ := get (qW.1 hw)
      exact ⟨_, (qR.2 ha).2⟩
    q_rw := by
      intro j k r w hr hw hjk
      obtain ⟨a, ha⟩ := get (qW.1 hw)
      obtain ⟨b, hb⟩ := get (qR.1 hr)
      exact G.po_of_pos (G.eq_of_nthEvent_pos hr (qR.2 hb)) (G.eq_of_nthEvent_pos hw (qW.2 ha))
        (by omega)
    q_rr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (qR.1 hr)
      obtain ⟨hP, h⟩ := qRA.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hr (qR.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    g_za := by
      intro m j w hw hmj
      have hj := gW hw
      obtain ⟨hP, h⟩ := gZpos (m := m) (by omega)
      refine ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hw (gWpos hj)) ?_⟩
      have h1 := nestedInnerStart_succ (K0 :: guessAXJsToKs I js) (m + 1)
      have hcl : nestedCallLen (m + 1) = 3 := by simp [nestedCallLen]
      have hmono := (nestedInnerStart_strictMono (K0 :: guessAXJsToKs I js)).monotone
        (show m + 1 + 1 ≤ j by omega)
      omega
    g_az' := by
      intro k w hw
      obtain ⟨hP, h⟩ := gZ'pos (gW hw)
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw (gWpos (gW hw))) ⟨hP, rfl⟩ (by omega)⟩
    p_a'z := by
      intro k w hw
      obtain ⟨a, ha⟩ := get (pW.1 hw)
      obtain ⟨hP, h⟩ := pZ.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw (pW.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    p_z'a' := by
      intro m j w hw hmj
      have hj := pW.1 hw
      obtain ⟨a, ha⟩ := get (pW.1 hw)
      obtain ⟨b, hb⟩ := get (show m < vals.length by omega)
      obtain ⟨hP, h⟩ := pR.2 hb
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hw (pW.2 ha)) (by omega)⟩ }

/-! ### `g_β^x`, `g_β^{x'}`, `c^x`, `c^{x'}` on `x_β`, `x'_β` -/

/-- `GuessBX`'s writes on `x_β` and `z_β^{x',x}` and reads on `z_β^{x,x'}`, at
their positions `nestedInnerStart ks P (+1, +2)`. -/
theorem guessBX_xB_pos (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ} {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hw1 : G.threadWord Tid.guessBX = (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (hinner0len : inner0Rest.length = K0) (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    (∀ {j : ℕ} {e : Event (domainOf I)}, G.nthWrite Tid.guessBX Loc.xB j = some e →
      j ≤ ksPrefix ks (N + 1)) ∧
    (∀ {j : ℕ}, j ≤ ksPrefix ks (N + 1) →
      ∃ hP : nestedInnerStart ks j < (G.threadEvents Tid.guessBX).length,
        G.nthWrite Tid.guessBX Loc.xB j =
          some ((G.threadEvents Tid.guessBX)[nestedInnerStart ks j]'hP).1) ∧
    (∀ {j : ℕ}, j ≤ ksPrefix ks (N + 1) →
      ∃ hP : nestedInnerStart ks j + 1 < (G.threadEvents Tid.guessBX).length,
        G.nthWrite Tid.guessBX Loc.zBx'x j =
          some ((G.threadEvents Tid.guessBX)[nestedInnerStart ks j + 1]'hP).1) ∧
    (∀ {m : ℕ}, m + 1 ≤ ksPrefix ks (N + 1) →
      ∃ hP : nestedInnerStart ks (m + 1) + 2 < (G.threadEvents Tid.guessBX).length,
        G.nthRead Tid.guessBX Loc.zBxx' m =
          some ((G.threadEvents Tid.guessBX)[nestedInnerStart ks (m + 1) + 2]'hP).1) := by
  have hthreadlen : (G.threadEvents Tid.guessBX).length =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).length := by
    have hlc := congrArg List.length hw1
    unfold ExecutionGraph.threadWord at hlc
    rwa [List.length_map, List.length_map] at hlc
  refine ⟨fun {j e} he => ?_, fun {j} hj => ?_, fun {j} hj => ?_, fun {m} hm => ?_⟩
  · have htotcount : (G.opEvents Tid.guessBX Loc.xB OpType.wt).length =
        ksPrefix ks (N + 1) + 1 := by
      have hL := G.opEvents_map_lab_eq_filter_threadLabels Tid.guessBX Loc.xB OpType.wt
      have hLlen := congrArg List.length hL
      rw [List.length_map, List.length_map, G.threadLabels_eq_of_threadWord hw1] at hLlen
      have hbridge := guessBX_xB_write_filter_eq'
        (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
      have hLlen2 := hbridge ▸ hLlen
      rw [hLlen2]
      exact guessBXBlockWord_xB_write_total_count I v1 v2 vB0 K0 inner0Rest outerRest ks N hks
        hK0 hinner0len houterLen houter houterLast
    have := (List.getElem?_eq_some_iff.mp he).1
    omega
  · obtain ⟨val, hval⟩ := guessBXBlockWord_xB_write_pos_full I v1 v2 vB0 K0 inner0Rest outerRest
      ks N hks hK0 hinner0len houterLen houter houterLast j hj
    have hlen : nestedInnerStart ks j < (G.threadEvents Tid.guessBX).length := by
      rw [hthreadlen]; exact (List.getElem?_eq_some_iff.mp hval).1
    have hcount : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks j)).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.wt)).length
        = j := by
      rw [guessBX_xB_write_filter_eq']
      exact guessBXBlockWord_xB_write_take_count_full I v1 v2 vB0 K0 inner0Rest outerRest ks N
        hks hK0 hinner0len houterLen houter houterLast j hj
    exact ⟨hlen, G.nthEvent_eq_of_threadWord_pos hw1 hlen hval rfl rfl hcount⟩
  · obtain ⟨val, hval⟩ := guessBXBlockWord_zBx'x_write_pos_full I v1 v2 vB0 K0 inner0Rest
      outerRest ks N hks hK0 hinner0len houterLen houter houterLast j hj
    have hlen : nestedInnerStart ks j + 1 < (G.threadEvents Tid.guessBX).length := by
      rw [hthreadlen]; exact (List.getElem?_eq_some_iff.mp hval).1
    have hcount : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks j + 1)).filter
        (fun l => l.1.loc = Loc.zBx'x ∧ l.1.op = OpType.wt)).length = j := by
      rw [guessBX_zBx'x_write_filter_eq]
      exact guessBXBlockWord_zBx'x_write_take_count_full I v1 v2 vB0 K0 inner0Rest outerRest ks N
        hks hK0 hinner0len houterLen houter houterLast j hj
    exact ⟨hlen, G.nthEvent_eq_of_threadWord_pos hw1 hlen hval rfl rfl hcount⟩
  · obtain ⟨val, hval⟩ := guessBXBlockWord_zBxx'_read_pos_full I v1 v2 vB0 K0 inner0Rest
      outerRest ks N hks hK0 hinner0len houterLen houter houterLast (m + 1) (by omega) hm
    have hlen : nestedInnerStart ks (m + 1) + 2 < (G.threadEvents Tid.guessBX).length := by
      rw [hthreadlen]; exact (List.getElem?_eq_some_iff.mp hval).1
    have hcount : (((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).take
        (nestedInnerStart ks (m + 1) + 2)).filter
        (fun l => l.1.loc = Loc.zBxx' ∧ l.1.op = OpType.rd)).length = m := by
      rw [guessBX_zBxx'_read_filter_eq, guessBXBlockWord_zBxx'_read_take_count_full I v1 v2 vB0 K0
        inner0Rest outerRest ks N hks hK0 hinner0len houterLen houter houterLast (m + 1)
        (by omega) hm]
      rfl
    exact ⟨hlen, G.nthEvent_eq_of_threadWord_pos hw1 hlen hval rfl rfl hcount⟩

/-- Eq. (17), second pair (`g_β^x`, `g_β^{x'}`, `c^x`, `c^{x'}` on `x_β`, `x'_β`): the facts
`ExecutionGraph.CrossPair` asks for, from the four threads' closed forms. -/
theorem crossPair_xB (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.CrossPair Tid.guessBX Tid.primeBX Tid.checkX Tid.primeCheckX
      Loc.xB Loc.xB' Loc.zBxx' Loc.zBx'x := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessBX_run_of_reaches I G hG
  obtain ⟨v0G, K0, js, v1, v2, vB0, inner0Rest, outerRest, -, -, hinner0len, houterLen, houter,
    houterLast, -, -, -, -, -, -, -, -, -, hσ1⟩ := guessBX_shape_inv I hrun1
  have hcX := checkX_run_of_reaches I G hG
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := hcX
  obtain ⟨v0, js2, kws, -, -, -, hσ2⟩ := checkX_shape_inv I hrun2
  obtain ⟨s3, cLast3, φ3, hrun3⟩ := primeBX_run_of_reaches I G hG
  obtain ⟨M, vals, -, -, -, hσ3⟩ := primeBX_shape_inv I hrun3
  obtain ⟨s4, cLast4, φ4, hrun4⟩ := primeCheckX_run_of_reaches I G hG
  obtain ⟨N, cnts, -, -, -, hσ4⟩ := primeCheckX_shape_inv I hrun4
  have hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBX, hσ1]
  have hw2 : G.threadWord Tid.checkX =
      (checkXBlock0Elems I v0 ++ kws.flatMap (checkXBlockRestElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkX, hσ2]; rfl
  have hw3 : G.threadWord Tid.primeBX = ([] ++ vals.flatMap (primeBXBlockElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeBX, hσ3]; rfl
  have hw4 : G.threadWord Tid.primeCheckX =
      ([] ++ cnts.flatMap (primeCheckXBlockElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeCheckX, hσ4]; rfl
  have hks : (K0 :: guessBXJsToKs I js).length = js.length + 1 := by simp [guessBXJsToKs]
  obtain ⟨gW, gWpos, gZ'pos, gZpos⟩ := guessBX_xB_pos I G hw1 hks rfl hinner0len houterLen houter
    houterLast
  -- `CheckX`: block 0 (`w(x_α)`, `w(x_β)`, `r(x_α)`, `r(x_β)`), then six-event blocks.
  have cW := G.nthEvent_of_uniform (x := Loc.xB) (op := OpType.wt) hw2 (n := 6) (p0 := 1)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have cR := G.nthEvent_of_uniform (x := Loc.xB) (op := OpType.rd) hw2 (n := 6) (p0 := 3)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have cR' := G.nthEvent_of_uniform (x := Loc.xB') (op := OpType.rd) hw2 (n := 6) (p0 := 5)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have cW0 := G.nthEvent_of_threadWord_pos (x := Loc.xB) (op := OpType.wt) (i := 0) (P := 1) hw2
    rfl rfl rfl rfl
  have cR0 := G.nthEvent_of_threadWord_pos (x := Loc.xB) (op := OpType.rd) (i := 0) (P := 3) hw2
    rfl rfl rfl rfl
  have hb0 : (checkXBlock0Elems I v0).length = 4 := rfl
  -- `PrimeCheckX`: six-event blocks (`w(x'_α)`, `w(x'_β)`, `r(x'_α)`, `r(x'_β)`, `r(x_α)`, `r(x_β)`).
  have qW := G.nthEvent_of_uniform (x := Loc.xB') (op := OpType.wt) hw4 (n := 6) (p0 := 1)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have qR := G.nthEvent_of_uniform (x := Loc.xB') (op := OpType.rd) hw4 (n := 6) (p0 := 3)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have qRA := G.nthEvent_of_uniform (x := Loc.xB) (op := OpType.rd) hw4 (n := 6) (p0 := 5)
    (c := 0) (by omega) (fun _ => rfl) rfl
  -- `PrimeBX`: three-event blocks (`w(x'_β)`, `w(z_β^{x,x'})`, `r(z_β^{x',x})`).
  have pW := G.nthEvent_of_uniform (x := Loc.xB') (op := OpType.wt) hw3 (n := 3) (p0 := 0)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have pZ := G.nthEvent_of_uniform (x := Loc.zBxx') (op := OpType.wt) hw3 (n := 3) (p0 := 1)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have pR := G.nthEvent_of_uniform (x := Loc.zBx'x) (op := OpType.rd) hw3 (n := 3) (p0 := 2)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have get : ∀ {β : Type} {L : List β} {j : ℕ}, j < L.length → ∃ a, L[j]? = some a :=
    fun h => ⟨_, List.getElem?_eq_getElem h⟩
  exact {
    tag_ca := fun her hrf => writer_of_read_tag G hG (checkX_run_of_reaches I G hG)
      (fun e φ h => (CheckX.hasRead_writerTid I h φ).2.1 rfl) her hrf
    tag_qa' := fun her hrf => writer_of_read_tag G hG (primeCheckX_run_of_reaches I G hG)
      (fun e φ h => (PrimeCheckX.hasRead_writerTid I h φ).2.1 rfl) her hrf
    hgc := by intro h; cases h
    hpq := by intro h; cases h
    base := fun hew her hrf => no_skipping_guessBX_checkX_xB_base I G hG _ hew her hrf
    rs_qa := G.readsFromSameIndex_of
      (writer_of_read_tag G hG (primeCheckX_run_of_reaches I G hG)
        (fun e φ h => (PrimeCheckX.hasRead_writerTid I h φ).2.2.2 rfl))
      (fun hew her hrf => no_skipping_checkX_primeCheckX_xB I G hG _ _ hew her hrf)
    rs_ca' := G.readsFromSameIndex_of
      (writer_of_read_tag G hG (checkX_run_of_reaches I G hG)
        (fun e φ h => (CheckX.hasRead_writerTid I h φ).2.2.2 rfl))
      (fun hew her hrf => no_skipping_checkX_primeCheckX_xB' I G hG _ _ hew her hrf)
    rs_gz := G.readsFromSameIndex_of (writer_of_single_writer I G hG rfl)
      (fun hew her hrf => no_skipping_guessBX_primeBX_zBxx' I G hG _ _ hew her hrf)
    rs_pz' := G.readsFromSameIndex_of (writer_of_single_writer I G hG rfl)
      (fun hew her hrf => no_skipping_guessBX_primeBX_zBx'x I G hG _ _ hew her hrf)
    c_wr := by
      intro k r hr
      rcases k with _ | j
      · obtain ⟨hP0, h0⟩ := cW0
        exact ⟨_, h0, G.po_of_pos ⟨hP0, rfl⟩ (G.eq_of_nthEvent_pos hr cR0) (by omega)⟩
      · obtain ⟨a, ha⟩ := get (cR.1 hr)
        obtain ⟨hPw, hw⟩ := cW.2 ha
        exact ⟨_, hw, G.po_of_pos ⟨hPw, rfl⟩ (G.eq_of_nthEvent_pos hr (cR.2 ha)) (by omega)⟩
    c_ex := by
      intro k w hw
      rcases k with _ | j
      · exact ⟨_, cR0.2⟩
      · obtain ⟨a, ha⟩ := get (cW.1 hw)
        exact ⟨_, (cR.2 ha).2⟩
    c_rw := by
      intro j k r w hr hw hjk
      rcases k with _ | m
      · omega
      obtain ⟨a, ha⟩ := get (cW.1 hw)
      have hwp := G.eq_of_nthEvent_pos hw (cW.2 ha)
      rcases j with _ | n
      · exact G.po_of_pos (G.eq_of_nthEvent_pos hr cR0) hwp (by omega)
      · obtain ⟨b, hb⟩ := get (cR.1 hr)
        exact G.po_of_pos (G.eq_of_nthEvent_pos hr (cR.2 hb)) hwp (by omega)
    c_rr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (cR.1 hr)
      obtain ⟨hP, h⟩ := cR'.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hr (cR.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    q_wr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (qR.1 hr)
      obtain ⟨hP, h⟩ := qW.2 ha
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hr (qR.2 ha)) (by omega)⟩
    q_ex := by
      intro k w hw
      obtain ⟨a, ha⟩ := get (qW.1 hw)
      exact ⟨_, (qR.2 ha).2⟩
    q_rw := by
      intro j k r w hr hw hjk
      obtain ⟨a, ha⟩ := get (qW.1 hw)
      obtain ⟨b, hb⟩ := get (qR.1 hr)
      exact G.po_of_pos (G.eq_of_nthEvent_pos hr (qR.2 hb)) (G.eq_of_nthEvent_pos hw (qW.2 ha))
        (by omega)
    q_rr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (qR.1 hr)
      obtain ⟨hP, h⟩ := qRA.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hr (qR.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    g_za := by
      intro m j w hw hmj
      have hj := gW hw
      obtain ⟨hP, h⟩ := gZpos (m := m) (by omega)
      refine ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hw (gWpos hj)) ?_⟩
      have h1 := nestedInnerStart_succ (K0 :: guessBXJsToKs I js) (m + 1)
      have hcl : nestedCallLen (m + 1) = 3 := by simp [nestedCallLen]
      have hmono := (nestedInnerStart_strictMono (K0 :: guessBXJsToKs I js)).monotone
        (show m + 1 + 1 ≤ j by omega)
      omega
    g_az' := by
      intro k w hw
      obtain ⟨hP, h⟩ := gZ'pos (gW hw)
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw (gWpos (gW hw))) ⟨hP, rfl⟩ (by omega)⟩
    p_a'z := by
      intro k w hw
      obtain ⟨a, ha⟩ := get (pW.1 hw)
      obtain ⟨hP, h⟩ := pZ.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw (pW.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    p_z'a' := by
      intro m j w hw hmj
      have hj := pW.1 hw
      obtain ⟨a, ha⟩ := get (pW.1 hw)
      obtain ⟨b, hb⟩ := get (show m < vals.length by omega)
      obtain ⟨hP, h⟩ := pR.2 hb
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hw (pW.2 ha)) (by omega)⟩ }

/-! ### `g_α^y`, `g_α^{y'}`, `c^y`, `c^{y'}` on `y_α`, `y'_α` -/

/-- Eq. (17), third pair (`g_α^y`, `g_α^{y'}`, `c^y`, `c^{y'}` on `y_α`, `y'_α`): the facts
`ExecutionGraph.CrossPair` asks for, from the four threads' closed forms. -/
theorem crossPair_yA (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.CrossPair Tid.guessAY Tid.primeAY Tid.checkY Tid.primeCheckY
      Loc.yA Loc.yA' Loc.zAyy' Loc.zAy'y := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessAY_run_of_reaches I G hG
  obtain ⟨v1, js1, kws1, -, -, -, hσ1⟩ := guessAY_shape_inv I hrun1
  have hcX := checkY_run_of_reaches I G hG
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := hcX
  obtain ⟨v0, js2, kws, -, -, -, hσ2⟩ := checkY_shape_inv I hrun2
  obtain ⟨s3, cLast3, φ3, hrun3⟩ := primeAY_run_of_reaches I G hG
  obtain ⟨M, vals, -, -, -, hσ3⟩ := primeAY_shape_inv I hrun3
  obtain ⟨s4, cLast4, φ4, hrun4⟩ := primeCheckY_run_of_reaches I G hG
  obtain ⟨N, cnts, -, -, -, hσ4⟩ := primeCheckY_shape_inv I hrun4
  have hw1 : G.threadWord Tid.guessAY =
      (guessAYBlock0Elems I v1 ++ kws1.flatMap (guessAYBlockRestElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAY, hσ1]; rfl
  have hw2 : G.threadWord Tid.checkY =
      (checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkY, hσ2]; rfl
  have hw3 : G.threadWord Tid.primeAY = ([] ++ vals.flatMap (primeAYBlockElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeAY, hσ3]; rfl
  have hw4 : G.threadWord Tid.primeCheckY =
      ([] ++ cnts.flatMap (primeCheckYBlockElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeCheckY, hσ4]; rfl
  -- `GuessAY`: block 0 (`w(y_α)`, `w(ℓ_α^{y,x})`, `w(z_α^{y',y})`), then five-event blocks
  -- (the same three writes, then `r(z_α^{x,y})`, `r(z_α^{y,y'})`).
  have gW := G.nthEvent_of_uniform (x := Loc.yA) (op := OpType.wt) hw1 (n := 5) (p0 := 0)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have gZ' := G.nthEvent_of_uniform (x := Loc.zAy'y) (op := OpType.wt) hw1 (n := 5) (p0 := 2)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have gZ := G.nthEvent_of_uniform (x := Loc.zAyy') (op := OpType.rd) hw1 (n := 5) (p0 := 4)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have gW0 := G.nthEvent_of_threadWord_pos (x := Loc.yA) (op := OpType.wt) (i := 0) (P := 0) hw1
    rfl rfl rfl rfl
  have gZ'0 := G.nthEvent_of_threadWord_pos (x := Loc.zAy'y) (op := OpType.wt) (i := 0) (P := 2)
    hw1 rfl rfl rfl rfl
  have hg0 : (guessAYBlock0Elems I v1).length = 3 := rfl
  -- `CheckY`: block 0 (`w(y_α)`, `w(y_β)`, `r(y_α)`, `r(y_β)`), then six-event blocks.
  have cW := G.nthEvent_of_uniform (x := Loc.yA) (op := OpType.wt) hw2 (n := 6) (p0 := 0)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have cR := G.nthEvent_of_uniform (x := Loc.yA) (op := OpType.rd) hw2 (n := 6) (p0 := 2)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have cR' := G.nthEvent_of_uniform (x := Loc.yA') (op := OpType.rd) hw2 (n := 6) (p0 := 4)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have cW0 := G.nthEvent_of_threadWord_pos (x := Loc.yA) (op := OpType.wt) (i := 0) (P := 0) hw2
    rfl rfl rfl rfl
  have cR0 := G.nthEvent_of_threadWord_pos (x := Loc.yA) (op := OpType.rd) (i := 0) (P := 2) hw2
    rfl rfl rfl rfl
  have hb0 : (checkYBlock0Elems I v0).length = 4 := rfl
  -- `PrimeCheckY`: six-event blocks (`w(y'_α)`, `w(y'_β)`, `r(y'_α)`, `r(y'_β)`, `r(y_α)`, `r(y_β)`).
  have qW := G.nthEvent_of_uniform (x := Loc.yA') (op := OpType.wt) hw4 (n := 6) (p0 := 0)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have qR := G.nthEvent_of_uniform (x := Loc.yA') (op := OpType.rd) hw4 (n := 6) (p0 := 2)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have qRA := G.nthEvent_of_uniform (x := Loc.yA) (op := OpType.rd) hw4 (n := 6) (p0 := 4)
    (c := 0) (by omega) (fun _ => rfl) rfl
  -- `PrimeAY`: three-event blocks (`w(y'_α)`, `w(z_α^{y,y'})`, `r(z_α^{y',y})`).
  have pW := G.nthEvent_of_uniform (x := Loc.yA') (op := OpType.wt) hw3 (n := 3) (p0 := 0)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have pZ := G.nthEvent_of_uniform (x := Loc.zAyy') (op := OpType.wt) hw3 (n := 3) (p0 := 1)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have pR := G.nthEvent_of_uniform (x := Loc.zAy'y) (op := OpType.rd) hw3 (n := 3) (p0 := 2)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have get : ∀ {β : Type} {L : List β} {j : ℕ}, j < L.length → ∃ a, L[j]? = some a :=
    fun h => ⟨_, List.getElem?_eq_getElem h⟩
  exact {
    tag_ca := fun her hrf => writer_of_read_tag G hG (checkY_run_of_reaches I G hG)
      (fun e φ h => (CheckY.hasRead_writerTid I h φ).1 rfl) her hrf
    tag_qa' := fun her hrf => writer_of_read_tag G hG (primeCheckY_run_of_reaches I G hG)
      (fun e φ h => (PrimeCheckY.hasRead_writerTid I h φ).1 rfl) her hrf
    hgc := by intro h; cases h
    hpq := by intro h; cases h
    base := fun hew her hrf => no_skipping_guessAY_checkY_yA_base I G hG _ hew her hrf
    rs_qa := G.readsFromSameIndex_of
      (writer_of_read_tag G hG (primeCheckY_run_of_reaches I G hG)
        (fun e φ h => (PrimeCheckY.hasRead_writerTid I h φ).2.2.1 rfl))
      (fun hew her hrf => no_skipping_checkY_primeCheckY_yA I G hG _ _ hew her hrf)
    rs_ca' := G.readsFromSameIndex_of
      (writer_of_read_tag G hG (checkY_run_of_reaches I G hG)
        (fun e φ h => (CheckY.hasRead_writerTid I h φ).2.2.1 rfl))
      (fun hew her hrf => no_skipping_checkY_primeCheckY_yA' I G hG _ _ hew her hrf)
    rs_gz := G.readsFromSameIndex_of (writer_of_single_writer I G hG rfl)
      (fun hew her hrf => no_skipping_guessAY_primeAY_zAyy' I G hG _ _ hew her hrf)
    rs_pz' := G.readsFromSameIndex_of (writer_of_single_writer I G hG rfl)
      (fun hew her hrf => no_skipping_guessAY_primeAY_zAy'y I G hG _ _ hew her hrf)
    c_wr := by
      intro k r hr
      rcases k with _ | j
      · obtain ⟨hP0, h0⟩ := cW0
        exact ⟨_, h0, G.po_of_pos ⟨hP0, rfl⟩ (G.eq_of_nthEvent_pos hr cR0) (by omega)⟩
      · obtain ⟨a, ha⟩ := get (cR.1 hr)
        obtain ⟨hPw, hw⟩ := cW.2 ha
        exact ⟨_, hw, G.po_of_pos ⟨hPw, rfl⟩ (G.eq_of_nthEvent_pos hr (cR.2 ha)) (by omega)⟩
    c_ex := by
      intro k w hw
      rcases k with _ | j
      · exact ⟨_, cR0.2⟩
      · obtain ⟨a, ha⟩ := get (cW.1 hw)
        exact ⟨_, (cR.2 ha).2⟩
    c_rw := by
      intro j k r w hr hw hjk
      rcases k with _ | m
      · omega
      obtain ⟨a, ha⟩ := get (cW.1 hw)
      have hwp := G.eq_of_nthEvent_pos hw (cW.2 ha)
      rcases j with _ | n
      · exact G.po_of_pos (G.eq_of_nthEvent_pos hr cR0) hwp (by omega)
      · obtain ⟨b, hb⟩ := get (cR.1 hr)
        exact G.po_of_pos (G.eq_of_nthEvent_pos hr (cR.2 hb)) hwp (by omega)
    c_rr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (cR.1 hr)
      obtain ⟨hP, h⟩ := cR'.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hr (cR.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    q_wr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (qR.1 hr)
      obtain ⟨hP, h⟩ := qW.2 ha
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hr (qR.2 ha)) (by omega)⟩
    q_ex := by
      intro k w hw
      obtain ⟨a, ha⟩ := get (qW.1 hw)
      exact ⟨_, (qR.2 ha).2⟩
    q_rw := by
      intro j k r w hr hw hjk
      obtain ⟨a, ha⟩ := get (qW.1 hw)
      obtain ⟨b, hb⟩ := get (qR.1 hr)
      exact G.po_of_pos (G.eq_of_nthEvent_pos hr (qR.2 hb)) (G.eq_of_nthEvent_pos hw (qW.2 ha))
        (by omega)
    q_rr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (qR.1 hr)
      obtain ⟨hP, h⟩ := qRA.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hr (qR.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    g_za := by
      intro m j w hw hmj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi := gW.1 hw
      obtain ⟨a, ha⟩ := get hi
      obtain ⟨b, hb⟩ := get (show m < kws1.length by omega)
      obtain ⟨hP, h⟩ := gZ.2 hb
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hw (gW.2 ha)) (by omega)⟩
    g_az' := by
      intro k w hw
      rcases k with _ | i
      · obtain ⟨hP, h⟩ := gZ'0
        exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw gW0) ⟨hP, rfl⟩ (by omega)⟩
      · obtain ⟨a, ha⟩ := get (gW.1 hw)
        obtain ⟨hP, h⟩ := gZ'.2 ha
        exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw (gW.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    p_a'z := by
      intro k w hw
      obtain ⟨a, ha⟩ := get (pW.1 hw)
      obtain ⟨hP, h⟩ := pZ.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw (pW.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    p_z'a' := by
      intro m j w hw hmj
      have hj := pW.1 hw
      obtain ⟨a, ha⟩ := get (pW.1 hw)
      obtain ⟨b, hb⟩ := get (show m < vals.length by omega)
      obtain ⟨hP, h⟩ := pR.2 hb
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hw (pW.2 ha)) (by omega)⟩ }

/-! ### `g_β^y`, `g_β^{y'}`, `c^y`, `c^{y'}` on `y_β`, `y'_β` -/

/-- Eq. (17), fourth pair (`g_β^y`, `g_β^{y'}`, `c^y`, `c^{y'}` on `y_β`, `y'_β`): the facts
`ExecutionGraph.CrossPair` asks for, from the four threads' closed forms. -/
theorem crossPair_yB (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    G.CrossPair Tid.guessBY Tid.primeBY Tid.checkY Tid.primeCheckY
      Loc.yB Loc.yB' Loc.zByy' Loc.zBy'y := by
  obtain ⟨s1, cLast1, φ1, hrun1⟩ := guessBY_run_of_reaches I G hG
  obtain ⟨v1, js1, kws1, -, -, -, hσ1⟩ := guessBY_shape_inv I hrun1
  have hcX := checkY_run_of_reaches I G hG
  obtain ⟨s2, cLast2, φ2, hrun2⟩ := hcX
  obtain ⟨v0, js2, kws, -, -, -, hσ2⟩ := checkY_shape_inv I hrun2
  obtain ⟨s3, cLast3, φ3, hrun3⟩ := primeBY_run_of_reaches I G hG
  obtain ⟨M, vals, -, -, -, hσ3⟩ := primeBY_shape_inv I hrun3
  obtain ⟨s4, cLast4, φ4, hrun4⟩ := primeCheckY_run_of_reaches I G hG
  obtain ⟨N, cnts, -, -, -, hσ4⟩ := primeCheckY_shape_inv I hrun4
  have hw1 : G.threadWord Tid.guessBY =
      (guessBYBlock0Elems I v1 ++ kws1.flatMap (guessBYBlockRestElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBY, hσ1]; rfl
  have hw2 : G.threadWord Tid.checkY =
      (checkYBlock0Elems I v0 ++ kws.flatMap (checkYBlockRestElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkY, hσ2]; rfl
  have hw3 : G.threadWord Tid.primeBY = ([] ++ vals.flatMap (primeBYBlockElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeBY, hσ3]; rfl
  have hw4 : G.threadWord Tid.primeCheckY =
      ([] ++ cnts.flatMap (primeCheckYBlockElems I)).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.primeCheckY, hσ4]; rfl
  -- `GuessBY`: block 0 (`w(y_β)`, `w(ℓ_β^{y,x})`, `w(z_β^{y',y})`), then five-event blocks
  -- (the same three writes, then `r(z_β^{x,y})`, `r(z_β^{y,y'})`).
  have gW := G.nthEvent_of_uniform (x := Loc.yB) (op := OpType.wt) hw1 (n := 5) (p0 := 0)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have gZ' := G.nthEvent_of_uniform (x := Loc.zBy'y) (op := OpType.wt) hw1 (n := 5) (p0 := 2)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have gZ := G.nthEvent_of_uniform (x := Loc.zByy') (op := OpType.rd) hw1 (n := 5) (p0 := 4)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have gW0 := G.nthEvent_of_threadWord_pos (x := Loc.yB) (op := OpType.wt) (i := 0) (P := 0) hw1
    rfl rfl rfl rfl
  have gZ'0 := G.nthEvent_of_threadWord_pos (x := Loc.zBy'y) (op := OpType.wt) (i := 0) (P := 2)
    hw1 rfl rfl rfl rfl
  have hg0 : (guessBYBlock0Elems I v1).length = 3 := rfl
  -- `CheckY`: block 0 (`w(y_α)`, `w(y_β)`, `r(y_α)`, `r(y_β)`), then six-event blocks.
  have cW := G.nthEvent_of_uniform (x := Loc.yB) (op := OpType.wt) hw2 (n := 6) (p0 := 1)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have cR := G.nthEvent_of_uniform (x := Loc.yB) (op := OpType.rd) hw2 (n := 6) (p0 := 3)
    (c := 1) (by omega) (fun _ => rfl) rfl
  have cR' := G.nthEvent_of_uniform (x := Loc.yB') (op := OpType.rd) hw2 (n := 6) (p0 := 5)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have cW0 := G.nthEvent_of_threadWord_pos (x := Loc.yB) (op := OpType.wt) (i := 0) (P := 1) hw2
    rfl rfl rfl rfl
  have cR0 := G.nthEvent_of_threadWord_pos (x := Loc.yB) (op := OpType.rd) (i := 0) (P := 3) hw2
    rfl rfl rfl rfl
  have hb0 : (checkYBlock0Elems I v0).length = 4 := rfl
  -- `PrimeCheckY`: six-event blocks (`w(y'_α)`, `w(y'_β)`, `r(y'_α)`, `r(y'_β)`, `r(y_α)`, `r(y_β)`).
  have qW := G.nthEvent_of_uniform (x := Loc.yB') (op := OpType.wt) hw4 (n := 6) (p0 := 1)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have qR := G.nthEvent_of_uniform (x := Loc.yB') (op := OpType.rd) hw4 (n := 6) (p0 := 3)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have qRA := G.nthEvent_of_uniform (x := Loc.yB) (op := OpType.rd) hw4 (n := 6) (p0 := 5)
    (c := 0) (by omega) (fun _ => rfl) rfl
  -- `PrimeBY`: three-event blocks (`w(y'_β)`, `w(z_β^{y,y'})`, `r(z_β^{y',y})`).
  have pW := G.nthEvent_of_uniform (x := Loc.yB') (op := OpType.wt) hw3 (n := 3) (p0 := 0)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have pZ := G.nthEvent_of_uniform (x := Loc.zByy') (op := OpType.wt) hw3 (n := 3) (p0 := 1)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have pR := G.nthEvent_of_uniform (x := Loc.zBy'y) (op := OpType.rd) hw3 (n := 3) (p0 := 2)
    (c := 0) (by omega) (fun _ => rfl) rfl
  have get : ∀ {β : Type} {L : List β} {j : ℕ}, j < L.length → ∃ a, L[j]? = some a :=
    fun h => ⟨_, List.getElem?_eq_getElem h⟩
  exact {
    tag_ca := fun her hrf => writer_of_read_tag G hG (checkY_run_of_reaches I G hG)
      (fun e φ h => (CheckY.hasRead_writerTid I h φ).2.1 rfl) her hrf
    tag_qa' := fun her hrf => writer_of_read_tag G hG (primeCheckY_run_of_reaches I G hG)
      (fun e φ h => (PrimeCheckY.hasRead_writerTid I h φ).2.1 rfl) her hrf
    hgc := by intro h; cases h
    hpq := by intro h; cases h
    base := fun hew her hrf => no_skipping_guessBY_checkY_yB_base I G hG _ hew her hrf
    rs_qa := G.readsFromSameIndex_of
      (writer_of_read_tag G hG (primeCheckY_run_of_reaches I G hG)
        (fun e φ h => (PrimeCheckY.hasRead_writerTid I h φ).2.2.2 rfl))
      (fun hew her hrf => no_skipping_checkY_primeCheckY_yB I G hG _ _ hew her hrf)
    rs_ca' := G.readsFromSameIndex_of
      (writer_of_read_tag G hG (checkY_run_of_reaches I G hG)
        (fun e φ h => (CheckY.hasRead_writerTid I h φ).2.2.2 rfl))
      (fun hew her hrf => no_skipping_checkY_primeCheckY_yB' I G hG _ _ hew her hrf)
    rs_gz := G.readsFromSameIndex_of (writer_of_single_writer I G hG rfl)
      (fun hew her hrf => no_skipping_guessBY_primeBY_zByy' I G hG _ _ hew her hrf)
    rs_pz' := G.readsFromSameIndex_of (writer_of_single_writer I G hG rfl)
      (fun hew her hrf => no_skipping_guessBY_primeBY_zBy'y I G hG _ _ hew her hrf)
    c_wr := by
      intro k r hr
      rcases k with _ | j
      · obtain ⟨hP0, h0⟩ := cW0
        exact ⟨_, h0, G.po_of_pos ⟨hP0, rfl⟩ (G.eq_of_nthEvent_pos hr cR0) (by omega)⟩
      · obtain ⟨a, ha⟩ := get (cR.1 hr)
        obtain ⟨hPw, hw⟩ := cW.2 ha
        exact ⟨_, hw, G.po_of_pos ⟨hPw, rfl⟩ (G.eq_of_nthEvent_pos hr (cR.2 ha)) (by omega)⟩
    c_ex := by
      intro k w hw
      rcases k with _ | j
      · exact ⟨_, cR0.2⟩
      · obtain ⟨a, ha⟩ := get (cW.1 hw)
        exact ⟨_, (cR.2 ha).2⟩
    c_rw := by
      intro j k r w hr hw hjk
      rcases k with _ | m
      · omega
      obtain ⟨a, ha⟩ := get (cW.1 hw)
      have hwp := G.eq_of_nthEvent_pos hw (cW.2 ha)
      rcases j with _ | n
      · exact G.po_of_pos (G.eq_of_nthEvent_pos hr cR0) hwp (by omega)
      · obtain ⟨b, hb⟩ := get (cR.1 hr)
        exact G.po_of_pos (G.eq_of_nthEvent_pos hr (cR.2 hb)) hwp (by omega)
    c_rr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (cR.1 hr)
      obtain ⟨hP, h⟩ := cR'.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hr (cR.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    q_wr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (qR.1 hr)
      obtain ⟨hP, h⟩ := qW.2 ha
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hr (qR.2 ha)) (by omega)⟩
    q_ex := by
      intro k w hw
      obtain ⟨a, ha⟩ := get (qW.1 hw)
      exact ⟨_, (qR.2 ha).2⟩
    q_rw := by
      intro j k r w hr hw hjk
      obtain ⟨a, ha⟩ := get (qW.1 hw)
      obtain ⟨b, hb⟩ := get (qR.1 hr)
      exact G.po_of_pos (G.eq_of_nthEvent_pos hr (qR.2 hb)) (G.eq_of_nthEvent_pos hw (qW.2 ha))
        (by omega)
    q_rr := by
      intro k r hr
      obtain ⟨a, ha⟩ := get (qR.1 hr)
      obtain ⟨hP, h⟩ := qRA.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hr (qR.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    g_za := by
      intro m j w hw hmj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi := gW.1 hw
      obtain ⟨a, ha⟩ := get hi
      obtain ⟨b, hb⟩ := get (show m < kws1.length by omega)
      obtain ⟨hP, h⟩ := gZ.2 hb
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hw (gW.2 ha)) (by omega)⟩
    g_az' := by
      intro k w hw
      rcases k with _ | i
      · obtain ⟨hP, h⟩ := gZ'0
        exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw gW0) ⟨hP, rfl⟩ (by omega)⟩
      · obtain ⟨a, ha⟩ := get (gW.1 hw)
        obtain ⟨hP, h⟩ := gZ'.2 ha
        exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw (gW.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    p_a'z := by
      intro k w hw
      obtain ⟨a, ha⟩ := get (pW.1 hw)
      obtain ⟨hP, h⟩ := pZ.2 ha
      exact ⟨_, h, G.po_of_pos (G.eq_of_nthEvent_pos hw (pW.2 ha)) ⟨hP, rfl⟩ (by omega)⟩
    p_z'a' := by
      intro m j w hw hmj
      have hj := pW.1 hw
      obtain ⟨a, ha⟩ := get (pW.1 hw)
      obtain ⟨b, hb⟩ := get (show m < vals.length by omega)
      obtain ⟨hP, h⟩ := pR.2 hb
      exact ⟨_, h, G.po_of_pos ⟨hP, rfl⟩ (G.eq_of_nthEvent_pos hw (pW.2 ha)) (by omega)⟩ }

/-- Eq. (17): an `rf`-edge from `w_i(g_α^x, x_α)` into `r_k(c^x, x_α)` has `i = k`. -/
theorem no_skipping_guessAX_checkX_xA (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessAX Loc.xA i = some ew)
    (her : G.nthRead Tid.checkX Loc.xA K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((crossPair_xA I G hG).no_skipping hG.1.1 K).1 hew her hrf

/-- Eq. (17): an `rf`-edge from `w_i(g_α^{x'}, x'_α)` into `r_k(c^{x'}, x'_α)` has `i = k`. -/
theorem no_skipping_primeAX_primeCheckX_xA' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeAX Loc.xA' i = some ew)
    (her : G.nthRead Tid.primeCheckX Loc.xA' K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((crossPair_xA I G hG).no_skipping hG.1.1 K).2 hew her hrf

/-- Eq. (17): an `rf`-edge from `w_i(g_β^x, x_β)` into `r_k(c^x, x_β)` has `i = k`. -/
theorem no_skipping_guessBX_checkX_xB (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessBX Loc.xB i = some ew)
    (her : G.nthRead Tid.checkX Loc.xB K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((crossPair_xB I G hG).no_skipping hG.1.1 K).1 hew her hrf

/-- Eq. (17): an `rf`-edge from `w_i(g_β^{x'}, x'_β)` into `r_k(c^{x'}, x'_β)` has `i = k`. -/
theorem no_skipping_primeBX_primeCheckX_xB' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeBX Loc.xB' i = some ew)
    (her : G.nthRead Tid.primeCheckX Loc.xB' K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((crossPair_xB I G hG).no_skipping hG.1.1 K).2 hew her hrf

/-- Eq. (17): an `rf`-edge from `w_i(g_α^y, y_α)` into `r_k(c^y, y_α)` has `i = k`. -/
theorem no_skipping_guessAY_checkY_yA (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessAY Loc.yA i = some ew)
    (her : G.nthRead Tid.checkY Loc.yA K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((crossPair_yA I G hG).no_skipping hG.1.1 K).1 hew her hrf

/-- Eq. (17): an `rf`-edge from `w_i(g_α^{y'}, y'_α)` into `r_k(c^{y'}, y'_α)` has `i = k`. -/
theorem no_skipping_primeAY_primeCheckY_yA' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeAY Loc.yA' i = some ew)
    (her : G.nthRead Tid.primeCheckY Loc.yA' K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((crossPair_yA I G hG).no_skipping hG.1.1 K).2 hew her hrf

/-- Eq. (17): an `rf`-edge from `w_i(g_β^y, y_β)` into `r_k(c^y, y_β)` has `i = k`. -/
theorem no_skipping_guessBY_checkY_yB (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.guessBY Loc.yB i = some ew)
    (her : G.nthRead Tid.checkY Loc.yB K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((crossPair_yB I G hG).no_skipping hG.1.1 K).1 hew her hrf

/-- Eq. (17): an `rf`-edge from `w_i(g_β^{y'}, y'_β)` into `r_k(c^{y'}, y'_β)` has `i = k`. -/
theorem no_skipping_primeBY_primeCheckY_yB' (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i K : ℕ) {ew er : Event (domainOf I)}
    (hew : G.nthWrite Tid.primeBY Loc.yB' i = some ew)
    (her : G.nthRead Tid.primeCheckY Loc.yB' K = some er) (hrf : G.rf ew er) :
    i = K :=
  ((crossPair_yB I G hG).no_skipping hG.1.1 K).2 hew her hrf

end RAUndecidability
