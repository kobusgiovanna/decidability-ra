import RAUndecidability.Reduction.Completeness.Graph
import RAUndecidability.Reduction.Completeness.Paths

/-!
# Consistency of the constructed execution graph

Section 3.5's consistency argument for `G := executionGraphOf I hsol`, with
proofs from Section 3.5 and Appendix B: Lemma 3.6, Lemma 3.7 at `G`,
Lemma 3.8, Lemma 3.9, Lemma 3.10,
Lemma 3.11, Lemma 3.12, Lemma 3.13, and the
two coherence obligations, assembled into RA-consistency of `G`.

Lemma 3.6 (`G.hb` is irreflexive) has four parts: the first two
(`Path.hasRf_of_cyclic`, `Path.exists_minimal_alternating_cycle`) and the
topology step shared by the last two (`Path.poThreads_cyclic_chain`,
`Path.exists_cycle_shape`) are in `Paths.lean`; the last two are here.

## The six non-bridge pairs (the non-bridge pairs of Lemma 3.6)

For each of the six thread pairs `{guessAX,primeAX}`, `{guessAY,primeAY}`,
`{guessBX,primeBX}`, `{guessBY,primeBY}`, `{checkX,primeCheckX}`,
`{checkY,primeCheckY}`, a minimal alternating `hb`-cycle confined to the pair
is impossible: its two `rf`-edges preserve indices and its two `po`-edges are
increasing (`executionGraphOf_po_monotone`, neither location being a bridge
location), giving `i < j < i`.
-/

namespace RAUndecidability

variable {I : PCPInstance}

/-- The twelve non-bridge locations of the six non-bridge pairs are not bridge
locations. (Stated without parameters so that `decide` applies.) -/
theorem nonbridge_locs_not_bridge :
    Loc.zAxx' ∉ BridgeLoc ∧ Loc.zAx'x ∉ BridgeLoc ∧ Loc.zAyy' ∉ BridgeLoc ∧ Loc.zAy'y ∉ BridgeLoc ∧
    Loc.zBxx' ∉ BridgeLoc ∧ Loc.zBx'x ∉ BridgeLoc ∧ Loc.zByy' ∉ BridgeLoc ∧ Loc.zBy'y ∉ BridgeLoc ∧
    Loc.xA ∉ BridgeLoc ∧ Loc.xA' ∉ BridgeLoc ∧ Loc.xB ∉ BridgeLoc ∧ Loc.xB' ∉ BridgeLoc ∧
    Loc.yA ∉ BridgeLoc ∧ Loc.yA' ∉ BridgeLoc ∧ Loc.yB ∉ BridgeLoc ∧ Loc.yB' ∉ BridgeLoc := by
  decide

theorem zAxx'_nb : Loc.zAxx' ∉ BridgeLoc := nonbridge_locs_not_bridge.1
theorem zAx'x_nb : Loc.zAx'x ∉ BridgeLoc := nonbridge_locs_not_bridge.2.1
theorem zAyy'_nb : Loc.zAyy' ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.1
theorem zAy'y_nb : Loc.zAy'y ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.1
theorem zBxx'_nb : Loc.zBxx' ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.1
theorem zBx'x_nb : Loc.zBx'x ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.1
theorem zByy'_nb : Loc.zByy' ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.1
theorem zBy'y_nb : Loc.zBy'y ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.1
theorem xA_nb : Loc.xA ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.2.1
theorem xAp_nb : Loc.xA' ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.2.2.1
theorem xB_nb : Loc.xB ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.2.2.2.1
theorem xBp_nb : Loc.xB' ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.2.2.2.2.1
theorem yA_nb : Loc.yA ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem yAp_nb : Loc.yA' ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem yB_nb : Loc.yB ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem yBp_nb : Loc.yB' ∉ BridgeLoc := nonbridge_locs_not_bridge.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Every `rf`-edge of `G` preserves indices ("`rf`-edges are non-decreasing
by construction"): `traceRf_rawIndex_eq` via
`ExecutionGraph.index_eq_rawIndex`. -/
theorem executionGraphOf_rf_index_eq (I : PCPInstance) (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er := by
  obtain ⟨hewmem, hermem, -, -, -⟩ := (executionGraphOf I hsol).rf_subset hrf
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hewmem
  have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hermem
  rw [hi1, hi2]
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  rw [hrfEq] at hrf
  exact traceRf_rawIndex_eq I hrf

-- The `simp` inside `first` makes the first alternative fail at the one location where
-- it does not apply; the unused-tactic linter misreports it as doing nothing.
set_option linter.unusedTactic false in
/-- An `rf`-edge between `guessAX` and `primeAX` (locations `zAxx'`/`zAx'x`)
relates events of equal `G.index`, both non-bridge. By unfolding `traceRf`
once both endpoints' threads are fixed: a case split on the reader's
location. -/
theorem executionGraphOf_rf_index_eq_guessAX_primeAX (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.primeAX ∧ er.tid = Tid.guessAX) ∨
      (ew.tid = Tid.guessAX ∧ er.tid = Tid.primeAX)) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er ∧
      ¬ ew.IsBridge ∧ ¬ er.IsBridge := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases ht with ⟨hewtid, hertid⟩ | ⟨hewtid, hertid⟩
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             exact zAxx'_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             exact zAxx'_nb)
        | exact hrf.elim
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             exact zAx'x_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             exact zAx'x_nb)
        | exact hrf.elim

/-- The non-bridge pairs of Lemma 3.6, the `{guessAX,primeAX}` case: a minimal alternating
`hb`-cycle confined to this pair is impossible. In the 4-event shape of
`Path.exists_cycle_shape`, both `rf`-edges preserve indices and both
`po`-edges are increasing (`executionGraphOf_po_monotone`), giving
`index w1 = index r1 < index w2 = index r2 < index w1`. -/
theorem executionGraphOf_hbirr_guessAX_primeAX (hsol : I.HasSolution)
    {w1 r1 w2 r2 : Event (domainOf I)}
    (hrf1 : (executionGraphOf I hsol).rf w1 r1) (hpo1 : (executionGraphOf I hsol).po r1 w2)
    (hrf2 : (executionGraphOf I hsol).rf w2 r2) (hpo2 : (executionGraphOf I hsol).po r2 w1)
    (ht1 : (w1.tid = Tid.primeAX ∧ r1.tid = Tid.guessAX) ∨
      (w1.tid = Tid.guessAX ∧ r1.tid = Tid.primeAX)) : False := by
  have hr1w2tid : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1tid : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have ht2 : (w2.tid = Tid.primeAX ∧ r2.tid = Tid.guessAX) ∨
      (w2.tid = Tid.guessAX ∧ r2.tid = Tid.primeAX) := by
    rcases ht1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩
    · exact Or.inr ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
    · exact Or.inl ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
  obtain ⟨hidx1, hnbw1, hnbr1⟩ := executionGraphOf_rf_index_eq_guessAX_primeAX hsol hrf1 ht1
  obtain ⟨hidx2, hnbw2, hnbr2⟩ := executionGraphOf_rf_index_eq_guessAX_primeAX hsol hrf2 ht2
  have hr1rd : r1.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf1).2.2.2.1
  have hr2rd : r2.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf2).2.2.2.1
  have hw2wt : w2.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf2).2.2.1
  have hw1wt : w1.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf1).2.2.1
  have hlt1 := (executionGraphOf_po_monotone I hsol hpo1 hw2wt hnbw2).2 hr1rd
  have hlt2 := (executionGraphOf_po_monotone I hsol hpo2 hw1wt hnbw1).2 hr2rd
  omega

-- The `simp` inside `first` makes the first alternative fail at the one location where
-- it does not apply; the unused-tactic linter misreports it as doing nothing.
set_option linter.unusedTactic false in
/-- An `rf`-edge between `guessAY` and `primeAY` (locations `zAyy'`/`zAy'y`)
relates events of equal `G.index`, both non-bridge. -/
theorem executionGraphOf_rf_index_eq_guessAY_primeAY (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.primeAY ∧ er.tid = Tid.guessAY) ∨
      (ew.tid = Tid.guessAY ∧ er.tid = Tid.primeAY)) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er ∧
      ¬ ew.IsBridge ∧ ¬ er.IsBridge := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases ht with ⟨hewtid, hertid⟩ | ⟨hewtid, hertid⟩
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             exact zAyy'_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             exact zAyy'_nb)
        | exact hrf.elim
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             exact zAy'y_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             exact zAy'y_nb)
        | exact hrf.elim

/-- The non-bridge pairs of Lemma 3.6, the `{guessAY,primeAY}` case. -/
theorem executionGraphOf_hbirr_guessAY_primeAY (hsol : I.HasSolution)
    {w1 r1 w2 r2 : Event (domainOf I)}
    (hrf1 : (executionGraphOf I hsol).rf w1 r1) (hpo1 : (executionGraphOf I hsol).po r1 w2)
    (hrf2 : (executionGraphOf I hsol).rf w2 r2) (hpo2 : (executionGraphOf I hsol).po r2 w1)
    (ht1 : (w1.tid = Tid.primeAY ∧ r1.tid = Tid.guessAY) ∨
      (w1.tid = Tid.guessAY ∧ r1.tid = Tid.primeAY)) : False := by
  have hr1w2tid : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1tid : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have ht2 : (w2.tid = Tid.primeAY ∧ r2.tid = Tid.guessAY) ∨
      (w2.tid = Tid.guessAY ∧ r2.tid = Tid.primeAY) := by
    rcases ht1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩
    · exact Or.inr ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
    · exact Or.inl ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
  obtain ⟨hidx1, hnbw1, hnbr1⟩ := executionGraphOf_rf_index_eq_guessAY_primeAY hsol hrf1 ht1
  obtain ⟨hidx2, hnbw2, hnbr2⟩ := executionGraphOf_rf_index_eq_guessAY_primeAY hsol hrf2 ht2
  have hr1rd : r1.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf1).2.2.2.1
  have hr2rd : r2.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf2).2.2.2.1
  have hw2wt : w2.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf2).2.2.1
  have hw1wt : w1.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf1).2.2.1
  have hlt1 := (executionGraphOf_po_monotone I hsol hpo1 hw2wt hnbw2).2 hr1rd
  have hlt2 := (executionGraphOf_po_monotone I hsol hpo2 hw1wt hnbw1).2 hr2rd
  omega


-- The `simp` inside `first` makes the first alternative fail at the one location where
-- it does not apply; the unused-tactic linter misreports it as doing nothing.
set_option linter.unusedTactic false in
/-- An `rf`-edge between `guessBX` and `primeBX` (locations `zBxx'`/`zBx'x`)
relates events of equal `G.index`, both non-bridge. -/
theorem executionGraphOf_rf_index_eq_guessBX_primeBX (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.primeBX ∧ er.tid = Tid.guessBX) ∨
      (ew.tid = Tid.guessBX ∧ er.tid = Tid.primeBX)) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er ∧
      ¬ ew.IsBridge ∧ ¬ er.IsBridge := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases ht with ⟨hewtid, hertid⟩ | ⟨hewtid, hertid⟩
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             exact zBxx'_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             exact zBxx'_nb)
        | exact hrf.elim
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             exact zBx'x_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             exact zBx'x_nb)
        | exact hrf.elim

/-- The non-bridge pairs of Lemma 3.6, the `{guessBX,primeBX}` case. -/
theorem executionGraphOf_hbirr_guessBX_primeBX (hsol : I.HasSolution)
    {w1 r1 w2 r2 : Event (domainOf I)}
    (hrf1 : (executionGraphOf I hsol).rf w1 r1) (hpo1 : (executionGraphOf I hsol).po r1 w2)
    (hrf2 : (executionGraphOf I hsol).rf w2 r2) (hpo2 : (executionGraphOf I hsol).po r2 w1)
    (ht1 : (w1.tid = Tid.primeBX ∧ r1.tid = Tid.guessBX) ∨
      (w1.tid = Tid.guessBX ∧ r1.tid = Tid.primeBX)) : False := by
  have hr1w2tid : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1tid : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have ht2 : (w2.tid = Tid.primeBX ∧ r2.tid = Tid.guessBX) ∨
      (w2.tid = Tid.guessBX ∧ r2.tid = Tid.primeBX) := by
    rcases ht1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩
    · exact Or.inr ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
    · exact Or.inl ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
  obtain ⟨hidx1, hnbw1, hnbr1⟩ := executionGraphOf_rf_index_eq_guessBX_primeBX hsol hrf1 ht1
  obtain ⟨hidx2, hnbw2, hnbr2⟩ := executionGraphOf_rf_index_eq_guessBX_primeBX hsol hrf2 ht2
  have hr1rd : r1.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf1).2.2.2.1
  have hr2rd : r2.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf2).2.2.2.1
  have hw2wt : w2.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf2).2.2.1
  have hw1wt : w1.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf1).2.2.1
  have hlt1 := (executionGraphOf_po_monotone I hsol hpo1 hw2wt hnbw2).2 hr1rd
  have hlt2 := (executionGraphOf_po_monotone I hsol hpo2 hw1wt hnbw1).2 hr2rd
  omega


-- The `simp` inside `first` makes the first alternative fail at the one location where
-- it does not apply; the unused-tactic linter misreports it as doing nothing.
set_option linter.unusedTactic false in
/-- An `rf`-edge between `guessBY` and `primeBY` (locations `zByy'`/`zBy'y`)
relates events of equal `G.index`, both non-bridge. -/
theorem executionGraphOf_rf_index_eq_guessBY_primeBY (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.primeBY ∧ er.tid = Tid.guessBY) ∨
      (ew.tid = Tid.guessBY ∧ er.tid = Tid.primeBY)) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er ∧
      ¬ ew.IsBridge ∧ ¬ er.IsBridge := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases ht with ⟨hewtid, hertid⟩ | ⟨hewtid, hertid⟩
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             exact zByy'_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             exact zByy'_nb)
        | exact hrf.elim
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             exact zBy'y_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             exact zBy'y_nb)
        | exact hrf.elim

/-- The non-bridge pairs of Lemma 3.6, the `{guessBY,primeBY}` case. -/
theorem executionGraphOf_hbirr_guessBY_primeBY (hsol : I.HasSolution)
    {w1 r1 w2 r2 : Event (domainOf I)}
    (hrf1 : (executionGraphOf I hsol).rf w1 r1) (hpo1 : (executionGraphOf I hsol).po r1 w2)
    (hrf2 : (executionGraphOf I hsol).rf w2 r2) (hpo2 : (executionGraphOf I hsol).po r2 w1)
    (ht1 : (w1.tid = Tid.primeBY ∧ r1.tid = Tid.guessBY) ∨
      (w1.tid = Tid.guessBY ∧ r1.tid = Tid.primeBY)) : False := by
  have hr1w2tid : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1tid : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have ht2 : (w2.tid = Tid.primeBY ∧ r2.tid = Tid.guessBY) ∨
      (w2.tid = Tid.guessBY ∧ r2.tid = Tid.primeBY) := by
    rcases ht1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩
    · exact Or.inr ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
    · exact Or.inl ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
  obtain ⟨hidx1, hnbw1, hnbr1⟩ := executionGraphOf_rf_index_eq_guessBY_primeBY hsol hrf1 ht1
  obtain ⟨hidx2, hnbw2, hnbr2⟩ := executionGraphOf_rf_index_eq_guessBY_primeBY hsol hrf2 ht2
  have hr1rd : r1.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf1).2.2.2.1
  have hr2rd : r2.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf2).2.2.2.1
  have hw2wt : w2.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf2).2.2.1
  have hw1wt : w1.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf1).2.2.1
  have hlt1 := (executionGraphOf_po_monotone I hsol hpo1 hw2wt hnbw2).2 hr1rd
  have hlt2 := (executionGraphOf_po_monotone I hsol hpo2 hw1wt hnbw1).2 hr2rd
  omega

/-- An `rf`-edge between `checkX` and `primeCheckX` (locations `xA`/`xB` and
`xA'`/`xB'`, Eq. (16)) relates events of equal `G.index`, both
non-bridge. -/
theorem executionGraphOf_rf_index_eq_checkX_primeCheckX (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.checkX ∧ er.tid = Tid.primeCheckX) ∨
      (ew.tid = Tid.primeCheckX ∧ er.tid = Tid.checkX)) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er ∧
      ¬ ew.IsBridge ∧ ¬ er.IsBridge := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases ht with ⟨hewtid, hertid⟩ | ⟨hewtid, hertid⟩
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             first | exact xA_nb | exact xB_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             first | exact xA_nb | exact xB_nb)
        | exact hrf.elim
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             first | exact xAp_nb | exact xBp_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             first | exact xAp_nb | exact xBp_nb)
        | exact hrf.elim

/-- The non-bridge pairs of Lemma 3.6, the `{checkX,primeCheckX}` case. -/
theorem executionGraphOf_hbirr_checkX_primeCheckX (hsol : I.HasSolution)
    {w1 r1 w2 r2 : Event (domainOf I)}
    (hrf1 : (executionGraphOf I hsol).rf w1 r1) (hpo1 : (executionGraphOf I hsol).po r1 w2)
    (hrf2 : (executionGraphOf I hsol).rf w2 r2) (hpo2 : (executionGraphOf I hsol).po r2 w1)
    (ht1 : (w1.tid = Tid.primeCheckX ∧ r1.tid = Tid.checkX) ∨
      (w1.tid = Tid.checkX ∧ r1.tid = Tid.primeCheckX)) : False := by
  have hr1w2tid : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1tid : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have ht2 : (w2.tid = Tid.primeCheckX ∧ r2.tid = Tid.checkX) ∨
      (w2.tid = Tid.checkX ∧ r2.tid = Tid.primeCheckX) := by
    rcases ht1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩
    · exact Or.inr ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
    · exact Or.inl ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
  obtain ⟨hidx1, hnbw1, hnbr1⟩ :=
    executionGraphOf_rf_index_eq_checkX_primeCheckX hsol hrf1 ht1.symm
  obtain ⟨hidx2, hnbw2, hnbr2⟩ :=
    executionGraphOf_rf_index_eq_checkX_primeCheckX hsol hrf2 ht2.symm
  have hr1rd : r1.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf1).2.2.2.1
  have hr2rd : r2.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf2).2.2.2.1
  have hw2wt : w2.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf2).2.2.1
  have hw1wt : w1.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf1).2.2.1
  have hlt1 := (executionGraphOf_po_monotone I hsol hpo1 hw2wt hnbw2).2 hr1rd
  have hlt2 := (executionGraphOf_po_monotone I hsol hpo2 hw1wt hnbw1).2 hr2rd
  omega

/-- An `rf`-edge between `checkY` and `primeCheckY` (locations `yA`/`yB` and
`yA'`/`yB'`, Eq. (16)) relates events of equal `G.index`, both
non-bridge. -/
theorem executionGraphOf_rf_index_eq_checkY_primeCheckY (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.checkY ∧ er.tid = Tid.primeCheckY) ∨
      (ew.tid = Tid.primeCheckY ∧ er.tid = Tid.checkY)) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er ∧
      ¬ ew.IsBridge ∧ ¬ er.IsBridge := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases ht with ⟨hewtid, hertid⟩ | ⟨hewtid, hertid⟩
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             first | exact yA_nb | exact yB_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             first | exact yA_nb | exact yB_nb)
        | exact hrf.elim
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]
             first | exact yAp_nb | exact yBp_nb
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]
             first | exact yAp_nb | exact yBp_nb)
        | exact hrf.elim

/-- The non-bridge pairs of Lemma 3.6, the `{checkY,primeCheckY}` case. -/
theorem executionGraphOf_hbirr_checkY_primeCheckY (hsol : I.HasSolution)
    {w1 r1 w2 r2 : Event (domainOf I)}
    (hrf1 : (executionGraphOf I hsol).rf w1 r1) (hpo1 : (executionGraphOf I hsol).po r1 w2)
    (hrf2 : (executionGraphOf I hsol).rf w2 r2) (hpo2 : (executionGraphOf I hsol).po r2 w1)
    (ht1 : (w1.tid = Tid.primeCheckY ∧ r1.tid = Tid.checkY) ∨
      (w1.tid = Tid.checkY ∧ r1.tid = Tid.primeCheckY)) : False := by
  have hr1w2tid : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1tid : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have ht2 : (w2.tid = Tid.primeCheckY ∧ r2.tid = Tid.checkY) ∨
      (w2.tid = Tid.checkY ∧ r2.tid = Tid.primeCheckY) := by
    rcases ht1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩
    · exact Or.inr ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
    · exact Or.inl ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
  obtain ⟨hidx1, hnbw1, hnbr1⟩ :=
    executionGraphOf_rf_index_eq_checkY_primeCheckY hsol hrf1 ht1.symm
  obtain ⟨hidx2, hnbw2, hnbr2⟩ :=
    executionGraphOf_rf_index_eq_checkY_primeCheckY hsol hrf2 ht2.symm
  have hr1rd : r1.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf1).2.2.2.1
  have hr2rd : r2.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf2).2.2.2.1
  have hw2wt : w2.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf2).2.2.1
  have hw1wt : w1.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf1).2.2.1
  have hlt1 := (executionGraphOf_po_monotone I hsol hpo1 hw2wt hnbw2).2 hr1rd
  have hlt2 := (executionGraphOf_po_monotone I hsol hpo2 hw1wt hnbw1).2 hr2rd
  omega

/-! ## The two bridge pairs (the bridge pairs of Lemma 3.6)

For `{guessAX,guessAY}` and `{guessBX,guessBY}` the argument is the same, but
the `rf`-edges join bridge events and the increasing `po`-edge fact is
specific to each thread (the bridge-write counterpart of Lemma 3.4), so the proof splits on
which thread each `po`-edge lies on. -/

/-- The four bridge locations are bridge locations. -/
theorem bridge_locs_is_bridge :
    Loc.zAxy ∈ BridgeLoc ∧ Loc.ellAyx ∈ BridgeLoc ∧ Loc.zBxy ∈ BridgeLoc ∧ Loc.ellByx ∈ BridgeLoc := by
  decide

theorem zAxy_ib : Loc.zAxy ∈ BridgeLoc := bridge_locs_is_bridge.1
theorem ellAyx_ib : Loc.ellAyx ∈ BridgeLoc := bridge_locs_is_bridge.2.1
theorem zBxy_ib : Loc.zBxy ∈ BridgeLoc := bridge_locs_is_bridge.2.2.1
theorem ellByx_ib : Loc.ellByx ∈ BridgeLoc := bridge_locs_is_bridge.2.2.2

/-- `guessAX_bridge_rw_increasing` (the bridge-write counterpart of Lemma 3.4) at the level of
`G.po`/`G.index`. -/
theorem executionGraphOf_guessAX_bridge_rw_increasing (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (hpo : (executionGraphOf I hsol).po e1 e2)
    (htid1 : e1.tid = Tid.guessAX) (hrd1 : e1.op = .rd) (hwt2 : e2.op = .wt)
    (hb1 : e1.IsBridge) (hb2 : e2.IsBridge) :
    (executionGraphOf I hsol).index e1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace Tid.guessAX := mem_traceEvents_of_tid hmem1 htid1
  have htid2 : e2.tid = Tid.guessAX := hpo'.1.symm.trans htid1
  have he2 : e2 ∈ traceEventsOf trace Tid.guessAX := mem_traceEvents_of_tid hmem2 htid2
  obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
      htrace⟩ := hshapes.guessAX
  have hraw := guessAX_bridge_rw_increasing I trace ks N v1 v2 vB0 hks inner0Rest outerRest
    hinner0 houterLen houter houterLast htrace he1 he2 hpo' hrd1 hwt2 hb1 hb2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `guessBX_bridge_rw_increasing` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_guessBX_bridge_rw_increasing (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (hpo : (executionGraphOf I hsol).po e1 e2)
    (htid1 : e1.tid = Tid.guessBX) (hrd1 : e1.op = .rd) (hwt2 : e2.op = .wt)
    (hb1 : e1.IsBridge) (hb2 : e2.IsBridge) :
    (executionGraphOf I hsol).index e1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace Tid.guessBX := mem_traceEvents_of_tid hmem1 htid1
  have htid2 : e2.tid = Tid.guessBX := hpo'.1.symm.trans htid1
  have he2 : e2 ∈ traceEventsOf trace Tid.guessBX := mem_traceEvents_of_tid hmem2 htid2
  obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
      htrace⟩ := hshapes.guessBX
  have hraw := guessBX_bridge_rw_increasing I trace ks N v1 v2 vB0 hks inner0Rest outerRest
    hinner0 houterLen houter houterLast htrace he1 he2 hpo' hrd1 hwt2 hb1 hb2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `guessAY_bridge_rw_increasing` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_guessAY_bridge_rw_increasing (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (hpo : (executionGraphOf I hsol).po e1 e2)
    (htid1 : e1.tid = Tid.guessAY) (hrd1 : e1.op = .rd) (hwt2 : e2.op = .wt)
    (hb1 : e1.IsBridge) (hb2 : e2.IsBridge) :
    (executionGraphOf I hsol).index e1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace Tid.guessAY := mem_traceEvents_of_tid hmem1 htid1
  have htid2 : e2.tid = Tid.guessAY := hpo'.1.symm.trans htid1
  have he2 : e2 ∈ traceEventsOf trace Tid.guessAY := mem_traceEvents_of_tid hmem2 htid2
  obtain ⟨v0, kws, htrace⟩ := hshapes.guessAY
  have hraw := guessAY_bridge_rw_increasing I trace v0 kws htrace he1 he2 hpo' hrd1 hwt2 hb1 hb2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `guessBY_bridge_rw_increasing` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_guessBY_bridge_rw_increasing (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (hpo : (executionGraphOf I hsol).po e1 e2)
    (htid1 : e1.tid = Tid.guessBY) (hrd1 : e1.op = .rd) (hwt2 : e2.op = .wt)
    (hb1 : e1.IsBridge) (hb2 : e2.IsBridge) :
    (executionGraphOf I hsol).index e1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace Tid.guessBY := mem_traceEvents_of_tid hmem1 htid1
  have htid2 : e2.tid = Tid.guessBY := hpo'.1.symm.trans htid1
  have he2 : e2 ∈ traceEventsOf trace Tid.guessBY := mem_traceEvents_of_tid hmem2 htid2
  obtain ⟨v0, kws, htrace⟩ := hshapes.guessBY
  have hraw := guessBY_bridge_rw_increasing I trace v0 kws htrace he1 he2 hpo' hrd1 hwt2 hb1 hb2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- An `rf`-edge between `guessAX` and `guessAY` (bridge locations
`zAxy`/`ellAyx`) relates events of equal `G.index`, both bridge events. -/
theorem executionGraphOf_rf_index_eq_guessAX_guessAY (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.guessAX ∧ er.tid = Tid.guessAY) ∨
      (ew.tid = Tid.guessAY ∧ er.tid = Tid.guessAX)) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er ∧
      ew.IsBridge ∧ er.IsBridge := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases ht with ⟨hewtid, hertid⟩ | ⟨hewtid, hertid⟩
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]; exact zAxy_ib
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]; exact zAxy_ib)
        | exact hrf.elim
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]; exact ellAyx_ib
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]; exact ellAyx_ib)
        | exact hrf.elim

/-- The bridge pairs of Lemma 3.6, the `{guessAX,guessAY}` case. The proof splits on the
direction of the cycle to apply `executionGraphOf_guessAX_bridge_rw_increasing`
and `executionGraphOf_guessAY_bridge_rw_increasing` to the right edges. -/
theorem executionGraphOf_hbirr_guessAX_guessAY (hsol : I.HasSolution)
    {w1 r1 w2 r2 : Event (domainOf I)}
    (hrf1 : (executionGraphOf I hsol).rf w1 r1) (hpo1 : (executionGraphOf I hsol).po r1 w2)
    (hrf2 : (executionGraphOf I hsol).rf w2 r2) (hpo2 : (executionGraphOf I hsol).po r2 w1)
    (ht1 : (w1.tid = Tid.guessAX ∧ r1.tid = Tid.guessAY) ∨
      (w1.tid = Tid.guessAY ∧ r1.tid = Tid.guessAX)) : False := by
  have hr1w2tid : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1tid : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have ht2 : (w2.tid = Tid.guessAX ∧ r2.tid = Tid.guessAY) ∨
      (w2.tid = Tid.guessAY ∧ r2.tid = Tid.guessAX) := by
    rcases ht1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩
    · exact Or.inr ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
    · exact Or.inl ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
  obtain ⟨hidx1, hbw1, hbr1⟩ := executionGraphOf_rf_index_eq_guessAX_guessAY hsol hrf1 ht1
  obtain ⟨hidx2, hbw2, hbr2⟩ := executionGraphOf_rf_index_eq_guessAX_guessAY hsol hrf2 ht2
  have hr1rd : r1.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf1).2.2.2.1
  have hr2rd : r2.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf2).2.2.2.1
  have hw2wt : w2.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf2).2.2.1
  have hw1wt : w1.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf1).2.2.1
  rcases ht1 with ⟨hw1t, hr1t⟩ | ⟨hw1t, hr1t⟩
  · have hlt1 := executionGraphOf_guessAY_bridge_rw_increasing hsol hpo1 hr1t hr1rd hw2wt hbr1 hbw2
    have hr2t : r2.tid = Tid.guessAX := hr2w1tid.trans hw1t
    have hlt2 := executionGraphOf_guessAX_bridge_rw_increasing hsol hpo2 hr2t hr2rd hw1wt hbr2 hbw1
    omega
  · have hlt1 := executionGraphOf_guessAX_bridge_rw_increasing hsol hpo1 hr1t hr1rd hw2wt hbr1 hbw2
    have hr2t : r2.tid = Tid.guessAY := hr2w1tid.trans hw1t
    have hlt2 := executionGraphOf_guessAY_bridge_rw_increasing hsol hpo2 hr2t hr2rd hw1wt hbr2 hbw1
    omega

/-- An `rf`-edge between `guessBX` and `guessBY` (bridge locations
`zBxy`/`ellByx`) relates events of equal `G.index`, both bridge events. -/
theorem executionGraphOf_rf_index_eq_guessBX_guessBY (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.guessBX ∧ er.tid = Tid.guessBY) ∨
      (ew.tid = Tid.guessBY ∧ er.tid = Tid.guessBX)) :
    (executionGraphOf I hsol).index ew = (executionGraphOf I hsol).index er ∧
      ew.IsBridge ∧ er.IsBridge := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases ht with ⟨hewtid, hertid⟩ | ⟨hewtid, hertid⟩
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]; exact zBxy_ib
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]; exact zBxy_ib)
        | exact hrf.elim
  · rw [hertid] at hrf
    rcases hloc : er.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
      rw [hloc] at hrf <;>
      first
        | exact absurd hewtid (by
            obtain ⟨i, hw, _⟩ := hrf
            rw [(rawNthEvent_mem hw).2.1]; simp)
        | (obtain ⟨i, hw, hr⟩ := hrf
           have hi1 : (executionGraphOf I hsol).index ew = rawIndex trace ew :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hw).1
           have hi2 : (executionGraphOf I hsol).index er = rawIndex trace er :=
             (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq
               (rawNthEvent_mem hr).1
           refine ⟨?_, ?_, ?_⟩
           · rw [hi1, hi2]; exact (rawNthEvent_rawIndex hw).trans (rawNthEvent_rawIndex hr).symm
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hw).2.2.1]; exact ellByx_ib
           · unfold Event.IsBridge; rw [(rawNthEvent_mem hr).2.2.1]; exact ellByx_ib)
        | exact hrf.elim

/-- The bridge pairs of Lemma 3.6, the `{guessBX,guessBY}` case. -/
theorem executionGraphOf_hbirr_guessBX_guessBY (hsol : I.HasSolution)
    {w1 r1 w2 r2 : Event (domainOf I)}
    (hrf1 : (executionGraphOf I hsol).rf w1 r1) (hpo1 : (executionGraphOf I hsol).po r1 w2)
    (hrf2 : (executionGraphOf I hsol).rf w2 r2) (hpo2 : (executionGraphOf I hsol).po r2 w1)
    (ht1 : (w1.tid = Tid.guessBX ∧ r1.tid = Tid.guessBY) ∨
      (w1.tid = Tid.guessBY ∧ r1.tid = Tid.guessBX)) : False := by
  have hr1w2tid : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1tid : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have ht2 : (w2.tid = Tid.guessBX ∧ r2.tid = Tid.guessBY) ∨
      (w2.tid = Tid.guessBY ∧ r2.tid = Tid.guessBX) := by
    rcases ht1 with ⟨hw1, hr1⟩ | ⟨hw1, hr1⟩
    · exact Or.inr ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
    · exact Or.inl ⟨by rw [← hr1w2tid]; exact hr1, by rw [hr2w1tid]; exact hw1⟩
  obtain ⟨hidx1, hbw1, hbr1⟩ := executionGraphOf_rf_index_eq_guessBX_guessBY hsol hrf1 ht1
  obtain ⟨hidx2, hbw2, hbr2⟩ := executionGraphOf_rf_index_eq_guessBX_guessBY hsol hrf2 ht2
  have hr1rd : r1.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf1).2.2.2.1
  have hr2rd : r2.op = OpType.rd := ((executionGraphOf I hsol).rf_subset hrf2).2.2.2.1
  have hw2wt : w2.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf2).2.2.1
  have hw1wt : w1.op = OpType.wt := ((executionGraphOf I hsol).rf_subset hrf1).2.2.1
  rcases ht1 with ⟨hw1t, hr1t⟩ | ⟨hw1t, hr1t⟩
  · have hlt1 := executionGraphOf_guessBY_bridge_rw_increasing hsol hpo1 hr1t hr1rd hw2wt hbr1 hbw2
    have hr2t : r2.tid = Tid.guessBX := hr2w1tid.trans hw1t
    have hlt2 := executionGraphOf_guessBX_bridge_rw_increasing hsol hpo2 hr2t hr2rd hw1wt hbr2 hbw1
    omega
  · have hlt1 := executionGraphOf_guessBX_bridge_rw_increasing hsol hpo1 hr1t hr1rd hw2wt hbr1 hbw2
    have hr2t : r2.tid = Tid.guessBY := hr2w1tid.trans hw1t
    have hlt2 := executionGraphOf_guessBY_bridge_rw_increasing hsol hpo2 hr2t hr2rd hw1wt hbr2 hbw1
    omega

/-- Restates `Path.poThreads_cyclic_chain`'s conclusion (phrased with `.head`)
in the `.headI` form of `executionGraphOf_rf_cycle_length_two`. -/
theorem executionGraphOf_poThreads_length_two (I : PCPInstance) (hsol : I.HasSolution)
    (l : List (domainOf I).Tid) (hne : l ≠ []) (hmin : l.Nodup)
    (hchain : List.IsChain (executionGraphOf I hsol).ThreadRf (l ++ [l.head hne])) :
    l.length = 2 := by
  refine executionGraphOf_rf_cycle_length_two I hsol l hne hmin ?_
  cases l with
  | nil => exact absurd rfl hne
  | cons x t => exact hchain

/-! ## Lemma 3.6 -/

/-- **Paper:** Lemma 3.6.

Lemma 3.6: `G.hb` is irreflexive. Shorten any `hb`-cycle to a minimal
alternating one (`Path.exists_alternating_of_hb`,
`Path.exists_minimal_alternating_cycle`); its `poThreads` form a cyclic
`rf`-chain of length `2` (`Path.poThreads_cyclic_chain`,
`executionGraphOf_rf_cycle_length_two`); extract its 4-event shape
(`Path.exists_cycle_shape`), and case on the threads of its first `rf`-edge
(`executionGraphOf_threadRf_pairs`). Sixteen cases are the eight pairs above
(in both directions); in the remaining eight (one-directional
guesser-to-checker edges) the second `rf`-edge would have to run in the
reverse direction, which no `rf`-edge does. -/
theorem executionGraphOf_hb_irrefl (I : PCPInstance) (hsol : I.HasSolution)
    (e : Event (domainOf I)) : ¬ (executionGraphOf I hsol).hb e e := by
  intro hhb
  obtain ⟨p, hp⟩ := Path.exists_alternating_of_hb hhb
  obtain ⟨e', p', hp', hmin'⟩ := Path.exists_minimal_alternating_cycle p.length e p hp rfl
  have hne : p'.poThreads ≠ [] := p'.poThreads_ne_nil_of_cyclic hp'
  have hchain := p'.poThreads_cyclic_chain hp' hmin' hne
  have hlen2 : p'.poThreads.length = 2 :=
    executionGraphOf_poThreads_length_two I hsol p'.poThreads hne hmin' hchain
  obtain ⟨w1, r1, w2, r2, hrf1, hpo1, hrf2, hpo2, _⟩ :=
    p'.exists_cycle_shape hp' hmin' hlen2
  have hr1w2 : r1.tid = w2.tid := ((executionGraphOf I hsol).po_subset hpo1).2.2
  have hr2w1 : r2.tid = w1.tid := ((executionGraphOf I hsol).po_subset hpo2).2.2
  have hthreadRf1 : executionGraphOf_ThreadRf I hsol w1.tid r1.tid := ⟨w1, r1, hrf1, rfl, rfl⟩
  rcases executionGraphOf_threadRf_pairs I hsol hthreadRf1 with
    ⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|
    ⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|
    ⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩|⟨hw1, hr1t⟩
  -- 1. (primeAX, guessAX)
  · exact executionGraphOf_hbirr_guessAX_primeAX hsol hrf1 hpo1 hrf2 hpo2 (Or.inl ⟨hw1, hr1t⟩)
  -- 2. (guessAX, primeAX)
  · exact executionGraphOf_hbirr_guessAX_primeAX hsol hrf1 hpo1 hrf2 hpo2 (Or.inr ⟨hw1, hr1t⟩)
  -- 3. (primeAY, guessAY)
  · exact executionGraphOf_hbirr_guessAY_primeAY hsol hrf1 hpo1 hrf2 hpo2 (Or.inl ⟨hw1, hr1t⟩)
  -- 4. (guessAY, primeAY)
  · exact executionGraphOf_hbirr_guessAY_primeAY hsol hrf1 hpo1 hrf2 hpo2 (Or.inr ⟨hw1, hr1t⟩)
  -- 5. (primeBX, guessBX)
  · exact executionGraphOf_hbirr_guessBX_primeBX hsol hrf1 hpo1 hrf2 hpo2 (Or.inl ⟨hw1, hr1t⟩)
  -- 6. (guessBX, primeBX)
  · exact executionGraphOf_hbirr_guessBX_primeBX hsol hrf1 hpo1 hrf2 hpo2 (Or.inr ⟨hw1, hr1t⟩)
  -- 7. (primeBY, guessBY)
  · exact executionGraphOf_hbirr_guessBY_primeBY hsol hrf1 hpo1 hrf2 hpo2 (Or.inl ⟨hw1, hr1t⟩)
  -- 8. (guessBY, primeBY)
  · exact executionGraphOf_hbirr_guessBY_primeBY hsol hrf1 hpo1 hrf2 hpo2 (Or.inr ⟨hw1, hr1t⟩)
  -- 9. (guessAX, guessAY)
  · exact executionGraphOf_hbirr_guessAX_guessAY hsol hrf1 hpo1 hrf2 hpo2 (Or.inl ⟨hw1, hr1t⟩)
  -- 10. (guessAY, guessAX)
  · exact executionGraphOf_hbirr_guessAX_guessAY hsol hrf1 hpo1 hrf2 hpo2 (Or.inr ⟨hw1, hr1t⟩)
  -- 11. (guessBX, guessBY)
  · exact executionGraphOf_hbirr_guessBX_guessBY hsol hrf1 hpo1 hrf2 hpo2 (Or.inl ⟨hw1, hr1t⟩)
  -- 12. (guessBY, guessBX)
  · exact executionGraphOf_hbirr_guessBX_guessBY hsol hrf1 hpo1 hrf2 hpo2 (Or.inr ⟨hw1, hr1t⟩)
  -- 13. (checkX, primeCheckX)
  · exact executionGraphOf_hbirr_checkX_primeCheckX hsol hrf1 hpo1 hrf2 hpo2 (Or.inr ⟨hw1, hr1t⟩)
  -- 14. (primeCheckX, checkX)
  · exact executionGraphOf_hbirr_checkX_primeCheckX hsol hrf1 hpo1 hrf2 hpo2 (Or.inl ⟨hw1, hr1t⟩)
  -- 15. (checkY, primeCheckY)
  · exact executionGraphOf_hbirr_checkY_primeCheckY hsol hrf1 hpo1 hrf2 hpo2 (Or.inr ⟨hw1, hr1t⟩)
  -- 16. (primeCheckY, checkY)
  · exact executionGraphOf_hbirr_checkY_primeCheckY hsol hrf1 hpo1 hrf2 hpo2 (Or.inl ⟨hw1, hr1t⟩)
  -- 17. (guessAX, checkX): forces w2.tid = checkX, r2.tid = guessAX -- not a listed pair
  · exfalso
    have hthreadRf2 : executionGraphOf_ThreadRf I hsol Tid.checkX Tid.guessAX :=
      ⟨w2, r2, hrf2, hr1w2.symm.trans hr1t, hr2w1.trans hw1⟩
    rcases executionGraphOf_threadRf_pairs I hsol hthreadRf2 with
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩ <;>
      first | (injection h2a; done) | injection h2b
  -- 18. (primeAX, primeCheckX): forces w2.tid = primeCheckX, r2.tid = primeAX
  · exfalso
    have hthreadRf2 : executionGraphOf_ThreadRf I hsol Tid.primeCheckX Tid.primeAX :=
      ⟨w2, r2, hrf2, hr1w2.symm.trans hr1t, hr2w1.trans hw1⟩
    rcases executionGraphOf_threadRf_pairs I hsol hthreadRf2 with
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩ <;>
      first | (injection h2a; done) | injection h2b
  -- 19. (guessBX, checkX): forces w2.tid = checkX, r2.tid = guessBX
  · exfalso
    have hthreadRf2 : executionGraphOf_ThreadRf I hsol Tid.checkX Tid.guessBX :=
      ⟨w2, r2, hrf2, hr1w2.symm.trans hr1t, hr2w1.trans hw1⟩
    rcases executionGraphOf_threadRf_pairs I hsol hthreadRf2 with
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩ <;>
      first | (injection h2a; done) | injection h2b
  -- 20. (primeBX, primeCheckX): forces w2.tid = primeCheckX, r2.tid = primeBX
  · exfalso
    have hthreadRf2 : executionGraphOf_ThreadRf I hsol Tid.primeCheckX Tid.primeBX :=
      ⟨w2, r2, hrf2, hr1w2.symm.trans hr1t, hr2w1.trans hw1⟩
    rcases executionGraphOf_threadRf_pairs I hsol hthreadRf2 with
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩ <;>
      first | (injection h2a; done) | injection h2b
  -- 21. (guessAY, checkY): forces w2.tid = checkY, r2.tid = guessAY
  · exfalso
    have hthreadRf2 : executionGraphOf_ThreadRf I hsol Tid.checkY Tid.guessAY :=
      ⟨w2, r2, hrf2, hr1w2.symm.trans hr1t, hr2w1.trans hw1⟩
    rcases executionGraphOf_threadRf_pairs I hsol hthreadRf2 with
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩ <;>
      first | (injection h2a; done) | injection h2b
  -- 22. (primeAY, primeCheckY): forces w2.tid = primeCheckY, r2.tid = primeAY
  · exfalso
    have hthreadRf2 : executionGraphOf_ThreadRf I hsol Tid.primeCheckY Tid.primeAY :=
      ⟨w2, r2, hrf2, hr1w2.symm.trans hr1t, hr2w1.trans hw1⟩
    rcases executionGraphOf_threadRf_pairs I hsol hthreadRf2 with
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩ <;>
      first | (injection h2a; done) | injection h2b
  -- 23. (guessBY, checkY): forces w2.tid = checkY, r2.tid = guessBY
  · exfalso
    have hthreadRf2 : executionGraphOf_ThreadRf I hsol Tid.checkY Tid.guessBY :=
      ⟨w2, r2, hrf2, hr1w2.symm.trans hr1t, hr2w1.trans hw1⟩
    rcases executionGraphOf_threadRf_pairs I hsol hthreadRf2 with
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩ <;>
      first | (injection h2a; done) | injection h2b
  -- 24. (primeBY, primeCheckY): forces w2.tid = primeCheckY, r2.tid = primeBY
  · exfalso
    have hthreadRf2 : executionGraphOf_ThreadRf I hsol Tid.primeCheckY Tid.primeBY :=
      ⟨w2, r2, hrf2, hr1w2.symm.trans hr1t, hr2w1.trans hw1⟩
    rcases executionGraphOf_threadRf_pairs I hsol hthreadRf2 with
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|
      ⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩|⟨h2a,h2b⟩ <;>
      first | (injection h2a; done) | injection h2b

/-! ## Lemma 3.7 at `G` -/

/-- **Paper:** Lemma 3.7.

Lemma 3.7 for `G := executionGraphOf I hsol`:
`Path.exists_minimal`, with `hirr` discharged by `executionGraphOf_hb_irrefl`
and the path obtained from `a ⟶hb b` by `Path.complete`. -/
theorem executionGraphOf_hb_minimal (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (hhb : (executionGraphOf I hsol).hb a b) :
    ∃ p : Path (executionGraphOf I hsol) a b, p.IsMinimal := by
  obtain ⟨p⟩ := Path.complete hhb
  exact Path.exists_minimal (executionGraphOf_hb_irrefl I hsol) p

/-! ## Lemma 3.8 (`write_to_write_no_bridge`) -/

/-- "bridge-free" (§3.5): no event the path touches accesses
a bridge location. -/
def Path.IsBridgeFree {G : ExecutionGraph (domainOf I)} {a b : Event (domainOf I)}
    (p : Path G a b) : Prop :=
  p.AllEventsSatisfy (fun e => ¬ e.IsBridge)

/-- The thread pairs of `executionGraphOf_threadRf_pairs` either stay within
one of `ThreadDomX`/`ThreadDomY` or are one of the bridge pairs
`{guessAX,guessAY}`/`{guessBX,guessBY}`. (Stated without parameters so that
`decide` applies.) -/
theorem threadRf_pairs_dom_or_bridge {t t' : Tid}
    (hp : (t = Tid.primeAX ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessAX ∧ t' = Tid.primeAX) ∨
      (t = Tid.primeAY ∧ t' = Tid.guessAY) ∨
      (t = Tid.guessAY ∧ t' = Tid.primeAY) ∨
      (t = Tid.primeBX ∧ t' = Tid.guessBX) ∨
      (t = Tid.guessBX ∧ t' = Tid.primeBX) ∨
      (t = Tid.primeBY ∧ t' = Tid.guessBY) ∨
      (t = Tid.guessBY ∧ t' = Tid.primeBY) ∨
      (t = Tid.guessAX ∧ t' = Tid.guessAY) ∨
      (t = Tid.guessAY ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessBX ∧ t' = Tid.guessBY) ∨
      (t = Tid.guessBY ∧ t' = Tid.guessBX) ∨
      (t = Tid.checkX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.primeCheckX ∧ t' = Tid.checkX) ∨
      (t = Tid.checkY ∧ t' = Tid.primeCheckY) ∨
      (t = Tid.primeCheckY ∧ t' = Tid.checkY) ∨
      (t = Tid.guessAX ∧ t' = Tid.checkX) ∨
      (t = Tid.primeAX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.guessBX ∧ t' = Tid.checkX) ∨
      (t = Tid.primeBX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.guessAY ∧ t' = Tid.checkY) ∨
      (t = Tid.primeAY ∧ t' = Tid.primeCheckY) ∨
      (t = Tid.guessBY ∧ t' = Tid.checkY) ∨
      (t = Tid.primeBY ∧ t' = Tid.primeCheckY)) :
    (t ∈ ThreadDomX ↔ t' ∈ ThreadDomX) ∨
      (t = Tid.guessAX ∧ t' = Tid.guessAY) ∨ (t = Tid.guessAY ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessBX ∧ t' = Tid.guessBY) ∨ (t = Tid.guessBY ∧ t' = Tid.guessBX) := by
  rcases hp with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|
    ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|
    ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    first | (left; decide) | (right; decide)

/-- A `ThreadRf` edge either stays within one of `ThreadDomX`/`ThreadDomY`, or
is one of the two bridge-crossing pairs `{guessAX,guessAY}`/`{guessBX,guessBY}`:
a `Tid_x`/`Tid_y` crossing can only happen at a bridge pair. -/
theorem executionGraphOf_threadRf_dom_or_bridge (I : PCPInstance) (hsol : I.HasSolution)
    {t t' : Tid} (h : executionGraphOf_ThreadRf I hsol t t') :
    (t ∈ ThreadDomX ↔ t' ∈ ThreadDomX) ∨
      (t = Tid.guessAX ∧ t' = Tid.guessAY) ∨ (t = Tid.guessAY ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessBX ∧ t' = Tid.guessBY) ∨ (t = Tid.guessBY ∧ t' = Tid.guessBX) :=
  threadRf_pairs_dom_or_bridge (executionGraphOf_threadRf_pairs I hsol h)

/-- A bridge event is on one of the four guessers `GuessAX`/`GuessAY`/
`GuessBX`/`GuessBY`: no other thread accesses a bridge location
(`traceEventsOf_<t>_not_bridge`). -/
theorem executionGraphOf_isBridge_tid (I : PCPInstance) (hsol : I.HasSolution)
    {e : Event (domainOf I)} (he : e ∈ (executionGraphOf I hsol).Events) (hb : e.IsBridge) :
    e.tid = Tid.guessAX ∨ e.tid = Tid.guessAY ∨ e.tid = Tid.guessBX ∨ e.tid = Tid.guessBY := by
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events =
      traceEvents (traceRf_valid_general I hsol).choose := rfl
  rw [hEvents] at he
  cases htid : e.tid with
  | guessAX => exact Or.inl rfl
  | guessAY => exact Or.inr (Or.inl rfl)
  | guessBX => exact Or.inr (Or.inr (Or.inl rfl))
  | guessBY => exact Or.inr (Or.inr (Or.inr rfl))
  | primeAX =>
      exact absurd hb (traceEventsOf_primeAX_not_bridge I hshapes (mem_traceEvents_of_tid he htid))
  | primeAY =>
      exact absurd hb (traceEventsOf_primeAY_not_bridge I hshapes (mem_traceEvents_of_tid he htid))
  | primeBX =>
      exact absurd hb (traceEventsOf_primeBX_not_bridge I hshapes (mem_traceEvents_of_tid he htid))
  | primeBY =>
      exact absurd hb (traceEventsOf_primeBY_not_bridge I hshapes (mem_traceEvents_of_tid he htid))
  | checkX =>
      exact absurd hb (traceEventsOf_checkX_not_bridge I hshapes (mem_traceEvents_of_tid he htid))
  | checkY =>
      exact absurd hb (traceEventsOf_checkY_not_bridge I hshapes (mem_traceEvents_of_tid he htid))
  | primeCheckX =>
      exact absurd hb
        (traceEventsOf_primeCheckX_not_bridge I hshapes (mem_traceEvents_of_tid he htid))
  | primeCheckY =>
      exact absurd hb
        (traceEventsOf_primeCheckY_not_bridge I hshapes (mem_traceEvents_of_tid he htid))

/-- The combinatorial core of `executionGraphOf_bridge_return_eq`: the
candidates for a second bridge crossing `mid → c`, resolved against `P0`'s
domain, either give `c.tid = P0` or are excluded by one of the two directions of the thread-level
`hb` separation (Fig. 4). (Stated without parameters so that `decide`
applies.) -/
theorem bridge_return_pairs_dispatch (P0 midtid ctid : Tid)
    (hP0grp : P0 = Tid.guessAX ∨ P0 = Tid.guessAY ∨ P0 = Tid.guessBX ∨ P0 = Tid.guessBY)
    (hoppo : (P0 ∈ ThreadDomX) ↔ ¬ (midtid ∈ ThreadDomX))
    (hpairs : (midtid = Tid.guessAX ∧ ctid = Tid.guessAY) ∨
      (midtid = Tid.guessAY ∧ ctid = Tid.guessAX) ∨
      (midtid = Tid.guessBX ∧ ctid = Tid.guessBY) ∨
      (midtid = Tid.guessBY ∧ ctid = Tid.guessBX)) :
    ctid = P0 ∨ (P0 ∈ AlphaGuesserTids ∧ midtid ∈ BetaGuesserTids) ∨
      (P0 ∈ BetaGuesserTids ∧ midtid ∈ AlphaGuesserTids) := by
  rcases hP0grp with rfl | rfl | rfl | rfl <;>
    rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl ⟨by decide, by decide⟩)
      | exact Or.inr (Or.inr ⟨by decide, by decide⟩)
      | exact absurd hoppo (by decide)

/-- `AlphaGuesserTids`/`BetaGuesserTids` are disjoint. -/
theorem alphaGuesserTids_betaGuesserTids_disjoint {t : Tid} (ha : t ∈ AlphaGuesserTids)
    (hb : t ∈ BetaGuesserTids) : False := by
  revert ha hb; revert t; decide

/-- An `rf`-edge whose threads form one of the four bridge-crossing pairs
joins two bridge events. -/
theorem executionGraphOf_rf_bridge_pairs (I : PCPInstance) (hsol : I.HasSolution)
    {ew er : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf ew er)
    (ht : (ew.tid = Tid.guessAX ∧ er.tid = Tid.guessAY) ∨
      (ew.tid = Tid.guessAY ∧ er.tid = Tid.guessAX) ∨
      (ew.tid = Tid.guessBX ∧ er.tid = Tid.guessBY) ∨
      (ew.tid = Tid.guessBY ∧ er.tid = Tid.guessBX)) :
    ew.IsBridge ∧ er.IsBridge := by
  rcases ht with h | h | h | h
  · exact (executionGraphOf_rf_index_eq_guessAX_guessAY hsol hrf (Or.inl h)).2
  · exact (executionGraphOf_rf_index_eq_guessAX_guessAY hsol hrf (Or.inr h)).2
  · exact (executionGraphOf_rf_index_eq_guessBX_guessBY hsol hrf (Or.inl h)).2
  · exact (executionGraphOf_rf_index_eq_guessBX_guessBY hsol hrf (Or.inr h)).2

/-- If both endpoints of a `ThreadRf` edge are among the four bridge-capable
threads, the edge is one of the two bridge-crossing pairs. -/
theorem threadRf_pairs_bridge_tids_dispatch {t t' : Tid}
    (h24 : (t = Tid.primeAX ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessAX ∧ t' = Tid.primeAX) ∨
      (t = Tid.primeAY ∧ t' = Tid.guessAY) ∨
      (t = Tid.guessAY ∧ t' = Tid.primeAY) ∨
      (t = Tid.primeBX ∧ t' = Tid.guessBX) ∨
      (t = Tid.guessBX ∧ t' = Tid.primeBX) ∨
      (t = Tid.primeBY ∧ t' = Tid.guessBY) ∨
      (t = Tid.guessBY ∧ t' = Tid.primeBY) ∨
      (t = Tid.guessAX ∧ t' = Tid.guessAY) ∨
      (t = Tid.guessAY ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessBX ∧ t' = Tid.guessBY) ∨
      (t = Tid.guessBY ∧ t' = Tid.guessBX) ∨
      (t = Tid.checkX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.primeCheckX ∧ t' = Tid.checkX) ∨
      (t = Tid.checkY ∧ t' = Tid.primeCheckY) ∨
      (t = Tid.primeCheckY ∧ t' = Tid.checkY) ∨
      (t = Tid.guessAX ∧ t' = Tid.checkX) ∨
      (t = Tid.primeAX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.guessBX ∧ t' = Tid.checkX) ∨
      (t = Tid.primeBX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.guessAY ∧ t' = Tid.checkY) ∨
      (t = Tid.primeAY ∧ t' = Tid.primeCheckY) ∨
      (t = Tid.guessBY ∧ t' = Tid.checkY) ∨
      (t = Tid.primeBY ∧ t' = Tid.primeCheckY))
    (ht : t = Tid.guessAX ∨ t = Tid.guessAY ∨ t = Tid.guessBX ∨ t = Tid.guessBY)
    (ht' : t' = Tid.guessAX ∨ t' = Tid.guessAY ∨ t' = Tid.guessBX ∨ t' = Tid.guessBY) :
    (t = Tid.guessAX ∧ t' = Tid.guessAY) ∨ (t = Tid.guessAY ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessBX ∧ t' = Tid.guessBY) ∨ (t = Tid.guessBY ∧ t' = Tid.guessBX) := by
  rcases ht with rfl | rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl | rfl <;> tauto

/-- A bridge-crossing pair puts its two threads on opposite sides of
`ThreadDomX`/`ThreadDomY`. -/
theorem bridge_pairs_dom_flip {t t' : Tid}
    (hpairs : (t = Tid.guessAX ∧ t' = Tid.guessAY) ∨ (t = Tid.guessAY ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessBX ∧ t' = Tid.guessBY) ∨ (t = Tid.guessBY ∧ t' = Tid.guessBX)) :
    (t ∈ ThreadDomX) ↔ ¬ (t' ∈ ThreadDomX) := by
  rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- A bridge-crossing pair's source thread is one of the four bridge-capable
threads. -/
theorem bridge_pairs_left_guesser {t t' : Tid}
    (hpairs : (t = Tid.guessAX ∧ t' = Tid.guessAY) ∨ (t = Tid.guessAY ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessBX ∧ t' = Tid.guessBY) ∨ (t = Tid.guessBY ∧ t' = Tid.guessBX)) :
    t = Tid.guessAX ∨ t = Tid.guessAY ∨ t = Tid.guessBX ∨ t = Tid.guessBY := by
  rcases hpairs with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> tauto

/-- "These two bridge edges would share a thread": if a path from `a`
(non-bridge) has touched thread `P0` (one of the four bridge-capable threads)
on `a`'s side of `ThreadDomX`/`ThreadDomY`, and later crosses back via a
second bridge-crossing edge `mid → c`, then `c.tid = P0`. The wrong-pair
candidate is excluded by the thread-level `hb` separation (Fig. 4)
(`executionGraphOf_alpha_not_hb_beta`/`executionGraphOf_beta_not_hb_alpha`),
using an event of thread `P0` extracted from the path by
`Path.extractThreadAlt`. -/
theorem executionGraphOf_bridge_return_eq (I : PCPInstance) (hsol : I.HasSolution)
    {a mid c : Event (domainOf I)} {P0 : Tid}
    (q' : Path (executionGraphOf I hsol) a mid) (hq' : q'.IsAlternating)
    (hP0mem : P0 ∈ q'.poThreads)
    (hP0grp : P0 = Tid.guessAX ∨ P0 = Tid.guessAY ∨ P0 = Tid.guessBX ∨ P0 = Tid.guessBY)
    (hP0dom : (P0 ∈ ThreadDomX) ↔ (a.tid ∈ ThreadDomX))
    (hmidmismatch : ¬ ((a.tid ∈ ThreadDomX) ↔ (mid.tid ∈ ThreadDomX)))
    (hpairs : (mid.tid = Tid.guessAX ∧ c.tid = Tid.guessAY) ∨
      (mid.tid = Tid.guessAY ∧ c.tid = Tid.guessAX) ∨
      (mid.tid = Tid.guessBX ∧ c.tid = Tid.guessBY) ∨
      (mid.tid = Tid.guessBY ∧ c.tid = Tid.guessBX)) :
    c.tid = P0 := by
  have hoppo : (P0 ∈ ThreadDomX) ↔ ¬ (mid.tid ∈ ThreadDomX) := by tauto
  obtain ⟨s, d, hsd, -, post, hstid, -, -, -, -, -, -, -, -, -⟩ :=
    q'.extractThreadAlt hq' P0 hP0mem
  have hdtid : d.tid = P0 := ((executionGraphOf I hsol).po_subset hsd).2.2.symm.trans hstid
  rcases bridge_return_pairs_dispatch P0 mid.tid c.tid hP0grp hoppo hpairs with
    heq | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact heq
  · exfalso
    have hdAlpha : d.tid ∈ AlphaGuesserTids := hdtid ▸ ha
    rcases post.sound with hhb | hdeq
    · exact executionGraphOf_alpha_not_hb_beta I hsol hdAlpha hb hhb
    · exact alphaGuesserTids_betaGuesserTids_disjoint (hdeq ▸ hdAlpha) hb
  · exfalso
    have hdBeta : d.tid ∈ BetaGuesserTids := hdtid ▸ ha
    rcases post.sound with hhb | hdeq
    · exact executionGraphOf_beta_not_hb_alpha I hsol hdBeta hb hhb
    · exact alphaGuesserTids_betaGuesserTids_disjoint hb (hdeq ▸ hdBeta)

/-- The bridge case of `hb_c_monotonic`, instance `guessAX`/`guessAY`
(`z_α^{x,y}`): an alternating, minimal path from a `guessAX` event `a` either
stays within `{guessAX, primeAX, checkX, primeCheckX}` (closed under every
`po`/`rf`-step except `guessAX -rf-> guessAY`) or has taken that edge. By
induction on the path. -/
theorem executionGraphOf_guessAX_guessAY_crossing_aux (I : PCPInstance) (hsol : I.HasSolution)
    {a : Event (domainOf I)} (ha : a.tid = Tid.guessAX) :
    ∀ {b : Event (domainOf I)} (p : Path (executionGraphOf I hsol) a b),
      p.AllEventsSatisfy (fun e => e.tid = Tid.guessAX ∨ e.tid = Tid.primeAX ∨
          e.tid = Tid.checkX ∨ e.tid = Tid.primeCheckX) ∨
      (∃ wc rc, (executionGraphOf I hsol).rf wc rc ∧ wc.tid = Tid.guessAX ∧
          rc.tid = Tid.guessAY ∧ (a = wc ∨ (executionGraphOf I hsol).hb a wc) ∧
          (b = rc ∨ (executionGraphOf I hsol).hb rc b)) := by
  intro b p
  induction p with
  | @single_po b h =>
      have hab : a.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      exact Or.inl ⟨Or.inl ha, Or.inl (hab.symm.trans ha)⟩
  | @single_rf b h =>
      have hthreadrf : executionGraphOf_ThreadRf I hsol Tid.guessAX b.tid := ⟨a, b, h, ha, rfl⟩
      have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadrf
      rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        first
          | exact Tid.noConfusion h1
          | exact Or.inl ⟨Or.inl ha, Or.inl h2⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inl h2)⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inr (Or.inl h2))⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inr (Or.inr h2))⟩
          | exact Or.inr ⟨a, b, h, ha, h2, Or.inl rfl, Or.inl rfl⟩
  | @tail_po mid b p' h ih =>
      have hbtideq : mid.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      rcases ih with hconf | ⟨wc, rc, hrf, hwctid, hrctid, hawc, hmidrc⟩
      · have hmidS1 := p'.allEventsSatisfy_right hconf
        have hbS1 : b.tid = Tid.guessAX ∨ b.tid = Tid.primeAX ∨ b.tid = Tid.checkX ∨
            b.tid = Tid.primeCheckX := by rwa [hbtideq] at hmidS1
        exact Or.inl ⟨hconf, hbS1⟩
      · refine Or.inr ⟨wc, rc, hrf, hwctid, hrctid, hawc, Or.inr ?_⟩
        rcases hmidrc with hmideq | hmidhb
        · rw [← hmideq]; exact Relation.TransGen.single (Or.inl h)
        · exact Relation.TransGen.tail hmidhb (Or.inl h)
  | @tail_rf mid b p' h ih =>
      rcases ih with hconf | ⟨wc, rc, hrf, hwctid, hrctid, hawc, hmidrc⟩
      · have hmidS1 := p'.allEventsSatisfy_right hconf
        have hthreadrf : executionGraphOf_ThreadRf I hsol mid.tid b.tid := ⟨mid, b, h, rfl, rfl⟩
        have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadrf
        rcases hmidS1 with hmt | hmt | hmt | hmt <;> rw [hmt] at hpairs <;>
          rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first
            | exact Tid.noConfusion h1
            | exact Or.inl ⟨hconf, Or.inl h2⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inl h2)⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inr (Or.inl h2))⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inr (Or.inr h2))⟩
            | exact Or.inr ⟨mid, b, h, hmt, h2, Or.inr p'.sound, Or.inl rfl⟩
      · refine Or.inr ⟨wc, rc, hrf, hwctid, hrctid, hawc, Or.inr ?_⟩
        rcases hmidrc with hmideq | hmidhb
        · rw [← hmideq]; exact Relation.TransGen.single (Or.inr h)
        · exact Relation.TransGen.tail hmidhb (Or.inr h)

/-- `executionGraphOf_guessAX_guessAY_crossing_aux`, for a path ending on the
`guessAY` side, where the first disjunct is impossible. -/
theorem executionGraphOf_guessAX_guessAY_crossing (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid = Tid.guessAX)
    (hb : b.tid = Tid.guessAY ∨ b.tid = Tid.primeAY ∨ b.tid = Tid.checkY ∨
        b.tid = Tid.primeCheckY)
    (p : Path (executionGraphOf I hsol) a b) :
    ∃ wc rc, (executionGraphOf I hsol).rf wc rc ∧ wc.tid = Tid.guessAX ∧
      rc.tid = Tid.guessAY ∧ (a = wc ∨ (executionGraphOf I hsol).hb a wc) ∧
      (b = rc ∨ (executionGraphOf I hsol).hb rc b) := by
  rcases executionGraphOf_guessAX_guessAY_crossing_aux I hsol ha p with hconf | hcross
  · exfalso
    have hbS1 := p.allEventsSatisfy_right hconf
    rcases hbS1 with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;> rw [h] at h' <;>
      exact Tid.noConfusion h'
  · exact hcross

theorem executionGraphOf_guessAY_guessAX_crossing_aux (I : PCPInstance) (hsol : I.HasSolution)
    {a : Event (domainOf I)} (ha : a.tid = Tid.guessAY) :
    ∀ {b : Event (domainOf I)} (p : Path (executionGraphOf I hsol) a b),
      p.AllEventsSatisfy (fun e => e.tid = Tid.guessAY ∨ e.tid = Tid.primeAY ∨
          e.tid = Tid.checkY ∨ e.tid = Tid.primeCheckY) ∨
      (∃ wc rc, (executionGraphOf I hsol).rf wc rc ∧ wc.tid = Tid.guessAY ∧
          rc.tid = Tid.guessAX ∧ (a = wc ∨ (executionGraphOf I hsol).hb a wc) ∧
          (b = rc ∨ (executionGraphOf I hsol).hb rc b)) := by
  intro b p
  induction p with
  | @single_po b h =>
      have hab : a.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      exact Or.inl ⟨Or.inl ha, Or.inl (hab.symm.trans ha)⟩
  | @single_rf b h =>
      have hthreadrf : executionGraphOf_ThreadRf I hsol Tid.guessAY b.tid := ⟨a, b, h, ha, rfl⟩
      have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadrf
      rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        first
          | exact Tid.noConfusion h1
          | exact Or.inl ⟨Or.inl ha, Or.inl h2⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inl h2)⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inr (Or.inl h2))⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inr (Or.inr h2))⟩
          | exact Or.inr ⟨a, b, h, ha, h2, Or.inl rfl, Or.inl rfl⟩
  | @tail_po mid b p' h ih =>
      have hbtideq : mid.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      rcases ih with hconf | ⟨wc, rc, hrf, hwctid, hrctid, hawc, hmidrc⟩
      · have hmidS1 := p'.allEventsSatisfy_right hconf
        have hbS1 : b.tid = Tid.guessAY ∨ b.tid = Tid.primeAY ∨ b.tid = Tid.checkY ∨
            b.tid = Tid.primeCheckY := by rwa [hbtideq] at hmidS1
        exact Or.inl ⟨hconf, hbS1⟩
      · refine Or.inr ⟨wc, rc, hrf, hwctid, hrctid, hawc, Or.inr ?_⟩
        rcases hmidrc with hmideq | hmidhb
        · rw [← hmideq]; exact Relation.TransGen.single (Or.inl h)
        · exact Relation.TransGen.tail hmidhb (Or.inl h)
  | @tail_rf mid b p' h ih =>
      rcases ih with hconf | ⟨wc, rc, hrf, hwctid, hrctid, hawc, hmidrc⟩
      · have hmidS1 := p'.allEventsSatisfy_right hconf
        have hthreadrf : executionGraphOf_ThreadRf I hsol mid.tid b.tid := ⟨mid, b, h, rfl, rfl⟩
        have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadrf
        rcases hmidS1 with hmt | hmt | hmt | hmt <;> rw [hmt] at hpairs <;>
          rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first
            | exact Tid.noConfusion h1
            | exact Or.inl ⟨hconf, Or.inl h2⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inl h2)⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inr (Or.inl h2))⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inr (Or.inr h2))⟩
            | exact Or.inr ⟨mid, b, h, hmt, h2, Or.inr p'.sound, Or.inl rfl⟩
      · refine Or.inr ⟨wc, rc, hrf, hwctid, hrctid, hawc, Or.inr ?_⟩
        rcases hmidrc with hmideq | hmidhb
        · rw [← hmideq]; exact Relation.TransGen.single (Or.inr h)
        · exact Relation.TransGen.tail hmidhb (Or.inr h)

/-- `executionGraphOf_guessAY_guessAX_crossing_aux`, for a path ending on the
`guessAX` side, where the first disjunct is impossible. -/
theorem executionGraphOf_guessAY_guessAX_crossing (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid = Tid.guessAY)
    (hb : b.tid = Tid.guessAX ∨ b.tid = Tid.primeAX ∨ b.tid = Tid.checkX ∨
        b.tid = Tid.primeCheckX)
    (p : Path (executionGraphOf I hsol) a b) :
    ∃ wc rc, (executionGraphOf I hsol).rf wc rc ∧ wc.tid = Tid.guessAY ∧
      rc.tid = Tid.guessAX ∧ (a = wc ∨ (executionGraphOf I hsol).hb a wc) ∧
      (b = rc ∨ (executionGraphOf I hsol).hb rc b) := by
  rcases executionGraphOf_guessAY_guessAX_crossing_aux I hsol ha p with hconf | hcross
  · exfalso
    have hbS1 := p.allEventsSatisfy_right hconf
    rcases hbS1 with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;> rw [h] at h' <;>
      exact Tid.noConfusion h'
  · exact hcross

theorem executionGraphOf_guessBX_guessBY_crossing_aux (I : PCPInstance) (hsol : I.HasSolution)
    {a : Event (domainOf I)} (ha : a.tid = Tid.guessBX) :
    ∀ {b : Event (domainOf I)} (p : Path (executionGraphOf I hsol) a b),
      p.AllEventsSatisfy (fun e => e.tid = Tid.guessBX ∨ e.tid = Tid.primeBX ∨
          e.tid = Tid.checkX ∨ e.tid = Tid.primeCheckX) ∨
      (∃ wc rc, (executionGraphOf I hsol).rf wc rc ∧ wc.tid = Tid.guessBX ∧
          rc.tid = Tid.guessBY ∧ (a = wc ∨ (executionGraphOf I hsol).hb a wc) ∧
          (b = rc ∨ (executionGraphOf I hsol).hb rc b)) := by
  intro b p
  induction p with
  | @single_po b h =>
      have hab : a.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      exact Or.inl ⟨Or.inl ha, Or.inl (hab.symm.trans ha)⟩
  | @single_rf b h =>
      have hthreadrf : executionGraphOf_ThreadRf I hsol Tid.guessBX b.tid := ⟨a, b, h, ha, rfl⟩
      have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadrf
      rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        first
          | exact Tid.noConfusion h1
          | exact Or.inl ⟨Or.inl ha, Or.inl h2⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inl h2)⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inr (Or.inl h2))⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inr (Or.inr h2))⟩
          | exact Or.inr ⟨a, b, h, ha, h2, Or.inl rfl, Or.inl rfl⟩
  | @tail_po mid b p' h ih =>
      have hbtideq : mid.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      rcases ih with hconf | ⟨wc, rc, hrf, hwctid, hrctid, hawc, hmidrc⟩
      · have hmidS1 := p'.allEventsSatisfy_right hconf
        have hbS1 : b.tid = Tid.guessBX ∨ b.tid = Tid.primeBX ∨ b.tid = Tid.checkX ∨
            b.tid = Tid.primeCheckX := by rwa [hbtideq] at hmidS1
        exact Or.inl ⟨hconf, hbS1⟩
      · refine Or.inr ⟨wc, rc, hrf, hwctid, hrctid, hawc, Or.inr ?_⟩
        rcases hmidrc with hmideq | hmidhb
        · rw [← hmideq]; exact Relation.TransGen.single (Or.inl h)
        · exact Relation.TransGen.tail hmidhb (Or.inl h)
  | @tail_rf mid b p' h ih =>
      rcases ih with hconf | ⟨wc, rc, hrf, hwctid, hrctid, hawc, hmidrc⟩
      · have hmidS1 := p'.allEventsSatisfy_right hconf
        have hthreadrf : executionGraphOf_ThreadRf I hsol mid.tid b.tid := ⟨mid, b, h, rfl, rfl⟩
        have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadrf
        rcases hmidS1 with hmt | hmt | hmt | hmt <;> rw [hmt] at hpairs <;>
          rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first
            | exact Tid.noConfusion h1
            | exact Or.inl ⟨hconf, Or.inl h2⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inl h2)⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inr (Or.inl h2))⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inr (Or.inr h2))⟩
            | exact Or.inr ⟨mid, b, h, hmt, h2, Or.inr p'.sound, Or.inl rfl⟩
      · refine Or.inr ⟨wc, rc, hrf, hwctid, hrctid, hawc, Or.inr ?_⟩
        rcases hmidrc with hmideq | hmidhb
        · rw [← hmideq]; exact Relation.TransGen.single (Or.inr h)
        · exact Relation.TransGen.tail hmidhb (Or.inr h)

/-- `executionGraphOf_guessBX_guessBY_crossing_aux`, for a path ending on the
`guessBY` side, where the first disjunct is impossible. -/
theorem executionGraphOf_guessBX_guessBY_crossing (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid = Tid.guessBX)
    (hb : b.tid = Tid.guessBY ∨ b.tid = Tid.primeBY ∨ b.tid = Tid.checkY ∨
        b.tid = Tid.primeCheckY)
    (p : Path (executionGraphOf I hsol) a b) :
    ∃ wc rc, (executionGraphOf I hsol).rf wc rc ∧ wc.tid = Tid.guessBX ∧
      rc.tid = Tid.guessBY ∧ (a = wc ∨ (executionGraphOf I hsol).hb a wc) ∧
      (b = rc ∨ (executionGraphOf I hsol).hb rc b) := by
  rcases executionGraphOf_guessBX_guessBY_crossing_aux I hsol ha p with hconf | hcross
  · exfalso
    have hbS1 := p.allEventsSatisfy_right hconf
    rcases hbS1 with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;> rw [h] at h' <;>
      exact Tid.noConfusion h'
  · exact hcross

theorem executionGraphOf_guessBY_guessBX_crossing_aux (I : PCPInstance) (hsol : I.HasSolution)
    {a : Event (domainOf I)} (ha : a.tid = Tid.guessBY) :
    ∀ {b : Event (domainOf I)} (p : Path (executionGraphOf I hsol) a b),
      p.AllEventsSatisfy (fun e => e.tid = Tid.guessBY ∨ e.tid = Tid.primeBY ∨
          e.tid = Tid.checkY ∨ e.tid = Tid.primeCheckY) ∨
      (∃ wc rc, (executionGraphOf I hsol).rf wc rc ∧ wc.tid = Tid.guessBY ∧
          rc.tid = Tid.guessBX ∧ (a = wc ∨ (executionGraphOf I hsol).hb a wc) ∧
          (b = rc ∨ (executionGraphOf I hsol).hb rc b)) := by
  intro b p
  induction p with
  | @single_po b h =>
      have hab : a.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      exact Or.inl ⟨Or.inl ha, Or.inl (hab.symm.trans ha)⟩
  | @single_rf b h =>
      have hthreadrf : executionGraphOf_ThreadRf I hsol Tid.guessBY b.tid := ⟨a, b, h, ha, rfl⟩
      have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadrf
      rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
          ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        first
          | exact Tid.noConfusion h1
          | exact Or.inl ⟨Or.inl ha, Or.inl h2⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inl h2)⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inr (Or.inl h2))⟩
          | exact Or.inl ⟨Or.inl ha, Or.inr (Or.inr (Or.inr h2))⟩
          | exact Or.inr ⟨a, b, h, ha, h2, Or.inl rfl, Or.inl rfl⟩
  | @tail_po mid b p' h ih =>
      have hbtideq : mid.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      rcases ih with hconf | ⟨wc, rc, hrf, hwctid, hrctid, hawc, hmidrc⟩
      · have hmidS1 := p'.allEventsSatisfy_right hconf
        have hbS1 : b.tid = Tid.guessBY ∨ b.tid = Tid.primeBY ∨ b.tid = Tid.checkY ∨
            b.tid = Tid.primeCheckY := by rwa [hbtideq] at hmidS1
        exact Or.inl ⟨hconf, hbS1⟩
      · refine Or.inr ⟨wc, rc, hrf, hwctid, hrctid, hawc, Or.inr ?_⟩
        rcases hmidrc with hmideq | hmidhb
        · rw [← hmideq]; exact Relation.TransGen.single (Or.inl h)
        · exact Relation.TransGen.tail hmidhb (Or.inl h)
  | @tail_rf mid b p' h ih =>
      rcases ih with hconf | ⟨wc, rc, hrf, hwctid, hrctid, hawc, hmidrc⟩
      · have hmidS1 := p'.allEventsSatisfy_right hconf
        have hthreadrf : executionGraphOf_ThreadRf I hsol mid.tid b.tid := ⟨mid, b, h, rfl, rfl⟩
        have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadrf
        rcases hmidS1 with hmt | hmt | hmt | hmt <;> rw [hmt] at hpairs <;>
          rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
              ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          first
            | exact Tid.noConfusion h1
            | exact Or.inl ⟨hconf, Or.inl h2⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inl h2)⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inr (Or.inl h2))⟩
            | exact Or.inl ⟨hconf, Or.inr (Or.inr (Or.inr h2))⟩
            | exact Or.inr ⟨mid, b, h, hmt, h2, Or.inr p'.sound, Or.inl rfl⟩
      · refine Or.inr ⟨wc, rc, hrf, hwctid, hrctid, hawc, Or.inr ?_⟩
        rcases hmidrc with hmideq | hmidhb
        · rw [← hmideq]; exact Relation.TransGen.single (Or.inr h)
        · exact Relation.TransGen.tail hmidhb (Or.inr h)

/-- `executionGraphOf_guessBY_guessBX_crossing_aux`, for a path ending on the
`guessBX` side, where the first disjunct is impossible. -/
theorem executionGraphOf_guessBY_guessBX_crossing (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid = Tid.guessBY)
    (hb : b.tid = Tid.guessBX ∨ b.tid = Tid.primeBX ∨ b.tid = Tid.checkX ∨
        b.tid = Tid.primeCheckX)
    (p : Path (executionGraphOf I hsol) a b) :
    ∃ wc rc, (executionGraphOf I hsol).rf wc rc ∧ wc.tid = Tid.guessBY ∧
      rc.tid = Tid.guessBX ∧ (a = wc ∨ (executionGraphOf I hsol).hb a wc) ∧
      (b = rc ∨ (executionGraphOf I hsol).hb rc b) := by
  rcases executionGraphOf_guessBY_guessBX_crossing_aux I hsol ha p with hconf | hcross
  · exfalso
    have hbS1 := p.allEventsSatisfy_right hconf
    rcases hbS1 with h | h | h | h <;> rcases hb with h' | h' | h' | h' <;> rw [h] at h' <;>
      exact Tid.noConfusion h'
  · exact hcross

/-- Lemma 3.8's induction, over the path's running endpoint `b` (with
`a` fixed and non-bridge, as in Appendix B). Two disjuncts, one per side of
`Tid_x`/`Tid_y`:
* same side as `a`: either the path is bridge-free so far, or its current
  endpoint `b` is a bridge event, the target of a crossing from thread `P0`;
* the other side: the path has crossed once (and not back), from thread `P0`
  on `a`'s side, which occurs in `poThreads`.

`p.poThreads.Nodup` is a hypothesis, contradicted by any step that would
repeat a thread. -/
theorem executionGraphOf_write_to_write_no_bridge_aux (I : PCPInstance) (hsol : I.HasSolution)
    {a : Event (domainOf I)} (hnba : ¬ a.IsBridge) :
    ∀ {b : Event (domainOf I)} (p : Path (executionGraphOf I hsol) a b),
      p.IsAlternating → p.poThreads.Nodup →
      ((a.tid ∈ ThreadDomX ↔ b.tid ∈ ThreadDomX) →
        p.IsBridgeFree ∨
        (b.IsBridge ∧ ∃ P0, (P0 = Tid.guessAX ∨ P0 = Tid.guessAY ∨ P0 = Tid.guessBX ∨
              P0 = Tid.guessBY) ∧
            (P0 ∈ ThreadDomX ↔ a.tid ∈ ThreadDomX) ∧ P0 = b.tid ∧ P0 ∈ p.poThreads)) ∧
      (¬ (a.tid ∈ ThreadDomX ↔ b.tid ∈ ThreadDomX) →
        ∃ P0, (P0 = Tid.guessAX ∨ P0 = Tid.guessAY ∨ P0 = Tid.guessBX ∨ P0 = Tid.guessBY) ∧
          (P0 ∈ ThreadDomX ↔ a.tid ∈ ThreadDomX) ∧ P0 ∈ p.poThreads) := by
  intro b p
  induction p with
  | @single_po b h =>
      intro _ _
      have hab : a.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      refine ⟨fun hm => ?_, fun hmis => ?_⟩
      · by_cases hbb : b.IsBridge
        · refine Or.inr ⟨hbb, b.tid, ?_, hm.symm, rfl, ?_⟩
          · exact executionGraphOf_isBridge_tid I hsol ((executionGraphOf I hsol).po_subset h).2.1
              hbb
          · change b.tid ∈ [b.tid]
            exact List.mem_singleton_self _
        · exact Or.inl ⟨hnba, hbb⟩
      · exact absurd (hab ▸ Iff.rfl) hmis
  | @single_rf b h =>
      intro _ _
      have hbnb : ¬ b.IsBridge := by
        intro hbb
        apply hnba
        change a.loc ∈ BridgeLoc
        rw [((executionGraphOf I hsol).rf_subset h).2.2.2.2]
        exact hbb
      have hthreadrf : executionGraphOf_ThreadRf I hsol a.tid b.tid := ⟨a, b, h, rfl, rfl⟩
      refine ⟨fun _ => Or.inl ⟨hnba, hbnb⟩, fun hmis => ?_⟩
      rcases executionGraphOf_threadRf_dom_or_bridge I hsol hthreadrf with hdm | hpairs
      · exact absurd hdm hmis
      · exact absurd (executionGraphOf_rf_bridge_pairs I hsol h hpairs).2 hbnb
  | @tail_po mid b p' h ih =>
      intro hp hnodup
      obtain ⟨hp'alt, -⟩ := hp
      have hpoeq : p'.poThreads ++ [b.tid] = (Path.tail_po p' h).poThreads := rfl
      have hnodup' : p'.poThreads.Nodup := by
        rw [← hpoeq] at hnodup; exact hnodup.of_append_left
      have hbtideq : mid.tid = b.tid := ((executionGraphOf I hsol).po_subset h).2.2
      refine ⟨fun hm => ?_, fun hmis => ?_⟩
      · have hmmid : a.tid ∈ ThreadDomX ↔ mid.tid ∈ ThreadDomX := by rw [hbtideq]; exact hm
        rcases (ih hp'alt hnodup').1 hmmid with hbf | ⟨-, P0, hP0grp, hP0dom, hP0eq, hP0mem⟩
        · by_cases hbb : b.IsBridge
          · refine Or.inr ⟨hbb, b.tid, ?_, ?_, rfl, ?_⟩
            · exact executionGraphOf_isBridge_tid I hsol
                ((executionGraphOf I hsol).po_subset h).2.1 hbb
            · rw [← hbtideq]; exact hmmid.symm
            · rw [← hpoeq]; exact List.mem_append_right _ (List.mem_singleton_self _)
          · exact Or.inl ⟨hbf, hbb⟩
        · exfalso
          have hbtidP0 : b.tid = P0 := (hP0eq.trans hbtideq).symm
          have hbmem : b.tid ∈ p'.poThreads := by rw [hbtidP0]; exact hP0mem
          rw [← hpoeq, List.nodup_append] at hnodup
          exact hnodup.2.2 b.tid hbmem b.tid (List.mem_singleton_self _) rfl
      · have hmismid : ¬ (a.tid ∈ ThreadDomX ↔ mid.tid ∈ ThreadDomX) := by
          rw [hbtideq]; exact hmis
        obtain ⟨P0, hP0grp, hP0dom, hP0mem⟩ := (ih hp'alt hnodup').2 hmismid
        exact ⟨P0, hP0grp, hP0dom, by rw [← hpoeq]; exact List.mem_append_left _ hP0mem⟩
  | @tail_rf mid b p' h ih =>
      intro hp hnodup
      obtain ⟨hp'alt, hp'lastpo⟩ := hp
      have hpoeq : p'.poThreads = (Path.tail_rf p' h).poThreads := rfl
      have hnodup' : p'.poThreads.Nodup := hpoeq ▸ hnodup
      have hne : p'.poThreads ≠ [] := p'.lastIsPo_poThreads_ne_nil hp'lastpo
      have hmidmem : mid.tid ∈ p'.poThreads :=
        (p'.lastIsPo_getLast hp'lastpo hne) ▸ List.getLast_mem hne
      have hthreadrf : executionGraphOf_ThreadRf I hsol mid.tid b.tid := ⟨mid, b, h, rfl, rfl⟩
      by_cases hbb : b.IsBridge
      · have hmidb : mid.IsBridge := by
          change mid.loc ∈ BridgeLoc
          rw [((executionGraphOf I hsol).rf_subset h).2.2.2.2]
          exact hbb
        have hmidtid : mid.tid = Tid.guessAX ∨ mid.tid = Tid.guessAY ∨ mid.tid = Tid.guessBX ∨
            mid.tid = Tid.guessBY :=
          executionGraphOf_isBridge_tid I hsol ((executionGraphOf I hsol).rf_subset h).1 hmidb
        have hbtid : b.tid = Tid.guessAX ∨ b.tid = Tid.guessAY ∨ b.tid = Tid.guessBX ∨
            b.tid = Tid.guessBY :=
          executionGraphOf_isBridge_tid I hsol ((executionGraphOf I hsol).rf_subset h).2.1 hbb
        have hpairs := threadRf_pairs_bridge_tids_dispatch
          (executionGraphOf_threadRf_pairs I hsol hthreadrf) hmidtid hbtid
        have hflip := bridge_pairs_dom_flip hpairs
        refine ⟨fun hm => ?_, fun hmis => ?_⟩
        · have hmismid : ¬ (a.tid ∈ ThreadDomX ↔ mid.tid ∈ ThreadDomX) := by
            intro hc
            exact iff_not_self ((hm.symm.trans hc).trans hflip)
          obtain ⟨P0, hP0grp, hP0dom, hP0mem⟩ := (ih hp'alt hnodup').2 hmismid
          have hceq : b.tid = P0 := executionGraphOf_bridge_return_eq I hsol p' hp'alt hP0mem
            hP0grp hP0dom hmismid hpairs
          exact Or.inr ⟨hbb, P0, hP0grp, hP0dom, hceq.symm, hpoeq ▸ hP0mem⟩
        · have hmmid : a.tid ∈ ThreadDomX ↔ mid.tid ∈ ThreadDomX :=
            ((Classical.not_iff.mp (fun hba => hmis hba.symm)).symm).trans hflip.symm
          rcases (ih hp'alt hnodup').1 hmmid with hbf | ⟨-, P0, hP0grp, hP0dom, hP0eq, hP0mem⟩
          · exact ⟨mid.tid, bridge_pairs_left_guesser hpairs, hmmid.symm, hpoeq ▸ hmidmem⟩
          · exact ⟨P0, hP0grp, hP0dom, hpoeq ▸ hP0mem⟩
      · have hmidnb : ¬ mid.IsBridge := by
          intro hc
          apply hbb
          change b.loc ∈ BridgeLoc
          rw [← ((executionGraphOf I hsol).rf_subset h).2.2.2.2]
          exact hc
        rcases executionGraphOf_threadRf_dom_or_bridge I hsol hthreadrf with hdm | hpairs
        · refine ⟨fun hm => ?_, fun hmis => ?_⟩
          · have hmmid : a.tid ∈ ThreadDomX ↔ mid.tid ∈ ThreadDomX := hm.trans hdm.symm
            rcases (ih hp'alt hnodup').1 hmmid with hbf | ⟨hmidbridge, -⟩
            · exact Or.inl ⟨hbf, hbb⟩
            · exact absurd hmidbridge hmidnb
          · have hmismid : ¬ (a.tid ∈ ThreadDomX ↔ mid.tid ∈ ThreadDomX) := fun hc =>
              hmis (hc.trans hdm)
            obtain ⟨P0, hP0grp, hP0dom, hP0mem⟩ := (ih hp'alt hnodup').2 hmismid
            exact ⟨P0, hP0grp, hP0dom, hpoeq ▸ hP0mem⟩
        · exact absurd (executionGraphOf_rf_bridge_pairs I hsol h hpairs).2 hbb

/-- `ThreadDomX`/`ThreadDomY` are disjoint. -/
theorem threadDomX_threadDomY_disjoint {t : Tid} (hx : t ∈ ThreadDomX) (hy : t ∈ ThreadDomY) :
    False := by
  revert hx hy; revert t; decide

/-- **Paper:** Lemma 3.8.

Lemma 3.8 for `G := executionGraphOf I hsol` (Appendix B's
`write_to_write_no_bridge`): a minimal path between two non-bridge events on
the same side of `Tid_x`/`Tid_y` contains no bridge event. -/
theorem executionGraphOf_write_to_write_no_bridge (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (hnba : ¬ a.IsBridge) (hnbb : ¬ b.IsBridge)
    (hdom : (a.tid ∈ ThreadDomX ∧ b.tid ∈ ThreadDomX) ∨
      (a.tid ∈ ThreadDomY ∧ b.tid ∈ ThreadDomY))
    (p : Path (executionGraphOf I hsol) a b) (hp : p.IsAlternating) (hmin : p.IsMinimal) :
    p.IsBridgeFree := by
  have hiff : a.tid ∈ ThreadDomX ↔ b.tid ∈ ThreadDomX := by
    rcases hdom with ⟨hax, hbx⟩ | ⟨hay, hby⟩
    · exact iff_of_true hax hbx
    · exact iff_of_false (fun hc => threadDomX_threadDomY_disjoint hc hay)
        (fun hc => threadDomX_threadDomY_disjoint hc hby)
  rcases (executionGraphOf_write_to_write_no_bridge_aux I hsol hnba p hp hmin).1 hiff with
    hbf | ⟨hbridge, -⟩
  · exact hbf
  · exact absurd hbridge hnbb

/-! ## Lemma 3.9 (`write_to_write_no_bridge_increasing`) -/

/-- Lemma 3.9's induction: strong induction on
`p.poThreads.length`, removing the path's last `po`-edge (found by
`Path.extractThreadAlt_pre_allEventsSatisfy` at `wj.tid`, which occurs once
by minimality). That edge ends at `wj`, and starts at `wi` or at a read whose
`rf`-source is a write, which is the shape of the recursive call. The strict
bound holds whenever `p` has an `rf`-edge (Appendix B: "if `tid` differs, `P`
contains at least one `rf`-edge, hence a read-to-write `po`-edge, which is
increasing"). -/
theorem executionGraphOf_write_to_write_no_bridge_increasing_aux (I : PCPInstance)
    (hsol : I.HasSolution) {wi : Event (domainOf I)} (_hwi : wi.op = .wt) :
    ∀ (n : ℕ) {wj : Event (domainOf I)} (p : Path (executionGraphOf I hsol) wi wj),
      p.poThreads.length = n → p.IsAlternating → p.IsMinimal → p.IsBridgeFree →
      wj.op = .wt →
      (executionGraphOf I hsol).index wi ≤ (executionGraphOf I hsol).index wj ∧
        (wi.tid ≠ wj.tid → (executionGraphOf I hsol).index wi <
          (executionGraphOf I hsol).index wj) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro wj p hlen hp hmin hnb hwj
    have hlastpo : p.lastIsPo := p.lastIsPo_of_wt hwj
    have hne : p.poThreads ≠ [] := p.lastIsPo_poThreads_ne_nil hlastpo
    have hgetlast : p.poThreads.getLast hne = wj.tid := p.lastIsPo_getLast hlastpo hne
    have hmemwj : wj.tid ∈ p.poThreads := hgetlast ▸ List.getLast_mem hne
    obtain ⟨s, d, hsd, pre, post, hstid, heq, hprealt, hpostalt, hprelast, hpostfirst,
      hrefl, hrelate, hprefirstrefl, hprefirstrelate, hpreAES⟩ :=
      p.extractThreadAlt_pre_allEventsSatisfy (fun e => ¬ e.IsBridge) hp hnb wj.tid hmemwj
    have hpostrefl : post.IsRefl := by
      by_contra hpostnotrefl
      have hpostlast : post.lastIsPo := (hrelate hpostnotrefl).mpr hlastpo
      have hpostne : post.poThreads ≠ [] := by
        cases post with
        | refl => exact absurd trivial hpostnotrefl
        | ofPath q => exact q.lastIsPo_poThreads_ne_nil hpostlast
      have hpostgetlast : post.poThreads.getLast hpostne = wj.tid := by
        cases post with
        | refl => exact absurd trivial hpostnotrefl
        | ofPath q => exact q.lastIsPo_getLast hpostlast hpostne
      have hmem2 : wj.tid ∈ post.poThreads := hpostgetlast ▸ List.getLast_mem hpostne
      have hmin2 : p.poThreads.Nodup := hmin
      rw [heq, List.nodup_append] at hmin2
      exact (hmin2.2.2 wj.tid (List.mem_append_right _ (List.mem_singleton_self _)) wj.tid hmem2)
        rfl
    have hpostnil : post.poThreads = [] := by
      cases post with
      | refl => rfl
      | ofPath r => exact absurd hpostrefl (by simp [Path0.IsRefl])
    have hpeq : p.poThreads = pre.poThreads ++ [wj.tid] := by
      rw [heq, hpostnil, List.append_nil]
    have hdwj : d = wj := by
      cases post with
      | refl => rfl
      | ofPath r => exact absurd hpostrefl (by simp [Path0.IsRefl])
    have hdop : d.op = .wt := by rw [hdwj]; exact hwj
    have hnbd : ¬ d.IsBridge := by rw [hdwj]; exact p.allEventsSatisfy_right hnb
    have hpom := executionGraphOf_po_monotone I hsol hsd hdop hnbd
    have hindexdwj : (executionGraphOf I hsol).index d = (executionGraphOf I hsol).index wj := by
      rw [hdwj]
    cases pre with
    | refl =>
      have hteq : wi.tid = wj.tid := by
        rw [← hdwj]; exact ((executionGraphOf I hsol).po_subset hsd).2.2
      exact ⟨hindexdwj ▸ hpom.1, fun hne2 => absurd hteq hne2⟩
    | ofPath q =>
      have hqAES : q.AllEventsSatisfy (fun e => ¬ e.IsBridge) := by
        rcases hpreAES with hr | hAES
        · exact absurd hr (by simp [Path0.IsRefl])
        · exact hAES
      have hmin' : Path.poThreads p |>.Nodup := hmin
      have hqmin : q.poThreads.Nodup := by
        rw [hpeq] at hmin'
        exact hmin'.of_append_left
      have hqlastrf : q.lastIsRf := hprelast
      cases q with
      | single_po h => exact absurd trivial hqlastrf
      | single_rf h2 =>
          have hiwi : (executionGraphOf I hsol).index wi =
              (executionGraphOf I hsol).index s := executionGraphOf_rf_index_eq I hsol h2
          have hsrd : s.op = .rd := ((executionGraphOf I hsol).rf_subset h2).2.2.2.1
          have hstrict : (executionGraphOf I hsol).index wi <
              (executionGraphOf I hsol).index wj := by
            rw [hiwi, ← hindexdwj]; exact hpom.2 hsrd
          exact ⟨le_of_lt hstrict, fun _ => hstrict⟩
      | tail_po q' h => exact absurd trivial hqlastrf
      | tail_rf q' h2 =>
          rename_i w2
          obtain ⟨hq'alt, hq'lastpo⟩ := hprealt
          have hq'AES : q'.AllEventsSatisfy (fun e => ¬ e.IsBridge) := hqAES.1
          have hq'min : q'.poThreads.Nodup := hqmin
          have hw2wt : w2.op = .wt := ((executionGraphOf I hsol).rf_subset h2).2.2.1
          have hlt : q'.poThreads.length < n := by
            have hlen' : q'.poThreads.length + 1 = n := by
              rw [← hlen, hpeq]
              simp [List.length_append, Path0.poThreads, Path.poThreads]
            omega
          have hrec := ih q'.poThreads.length hlt q' rfl hq'alt hq'min hq'AES hw2wt
          have hiw2 : (executionGraphOf I hsol).index w2 =
              (executionGraphOf I hsol).index s := executionGraphOf_rf_index_eq I hsol h2
          have hsrd : s.op = .rd := ((executionGraphOf I hsol).rf_subset h2).2.2.2.1
          have hstrict : (executionGraphOf I hsol).index wi <
              (executionGraphOf I hsol).index wj := by
            have hb1 : (executionGraphOf I hsol).index wi ≤
                (executionGraphOf I hsol).index w2 := hrec.1
            have hb2 : (executionGraphOf I hsol).index s <
                (executionGraphOf I hsol).index wj := by
              rw [← hindexdwj]; exact hpom.2 hsrd
            omega
          exact ⟨le_of_lt hstrict, fun _ => hstrict⟩

/-- **Paper:** Lemma 3.9.

Lemma 3.9 for `G := executionGraphOf I hsol`
(`write_to_write_no_bridge_increasing`). -/
theorem executionGraphOf_write_to_write_no_bridge_increasing (I : PCPInstance)
    (hsol : I.HasSolution) {wi wj : Event (domainOf I)} (hwi : wi.op = .wt) (hwj : wj.op = .wt)
    (p : Path (executionGraphOf I hsol) wi wj) (hp : p.IsAlternating) (hmin : p.IsMinimal)
    (hnb : p.IsBridgeFree) :
    (executionGraphOf I hsol).index wi ≤ (executionGraphOf I hsol).index wj ∧
      (wi.tid ≠ wj.tid → (executionGraphOf I hsol).index wi <
        (executionGraphOf I hsol).index wj) :=
  executionGraphOf_write_to_write_no_bridge_increasing_aux I hsol hwi p.poThreads.length p rfl
    hp hmin hnb hwj

/-! ## Lemma 3.10 (`rr_bridge_monotonic`) -/

/-- No `po`/`rf`-edge leads from `XCheckerTids` to a guesser thread. (Stated
without parameters so that `decide` applies.) -/
theorem xCheckerTids_not_guesser : ∀ t ∈ XCheckerTids, t ≠ Tid.guessAX ∧ t ≠ Tid.guessAY ∧
    t ≠ Tid.guessBX ∧ t ≠ Tid.guessBY := by decide

/-- No `po`/`rf`-edge leads from `YCheckerTids` to a guesser thread. -/
theorem yCheckerTids_not_guesser : ∀ t ∈ YCheckerTids, t ≠ Tid.guessAX ∧ t ≠ Tid.guessAY ∧
    t ≠ Tid.guessBX ∧ t ≠ Tid.guessBY := by decide

/-- Neither guesser group contains a checker. -/
theorem hSguesserAlpha : ∀ t ∈ AlphaGuesserTids, t ≠ Tid.checkX ∧ t ≠ Tid.primeCheckX ∧
    t ≠ Tid.checkY ∧ t ≠ Tid.primeCheckY := by decide

theorem hSguesserBeta : ∀ t ∈ BetaGuesserTids, t ≠ Tid.checkX ∧ t ≠ Tid.primeCheckX ∧
    t ≠ Tid.checkY ∧ t ≠ Tid.primeCheckY := by decide

/-- Membership facts seeding `executionGraphOf_hb_checker_reads_aux` from each
case of `executionGraphOf_hb_checker_reads`'s hypothesis. -/
theorem checkX_mem_xCheckerTids : Tid.checkX ∈ XCheckerTids := by decide

theorem primeCheckX_mem_xCheckerTids : Tid.primeCheckX ∈ XCheckerTids := by decide

theorem checkY_mem_yCheckerTids : Tid.checkY ∈ YCheckerTids := by decide

theorem primeCheckY_mem_yCheckerTids : Tid.primeCheckY ∈ YCheckerTids := by decide

/-- `rr_bridge_monotonic`'s argument, for a checker group `S` (`XCheckerTids`
or `YCheckerTids`), closed under `hb` and containing no guesser.

As in the paper's three bullets: `p`'s first `po`-edge `r_i ⟶po w_ℓ` is
increasing (`executionGraphOf_po_monotone`); the write-to-write segment up to
`w_{ℓ'}` is non-decreasing
(`executionGraphOf_write_to_write_no_bridge_increasing`); the closing `rf`-edge
into `r_{ℓ'}` preserves the index (`executionGraphOf_rf_index_eq`); and a
closing `r_{ℓ'} ⟶po r_j` edge is not one of Lemma 3.5's
exceptions, since `r_{ℓ'}` reads from a writer in `S`, not a guesser. -/
theorem executionGraphOf_hb_checker_reads_aux (I : PCPInstance) (hsol : I.HasSolution)
    (S : Finset Tid)
    (hSclosed : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ S → (executionGraphOf I hsol).hb x y →
      y.tid ∈ S)
    (hSguesser : ∀ t ∈ S, t ≠ Tid.guessAX ∧ t ≠ Tid.guessAY ∧ t ≠ Tid.guessBX ∧
      t ≠ Tid.guessBY)
    {rdi rdj : Event (domainOf I)} (hrdi : rdi.op = .rd) (hrdj : rdj.op = .rd)
    (hloc : rdi.loc = rdj.loc) (hseed : rdi.tid ∈ S)
    (hhb : (executionGraphOf I hsol).hb rdi rdj) :
    (executionGraphOf I hsol).index rdi < (executionGraphOf I hsol).index rdj := by
  set G := executionGraphOf I hsol with hG
  have hSclosed2 : ∀ ⦃x y : Event (domainOf I)⦄, (x.tid ∈ S ∧ x ∈ G.Events) → G.hb x y →
      (y.tid ∈ S ∧ y ∈ G.Events) :=
    fun x y hx hxy => ⟨hSclosed hx.1 hxy, G.hb_mem_events hxy⟩
  have hmono : ∀ e : Event (domainOf I), (e.tid ∈ S ∧ e ∈ G.Events) → ¬ e.IsBridge := by
    rintro e ⟨heS, heMem⟩ hbridge
    obtain hg := executionGraphOf_isBridge_tid I hsol heMem hbridge
    obtain ⟨h1, h2, h3, h4⟩ := hSguesser e.tid heS
    rcases hg with hg | hg | hg | hg
    exacts [h1 hg, h2 hg, h3 hg, h4 hg]
  obtain ⟨p, hmin⟩ := executionGraphOf_hb_minimal I hsol hhb
  have hp : p.IsAlternating := p.isAlternating_of_isMinimal hmin
  have hfirstpo := p.firstIsPo_of_rd hrdi
  have hne := p.firstIsPo_poThreads_ne_nil hfirstpo
  have hhead := p.firstIsPo_head hfirstpo hne
  have hmemrdi : rdi.tid ∈ p.poThreads := hhead ▸ List.head_mem hne
  obtain ⟨s, d, hsd, pre, post, hstid, heq, hprealt, hpostalt, hprelast, hpostfirst,
      hrefl, hrelate, hprefirstrefl, hprefirstrelate⟩ := p.extractThreadAlt hp rdi.tid hmemrdi
  have hprerefl : pre.IsRefl := by
    cases pre with
    | refl => trivial
    | ofPath q0 =>
        have hnr : ¬ (Path0.ofPath q0 : Path0 G rdi s).IsRefl := by simp [Path0.IsRefl]
        have hprefirst : q0.firstIsPo := (hprefirstrelate hnr).mpr hfirstpo
        have hqne : q0.poThreads ≠ [] := q0.firstIsPo_poThreads_ne_nil hprefirst
        have hqhead : q0.poThreads.head hqne = rdi.tid := q0.firstIsPo_head hprefirst hqne
        have hmem2 : rdi.tid ∈ q0.poThreads := hqhead ▸ List.head_mem hqne
        have hmin2 : p.poThreads.Nodup := hmin
        rw [heq] at hmin2
        have hdisj := (List.nodup_append.mp (List.nodup_append.mp hmin2).1).2.2
        exact hdisj rdi.tid hmem2 rdi.tid (List.mem_singleton_self rdi.tid) rfl
  have hprenil : pre.poThreads = [] := by
    cases pre with
    | refl => rfl
    | ofPath q0 => exact absurd hprerefl (by simp [Path0.IsRefl])
  have hsrdi : s = rdi := by
    cases pre with
    | refl => rfl
    | ofPath q0 => exact absurd hprerefl (by simp [Path0.IsRefl])
  have hrdid : G.po rdi d := by rw [← hsrdi]; exact hsd
  have hrdiMem : rdi ∈ G.Events := (G.po_subset hrdid).1
  have hdMem : d ∈ G.Events := (G.po_subset hrdid).2.1
  have hdS : d.tid ∈ S := hSclosed hseed (Relation.TransGen.single (Or.inl hrdid))
  by_cases hpostrefl : post.IsRefl
  · -- `r_i ⟶po r_j` directly: the shared location rules out every
    -- Lemma 3.5 exception, all of which need different locations
    have hdrdj : d = rdj := by
      cases post with
      | refl => rfl
      | ofPath q0 => exact absurd hpostrefl (by simp [Path0.IsRefl])
    have hpoedge : G.po rdi rdj := by rw [← hdrdj]; exact hrdid
    have hrdjS : rdj.tid ∈ S := by rw [← hdrdj]; exact hdS
    have hrdjMem : rdj ∈ G.Events := by rw [← hdrdj]; exact hdMem
    have hnbi : ¬ rdi.IsBridge := hmono rdi ⟨hseed, hrdiMem⟩
    have hnbj : ¬ rdj.IsBridge := hmono rdj ⟨hrdjS, hrdjMem⟩
    rcases lt_trichotomy (G.index rdj) (G.index rdi) with hlt | heqidx | hgt
    · exfalso
      obtain ⟨_, hlocdis, _⟩ := executionGraphOf_po_reads_decreasing I hsol hpoedge hrdi hrdj
        hnbi hnbj hlt
      rw [hloc] at hlocdis
      rcases hlocdis with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) |
          (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
        exact Loc.noConfusion (h1.symm.trans h2)
    · exfalso
      have htideq : rdi.tid = rdj.tid := (G.po_subset hpoedge).2.2
      have hopeq : rdi.op = rdj.op := hrdi.trans hrdj.symm
      have h1 : G.nthEvent rdi.tid rdi.loc rdi.op (G.index rdi) = some rdi :=
        G.index_nthEvent hrdiMem
      have h2 : G.nthEvent rdi.tid rdi.loc rdi.op (G.index rdi) = some rdj := by
        have h2' := G.index_nthEvent hrdjMem
        rwa [← htideq, ← hloc, ← hopeq, heqidx] at h2'
      have hrdieq : rdi = rdj := by
        have hcomb : some rdi = some rdj := h1.symm.trans h2
        injection hcomb
      rw [← hrdieq] at hhb
      exact executionGraphOf_hb_irrefl I hsol rdi hhb
    · exact hgt
  · -- the write-to-write chain `w_ℓ hb^? w_{ℓ'}`, then possibly a closing
    -- `r_{ℓ'} ⟶po r_j`
    obtain ⟨q, hqeq⟩ : ∃ q : Path G d rdj, post = .ofPath q := by
      cases post with
      | refl => exact absurd trivial hpostrefl
      | ofPath q0 => exact ⟨q0, rfl⟩
    subst hqeq
    have hqfirstrf : q.firstIsRf := hpostfirst
    obtain ⟨e2, hde2⟩ := q.firstIsRf_rf hqfirstrf
    have hwtd : d.op = .wt := (G.rf_subset hde2).2.2.1
    have hstep1 : G.index rdi < G.index d :=
      (executionGraphOf_po_monotone I hsol hrdid hwtd (hmono d ⟨hdS, hdMem⟩)).2 hrdi
    have hqalt : q.IsAlternating := hpostalt
    have hqmin : q.poThreads.Nodup := by
      have hmin2 : p.poThreads.Nodup := hmin
      rw [heq, hprenil, List.nil_append] at hmin2
      exact hmin2.of_cons
    cases q with
    | single_po h => exact absurd trivial hqfirstrf
    | single_rf h =>
        have hstep2 : G.index d = G.index rdj := executionGraphOf_rf_index_eq I hsol h
        omega
    | tail_po q' h =>
        rename_i s2
        -- q' : Path G d s2 (the write-to-write chain), h : G.po s2 rdj (the
        -- closing read-to-read `po`-edge, `po?` in the paper's decomposition)
        obtain ⟨hq'alt, hq'lastrf⟩ := hqalt
        have hq'min : q'.poThreads.Nodup := (List.nodup_append.mp hqmin).1
        have hs2S : s2.tid ∈ S := hSclosed hdS q'.sound
        have hs2Mem : s2 ∈ G.Events := G.hb_mem_events q'.sound
        have hnbs2 : ¬ s2.IsBridge := hmono s2 ⟨hs2S, hs2Mem⟩
        have hrdjS : rdj.tid ∈ S := hSclosed hs2S (Relation.TransGen.single (Or.inl h))
        have hrdjMem : rdj ∈ G.Events := G.hb_mem_events hhb
        have hnbrdj : ¬ rdj.IsBridge := hmono rdj ⟨hrdjS, hrdjMem⟩
        cases q' with
        | single_po h' => exact absurd trivial hq'lastrf
        | single_rf h' =>
            -- `d ⟶rf s2` directly: `d` is the closing edge's known writer
            have hrds2 : s2.op = .rd := (G.rf_subset h').2.2.2.1
            have hdeq : G.index d = G.index s2 := executionGraphOf_rf_index_eq I hsol h'
            have hs2rdj : G.index s2 ≤ G.index rdj := by
              by_contra hcon
              push Not at hcon
              obtain ⟨_, _, w1, hw1rf, hg⟩ := executionGraphOf_po_reads_decreasing I hsol h
                hrds2 hrdj hnbs2 hnbrdj hcon
              have hw1eq : w1 = d := G.rf_unique hw1rf h'
              rw [hw1eq] at hg
              obtain ⟨g1, g2, g3, g4⟩ := hSguesser d.tid hdS
              rcases hg with hg | hg | hg | hg
              exacts [g1 hg, g2 hg, g3 hg, g4 hg]
            omega
        | tail_po q'' h' => exact absurd trivial hq'lastrf
        | tail_rf q'' h' =>
            rename_i w0
            -- q'' : Path G d w0 (both writes), h' : G.rf w0 s2
            obtain ⟨hq''alt, hq''lastpo⟩ := hq'alt
            have hq''min : q''.poThreads.Nodup := hq'min
            have hw0wt : w0.op = .wt := (G.rf_subset h').2.2.1
            have hw0S : w0.tid ∈ S := hSclosed hdS q''.sound
            have hq''nb : q''.IsBridgeFree :=
              q''.allEventsSatisfy_mono hmono
                (q''.allEventsSatisfy_of_hb_closed hSclosed2 ⟨hdS, hdMem⟩)
            have hww := executionGraphOf_write_to_write_no_bridge_increasing I hsol hwtd hw0wt
              q'' hq''alt hq''min hq''nb
            have hdw0 : G.index d ≤ G.index w0 := hww.1
            have hrds2 : s2.op = .rd := (G.rf_subset h').2.2.2.1
            have hw0eq : G.index w0 = G.index s2 := executionGraphOf_rf_index_eq I hsol h'
            have hs2rdj : G.index s2 ≤ G.index rdj := by
              by_contra hcon
              push Not at hcon
              obtain ⟨_, _, w1, hw1rf, hg⟩ := executionGraphOf_po_reads_decreasing I hsol h
                hrds2 hrdj hnbs2 hnbrdj hcon
              have hw1eq : w1 = w0 := G.rf_unique hw1rf h'
              rw [hw1eq] at hg
              obtain ⟨g1, g2, g3, g4⟩ := hSguesser w0.tid hw0S
              rcases hg with hg | hg | hg | hg
              exacts [g1 hg, g2 hg, g3 hg, g4 hg]
            omega
    | tail_rf q' h =>
        rename_i w2
        -- q' : Path G d w2 (the write-to-write chain), h : G.rf w2 rdj (the
        -- closing `rf`-edge directly onto `rdj`, no trailing `po?`)
        obtain ⟨hq'alt, hq'lastpo⟩ := hqalt
        have hq'min : q'.poThreads.Nodup := hqmin
        have hw2wt : w2.op = .wt := (G.rf_subset h).2.2.1
        have hq'nb : q'.IsBridgeFree :=
          q'.allEventsSatisfy_mono hmono
            (q'.allEventsSatisfy_of_hb_closed hSclosed2 ⟨hdS, hdMem⟩)
        have hww := executionGraphOf_write_to_write_no_bridge_increasing I hsol hwtd hw2wt q'
          hq'alt hq'min hq'nb
        have hdw2 : G.index d ≤ G.index w2 := hww.1
        have hweq : G.index w2 = G.index rdj := executionGraphOf_rf_index_eq I hsol h
        omega

/-- **Paper:** Lemma 3.10.

Lemma 3.10 for `G := executionGraphOf I hsol`
(`rr_bridge_monotonic`). The proof picks the checker group of `rdi.tid` and
applies `executionGraphOf_hb_checker_reads_aux`. -/
theorem executionGraphOf_hb_checker_reads (I : PCPInstance) (hsol : I.HasSolution)
    {rdi rdj : Event (domainOf I)} (hrdi : rdi.op = .rd) (hrdj : rdj.op = .rd)
    (hloc : rdi.loc = rdj.loc)
    (htidi : rdi.tid = Tid.checkX ∨ rdi.tid = Tid.primeCheckX ∨
      rdi.tid = Tid.checkY ∨ rdi.tid = Tid.primeCheckY)
    (_htidj : rdj.tid = Tid.checkX ∨ rdj.tid = Tid.primeCheckX ∨
      rdj.tid = Tid.checkY ∨ rdj.tid = Tid.primeCheckY)
    (hhb : (executionGraphOf I hsol).hb rdi rdj) :
    (executionGraphOf I hsol).index rdi < (executionGraphOf I hsol).index rdj := by
  have hclosedX : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ XCheckerTids →
      (executionGraphOf I hsol).hb x y → y.tid ∈ XCheckerTids := by
    intro x y hx hxy
    by_contra hc
    exact executionGraphOf_xChecker_not_hb_outside I hsol hx hc hxy
  have hclosedY : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ YCheckerTids →
      (executionGraphOf I hsol).hb x y → y.tid ∈ YCheckerTids := by
    intro x y hx hxy
    by_contra hc
    exact executionGraphOf_yChecker_not_hb_outside I hsol hx hc hxy
  rcases htidi with h | h | h | h
  · exact executionGraphOf_hb_checker_reads_aux I hsol XCheckerTids hclosedX
      xCheckerTids_not_guesser hrdi hrdj hloc (h ▸ checkX_mem_xCheckerTids) hhb
  · exact executionGraphOf_hb_checker_reads_aux I hsol XCheckerTids hclosedX
      xCheckerTids_not_guesser hrdi hrdj hloc (h ▸ primeCheckX_mem_xCheckerTids) hhb
  · exact executionGraphOf_hb_checker_reads_aux I hsol YCheckerTids hclosedY
      yCheckerTids_not_guesser hrdi hrdj hloc (h ▸ checkY_mem_yCheckerTids) hhb
  · exact executionGraphOf_hb_checker_reads_aux I hsol YCheckerTids hclosedY
      yCheckerTids_not_guesser hrdi hrdj hloc (h ▸ primeCheckY_mem_yCheckerTids) hhb

/-! ## Lemma 3.11 (`ww_dec_2`) -/

/-- Membership facts used by `executionGraphOf_hb_primeAX_guessAX_gap` and its
three analogues. -/
theorem primed_gap_tids_mem_threadDom :
    (Tid.primeAX ∈ ThreadDomX ∧ Tid.guessAX ∈ ThreadDomX) ∧
      (Tid.primeAY ∈ ThreadDomY ∧ Tid.guessAY ∈ ThreadDomY) ∧
      (Tid.primeBX ∈ ThreadDomX ∧ Tid.guessBX ∈ ThreadDomX) ∧
      (Tid.primeBY ∈ ThreadDomY ∧ Tid.guessBY ∈ ThreadDomY) := by decide

/-- `ww_dec_2`, the `g_α^{x'}`/`g_α^x` (`primeAX`/`guessAX`) instance: `w_i(g_α^{x'},
x'_α) ⟶hb w_j(g_α^x, x_α)` has `i < j - 1`, stated as `i + 1 < j`.

As in Appendix B, the path is confined in two steps:

* *forward*, `{g_α^{x'}, g_α^x, c^x, c^{x'}}` is closed under single `po`/`rf`-steps
  between non-bridge events (`Path.allEventsSatisfy_of_step_closed`): by
  the thread-level `rf` topology (Fig. 4) (`executionGraphOf_threadRf_pairs`), except for
  `g_α^x ⟶rf g_α^y`, which is a bridge edge, excluded by Lemma 3.8;
* *backward*, `{c^x, c^{x'}}` is closed under `hb`
  (`executionGraphOf_xChecker_not_hb_outside`) and the path's target is
  outside it, so no event of the path is in it
  (`Path.allEventsSatisfy_not_of_hb_closed_end`).

So every event of the path is on `g_α^{x'}` or `g_α^x`, every `rf`-edge is at
`z_α^{x,x'}`/`z_α^{x',x}`, the last edge is a read-to-write `po`-edge on `g_α^x` from a
read of `z_α^{x,x'}`, and counting loop iterations gives `i + 1 < j`. -/
theorem executionGraphOf_hb_primeAX_guessAX_gap (I : PCPInstance) (hsol : I.HasSolution)
    {wi wj : Event (domainOf I)}
    (hwitid : wi.tid = Tid.primeAX) (hwiloc : wi.loc = Loc.xA') (hwiop : wi.op = .wt)
    (hwjtid : wj.tid = Tid.guessAX) (hwjloc : wj.loc = Loc.xA) (hwjop : wj.op = .wt)
    (hhb : (executionGraphOf I hsol).hb wi wj) :
    (executionGraphOf I hsol).index wi + 1 < (executionGraphOf I hsol).index wj := by
  set G := executionGraphOf I hsol with hG
  have hnbi : ¬ wi.IsBridge := by unfold Event.IsBridge; rw [hwiloc]; exact xAp_nb
  have hnbj : ¬ wj.IsBridge := by unfold Event.IsBridge; rw [hwjloc]; exact xA_nb
  obtain ⟨p, hmin⟩ := executionGraphOf_hb_minimal I hsol hhb
  have hp : p.IsAlternating := p.isAlternating_of_isMinimal hmin
  have hdom : wi.tid ∈ ThreadDomX ∧ wj.tid ∈ ThreadDomX := by
    rw [hwitid, hwjtid]; exact primed_gap_tids_mem_threadDom.1
  have hnb : p.IsBridgeFree :=
    executionGraphOf_write_to_write_no_bridge I hsol hnbi hnbj (Or.inl hdom) p hp hmin
  -- Forward confinement: `{g_α^{x'},g_α^x,c^x,c^{x'}}` is closed under a single
  -- `po`/`rf`-step given bridge-freeness (the thread-level `rf` topology (Fig. 4)' branch list,
  -- excluding `g_α^x ⟶rf g_α^y` since that pair is always a bridge edge).
  have hstep : ∀ x y : Event (domainOf I),
      (x.tid = Tid.primeAX ∨ x.tid = Tid.guessAX ∨ x.tid = Tid.checkX ∨
        x.tid = Tid.primeCheckX) →
      ¬ x.IsBridge → ¬ y.IsBridge → (G.po x y ∨ G.rf x y) →
      (y.tid = Tid.primeAX ∨ y.tid = Tid.guessAX ∨ y.tid = Tid.checkX ∨
        y.tid = Tid.primeCheckX) := by
    rintro x y hx hnbx hnby (hpo | hrf)
    · rw [(G.po_subset hpo).2.2] at hx
      exact hx
    · have hthreadRf : executionGraphOf_ThreadRf I hsol x.tid y.tid := ⟨x, y, hrf, rfl, rfl⟩
      have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadRf
      rcases hx with hx | hx | hx | hx <;> rw [hx] at hpairs <;>
        rcases hpairs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
          h | h | h | h | h | h <;>
        first
          | (cases h.1 <;> done)
          | (rw [h.2]; tauto)
          | (exact absurd (executionGraphOf_rf_index_eq_guessAX_guessAY hsol hrf
              (Or.inl ⟨hx, h.2⟩)).2.1 hnbx)
  have hconfFwd := p.allEventsSatisfy_of_step_closed hstep (Or.inl hwitid) hnb
  -- Backward exclusion: `{c^x,c^{x'}}` is closed under all of `hb`
  -- (the thread-level `rf` topology (Fig. 4)' own fact, not the thread-level `hb` separation (Fig. 4)), but `p` ends outside
  -- it, so (`allEventsSatisfy_not_of_hb_closed_end`) it never enters.
  have hclosedX : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ XCheckerTids → G.hb x y →
      y.tid ∈ XCheckerTids := by
    intro x y hx hxy
    by_contra hc
    exact executionGraphOf_xChecker_not_hb_outside I hsol hx hc hxy
  have hwjnotX : wj.tid ∉ XCheckerTids := by
    rw [hwjtid]
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Tid.noConfusion h
    · exact Tid.noConfusion (Finset.mem_singleton.mp h)
  have hconfBwd := p.allEventsSatisfy_not_of_hb_closed_end hclosedX hwjnotX
  -- Intersecting the two confines every event to exactly `{g_α^{x'},g_α^x}`.
  have hmono : ∀ e : Event (domainOf I),
      ((e.tid = Tid.primeAX ∨ e.tid = Tid.guessAX ∨ e.tid = Tid.checkX ∨
          e.tid = Tid.primeCheckX) ∧ e.tid ∉ XCheckerTids) →
      (e.tid = Tid.primeAX ∨ e.tid = Tid.guessAX) := by
    rintro e ⟨h1, h2⟩
    rcases h1 with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (by rw [h1]; exact checkX_mem_xCheckerTids) h2
    · exact absurd (by rw [h1]; exact primeCheckX_mem_xCheckerTids) h2
  have hconf : p.AllEventsSatisfy (fun e => e.tid = Tid.primeAX ∨ e.tid = Tid.guessAX) :=
    p.allEventsSatisfy_mono hmono (p.allEventsSatisfy_and hconfFwd hconfBwd)
  -- `p`'s final edge is forced to be `po`, since `wj` is a write.
  have hlastpo := p.lastIsPo_of_wt hwjop
  cases p with
  | single_po h =>
      exfalso
      have heq := (G.po_subset h).2.2
      rw [hwitid, hwjtid] at heq
      exact Tid.noConfusion heq
  | single_rf h => exact hlastpo.elim
  | tail_rf p' h => exact hlastpo.elim
  | tail_po p' h =>
      rename_i s2
      obtain ⟨hp'alt, hp'lastrf⟩ := hp
      have hs2tid : s2.tid = Tid.guessAX := by
        have heq := (G.po_subset h).2.2
        rw [hwjtid] at heq
        exact heq
      have hnbs2 : ¬ s2.IsBridge := p'.allEventsSatisfy_right hnb.1
      obtain ⟨w', hs2rf⟩ := p'.lastIsRf_rf hp'lastrf
      have hs2rd : s2.op = .rd := (G.rf_subset hs2rf).2.2.2.1
      have hw'wt : w'.op = .wt := (G.rf_subset hs2rf).2.2.1
      have hgap := executionGraphOf_guessAX_read_write_gap I hsol hs2tid hwjtid h hs2rd hnbs2
        hwjop hnbj
      rw [← hG] at hgap
      cases p' with
      | single_po h' => exact absurd trivial hp'lastrf
      | tail_po p'' h' => exact absurd trivial hp'lastrf
      | single_rf h' =>
          have hw'wi : w' = wi := G.rf_unique hs2rf h'
          have hindexeq : (executionGraphOf I hsol).index w' =
              (executionGraphOf I hsol).index s2 := executionGraphOf_rf_index_eq I hsol hs2rf
          rw [hw'wi, ← hG] at hindexeq
          omega
      | tail_rf p'' h' =>
          rename_i w2
          have hw2w' : w2 = w' := G.rf_unique h' hs2rf
          obtain ⟨hp''alt, hp''lastpo⟩ := hp'alt
          have hp''min : p''.poThreads.Nodup := (List.nodup_append.mp hmin).1
          have hp''nb : p''.IsBridgeFree := hnb.1.1
          have hw2wt : w2.op = .wt := by rw [hw2w']; exact hw'wt
          have hww := executionGraphOf_write_to_write_no_bridge_increasing I hsol hwiop hw2wt p''
            hp''alt hp''min hp''nb
          have hwiw2 : (executionGraphOf I hsol).index wi ≤
              (executionGraphOf I hsol).index w2 := hww.1
          have hw2s2 : (executionGraphOf I hsol).index w2 =
              (executionGraphOf I hsol).index s2 := executionGraphOf_rf_index_eq I hsol h'
          rw [← hG] at hwiw2 hw2s2
          omega

/-- `ww_dec_2`, the `g_α^{y'}`/`g_α^y` (`primeAY`/`guessAY`) instance, as
`executionGraphOf_hb_primeAX_guessAX_gap` (with the bridge edge
`g_α^y ⟶rf g_α^x` excluded). -/
theorem executionGraphOf_hb_primeAY_guessAY_gap (I : PCPInstance) (hsol : I.HasSolution)
    {wi wj : Event (domainOf I)}
    (hwitid : wi.tid = Tid.primeAY) (hwiloc : wi.loc = Loc.yA') (hwiop : wi.op = .wt)
    (hwjtid : wj.tid = Tid.guessAY) (hwjloc : wj.loc = Loc.yA) (hwjop : wj.op = .wt)
    (hhb : (executionGraphOf I hsol).hb wi wj) :
    (executionGraphOf I hsol).index wi + 1 < (executionGraphOf I hsol).index wj := by
  set G := executionGraphOf I hsol with hG
  have hnbi : ¬ wi.IsBridge := by unfold Event.IsBridge; rw [hwiloc]; exact yAp_nb
  have hnbj : ¬ wj.IsBridge := by unfold Event.IsBridge; rw [hwjloc]; exact yA_nb
  obtain ⟨p, hmin⟩ := executionGraphOf_hb_minimal I hsol hhb
  have hp : p.IsAlternating := p.isAlternating_of_isMinimal hmin
  have hdom : wi.tid ∈ ThreadDomY ∧ wj.tid ∈ ThreadDomY := by
    rw [hwitid, hwjtid]; exact primed_gap_tids_mem_threadDom.2.1
  have hnb : p.IsBridgeFree :=
    executionGraphOf_write_to_write_no_bridge I hsol hnbi hnbj (Or.inr hdom) p hp hmin
  have hstep : ∀ x y : Event (domainOf I),
      (x.tid = Tid.primeAY ∨ x.tid = Tid.guessAY ∨ x.tid = Tid.checkY ∨
        x.tid = Tid.primeCheckY) →
      ¬ x.IsBridge → ¬ y.IsBridge → (G.po x y ∨ G.rf x y) →
      (y.tid = Tid.primeAY ∨ y.tid = Tid.guessAY ∨ y.tid = Tid.checkY ∨
        y.tid = Tid.primeCheckY) := by
    rintro x y hx hnbx hnby (hpo | hrf)
    · rw [(G.po_subset hpo).2.2] at hx
      exact hx
    · have hthreadRf : executionGraphOf_ThreadRf I hsol x.tid y.tid := ⟨x, y, hrf, rfl, rfl⟩
      have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadRf
      rcases hx with hx | hx | hx | hx <;> rw [hx] at hpairs <;>
        rcases hpairs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
          h | h | h | h | h | h <;>
        first
          | (cases h.1 <;> done)
          | (rw [h.2]; tauto)
          | (exact absurd (executionGraphOf_rf_index_eq_guessAX_guessAY hsol hrf
              (Or.inr ⟨hx, h.2⟩)).2.1 hnbx)
  have hconfFwd := p.allEventsSatisfy_of_step_closed hstep (Or.inl hwitid) hnb
  have hclosedY : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ YCheckerTids → G.hb x y →
      y.tid ∈ YCheckerTids := by
    intro x y hx hxy
    by_contra hc
    exact executionGraphOf_yChecker_not_hb_outside I hsol hx hc hxy
  have hwjnotY : wj.tid ∉ YCheckerTids := by
    rw [hwjtid]
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Tid.noConfusion h
    · exact Tid.noConfusion (Finset.mem_singleton.mp h)
  have hconfBwd := p.allEventsSatisfy_not_of_hb_closed_end hclosedY hwjnotY
  have hmono : ∀ e : Event (domainOf I),
      ((e.tid = Tid.primeAY ∨ e.tid = Tid.guessAY ∨ e.tid = Tid.checkY ∨
          e.tid = Tid.primeCheckY) ∧ e.tid ∉ YCheckerTids) →
      (e.tid = Tid.primeAY ∨ e.tid = Tid.guessAY) := by
    rintro e ⟨h1, h2⟩
    rcases h1 with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (by rw [h1]; exact checkY_mem_yCheckerTids) h2
    · exact absurd (by rw [h1]; exact primeCheckY_mem_yCheckerTids) h2
  have hconf : p.AllEventsSatisfy (fun e => e.tid = Tid.primeAY ∨ e.tid = Tid.guessAY) :=
    p.allEventsSatisfy_mono hmono (p.allEventsSatisfy_and hconfFwd hconfBwd)
  have hlastpo := p.lastIsPo_of_wt hwjop
  cases p with
  | single_po h =>
      exfalso
      have heq := (G.po_subset h).2.2
      rw [hwitid, hwjtid] at heq
      exact Tid.noConfusion heq
  | single_rf h => exact hlastpo.elim
  | tail_rf p' h => exact hlastpo.elim
  | tail_po p' h =>
      rename_i s2
      obtain ⟨hp'alt, hp'lastrf⟩ := hp
      have hs2tid : s2.tid = Tid.guessAY := by
        have heq := (G.po_subset h).2.2
        rw [hwjtid] at heq
        exact heq
      have hnbs2 : ¬ s2.IsBridge := p'.allEventsSatisfy_right hnb.1
      obtain ⟨w', hs2rf⟩ := p'.lastIsRf_rf hp'lastrf
      have hs2rd : s2.op = .rd := (G.rf_subset hs2rf).2.2.2.1
      have hw'wt : w'.op = .wt := (G.rf_subset hs2rf).2.2.1
      have hgap := executionGraphOf_guessAY_read_write_gap I hsol hs2tid hwjtid h hs2rd hwjop
      rw [← hG] at hgap
      cases p' with
      | single_po h' => exact absurd trivial hp'lastrf
      | tail_po p'' h' => exact absurd trivial hp'lastrf
      | single_rf h' =>
          have hw'wi : w' = wi := G.rf_unique hs2rf h'
          have hindexeq : (executionGraphOf I hsol).index w' =
              (executionGraphOf I hsol).index s2 := executionGraphOf_rf_index_eq I hsol hs2rf
          rw [hw'wi, ← hG] at hindexeq
          omega
      | tail_rf p'' h' =>
          rename_i w2
          have hw2w' : w2 = w' := G.rf_unique h' hs2rf
          obtain ⟨hp''alt, hp''lastpo⟩ := hp'alt
          have hp''min : p''.poThreads.Nodup := (List.nodup_append.mp hmin).1
          have hp''nb : p''.IsBridgeFree := hnb.1.1
          have hw2wt : w2.op = .wt := by rw [hw2w']; exact hw'wt
          have hww := executionGraphOf_write_to_write_no_bridge_increasing I hsol hwiop hw2wt p''
            hp''alt hp''min hp''nb
          have hwiw2 : (executionGraphOf I hsol).index wi ≤
              (executionGraphOf I hsol).index w2 := hww.1
          have hw2s2 : (executionGraphOf I hsol).index w2 =
              (executionGraphOf I hsol).index s2 := executionGraphOf_rf_index_eq I hsol h'
          rw [← hG] at hwiw2 hw2s2
          omega

/-- `ww_dec_2`, the `g_β^{x'}`/`g_β^x` (`primeBX`/`guessBX`) instance, as
`executionGraphOf_hb_primeAX_guessAX_gap` (with the bridge edge
`guessBX ⟶rf guessBY` excluded). -/
theorem executionGraphOf_hb_primeBX_guessBX_gap (I : PCPInstance) (hsol : I.HasSolution)
    {wi wj : Event (domainOf I)}
    (hwitid : wi.tid = Tid.primeBX) (hwiloc : wi.loc = Loc.xB') (hwiop : wi.op = .wt)
    (hwjtid : wj.tid = Tid.guessBX) (hwjloc : wj.loc = Loc.xB) (hwjop : wj.op = .wt)
    (hhb : (executionGraphOf I hsol).hb wi wj) :
    (executionGraphOf I hsol).index wi + 1 < (executionGraphOf I hsol).index wj := by
  set G := executionGraphOf I hsol with hG
  have hnbi : ¬ wi.IsBridge := by unfold Event.IsBridge; rw [hwiloc]; exact xBp_nb
  have hnbj : ¬ wj.IsBridge := by unfold Event.IsBridge; rw [hwjloc]; exact xB_nb
  obtain ⟨p, hmin⟩ := executionGraphOf_hb_minimal I hsol hhb
  have hp : p.IsAlternating := p.isAlternating_of_isMinimal hmin
  have hdom : wi.tid ∈ ThreadDomX ∧ wj.tid ∈ ThreadDomX := by
    rw [hwitid, hwjtid]; exact primed_gap_tids_mem_threadDom.2.2.1
  have hnb : p.IsBridgeFree :=
    executionGraphOf_write_to_write_no_bridge I hsol hnbi hnbj (Or.inl hdom) p hp hmin
  have hstep : ∀ x y : Event (domainOf I),
      (x.tid = Tid.primeBX ∨ x.tid = Tid.guessBX ∨ x.tid = Tid.checkX ∨
        x.tid = Tid.primeCheckX) →
      ¬ x.IsBridge → ¬ y.IsBridge → (G.po x y ∨ G.rf x y) →
      (y.tid = Tid.primeBX ∨ y.tid = Tid.guessBX ∨ y.tid = Tid.checkX ∨
        y.tid = Tid.primeCheckX) := by
    rintro x y hx hnbx hnby (hpo | hrf)
    · rw [(G.po_subset hpo).2.2] at hx
      exact hx
    · have hthreadRf : executionGraphOf_ThreadRf I hsol x.tid y.tid := ⟨x, y, hrf, rfl, rfl⟩
      have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadRf
      rcases hx with hx | hx | hx | hx <;> rw [hx] at hpairs <;>
        rcases hpairs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
          h | h | h | h | h | h <;>
        first
          | (cases h.1 <;> done)
          | (rw [h.2]; tauto)
          | (exact absurd (executionGraphOf_rf_index_eq_guessBX_guessBY hsol hrf
              (Or.inl ⟨hx, h.2⟩)).2.1 hnbx)
  have hconfFwd := p.allEventsSatisfy_of_step_closed hstep (Or.inl hwitid) hnb
  have hclosedX : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ XCheckerTids → G.hb x y →
      y.tid ∈ XCheckerTids := by
    intro x y hx hxy
    by_contra hc
    exact executionGraphOf_xChecker_not_hb_outside I hsol hx hc hxy
  have hwjnotX : wj.tid ∉ XCheckerTids := by
    rw [hwjtid]
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Tid.noConfusion h
    · exact Tid.noConfusion (Finset.mem_singleton.mp h)
  have hconfBwd := p.allEventsSatisfy_not_of_hb_closed_end hclosedX hwjnotX
  have hmono : ∀ e : Event (domainOf I),
      ((e.tid = Tid.primeBX ∨ e.tid = Tid.guessBX ∨ e.tid = Tid.checkX ∨
          e.tid = Tid.primeCheckX) ∧ e.tid ∉ XCheckerTids) →
      (e.tid = Tid.primeBX ∨ e.tid = Tid.guessBX) := by
    rintro e ⟨h1, h2⟩
    rcases h1 with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (by rw [h1]; exact checkX_mem_xCheckerTids) h2
    · exact absurd (by rw [h1]; exact primeCheckX_mem_xCheckerTids) h2
  have hconf : p.AllEventsSatisfy (fun e => e.tid = Tid.primeBX ∨ e.tid = Tid.guessBX) :=
    p.allEventsSatisfy_mono hmono (p.allEventsSatisfy_and hconfFwd hconfBwd)
  have hlastpo := p.lastIsPo_of_wt hwjop
  cases p with
  | single_po h =>
      exfalso
      have heq := (G.po_subset h).2.2
      rw [hwitid, hwjtid] at heq
      exact Tid.noConfusion heq
  | single_rf h => exact hlastpo.elim
  | tail_rf p' h => exact hlastpo.elim
  | tail_po p' h =>
      rename_i s2
      obtain ⟨hp'alt, hp'lastrf⟩ := hp
      have hs2tid : s2.tid = Tid.guessBX := by
        have heq := (G.po_subset h).2.2
        rw [hwjtid] at heq
        exact heq
      have hnbs2 : ¬ s2.IsBridge := p'.allEventsSatisfy_right hnb.1
      obtain ⟨w', hs2rf⟩ := p'.lastIsRf_rf hp'lastrf
      have hs2rd : s2.op = .rd := (G.rf_subset hs2rf).2.2.2.1
      have hw'wt : w'.op = .wt := (G.rf_subset hs2rf).2.2.1
      have hgap := executionGraphOf_guessBX_read_write_gap I hsol hs2tid hwjtid h hs2rd hnbs2
        hwjop hnbj
      rw [← hG] at hgap
      cases p' with
      | single_po h' => exact absurd trivial hp'lastrf
      | tail_po p'' h' => exact absurd trivial hp'lastrf
      | single_rf h' =>
          have hw'wi : w' = wi := G.rf_unique hs2rf h'
          have hindexeq : (executionGraphOf I hsol).index w' =
              (executionGraphOf I hsol).index s2 := executionGraphOf_rf_index_eq I hsol hs2rf
          rw [hw'wi, ← hG] at hindexeq
          omega
      | tail_rf p'' h' =>
          rename_i w2
          have hw2w' : w2 = w' := G.rf_unique h' hs2rf
          obtain ⟨hp''alt, hp''lastpo⟩ := hp'alt
          have hp''min : p''.poThreads.Nodup := (List.nodup_append.mp hmin).1
          have hp''nb : p''.IsBridgeFree := hnb.1.1
          have hw2wt : w2.op = .wt := by rw [hw2w']; exact hw'wt
          have hww := executionGraphOf_write_to_write_no_bridge_increasing I hsol hwiop hw2wt p''
            hp''alt hp''min hp''nb
          have hwiw2 : (executionGraphOf I hsol).index wi ≤
              (executionGraphOf I hsol).index w2 := hww.1
          have hw2s2 : (executionGraphOf I hsol).index w2 =
              (executionGraphOf I hsol).index s2 := executionGraphOf_rf_index_eq I hsol h'
          rw [← hG] at hwiw2 hw2s2
          omega

/-- `ww_dec_2`, the `g_β^{y'}`/`g_β^y` (`primeBY`/`guessBY`) instance, as
`executionGraphOf_hb_primeAY_guessAY_gap` (with the bridge edge
`guessBY ⟶rf guessBX` excluded). -/
theorem executionGraphOf_hb_primeBY_guessBY_gap (I : PCPInstance) (hsol : I.HasSolution)
    {wi wj : Event (domainOf I)}
    (hwitid : wi.tid = Tid.primeBY) (hwiloc : wi.loc = Loc.yB') (hwiop : wi.op = .wt)
    (hwjtid : wj.tid = Tid.guessBY) (hwjloc : wj.loc = Loc.yB) (hwjop : wj.op = .wt)
    (hhb : (executionGraphOf I hsol).hb wi wj) :
    (executionGraphOf I hsol).index wi + 1 < (executionGraphOf I hsol).index wj := by
  set G := executionGraphOf I hsol with hG
  have hnbi : ¬ wi.IsBridge := by unfold Event.IsBridge; rw [hwiloc]; exact yBp_nb
  have hnbj : ¬ wj.IsBridge := by unfold Event.IsBridge; rw [hwjloc]; exact yB_nb
  obtain ⟨p, hmin⟩ := executionGraphOf_hb_minimal I hsol hhb
  have hp : p.IsAlternating := p.isAlternating_of_isMinimal hmin
  have hdom : wi.tid ∈ ThreadDomY ∧ wj.tid ∈ ThreadDomY := by
    rw [hwitid, hwjtid]; exact primed_gap_tids_mem_threadDom.2.2.2
  have hnb : p.IsBridgeFree :=
    executionGraphOf_write_to_write_no_bridge I hsol hnbi hnbj (Or.inr hdom) p hp hmin
  have hstep : ∀ x y : Event (domainOf I),
      (x.tid = Tid.primeBY ∨ x.tid = Tid.guessBY ∨ x.tid = Tid.checkY ∨
        x.tid = Tid.primeCheckY) →
      ¬ x.IsBridge → ¬ y.IsBridge → (G.po x y ∨ G.rf x y) →
      (y.tid = Tid.primeBY ∨ y.tid = Tid.guessBY ∨ y.tid = Tid.checkY ∨
        y.tid = Tid.primeCheckY) := by
    rintro x y hx hnbx hnby (hpo | hrf)
    · rw [(G.po_subset hpo).2.2] at hx
      exact hx
    · have hthreadRf : executionGraphOf_ThreadRf I hsol x.tid y.tid := ⟨x, y, hrf, rfl, rfl⟩
      have hpairs := executionGraphOf_threadRf_pairs I hsol hthreadRf
      rcases hx with hx | hx | hx | hx <;> rw [hx] at hpairs <;>
        rcases hpairs with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
          h | h | h | h | h | h <;>
        first
          | (cases h.1 <;> done)
          | (rw [h.2]; tauto)
          | (exact absurd (executionGraphOf_rf_index_eq_guessBX_guessBY hsol hrf
              (Or.inr ⟨hx, h.2⟩)).2.1 hnbx)
  have hconfFwd := p.allEventsSatisfy_of_step_closed hstep (Or.inl hwitid) hnb
  have hclosedY : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ YCheckerTids → G.hb x y →
      y.tid ∈ YCheckerTids := by
    intro x y hx hxy
    by_contra hc
    exact executionGraphOf_yChecker_not_hb_outside I hsol hx hc hxy
  have hwjnotY : wj.tid ∉ YCheckerTids := by
    rw [hwjtid]
    intro hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Tid.noConfusion h
    · exact Tid.noConfusion (Finset.mem_singleton.mp h)
  have hconfBwd := p.allEventsSatisfy_not_of_hb_closed_end hclosedY hwjnotY
  have hmono : ∀ e : Event (domainOf I),
      ((e.tid = Tid.primeBY ∨ e.tid = Tid.guessBY ∨ e.tid = Tid.checkY ∨
          e.tid = Tid.primeCheckY) ∧ e.tid ∉ YCheckerTids) →
      (e.tid = Tid.primeBY ∨ e.tid = Tid.guessBY) := by
    rintro e ⟨h1, h2⟩
    rcases h1 with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd (by rw [h1]; exact checkY_mem_yCheckerTids) h2
    · exact absurd (by rw [h1]; exact primeCheckY_mem_yCheckerTids) h2
  have hconf : p.AllEventsSatisfy (fun e => e.tid = Tid.primeBY ∨ e.tid = Tid.guessBY) :=
    p.allEventsSatisfy_mono hmono (p.allEventsSatisfy_and hconfFwd hconfBwd)
  have hlastpo := p.lastIsPo_of_wt hwjop
  cases p with
  | single_po h =>
      exfalso
      have heq := (G.po_subset h).2.2
      rw [hwitid, hwjtid] at heq
      exact Tid.noConfusion heq
  | single_rf h => exact hlastpo.elim
  | tail_rf p' h => exact hlastpo.elim
  | tail_po p' h =>
      rename_i s2
      obtain ⟨hp'alt, hp'lastrf⟩ := hp
      have hs2tid : s2.tid = Tid.guessBY := by
        have heq := (G.po_subset h).2.2
        rw [hwjtid] at heq
        exact heq
      have hnbs2 : ¬ s2.IsBridge := p'.allEventsSatisfy_right hnb.1
      obtain ⟨w', hs2rf⟩ := p'.lastIsRf_rf hp'lastrf
      have hs2rd : s2.op = .rd := (G.rf_subset hs2rf).2.2.2.1
      have hw'wt : w'.op = .wt := (G.rf_subset hs2rf).2.2.1
      have hgap := executionGraphOf_guessBY_read_write_gap I hsol hs2tid hwjtid h hs2rd hwjop
      rw [← hG] at hgap
      cases p' with
      | single_po h' => exact absurd trivial hp'lastrf
      | tail_po p'' h' => exact absurd trivial hp'lastrf
      | single_rf h' =>
          have hw'wi : w' = wi := G.rf_unique hs2rf h'
          have hindexeq : (executionGraphOf I hsol).index w' =
              (executionGraphOf I hsol).index s2 := executionGraphOf_rf_index_eq I hsol hs2rf
          rw [hw'wi, ← hG] at hindexeq
          omega
      | tail_rf p'' h' =>
          rename_i w2
          have hw2w' : w2 = w' := G.rf_unique h' hs2rf
          obtain ⟨hp''alt, hp''lastpo⟩ := hp'alt
          have hp''min : p''.poThreads.Nodup := (List.nodup_append.mp hmin).1
          have hp''nb : p''.IsBridgeFree := hnb.1.1
          have hw2wt : w2.op = .wt := by rw [hw2w']; exact hw'wt
          have hww := executionGraphOf_write_to_write_no_bridge_increasing I hsol hwiop hw2wt p''
            hp''alt hp''min hp''nb
          have hwiw2 : (executionGraphOf I hsol).index wi ≤
              (executionGraphOf I hsol).index w2 := hww.1
          have hw2s2 : (executionGraphOf I hsol).index w2 =
              (executionGraphOf I hsol).index s2 := executionGraphOf_rf_index_eq I hsol h'
          rw [← hG] at hwiw2 hw2s2
          omega

/-- The four pairs of Lemma 3.11, `((tid(w_i), loc(w_i)), (tid(w_j), loc(w_j)))`,
in the paper's order: `⟨w_i(g_α^{x'}, x'_α), w_j(g_α^x, x_α)⟩`,
`⟨w_i(g_α^{y'}, y'_α), w_j(g_α^y, y_α)⟩`, `⟨w_i(g_β^{x'}, x'_β), w_j(g_β^x, x_β)⟩`,
`⟨w_i(g_β^{y'}, y'_β), w_j(g_β^y, y_β)⟩`. -/
def primedGapPairs : List ((Tid × Loc) × (Tid × Loc)) :=
  [ ((.primeAX, .xA'), (.guessAX, .xA)), ((.primeAY, .yA'), (.guessAY, .yA)),
    ((.primeBX, .xB'), (.guessBX, .xB)), ((.primeBY, .yB'), (.guessBY, .yB)) ]

/-- **Paper:** Lemma 3.11.

**Lemma 3.11**, for `G := executionGraphOf I hsol`. Every
`hb`-edge `w_i ⟶hb w_j` where `⟨w_i, w_j⟩` is one of the pairs of
`primedGapPairs` is such that `i < j - 1` (stated as `i + 1 < j`). -/
theorem executionGraphOf_hb_primed_gap (I : PCPInstance) (hsol : I.HasSolution) :
    ∀ c ∈ primedGapPairs, ∀ {wi wj : Event (domainOf I)},
      wi.tid = c.1.1 → wi.loc = c.1.2 → wi.op = .wt →
      wj.tid = c.2.1 → wj.loc = c.2.2 → wj.op = .wt →
      (executionGraphOf I hsol).hb wi wj →
      (executionGraphOf I hsol).index wi + 1 < (executionGraphOf I hsol).index wj := by
  intro c hc
  simp only [primedGapPairs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact executionGraphOf_hb_primeAX_guessAX_gap I hsol
  · exact executionGraphOf_hb_primeAY_guessAY_gap I hsol
  · exact executionGraphOf_hb_primeBX_guessBX_gap I hsol
  · exact executionGraphOf_hb_primeBY_guessBY_gap I hsol

/-! ## Lemma 3.12 (`hb_conflicting_writes_strictly_monotonic`) -/

/-- A `po`-edge between two events of the same location and operation
increases the index (`rawIndex_lt_of_tracePo_sameLocOp` at the level of `G`). -/
theorem executionGraphOf_index_lt_of_po_sameLocOp (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (hpo : (executionGraphOf I hsol).po e1 e2)
    (hloc : e1.loc = e2.loc) (hop : e1.op = e2.op) :
    (executionGraphOf I hsol).index e1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [hpo'.1] at he1
  have hraw := rawIndex_lt_of_tracePo_sameLocOp he1 he2 hpo' hloc hop
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- Every writing event's thread is among its location's `writerTids`
(`traceMo_writers_confined` at the level of `G`). -/
theorem executionGraphOf_writers_confined (I : PCPInstance) (hsol : I.HasSolution)
    {e : Event (domainOf I)} (he : e ∈ (executionGraphOf I hsol).Events) (hw : e.IsWriting) :
    e.tid ∈ writerTids e.loc := by
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events =
      traceEvents (traceRf_valid_general I hsol).choose := rfl
  rw [hEvents] at he
  exact traceMo_writers_confined I hshapes e he hw

/-- `hb` (or equality) between two reads of the same thread and location is
non-decreasing. -/
theorem executionGraphOf_hb_reads_sameThread_le (I : PCPInstance) (hsol : I.HasSolution)
    {rc rj : Event (domainOf I)} (hrc : rc.op = .rd) (hrj : rj.op = .rd)
    (htid : rc.tid = rj.tid) (hloc : rc.loc = rj.loc)
    (hhb : rc = rj ∨ (executionGraphOf I hsol).hb rc rj) :
    (executionGraphOf I hsol).index rc ≤ (executionGraphOf I hsol).index rj := by
  rcases hhb with heq | hhb
  · exact le_of_eq (congrArg (executionGraphOf I hsol).index heq)
  · set G := executionGraphOf I hsol with hG
    have hrcMem : rc ∈ G.Events := G.hb_mem_events_left hhb
    have hrjMem : rj ∈ G.Events := G.hb_mem_events hhb
    have hSTO := G.po_total rc.tid
    have hmemS : rc ∈ G.Events.filter (fun e => e.tid = rc.tid) :=
      Finset.mem_filter.mpr ⟨hrcMem, rfl⟩
    have hmemC : rj ∈ G.Events.filter (fun e => e.tid = rc.tid) :=
      Finset.mem_filter.mpr ⟨hrjMem, htid.symm⟩
    by_cases h1 : G.po rc rj
    · exact le_of_lt
        (executionGraphOf_index_lt_of_po_sameLocOp I hsol h1 hloc (hrc.trans hrj.symm))
    · by_cases h2 : G.po rj rc
      · exfalso
        have hbrjrc : G.hb rj rc := Relation.TransGen.single (Or.inl h2)
        exact executionGraphOf_hb_irrefl I hsol rc (Relation.TransGen.trans hhb hbrjrc)
      · exfalso
        have heq : rc = rj := congrArg Subtype.val
          (hSTO.toTrichotomous.trichotomous ⟨rc, hmemS⟩ ⟨rj, hmemC⟩ h1 h2)
        rw [heq] at hhb
        exact executionGraphOf_hb_irrefl I hsol rj hhb

/-- **Paper:** Lemma 3.12.

`hb_conflicting_writes_strictly_monotonic`: `hb` is increasing between
same-location writes. Two cases, as in Appendix B:

* *Same thread*: by `po_total`, `G.po wi wj ∨ wi = wj ∨ G.po wj wi`. The last
  two give `G.hb wi wi`, contradicting Lemma 3.6 (the paper's proof only
  rules out `i > j`; the case `wi = wj` is also excluded by Lemma 3.6).
  `G.po wi wj` gives `i < j` by `executionGraphOf_index_lt_of_po_sameLocOp`.
* *Different threads*: both threads are writers of `wi.loc`, so
  (`writerTids_two_diff_dom`) `wi.loc` is one of the eight two-writer,
  non-bridge locations, with both threads in the same
  `ThreadDomX`/`ThreadDomY` (the paper's "case analysis on `u`"). Then
  Lemma 3.8 and Lemma 3.9 give `i < j`. -/
theorem executionGraphOf_hb_writes_increasing (I : PCPInstance) (hsol : I.HasSolution)
    {wi wj : Event (domainOf I)} (hwi : wi.op = .wt) (hwj : wj.op = .wt)
    (hloc : wi.loc = wj.loc) (hhb : (executionGraphOf I hsol).hb wi wj) :
    (executionGraphOf I hsol).index wi < (executionGraphOf I hsol).index wj := by
  set G := executionGraphOf I hsol with hG
  have hwiMem : wi ∈ G.Events := G.hb_mem_events_left hhb
  have hwjMem : wj ∈ G.Events := G.hb_mem_events hhb
  by_cases htid : wi.tid = wj.tid
  · have hSTO := G.po_total wi.tid
    have hmemS : wi ∈ G.Events.filter (fun e => e.tid = wi.tid) :=
      Finset.mem_filter.mpr ⟨hwiMem, rfl⟩
    have hmemC : wj ∈ G.Events.filter (fun e => e.tid = wi.tid) :=
      Finset.mem_filter.mpr ⟨hwjMem, htid.symm⟩
    by_cases h1 : G.po wi wj
    · exact executionGraphOf_index_lt_of_po_sameLocOp I hsol h1 hloc (hwi.trans hwj.symm)
    · by_cases h2 : G.po wj wi
      · exfalso
        have hbwjwi : G.hb wj wi := Relation.TransGen.single (Or.inl h2)
        exact executionGraphOf_hb_irrefl I hsol wi (Relation.TransGen.trans hhb hbwjwi)
      · exfalso
        have heq : wi = wj := congrArg Subtype.val
          (hSTO.toTrichotomous.trichotomous ⟨wi, hmemS⟩ ⟨wj, hmemC⟩ h1 h2)
        rw [heq] at hhb
        exact executionGraphOf_hb_irrefl I hsol wj hhb
  · have hwitids : wi.tid ∈ writerTids wi.loc := executionGraphOf_writers_confined I hsol hwiMem hwi
    have hwjtids : wj.tid ∈ writerTids wi.loc := by
      have := executionGraphOf_writers_confined I hsol hwjMem hwj
      rwa [← hloc] at this
    obtain ⟨hdom, hlocnb⟩ := writerTids_two_diff_dom wi.loc wi.tid wj.tid hwitids hwjtids htid
    have hnbi : ¬ wi.IsBridge := hlocnb
    have hnbj : ¬ wj.IsBridge := by
      change wj.loc ∉ BridgeLoc
      rw [← hloc]
      exact hlocnb
    obtain ⟨p, hmin⟩ := executionGraphOf_hb_minimal I hsol hhb
    have hp : p.IsAlternating := p.isAlternating_of_isMinimal hmin
    have hnb : p.IsBridgeFree :=
      executionGraphOf_write_to_write_no_bridge I hsol hnbi hnbj hdom p hp hmin
    exact (executionGraphOf_write_to_write_no_bridge_increasing I hsol hwi hwj p hp hmin hnb).2
      htid

/-- `checkX_po_monotone_write_read` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_checkX_po_monotone_write_read (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (ht1 : e1.tid = Tid.checkX) (ht2 : e2.tid = Tid.checkX)
    (hpo : (executionGraphOf I hsol).po e1 e2)
    (hwt1 : e1.op = .wt) (hrd2 : e2.op = .rd) (hloc : e1.loc = e2.loc) :
    (executionGraphOf I hsol).index e1 ≤ (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [ht1] at he1
  rw [ht2] at he2
  obtain ⟨v0, kws, htrace⟩ := hshapes.checkX
  have hraw := checkX_po_monotone_write_read I trace v0 kws htrace he1 he2 hpo' hwt1 hrd2 hloc
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `checkY_po_monotone_write_read` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_checkY_po_monotone_write_read (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (ht1 : e1.tid = Tid.checkY) (ht2 : e2.tid = Tid.checkY)
    (hpo : (executionGraphOf I hsol).po e1 e2)
    (hwt1 : e1.op = .wt) (hrd2 : e2.op = .rd) (hloc : e1.loc = e2.loc) :
    (executionGraphOf I hsol).index e1 ≤ (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [ht1] at he1
  rw [ht2] at he2
  obtain ⟨v0, kws, htrace⟩ := hshapes.checkY
  have hraw := checkY_po_monotone_write_read I trace v0 kws htrace he1 he2 hpo' hwt1 hrd2 hloc
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `primeCheckX_po_monotone_write_read` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_primeCheckX_po_monotone_write_read (I : PCPInstance)
    (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (ht1 : e1.tid = Tid.primeCheckX) (ht2 : e2.tid = Tid.primeCheckX)
    (hpo : (executionGraphOf I hsol).po e1 e2)
    (hwt1 : e1.op = .wt) (hrd2 : e2.op = .rd) (hloc : e1.loc = e2.loc) :
    (executionGraphOf I hsol).index e1 ≤ (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [ht1] at he1
  rw [ht2] at he2
  obtain ⟨cnts, htrace⟩ := hshapes.primeCheckX
  have hraw := primeCheckX_po_monotone_write_read I trace cnts htrace he1 he2 hpo' hwt1 hrd2 hloc
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `primeCheckY_po_monotone_write_read` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_primeCheckY_po_monotone_write_read (I : PCPInstance)
    (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (ht1 : e1.tid = Tid.primeCheckY) (ht2 : e2.tid = Tid.primeCheckY)
    (hpo : (executionGraphOf I hsol).po e1 e2)
    (hwt1 : e1.op = .wt) (hrd2 : e2.op = .rd) (hloc : e1.loc = e2.loc) :
    (executionGraphOf I hsol).index e1 ≤ (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [ht1] at he1
  rw [ht2] at he2
  obtain ⟨cnts, htrace⟩ := hshapes.primeCheckY
  have hraw := primeCheckY_po_monotone_write_read I trace cnts htrace he1 he2 hpo' hwt1 hrd2 hloc
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- Every reading event's `(tid, loc)` is one of the threads' read locations
(`traceRf_reads_confined` at the level of `G`). -/
theorem executionGraphOf_reads_confined (I : PCPInstance) (hsol : I.HasSolution)
    {e : Event (domainOf I)} (he : e ∈ (executionGraphOf I hsol).Events) (hr : e.IsReading) :
    (e.tid = Tid.guessAX ∧ (e.loc = Loc.zAxx' ∨ e.loc = Loc.ellAyx)) ∨
    (e.tid = Tid.primeAX ∧ e.loc = Loc.zAx'x) ∨
    (e.tid = Tid.guessAY ∧ (e.loc = Loc.zAxy ∨ e.loc = Loc.zAyy')) ∨
    (e.tid = Tid.primeAY ∧ e.loc = Loc.zAy'y) ∨
    (e.tid = Tid.guessBX ∧ (e.loc = Loc.zBxx' ∨ e.loc = Loc.ellByx)) ∨
    (e.tid = Tid.primeBX ∧ e.loc = Loc.zBx'x) ∨
    (e.tid = Tid.guessBY ∧ (e.loc = Loc.zBxy ∨ e.loc = Loc.zByy')) ∨
    (e.tid = Tid.primeBY ∧ e.loc = Loc.zBy'y) ∨
    (e.tid = Tid.checkX ∧
      (e.loc = Loc.xA ∨ e.loc = Loc.xB ∨ e.loc = Loc.xA' ∨ e.loc = Loc.xB')) ∨
    (e.tid = Tid.primeCheckX ∧
      (e.loc = Loc.xA' ∨ e.loc = Loc.xB' ∨ e.loc = Loc.xA ∨ e.loc = Loc.xB)) ∨
    (e.tid = Tid.checkY ∧
      (e.loc = Loc.yA ∨ e.loc = Loc.yB ∨ e.loc = Loc.yA' ∨ e.loc = Loc.yB')) ∨
    (e.tid = Tid.primeCheckY ∧
      (e.loc = Loc.yA' ∨ e.loc = Loc.yB' ∨ e.loc = Loc.yA ∨ e.loc = Loc.yB)) := by
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events =
      traceEvents (traceRf_valid_general I hsol).choose := rfl
  rw [hEvents] at he
  exact traceRf_reads_confined I hshapes he hr

/-- The paper's "the pair `⟨tid(wi),u⟩` can only be one of the following": a
location written and read by the same thread forces that thread to be one of
`CheckX`/`CheckY`/`PrimeCheckX`/`PrimeCheckY`, at one of its matching
locations. (Stated without parameters so that `decide` applies.) -/
theorem writeRead_selfthread_confined :
    ∀ (t : Tid) (u : Loc), t ∈ writerTids u →
      ((t = Tid.guessAX ∧ (u = Loc.zAxx' ∨ u = Loc.ellAyx)) ∨
       (t = Tid.primeAX ∧ u = Loc.zAx'x) ∨
       (t = Tid.guessAY ∧ (u = Loc.zAxy ∨ u = Loc.zAyy')) ∨
       (t = Tid.primeAY ∧ u = Loc.zAy'y) ∨
       (t = Tid.guessBX ∧ (u = Loc.zBxx' ∨ u = Loc.ellByx)) ∨
       (t = Tid.primeBX ∧ u = Loc.zBx'x) ∨
       (t = Tid.guessBY ∧ (u = Loc.zBxy ∨ u = Loc.zByy')) ∨
       (t = Tid.primeBY ∧ u = Loc.zBy'y) ∨
       (t = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (t = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (t = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (t = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      (t = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB)) ∨
      (t = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB)) ∨
      (t = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB')) ∨
      (t = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB')) := by
  intro t u hw hr
  fin_cases u <;> fin_cases t <;> simp_all [writerTids]

/-- The paper's "since only bridge locations are accessed by threads in both
`Tid_x` and `Tid_y`, and neither `wi` nor `rj` is a bridge event,
either both belong to threads in `Tid_x`, or both belong to threads in
`Tid_y`": a non-bridge location's writer and readers share a
`ThreadDom`. -/
theorem writeRead_diffThread_sameDom :
    ∀ (t1 t2 : Tid) (u : Loc), t1 ∈ writerTids u → u ∉ BridgeLoc →
      ((t2 = Tid.guessAX ∧ (u = Loc.zAxx' ∨ u = Loc.ellAyx)) ∨
       (t2 = Tid.primeAX ∧ u = Loc.zAx'x) ∨
       (t2 = Tid.guessAY ∧ (u = Loc.zAxy ∨ u = Loc.zAyy')) ∨
       (t2 = Tid.primeAY ∧ u = Loc.zAy'y) ∨
       (t2 = Tid.guessBX ∧ (u = Loc.zBxx' ∨ u = Loc.ellByx)) ∨
       (t2 = Tid.primeBX ∧ u = Loc.zBx'x) ∨
       (t2 = Tid.guessBY ∧ (u = Loc.zBxy ∨ u = Loc.zByy')) ∨
       (t2 = Tid.primeBY ∧ u = Loc.zBy'y) ∨
       (t2 = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (t2 = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (t2 = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (t2 = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      ((t1 ∈ ThreadDomX ∧ t2 ∈ ThreadDomX) ∨ (t1 ∈ ThreadDomY ∧ t2 ∈ ThreadDomY)) := by
  intro t1 t2 u hw hnb hr
  fin_cases u <;> fin_cases t1 <;> simp_all [writerTids, ThreadDomX, ThreadDomY, BridgeLoc]

/-- `ThreadDomX` is closed under a single non-bridge `po`/`rf`-step. Together
with the thread-level `hb` separation (Fig. 4) (which separates `α` from `β`), this separates the `x`
and `y` coordinates of a bridge-free path. -/
theorem executionGraphOf_threadDomX_step_closed (I : PCPInstance) (hsol : I.HasSolution) :
    ∀ x y : Event (domainOf I), x.tid ∈ ThreadDomX → ¬ x.IsBridge → ¬ y.IsBridge →
      ((executionGraphOf I hsol).po x y ∨ (executionGraphOf I hsol).rf x y) →
      y.tid ∈ ThreadDomX := by
  set G := executionGraphOf I hsol with hG
  rintro x y hxX hnbx hnby (hpo | hrf)
  · rw [← (G.po_subset hpo).2.2]; exact hxX
  · have hxwt : x.op = .wt := (G.rf_subset hrf).2.2.1
    have hyrd : y.op = .rd := (G.rf_subset hrf).2.2.2.1
    have hxyloc : x.loc = y.loc := (G.rf_subset hrf).2.2.2.2
    have hxMem : x ∈ G.Events := (G.rf_subset hrf).1
    have hyMem : y ∈ G.Events := (G.rf_subset hrf).2.1
    have hxtid : x.tid ∈ writerTids x.loc := executionGraphOf_writers_confined I hsol hxMem hxwt
    have hytid := executionGraphOf_reads_confined I hsol hyMem hyrd
    rw [← hxyloc] at hytid
    rcases writeRead_diffThread_sameDom x.tid y.tid x.loc hxtid hnbx hytid with
      ⟨-, hyX⟩ | ⟨hxY, -⟩
    · exact hyX
    · exact absurd hxY (fun h => threadDomX_threadDomY_disjoint hxX h)

/-- `executionGraphOf_threadDomX_step_closed`'s `ThreadDomY` analogue. -/
theorem executionGraphOf_threadDomY_step_closed (I : PCPInstance) (hsol : I.HasSolution) :
    ∀ x y : Event (domainOf I), x.tid ∈ ThreadDomY → ¬ x.IsBridge → ¬ y.IsBridge →
      ((executionGraphOf I hsol).po x y ∨ (executionGraphOf I hsol).rf x y) →
      y.tid ∈ ThreadDomY := by
  set G := executionGraphOf I hsol with hG
  rintro x y hxY hnbx hnby (hpo | hrf)
  · rw [← (G.po_subset hpo).2.2]; exact hxY
  · have hxwt : x.op = .wt := (G.rf_subset hrf).2.2.1
    have hyrd : y.op = .rd := (G.rf_subset hrf).2.2.2.1
    have hxyloc : x.loc = y.loc := (G.rf_subset hrf).2.2.2.2
    have hxMem : x ∈ G.Events := (G.rf_subset hrf).1
    have hyMem : y ∈ G.Events := (G.rf_subset hrf).2.1
    have hxtid : x.tid ∈ writerTids x.loc := executionGraphOf_writers_confined I hsol hxMem hxwt
    have hytid := executionGraphOf_reads_confined I hsol hyMem hyrd
    rw [← hxyloc] at hytid
    rcases writeRead_diffThread_sameDom x.tid y.tid x.loc hxtid hnbx hytid with
      ⟨hxX, -⟩ | ⟨-, hyY⟩
    · exact absurd hxX (fun h => threadDomX_threadDomY_disjoint h hxY)
    · exact hyY

/-- The bridge case of `hb_c_monotonic`: `wi.tid`/`rj.tid`/`u` are one of the
paper's four symmetric instances (`loc(wi) = z_α^{x,y}` and its analogues). -/
theorem writeRead_bridge_pairs :
    ∀ (t1 t2 : Tid) (u : Loc), t1 ∈ writerTids u → u ∈ BridgeLoc →
      ((t2 = Tid.guessAX ∧ (u = Loc.zAxx' ∨ u = Loc.ellAyx)) ∨
       (t2 = Tid.primeAX ∧ u = Loc.zAx'x) ∨
       (t2 = Tid.guessAY ∧ (u = Loc.zAxy ∨ u = Loc.zAyy')) ∨
       (t2 = Tid.primeAY ∧ u = Loc.zAy'y) ∨
       (t2 = Tid.guessBX ∧ (u = Loc.zBxx' ∨ u = Loc.ellByx)) ∨
       (t2 = Tid.primeBX ∧ u = Loc.zBx'x) ∨
       (t2 = Tid.guessBY ∧ (u = Loc.zBxy ∨ u = Loc.zByy')) ∨
       (t2 = Tid.primeBY ∧ u = Loc.zBy'y) ∨
       (t2 = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (t2 = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (t2 = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (t2 = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      (u = Loc.zAxy ∧ t1 = Tid.guessAX ∧ t2 = Tid.guessAY) ∨
      (u = Loc.ellAyx ∧ t1 = Tid.guessAY ∧ t2 = Tid.guessAX) ∨
      (u = Loc.zBxy ∧ t1 = Tid.guessBX ∧ t2 = Tid.guessBY) ∨
      (u = Loc.ellByx ∧ t1 = Tid.guessBY ∧ t2 = Tid.guessBX) := by
  intro t1 t2 u hw hbr hr
  fin_cases u <;> simp_all [writerTids, BridgeLoc]

/-- The crossing edge of `executionGraphOf_guessAX_guessAY_crossing` is at
`z_α^{x,y}`, `guessAX`'s only write location read by `guessAY`. -/
theorem executionGraphOf_guessAX_guessAY_crossing_loc (I : PCPInstance) (hsol : I.HasSolution)
    {wc rc : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf wc rc)
    (hwctid : wc.tid = Tid.guessAX) (hrctid : rc.tid = Tid.guessAY) :
    wc.loc = Loc.zAxy ∧ rc.loc = Loc.zAxy := by
  have hwcMem : wc ∈ (executionGraphOf I hsol).Events :=
    ((executionGraphOf I hsol).rf_subset hrf).1
  have hwcWt : wc.op = .wt := ((executionGraphOf I hsol).rf_subset hrf).2.2.1
  have hwctids : wc.tid ∈ writerTids wc.loc := executionGraphOf_writers_confined I hsol hwcMem hwcWt
  have hrcMem : rc ∈ (executionGraphOf I hsol).Events :=
    ((executionGraphOf I hsol).rf_subset hrf).2.1
  have hrcRd : rc.op = .rd := ((executionGraphOf I hsol).rf_subset hrf).2.2.2.1
  have hrctid2 := executionGraphOf_reads_confined I hsol hrcMem hrcRd
  have hloceq0 : wc.loc = rc.loc := ((executionGraphOf I hsol).rf_subset hrf).2.2.2.2
  rw [← hloceq0] at hrctid2
  have hwcbridge : wc.IsBridge :=
    (executionGraphOf_rf_bridge_pairs I hsol hrf (Or.inl ⟨hwctid, hrctid⟩)).1
  rcases writeRead_bridge_pairs wc.tid rc.tid wc.loc hwctids hwcbridge hrctid2 with
    ⟨hwcu, -, -⟩ | ⟨-, hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, hh, -⟩
  · exact ⟨hwcu, hloceq0.symm.trans hwcu⟩
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact Tid.noConfusion (hwctid.symm.trans hh)
/-- The crossing edge of `executionGraphOf_guessAY_guessAX_crossing` is at
`ℓ_α^{y,x}`, `guessAY`'s only write location read by `guessAX`. -/
theorem executionGraphOf_guessAY_guessAX_crossing_loc (I : PCPInstance) (hsol : I.HasSolution)
    {wc rc : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf wc rc)
    (hwctid : wc.tid = Tid.guessAY) (hrctid : rc.tid = Tid.guessAX) :
    wc.loc = Loc.ellAyx ∧ rc.loc = Loc.ellAyx := by
  have hwcMem : wc ∈ (executionGraphOf I hsol).Events :=
    ((executionGraphOf I hsol).rf_subset hrf).1
  have hwcWt : wc.op = .wt := ((executionGraphOf I hsol).rf_subset hrf).2.2.1
  have hwctids : wc.tid ∈ writerTids wc.loc := executionGraphOf_writers_confined I hsol hwcMem hwcWt
  have hrcMem : rc ∈ (executionGraphOf I hsol).Events :=
    ((executionGraphOf I hsol).rf_subset hrf).2.1
  have hrcRd : rc.op = .rd := ((executionGraphOf I hsol).rf_subset hrf).2.2.2.1
  have hrctid2 := executionGraphOf_reads_confined I hsol hrcMem hrcRd
  have hloceq0 : wc.loc = rc.loc := ((executionGraphOf I hsol).rf_subset hrf).2.2.2.2
  rw [← hloceq0] at hrctid2
  have hwcbridge : wc.IsBridge :=
    (executionGraphOf_rf_bridge_pairs I hsol hrf (Or.inr (Or.inl ⟨hwctid, hrctid⟩))).1
  rcases writeRead_bridge_pairs wc.tid rc.tid wc.loc hwctids hwcbridge hrctid2 with
    ⟨-, hh, -⟩ | ⟨hwcu, -, -⟩ | ⟨-, hh, -⟩ | ⟨-, hh, -⟩
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact ⟨hwcu, hloceq0.symm.trans hwcu⟩
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact Tid.noConfusion (hwctid.symm.trans hh)
/-- The crossing edge of `executionGraphOf_guessBX_guessBY_crossing` is at
`z_β^{x,y}`, `guessBX`'s only write location read by `guessBY`. -/
theorem executionGraphOf_guessBX_guessBY_crossing_loc (I : PCPInstance) (hsol : I.HasSolution)
    {wc rc : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf wc rc)
    (hwctid : wc.tid = Tid.guessBX) (hrctid : rc.tid = Tid.guessBY) :
    wc.loc = Loc.zBxy ∧ rc.loc = Loc.zBxy := by
  have hwcMem : wc ∈ (executionGraphOf I hsol).Events :=
    ((executionGraphOf I hsol).rf_subset hrf).1
  have hwcWt : wc.op = .wt := ((executionGraphOf I hsol).rf_subset hrf).2.2.1
  have hwctids : wc.tid ∈ writerTids wc.loc := executionGraphOf_writers_confined I hsol hwcMem hwcWt
  have hrcMem : rc ∈ (executionGraphOf I hsol).Events :=
    ((executionGraphOf I hsol).rf_subset hrf).2.1
  have hrcRd : rc.op = .rd := ((executionGraphOf I hsol).rf_subset hrf).2.2.2.1
  have hrctid2 := executionGraphOf_reads_confined I hsol hrcMem hrcRd
  have hloceq0 : wc.loc = rc.loc := ((executionGraphOf I hsol).rf_subset hrf).2.2.2.2
  rw [← hloceq0] at hrctid2
  have hwcbridge : wc.IsBridge :=
    (executionGraphOf_rf_bridge_pairs I hsol hrf (Or.inr (Or.inr (Or.inl ⟨hwctid, hrctid⟩)))).1
  rcases writeRead_bridge_pairs wc.tid rc.tid wc.loc hwctids hwcbridge hrctid2 with
    ⟨-, hh, -⟩ | ⟨-, hh, -⟩ | ⟨hwcu, -, -⟩ | ⟨-, hh, -⟩
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact ⟨hwcu, hloceq0.symm.trans hwcu⟩
  · exact Tid.noConfusion (hwctid.symm.trans hh)
/-- The crossing edge of `executionGraphOf_guessBY_guessBX_crossing` is at
`ℓ_β^{y,x}`, `guessBY`'s only write location read by `guessBX`. -/
theorem executionGraphOf_guessBY_guessBX_crossing_loc (I : PCPInstance) (hsol : I.HasSolution)
    {wc rc : Event (domainOf I)} (hrf : (executionGraphOf I hsol).rf wc rc)
    (hwctid : wc.tid = Tid.guessBY) (hrctid : rc.tid = Tid.guessBX) :
    wc.loc = Loc.ellByx ∧ rc.loc = Loc.ellByx := by
  have hwcMem : wc ∈ (executionGraphOf I hsol).Events :=
    ((executionGraphOf I hsol).rf_subset hrf).1
  have hwcWt : wc.op = .wt := ((executionGraphOf I hsol).rf_subset hrf).2.2.1
  have hwctids : wc.tid ∈ writerTids wc.loc := executionGraphOf_writers_confined I hsol hwcMem hwcWt
  have hrcMem : rc ∈ (executionGraphOf I hsol).Events :=
    ((executionGraphOf I hsol).rf_subset hrf).2.1
  have hrcRd : rc.op = .rd := ((executionGraphOf I hsol).rf_subset hrf).2.2.2.1
  have hrctid2 := executionGraphOf_reads_confined I hsol hrcMem hrcRd
  have hloceq0 : wc.loc = rc.loc := ((executionGraphOf I hsol).rf_subset hrf).2.2.2.2
  rw [← hloceq0] at hrctid2
  have hwcbridge : wc.IsBridge :=
    (executionGraphOf_rf_bridge_pairs I hsol hrf (Or.inr (Or.inr (Or.inr ⟨hwctid, hrctid⟩)))).1
  rcases writeRead_bridge_pairs wc.tid rc.tid wc.loc hwctids hwcbridge hrctid2 with
    ⟨-, hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, hh, -⟩ | ⟨hwcu, -, -⟩
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact Tid.noConfusion (hwctid.symm.trans hh)
  · exact ⟨hwcu, hloceq0.symm.trans hwcu⟩

/-- A thread reading two distinct non-bridge locations is one of the four
checkers. -/
theorem reads_two_nonbridge_locs_checker :
    ∀ (t : Tid) (u1 u2 : Loc), u1 ≠ u2 → u1 ∉ BridgeLoc → u2 ∉ BridgeLoc →
      ((t = Tid.guessAX ∧ (u1 = Loc.zAxx' ∨ u1 = Loc.ellAyx)) ∨
       (t = Tid.primeAX ∧ u1 = Loc.zAx'x) ∨
       (t = Tid.guessAY ∧ (u1 = Loc.zAxy ∨ u1 = Loc.zAyy')) ∨
       (t = Tid.primeAY ∧ u1 = Loc.zAy'y) ∨
       (t = Tid.guessBX ∧ (u1 = Loc.zBxx' ∨ u1 = Loc.ellByx)) ∨
       (t = Tid.primeBX ∧ u1 = Loc.zBx'x) ∨
       (t = Tid.guessBY ∧ (u1 = Loc.zBxy ∨ u1 = Loc.zByy')) ∨
       (t = Tid.primeBY ∧ u1 = Loc.zBy'y) ∨
       (t = Tid.checkX ∧ (u1 = Loc.xA ∨ u1 = Loc.xB ∨ u1 = Loc.xA' ∨ u1 = Loc.xB')) ∨
       (t = Tid.primeCheckX ∧ (u1 = Loc.xA' ∨ u1 = Loc.xB' ∨ u1 = Loc.xA ∨ u1 = Loc.xB)) ∨
       (t = Tid.checkY ∧ (u1 = Loc.yA ∨ u1 = Loc.yB ∨ u1 = Loc.yA' ∨ u1 = Loc.yB')) ∨
       (t = Tid.primeCheckY ∧ (u1 = Loc.yA' ∨ u1 = Loc.yB' ∨ u1 = Loc.yA ∨ u1 = Loc.yB))) →
      ((t = Tid.guessAX ∧ (u2 = Loc.zAxx' ∨ u2 = Loc.ellAyx)) ∨
       (t = Tid.primeAX ∧ u2 = Loc.zAx'x) ∨
       (t = Tid.guessAY ∧ (u2 = Loc.zAxy ∨ u2 = Loc.zAyy')) ∨
       (t = Tid.primeAY ∧ u2 = Loc.zAy'y) ∨
       (t = Tid.guessBX ∧ (u2 = Loc.zBxx' ∨ u2 = Loc.ellByx)) ∨
       (t = Tid.primeBX ∧ u2 = Loc.zBx'x) ∨
       (t = Tid.guessBY ∧ (u2 = Loc.zBxy ∨ u2 = Loc.zByy')) ∨
       (t = Tid.primeBY ∧ u2 = Loc.zBy'y) ∨
       (t = Tid.checkX ∧ (u2 = Loc.xA ∨ u2 = Loc.xB ∨ u2 = Loc.xA' ∨ u2 = Loc.xB')) ∨
       (t = Tid.primeCheckX ∧ (u2 = Loc.xA' ∨ u2 = Loc.xB' ∨ u2 = Loc.xA ∨ u2 = Loc.xB)) ∨
       (t = Tid.checkY ∧ (u2 = Loc.yA ∨ u2 = Loc.yB ∨ u2 = Loc.yA' ∨ u2 = Loc.yB')) ∨
       (t = Tid.primeCheckY ∧ (u2 = Loc.yA' ∨ u2 = Loc.yB' ∨ u2 = Loc.yA ∨ u2 = Loc.yB))) →
      (t = Tid.checkX ∨ t = Tid.primeCheckX ∨ t = Tid.checkY ∨ t = Tid.primeCheckY) := by
  intro t u1 u2 hne hnb1 hnb2 hr1 hr2
  fin_cases t <;> simp_all [BridgeLoc]

/-- If a guesser or primed guesser `tg` writes a non-bridge location `u` that
a checker reads, then `u` is `tg`'s location shared with the checkers (`xA`
for `guessAX`, `xA'` for `primeAX`, and so on): the paper's "different
guesser threads write different locations of `{x_α,x'_α}`", for all four
coordinate/side combinations. -/
theorem writeRead_guesser_crossing_loc :
    ∀ (tg tv : Tid) (u : Loc), tg ∈ writerTids u → u ∉ BridgeLoc →
      (tg ≠ Tid.checkX ∧ tg ≠ Tid.primeCheckX ∧ tg ≠ Tid.checkY ∧ tg ≠ Tid.primeCheckY) →
      (tv = Tid.checkX ∨ tv = Tid.primeCheckX ∨ tv = Tid.checkY ∨ tv = Tid.primeCheckY) →
      ((tv = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (tv = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (tv = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (tv = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      (tg = Tid.guessAX ∧ u = Loc.xA) ∨ (tg = Tid.primeAX ∧ u = Loc.xA') ∨
      (tg = Tid.guessBX ∧ u = Loc.xB) ∨ (tg = Tid.primeBX ∧ u = Loc.xB') ∨
      (tg = Tid.guessAY ∧ u = Loc.yA) ∨ (tg = Tid.primeAY ∧ u = Loc.yA') ∨
      (tg = Tid.guessBY ∧ u = Loc.yB) ∨ (tg = Tid.primeBY ∧ u = Loc.yB') := by
  intro tg tv u hw hnb htg hv hr
  fin_cases u <;> simp_all [writerTids]

/-- The location of `writeRead_guesser_crossing_loc` is a function of the
thread. -/
theorem guesser_crossing_loc_functional :
    ∀ (t : Tid) (u1 u2 : Loc),
      ((t = Tid.guessAX ∧ u1 = Loc.xA) ∨ (t = Tid.primeAX ∧ u1 = Loc.xA') ∨
       (t = Tid.guessBX ∧ u1 = Loc.xB) ∨ (t = Tid.primeBX ∧ u1 = Loc.xB') ∨
       (t = Tid.guessAY ∧ u1 = Loc.yA) ∨ (t = Tid.primeAY ∧ u1 = Loc.yA') ∨
       (t = Tid.guessBY ∧ u1 = Loc.yB) ∨ (t = Tid.primeBY ∧ u1 = Loc.yB')) →
      ((t = Tid.guessAX ∧ u2 = Loc.xA) ∨ (t = Tid.primeAX ∧ u2 = Loc.xA') ∨
       (t = Tid.guessBX ∧ u2 = Loc.xB) ∨ (t = Tid.primeBX ∧ u2 = Loc.xB') ∨
       (t = Tid.guessAY ∧ u2 = Loc.yA) ∨ (t = Tid.primeAY ∧ u2 = Loc.yA') ∨
       (t = Tid.guessBY ∧ u2 = Loc.yB) ∨ (t = Tid.primeBY ∧ u2 = Loc.yB')) →
      u1 = u2 := by
  intro t u1 u2 h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h2 with ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ | ⟨h2, rfl⟩ |
      ⟨h2, rfl⟩ | ⟨h2, rfl⟩ <;>
    first | rfl | exact absurd h2 (by decide)

/-- `executionGraphOf_reads_confined` for a checker thread `t`. -/
theorem reads_confined_checker_filter :
    ∀ (t : Tid) (u : Loc),
      ((t = Tid.guessAX ∧ (u = Loc.zAxx' ∨ u = Loc.ellAyx)) ∨
       (t = Tid.primeAX ∧ u = Loc.zAx'x) ∨
       (t = Tid.guessAY ∧ (u = Loc.zAxy ∨ u = Loc.zAyy')) ∨
       (t = Tid.primeAY ∧ u = Loc.zAy'y) ∨
       (t = Tid.guessBX ∧ (u = Loc.zBxx' ∨ u = Loc.ellByx)) ∨
       (t = Tid.primeBX ∧ u = Loc.zBx'x) ∨
       (t = Tid.guessBY ∧ (u = Loc.zBxy ∨ u = Loc.zByy')) ∨
       (t = Tid.primeBY ∧ u = Loc.zBy'y) ∨
       (t = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (t = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (t = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (t = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      (t = Tid.checkX ∨ t = Tid.primeCheckX ∨ t = Tid.checkY ∨ t = Tid.primeCheckY) →
      ((t = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (t = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (t = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (t = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) := by
  intro t u h12 hv
  rcases hv with hv | hv | hv | hv <;> rw [hv] at h12 ⊢ <;>
    rcases h12 with h | h | h | h | h | h | h | h | h | h | h | h <;> tauto

/-- **Paper:** Lemma 3.13.

`hb_c_monotonic`: `hb` is non-decreasing from a write to a read of the
same location. By cases on a minimal `hb`-path `Path : wi ⟶hb rj`, as in
Appendix B:

* *a single `po`-edge*: `wi.tid = rj.tid` is one of
  `CheckX`/`CheckY`/`PrimeCheckX`/`PrimeCheckY`
  (`writeRead_selfthread_confined`, the paper's eight `⟨tid,u⟩` pairs), and
  each closes by the matching `executionGraphOf_*_po_monotone_write_read`.
* *ends in an `rf`-edge*, `wi ⇝hb^? wj ⟶rf rj`: if `wi = wj`,
  `executionGraphOf_rf_index_eq`; otherwise `executionGraphOf_hb_writes_increasing`
  gives `i < j`, then `executionGraphOf_rf_index_eq`.
* *ends in a `po`-edge, non-bridge*, `wi ⇝hb^? wℓ ⟶rf rℓ
  ⟶po rj`: if `loc(wℓ) = u`, `i ≤ ℓ < j`. Otherwise `wi` and `rj` share
  a `ThreadDom` (`writeRead_diffThread_sameDom`) and the path is bridge-free
  (Lemma 3.8), so `i ≤ ℓ`; then
  - if `tid(wi)` is a checker, so is `tid(wℓ)` (`hb`-closure of the checker
    groups), so the closing edge `rℓ ⟶po rj` is non-decreasing: `ℓ ≤ j`;
  - if `tid(wi)` is a guesser, `rj.tid` reads two distinct non-bridge
    locations and so is a checker (`reads_two_nonbridge_locs_checker`); then
    either `wℓ` is a checker (as above) or a guesser different from `tid(wi)`
    (`guesser_crossing_loc_functional`), giving `i < ℓ` (Lemma 3.9(ii)),
    and the closing edge decreases by at most one, so `i ≤ j`.
* *ends in a `po`-edge, bridge*: `wi.tid`/`rj.tid`/`u` are one of the paper's
  four symmetric instances (`writeRead_bridge_pairs`); the crossing `rf`-edge
  `wc ⟶rf rc` at `u` is located by
  `executionGraphOf_guessAX_guessAY_crossing_aux` (and siblings), and
  `wi ⟶hb^? wc`, `rc ⟶hb^? rj` give `i ≤ index wc = index rc ≤ j`
  (`executionGraphOf_hb_writes_increasing`,
  `executionGraphOf_hb_reads_sameThread_le`). -/
theorem executionGraphOf_hb_write_read (I : PCPInstance) (hsol : I.HasSolution)
    {wi rj : Event (domainOf I)} (hwi : wi.op = .wt) (hrj : rj.op = .rd)
    (hloc : wi.loc = rj.loc) (hhb : (executionGraphOf I hsol).hb wi rj) :
    (executionGraphOf I hsol).index wi ≤ (executionGraphOf I hsol).index rj := by
  set G := executionGraphOf I hsol with hG
  obtain ⟨p, hmin⟩ := executionGraphOf_hb_minimal I hsol hhb
  have hp : p.IsAlternating := p.isAlternating_of_isMinimal hmin
  match p with
  | .single_po hpo =>
    obtain ⟨hwiMem, hrjMem, htid⟩ := G.po_subset hpo
    have hwtid : wi.tid ∈ writerTids wi.loc := executionGraphOf_writers_confined I hsol hwiMem hwi
    have hrtid := executionGraphOf_reads_confined I hsol hrjMem hrj
    rw [← hloc] at hrtid
    rw [← htid] at hrtid
    rcases writeRead_selfthread_confined wi.tid wi.loc hwtid hrtid with
      ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact executionGraphOf_checkX_po_monotone_write_read I hsol ht (htid ▸ ht) hpo hwi hrj hloc
    · exact executionGraphOf_checkY_po_monotone_write_read I hsol ht (htid ▸ ht) hpo hwi hrj hloc
    · exact executionGraphOf_primeCheckX_po_monotone_write_read I hsol ht (htid ▸ ht) hpo hwi hrj
        hloc
    · exact executionGraphOf_primeCheckY_po_monotone_write_read I hsol ht (htid ▸ ht) hpo hwi hrj
        hloc
  | .single_rf hrf =>
    exact le_of_eq (executionGraphOf_rf_index_eq I hsol hrf)
  | .tail_rf (b := wj) p' hrf =>
    by_cases heq : wi = wj
    · subst heq
      exact le_of_eq (executionGraphOf_rf_index_eq I hsol hrf)
    · have hwjWt : wj.op = .wt := (G.rf_subset hrf).2.2.1
      have hwjLoc : wj.loc = rj.loc := (G.rf_subset hrf).2.2.2.2
      have hhbij : G.hb wi wj := p'.sound
      have hlt : G.index wi < G.index wj :=
        executionGraphOf_hb_writes_increasing I hsol hwi hwjWt (hloc.trans hwjLoc.symm) hhbij
      have heqidx : G.index wj = G.index rj := executionGraphOf_rf_index_eq I hsol hrf
      omega
  | .tail_po (b := rl) p' hpo =>
    have hpCopy := hp
    obtain ⟨hp'alt, hp'lastrf⟩ := hpCopy
    by_cases hbr : wi.loc ∈ BridgeLoc
    · -- `wi` and `rj` are bridge events.
      have hwiMem : wi ∈ G.Events := G.hb_mem_events_left hhb
      have hrjMem : rj ∈ G.Events := G.hb_mem_events hhb
      have hwtid : wi.tid ∈ writerTids wi.loc := executionGraphOf_writers_confined I hsol hwiMem
        hwi
      have hrtid := executionGraphOf_reads_confined I hsol hrjMem hrj
      rw [← hloc] at hrtid
      obtain ⟨p0⟩ := Path.complete hhb
      rcases writeRead_bridge_pairs wi.tid rj.tid wi.loc hwtid hbr hrtid with
        ⟨hu, hwit, hrjt⟩ | ⟨hu, hwit, hrjt⟩ | ⟨hu, hwit, hrjt⟩ | ⟨hu, hwit, hrjt⟩
      · -- `z_α^{x,y}`: `guessAX` writes, `guessAY` reads.
        obtain ⟨wc, rc, hrf, hwctid, hrctid, hawc, hrcrj⟩ :=
          executionGraphOf_guessAX_guessAY_crossing I hsol hwit (Or.inl hrjt) p0
        obtain ⟨hwcloc, hrcloc⟩ :=
          executionGraphOf_guessAX_guessAY_crossing_loc I hsol hrf hwctid hrctid
        have hwiwc : G.index wi ≤ G.index wc := by
          rcases hawc with heq | hbb
          · exact le_of_eq (congrArg G.index heq)
          · exact le_of_lt (executionGraphOf_hb_writes_increasing I hsol hwi
              ((G.rf_subset hrf).2.2.1) (hu.trans hwcloc.symm) hbb)
        have hwcrc : G.index wc = G.index rc := executionGraphOf_rf_index_eq I hsol hrf
        have hrcrj' : G.index rc ≤ G.index rj :=
          executionGraphOf_hb_reads_sameThread_le I hsol ((G.rf_subset hrf).2.2.2.1) hrj
            (hrctid.trans hrjt.symm) (hrcloc.trans (hu.symm.trans hloc)) (hrcrj.imp Eq.symm id)
        omega
      · -- `ℓ_α^{y,x}`: `guessAY` writes, `guessAX` reads.
        obtain ⟨wc, rc, hrf, hwctid, hrctid, hawc, hrcrj⟩ :=
          executionGraphOf_guessAY_guessAX_crossing I hsol hwit (Or.inl hrjt) p0
        obtain ⟨hwcloc, hrcloc⟩ :=
          executionGraphOf_guessAY_guessAX_crossing_loc I hsol hrf hwctid hrctid
        have hwiwc : G.index wi ≤ G.index wc := by
          rcases hawc with heq | hbb
          · exact le_of_eq (congrArg G.index heq)
          · exact le_of_lt (executionGraphOf_hb_writes_increasing I hsol hwi
              ((G.rf_subset hrf).2.2.1) (hu.trans hwcloc.symm) hbb)
        have hwcrc : G.index wc = G.index rc := executionGraphOf_rf_index_eq I hsol hrf
        have hrcrj' : G.index rc ≤ G.index rj :=
          executionGraphOf_hb_reads_sameThread_le I hsol ((G.rf_subset hrf).2.2.2.1) hrj
            (hrctid.trans hrjt.symm) (hrcloc.trans (hu.symm.trans hloc)) (hrcrj.imp Eq.symm id)
        omega
      · -- `z_β^{x,y}`: `guessBX` writes, `guessBY` reads.
        obtain ⟨wc, rc, hrf, hwctid, hrctid, hawc, hrcrj⟩ :=
          executionGraphOf_guessBX_guessBY_crossing I hsol hwit (Or.inl hrjt) p0
        obtain ⟨hwcloc, hrcloc⟩ :=
          executionGraphOf_guessBX_guessBY_crossing_loc I hsol hrf hwctid hrctid
        have hwiwc : G.index wi ≤ G.index wc := by
          rcases hawc with heq | hbb
          · exact le_of_eq (congrArg G.index heq)
          · exact le_of_lt (executionGraphOf_hb_writes_increasing I hsol hwi
              ((G.rf_subset hrf).2.2.1) (hu.trans hwcloc.symm) hbb)
        have hwcrc : G.index wc = G.index rc := executionGraphOf_rf_index_eq I hsol hrf
        have hrcrj' : G.index rc ≤ G.index rj :=
          executionGraphOf_hb_reads_sameThread_le I hsol ((G.rf_subset hrf).2.2.2.1) hrj
            (hrctid.trans hrjt.symm) (hrcloc.trans (hu.symm.trans hloc)) (hrcrj.imp Eq.symm id)
        omega
      · -- `ℓ_β^{y,x}`: `guessBY` writes, `guessBX` reads.
        obtain ⟨wc, rc, hrf, hwctid, hrctid, hawc, hrcrj⟩ :=
          executionGraphOf_guessBY_guessBX_crossing I hsol hwit (Or.inl hrjt) p0
        obtain ⟨hwcloc, hrcloc⟩ :=
          executionGraphOf_guessBY_guessBX_crossing_loc I hsol hrf hwctid hrctid
        have hwiwc : G.index wi ≤ G.index wc := by
          rcases hawc with heq | hbb
          · exact le_of_eq (congrArg G.index heq)
          · exact le_of_lt (executionGraphOf_hb_writes_increasing I hsol hwi
              ((G.rf_subset hrf).2.2.1) (hu.trans hwcloc.symm) hbb)
        have hwcrc : G.index wc = G.index rc := executionGraphOf_rf_index_eq I hsol hrf
        have hrcrj' : G.index rc ≤ G.index rj :=
          executionGraphOf_hb_reads_sameThread_le I hsol ((G.rf_subset hrf).2.2.2.1) hrj
            (hrctid.trans hrjt.symm) (hrcloc.trans (hu.symm.trans hloc)) (hrcrj.imp Eq.symm id)
        omega
    · have hnbwi : ¬ wi.IsBridge := hbr
      have hnbrj : ¬ rj.IsBridge := by unfold Event.IsBridge; rw [← hloc]; exact hbr
      have hwiMem : wi ∈ G.Events := G.hb_mem_events_left hhb
      have hrjMem : rj ∈ G.Events := G.hb_mem_events hhb
      cases p' with
      | single_po h' => exact absurd trivial hp'lastrf
      | tail_po q' h' => exact absurd trivial hp'lastrf
      | single_rf h' =>
          -- `wℓ = wi`: `loc(wℓ) = u` automatically, matching the "`wi = wℓ`"
          -- sub-branch of the `loc(wℓ) = u` case trivially.
          have hrlop : rl.op = .rd := (G.rf_subset h').2.2.2.1
          have hrlloc : rl.loc = wi.loc := (G.rf_subset h').2.2.2.2.symm
          have hidx : G.index wi = G.index rl := executionGraphOf_rf_index_eq I hsol h'
          have hlt : G.index rl < G.index rj :=
            executionGraphOf_index_lt_of_po_sameLocOp I hsol hpo (hrlloc.trans hloc)
              (hrlop.trans hrj.symm)
          omega
      | tail_rf q' h' =>
          rename_i wl
          have hrlop : rl.op = .rd := (G.rf_subset h').2.2.2.1
          have hwlop : wl.op = .wt := (G.rf_subset h').2.2.1
          have hwlrl_loc : wl.loc = rl.loc := (G.rf_subset h').2.2.2.2
          by_cases hloc2 : wl.loc = wi.loc
          · -- `loc(wℓ) = u`.
            have hidx1 : G.index wi ≤ G.index wl :=
              le_of_lt (executionGraphOf_hb_writes_increasing I hsol hwi hwlop hloc2.symm
                q'.sound)
            have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
            have hrlrjloc : rl.loc = rj.loc := hwlrl_loc.symm.trans (hloc2.trans hloc)
            have hlt : G.index rl < G.index rj :=
              executionGraphOf_index_lt_of_po_sameLocOp I hsol hpo hrlrjloc
                (hrlop.trans hrj.symm)
            omega
          · -- `loc(wℓ) ≠ u`: shared preamble first — `wi`, `rj` on the same
            -- `ThreadDom`, the whole path bridge-free (the general
            -- Lemma 3.8, not the write-write
            -- specialization its Lean name suggests: it needs no hypothesis
            -- on `b`'s operation, so it applies directly to `p` itself).
            have hwtid : wi.tid ∈ writerTids wi.loc :=
              executionGraphOf_writers_confined I hsol hwiMem hwi
            have hrtid := executionGraphOf_reads_confined I hsol hrjMem hrj
            rw [← hloc] at hrtid
            have hdom := writeRead_diffThread_sameDom wi.tid rj.tid wi.loc hwtid hbr hrtid
            have hnbAll := executionGraphOf_write_to_write_no_bridge I hsol hnbwi hnbrj hdom _ hp
              hmin
            obtain ⟨hnbp', -⟩ := hnbAll
            obtain ⟨hnbq', hnbrl⟩ := hnbp'
            have hm := hmin
            simp only [Path.IsMinimal, Path.poThreads] at hm
            have hq'min : q'.poThreads.Nodup := (List.nodup_append.mp hm).1
            obtain ⟨hq'alt, -⟩ := hp'alt
            have hidx1 : G.index wi ≤ G.index wl :=
              (executionGraphOf_write_to_write_no_bridge_increasing I hsol hwi hwlop q' hq'alt
                hq'min hnbq').1
            -- `tid(rj) = tid(rl)` reads two *distinct* non-bridge locations
            -- (`u` via `rj`, `loc(wℓ) ≠ u` via `rl`), so it is a checker —
            -- the fact that lets case 3b's crossing coincide with the
            -- already-established `wl`/`rl`, with no further search.
            have hrlMem : rl ∈ G.Events := (G.po_subset hpo).1
            have hrltid : rl.tid = rj.tid := (G.po_subset hpo).2.2
            have hne : rl.loc ≠ rj.loc := by rw [← hwlrl_loc, ← hloc]; exact hloc2
            have hr1 := executionGraphOf_reads_confined I hsol hrlMem hrlop
            rw [hrltid] at hr1
            have hrtid2 := executionGraphOf_reads_confined I hsol hrjMem hrj
            have hrj_verif := reads_two_nonbridge_locs_checker rj.tid rl.loc rj.loc hne hnbrl
              hnbrj hr1 hrtid2
            have hrtid2wi := hrtid2
            rw [← hloc] at hrtid2wi
            have hrtid2wi' := reads_confined_checker_filter rj.tid wi.loc hrtid2wi hrj_verif
            have hr1wl := hr1
            rw [← hwlrl_loc] at hr1wl
            have hr1wl' := reads_confined_checker_filter rj.tid wl.loc hr1wl hrj_verif
            -- The shared "`tid(wi)` is a guesser" argument, uniform over all
            -- eight guesser/primed-guesser threads at once (no per-thread
            -- split needed, unlike the checker case below, since neither
            -- `writeRead_guesser_crossing_loc` nor
            -- `guesser_crossing_loc_functional` need one).
            have hAllGuesserCase : wi.tid ≠ Tid.checkX → wi.tid ≠ Tid.primeCheckX →
                wi.tid ≠ Tid.checkY → wi.tid ≠ Tid.primeCheckY →
                G.index wi ≤ G.index rj := by
              intro htg1 htg2 htg3 htg4
              have htgloc := writeRead_guesser_crossing_loc wi.tid rj.tid wi.loc hwtid hbr
                ⟨htg1, htg2, htg3, htg4⟩ hrj_verif hrtid2wi'
              by_cases hwlv : wl.tid = Tid.checkX ∨ wl.tid = Tid.primeCheckX ∨
                  wl.tid = Tid.checkY ∨ wl.tid = Tid.primeCheckY
              · -- `wl` is *already* a checker: same "closing edge
                -- non-decreasing" mechanism as the checker case below.
                have hrjrl : G.index rl ≤ G.index rj := by
                  by_contra hcon
                  push Not at hcon
                  obtain ⟨-, -, w1, hw1rf, hgg⟩ :=
                    executionGraphOf_po_reads_decreasing I hsol hpo hrlop hrj hnbrl hnbrj hcon
                  have hw1eq : w1 = wl := G.rf_unique hw1rf h'
                  rw [hw1eq] at hgg
                  rcases hwlv with hwlv | hwlv | hwlv | hwlv <;> rw [hwlv] at hgg <;>
                    rcases hgg with hgg | hgg | hgg | hgg <;> exact Tid.noConfusion hgg
                have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
                omega
              · -- `wl` is a guesser: the crossing edge `h'` itself is the
                -- one the paper calls `wℓ'-rf->rℓ'`, forced distinct from
                -- `wi` (`guesser_crossing_loc_functional`, since their
                -- locations differ by `hloc2`), giving the *strict* `i < ℓ`
                -- (Lemma 3.9(ii)); combined with `po_reads_decreasing`'s
                -- unconditional "decreases by exactly one" bound on the
                -- closing edge, `i < ℓ = index(rl) ≤ j + 1` gives `i ≤ j`.
                push Not at hwlv
                obtain ⟨hwlv1, hwlv2, hwlv3, hwlv4⟩ := hwlv
                have hwlMem : wl ∈ G.Events := (G.rf_subset h').1
                have hwltid : wl.tid ∈ writerTids wl.loc :=
                  executionGraphOf_writers_confined I hsol hwlMem hwlop
                have hwlnb : wl.loc ∉ BridgeLoc := by rw [hwlrl_loc]; exact hnbrl
                have hwl8 := writeRead_guesser_crossing_loc wl.tid rj.tid wl.loc hwltid hwlnb
                  ⟨hwlv1, hwlv2, hwlv3, hwlv4⟩ hrj_verif hr1wl'
                have hwitidne : wi.tid ≠ wl.tid := by
                  intro heq
                  have hloceq := guesser_crossing_loc_functional wl.tid wi.loc wl.loc
                    (heq ▸ htgloc) hwl8
                  exact hloc2 hloceq.symm
                have hlt : G.index wi < G.index wl :=
                  (executionGraphOf_write_to_write_no_bridge_increasing I hsol hwi hwlop q'
                    hq'alt hq'min hnbq').2 hwitidne
                have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
                have hle1 : G.index rl ≤ G.index rj + 1 := by
                  rcases lt_trichotomy (G.index rj) (G.index rl) with hcon | heqidx | hgt
                  · obtain ⟨heqidx2, -, -⟩ :=
                      executionGraphOf_po_reads_decreasing I hsol hpo hrlop hrj hnbrl hnbrj hcon
                    have heqidx2' : G.index rl = G.index rj + 1 := heqidx2
                    omega
                  · omega
                  · omega
                omega
            rcases threadGroups_cover wi.tid with hg | hg | hg | hg
            · -- `tid(wi)` is an α-guesser.
              obtain ⟨g1, g2, g3, g4⟩ := hSguesserAlpha wi.tid hg
              exact hAllGuesserCase g1 g2 g3 g4
            · -- `tid(wi)` is a β-guesser.
              obtain ⟨g1, g2, g3, g4⟩ := hSguesserBeta wi.tid hg
              exact hAllGuesserCase g1 g2 g3 g4
            · -- `tid(wi)` is an `X`-checker.
              have hSclosed : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ XCheckerTids →
                  G.hb x y → y.tid ∈ XCheckerTids := by
                intro x y hx hxy
                by_contra hc
                exact executionGraphOf_xChecker_not_hb_outside I hsol hx hc hxy
              have hwltid : wl.tid ∈ XCheckerTids := hSclosed hg q'.sound
              have hrjrl : G.index rl ≤ G.index rj := by
                by_contra hcon
                push Not at hcon
                obtain ⟨-, -, w1, hw1rf, hgg⟩ :=
                  executionGraphOf_po_reads_decreasing I hsol hpo hrlop hrj hnbrl hnbrj hcon
                have hw1eq : w1 = wl := G.rf_unique hw1rf h'
                rw [hw1eq] at hgg
                obtain ⟨g1, g2, g3, g4⟩ := xCheckerTids_not_guesser wl.tid hwltid
                rcases hgg with hgg | hgg | hgg | hgg
                exacts [g1 hgg, g2 hgg, g3 hgg, g4 hgg]
              have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
              omega
            · -- `tid(wi)` is a `Y`-checker (symmetric).
              have hSclosed : ∀ ⦃x y : Event (domainOf I)⦄, x.tid ∈ YCheckerTids →
                  G.hb x y → y.tid ∈ YCheckerTids := by
                intro x y hx hxy
                by_contra hc
                exact executionGraphOf_yChecker_not_hb_outside I hsol hx hc hxy
              have hwltid : wl.tid ∈ YCheckerTids := hSclosed hg q'.sound
              have hrjrl : G.index rl ≤ G.index rj := by
                by_contra hcon
                push Not at hcon
                obtain ⟨-, -, w1, hw1rf, hgg⟩ :=
                  executionGraphOf_po_reads_decreasing I hsol hpo hrlop hrj hnbrl hnbrj hcon
                have hw1eq : w1 = wl := G.rf_unique hw1rf h'
                rw [hw1eq] at hgg
                obtain ⟨g1, g2, g3, g4⟩ := yCheckerTids_not_guesser wl.tid hwltid
                rcases hgg with hgg | hgg | hgg | hgg
                exacts [g1 hgg, g2 hgg, g3 hgg, g4 hgg]
              have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
              omega

/-- Lemma 3.3's write-coherence obligation (Section 3.5, paragraph
write-coherence): any `mo`-edge of `G` has `i ≤ j` by construction (`traceMo`), while
`wj ⟶hb wi` would give `j < i` (`executionGraphOf_hb_writes_increasing`). -/
theorem executionGraphOf_write_coherence (I : PCPInstance) (hsol : I.HasSolution) :
    ∀ e, ¬ Relation.Comp (executionGraphOf I hsol).mo (executionGraphOf I hsol).hb e e := by
  set G := executionGraphOf I hsol with hG
  rintro wi ⟨wj, hmo, hhb⟩
  have hmo' : traceEventsMo I (traceRf_valid_general I hsol).choose wi wj := hmo
  obtain ⟨hwiMem, hwjMem, hwiwt, hwjwt, hloc, hraw⟩ := hmo'
  have hEvents : G.Events = traceEvents (traceRf_valid_general I hsol).choose := rfl
  have hpoEq : G.po = traceEventsPo (traceRf_valid_general I hsol).choose := rfl
  have hi1 : G.index wi = rawIndex (traceRf_valid_general I hsol).choose wi :=
    G.index_eq_rawIndex (traceRf_valid_general I hsol).choose hEvents hpoEq hwiMem
  have hi2 : G.index wj = rawIndex (traceRf_valid_general I hsol).choose wj :=
    G.index_eq_rawIndex (traceRf_valid_general I hsol).choose hEvents hpoEq hwjMem
  have hle : G.index wi ≤ G.index wj := by
    rw [hi1, hi2]
    rcases hraw with h | ⟨h, -⟩
    · exact le_of_lt h
    · exact le_of_eq h
  have hlt : G.index wj < G.index wi :=
    executionGraphOf_hb_writes_increasing I hsol hwjwt hwiwt hloc.symm hhb
  omega

/-- The `i = j` case of `traceMo` (`G`'s `mo`): `⟨w1,w2,u⟩` is one of
Eq. (21)'s eight triples, with `w1` on a checker and `w2` on a guesser or
primed guesser. (Stated without parameters so that `decide` applies.) -/
theorem traceMo_tieBreak_dispatch :
    ∀ (t1 t2 : Tid) (u : Loc),
      ((t1 = Tid.checkX ∧ t2 = Tid.guessAX ∧ u = Loc.xA) ∨
       (t1 = Tid.checkX ∧ t2 = Tid.guessBX ∧ u = Loc.xB) ∨
       (t1 = Tid.checkY ∧ t2 = Tid.guessAY ∧ u = Loc.yA) ∨
       (t1 = Tid.checkY ∧ t2 = Tid.guessBY ∧ u = Loc.yB) ∨
       (t1 = Tid.primeCheckX ∧ t2 = Tid.primeAX ∧ u = Loc.xA') ∨
       (t1 = Tid.primeCheckX ∧ t2 = Tid.primeBX ∧ u = Loc.xB') ∨
       (t1 = Tid.primeCheckY ∧ t2 = Tid.primeAY ∧ u = Loc.yA') ∨
       (t1 = Tid.primeCheckY ∧ t2 = Tid.primeBY ∧ u = Loc.yB')) →
      t1 ≠ t2 ∧
      (t1 = Tid.checkX ∨ t1 = Tid.primeCheckX ∨ t1 = Tid.checkY ∨ t1 = Tid.primeCheckY) ∧
      (t2 ≠ Tid.checkX ∧ t2 ≠ Tid.primeCheckX ∧ t2 ≠ Tid.checkY ∧ t2 ≠ Tid.primeCheckY) := by
  intro t1 t2 u h
  rcases h with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ |
    ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;> decide

/-- A non-primed guesser writes no primed checker-shared location, and each
primed guesser writes only its own. (Stated without parameters so that
`decide` applies.) -/
theorem writerTids_primed_dispatch :
    ∀ (t : Tid) (u : Loc), t ∈ writerTids u →
      ((t = Tid.guessAX ∨ t = Tid.guessBX ∨ t = Tid.guessAY ∨ t = Tid.guessBY) →
        u ≠ Loc.xA' ∧ u ≠ Loc.xB' ∧ u ≠ Loc.yA' ∧ u ≠ Loc.yB') ∧
      ((u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.yA' ∨ u = Loc.yB') →
        (t = Tid.primeAX → u = Loc.xA') ∧ (t = Tid.primeBX → u = Loc.xB') ∧
        (t = Tid.primeAY → u = Loc.yA') ∧ (t = Tid.primeBY → u = Loc.yB')) := by
  decide

/-- Each of the eight guesser/primed-guesser threads writes exactly one of
the locations `xA,xB,xA',xB',yA,yB,yA',yB'` read by the checkers. (Stated
without parameters so that `decide` applies.) -/
theorem writerTids_guessAX_checker_loc :
    ∀ (tv : Tid) (u : Loc), Tid.guessAX ∈ writerTids u →
      ((tv = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (tv = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (tv = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (tv = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      u = Loc.xA := by decide

theorem writerTids_guessBX_checker_loc :
    ∀ (tv : Tid) (u : Loc), Tid.guessBX ∈ writerTids u →
      ((tv = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (tv = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (tv = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (tv = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      u = Loc.xB := by decide

theorem writerTids_guessAY_checker_loc :
    ∀ (tv : Tid) (u : Loc), Tid.guessAY ∈ writerTids u →
      ((tv = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (tv = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (tv = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (tv = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      u = Loc.yA := by decide

theorem writerTids_guessBY_checker_loc :
    ∀ (tv : Tid) (u : Loc), Tid.guessBY ∈ writerTids u →
      ((tv = Tid.checkX ∧ (u = Loc.xA ∨ u = Loc.xB ∨ u = Loc.xA' ∨ u = Loc.xB')) ∨
       (tv = Tid.primeCheckX ∧ (u = Loc.xA' ∨ u = Loc.xB' ∨ u = Loc.xA ∨ u = Loc.xB)) ∨
       (tv = Tid.checkY ∧ (u = Loc.yA ∨ u = Loc.yB ∨ u = Loc.yA' ∨ u = Loc.yB')) ∨
       (tv = Tid.primeCheckY ∧ (u = Loc.yA' ∨ u = Loc.yB' ∨ u = Loc.yA ∨ u = Loc.yB))) →
      u = Loc.yB := by decide

/-- Two distinct threads in the same `AlphaGuesserTids`/`BetaGuesserTids`
group and on the same `ThreadDomX`/`ThreadDomY` side are a guesser and its
primed partner. (Stated without parameters so that `decide` applies.) -/
theorem alphaBetaXY_pair_dispatch :
    ∀ (t1 t2 : Tid),
      ((t1 ∈ AlphaGuesserTids ∧ t2 ∈ AlphaGuesserTids) ∨
        (t1 ∈ BetaGuesserTids ∧ t2 ∈ BetaGuesserTids)) →
      ((t1 ∈ ThreadDomX ∧ t2 ∈ ThreadDomX) ∨ (t1 ∈ ThreadDomY ∧ t2 ∈ ThreadDomY)) →
      t1 ≠ t2 →
      (t1 = Tid.guessAX ∧ t2 = Tid.primeAX) ∨ (t1 = Tid.primeAX ∧ t2 = Tid.guessAX) ∨
      (t1 = Tid.guessBX ∧ t2 = Tid.primeBX) ∨ (t1 = Tid.primeBX ∧ t2 = Tid.guessBX) ∨
      (t1 = Tid.guessAY ∧ t2 = Tid.primeAY) ∨ (t1 = Tid.primeAY ∧ t2 = Tid.guessAY) ∨
      (t1 = Tid.guessBY ∧ t2 = Tid.primeBY) ∨ (t1 = Tid.primeBY ∧ t2 = Tid.guessBY) := by
  intro t1 t2 hab hxy hne
  revert hne hxy hab
  revert t2 t1
  decide

set_option maxHeartbeats 1000000 in
-- The proof's context grows to about 70 hypotheses in its deepest case, so
-- elaboration steps there are slow.
/-- Lemma 3.3's read-coherence obligation (Section 3.5, paragraph
read-coherence): given `w1 ⟶rf r1` and `w1 ⟶mo w2` (so `i ≤ j`), `w2 ⟶̸hb r1`. The
case `i < j` is Lemma 3.13. If `i = j`, `⟨w1,r1,w2⟩` is one of
Eq. (21)'s eight triples (`traceMo_tieBreak_dispatch`), and a minimal
`hb`-path `w2 ⟶hb r1` is excluded by the case analysis of Lemma 3.13,
now with strict inequalities. In the case where the crossing write `wℓ` is a
guesser and `u` is primed, the closing edge may decrease by one, so the
sharper `i + 1 < ℓ` of Lemma 3.11 is used; `wℓ`'s thread is pinned
to `w2`'s primed partner by the thread-level `hb` separation (Fig. 4) (`α`/`β`),
`executionGraphOf_threadDomX_step_closed`/`_threadDomY_step_closed` (`x`/`y`),
and `guesser_crossing_loc_functional`. -/
theorem executionGraphOf_read_coherence (I : PCPInstance) (hsol : I.HasSolution) :
    ∀ e, ¬ Relation.Comp (Relation.Comp (executionGraphOf I hsol).mo (executionGraphOf I hsol).hb)
      (flip (executionGraphOf I hsol).rf) e e := by
  set G := executionGraphOf I hsol with hG
  rintro w1 ⟨r1, ⟨w2, hmo, hhb⟩, hrf⟩
  have hEvents : G.Events = traceEvents (traceRf_valid_general I hsol).choose := rfl
  have hpoEq : G.po = traceEventsPo (traceRf_valid_general I hsol).choose := rfl
  have hw1wt : w1.op = .wt := (G.rf_subset hrf).2.2.1
  have hr1rd : r1.op = .rd := (G.rf_subset hrf).2.2.2.1
  have hloc1r : w1.loc = r1.loc := (G.rf_subset hrf).2.2.2.2
  have hidxr1 : G.index w1 = G.index r1 := executionGraphOf_rf_index_eq I hsol hrf
  have hmo' : traceEventsMo I (traceRf_valid_general I hsol).choose w1 w2 := hmo
  obtain ⟨hw1Mem, hw2Mem, hw1wt', hw2wt, hloc12, hraw⟩ := hmo'
  have hi1 : G.index w1 = rawIndex (traceRf_valid_general I hsol).choose w1 :=
    G.index_eq_rawIndex _ hEvents hpoEq hw1Mem
  have hi2 : G.index w2 = rawIndex (traceRf_valid_general I hsol).choose w2 :=
    G.index_eq_rawIndex _ hEvents hpoEq hw2Mem
  have hle : G.index w1 ≤ G.index w2 := by
    rw [hi1, hi2]
    rcases hraw with h | ⟨h, -⟩
    · exact le_of_lt h
    · exact le_of_eq h
  rcases eq_or_lt_of_le hle with heq | hlt
  swap
  · have hbound := executionGraphOf_hb_write_read I hsol hw2wt hr1rd (hloc12.symm.trans hloc1r) hhb
    exact absurd (lt_of_lt_of_le hlt hbound) (by rw [← hidxr1]; exact lt_irrefl _)
  exfalso
  have hrawEq : rawIndex (traceRf_valid_general I hsol).choose w1 =
      rawIndex (traceRf_valid_general I hsol).choose w2 := by
    rw [← hi1, ← hi2]; exact heq
  have h8 := hraw.resolve_left (by omega)
  obtain ⟨htidne, htid1, htid2⟩ := traceMo_tieBreak_dispatch w1.tid w2.tid w1.loc h8.2
  have hw1tid : w1.tid ∈ writerTids w1.loc := executionGraphOf_writers_confined I hsol hw1Mem hw1wt'
  have hw2confined : w2.tid ∈ writerTids w2.loc :=
    executionGraphOf_writers_confined I hsol hw2Mem hw2wt
  have hw2wt2 : w2.tid ∈ writerTids w1.loc := by rwa [← hloc12] at hw2confined
  obtain ⟨hdomWW, hnbU⟩ := writerTids_two_diff_dom w1.loc w1.tid w2.tid hw1tid hw2wt2 htidne
  have hw1nb : ¬ w1.IsBridge := hnbU
  have hr1nb : ¬ r1.IsBridge := by unfold Event.IsBridge; rw [← hloc1r]; exact hnbU
  have hw2nb : ¬ w2.IsBridge := by unfold Event.IsBridge; rw [← hloc12]; exact hnbU
  obtain ⟨p, hmin⟩ := executionGraphOf_hb_minimal I hsol hhb
  have hp : p.IsAlternating := p.isAlternating_of_isMinimal hmin
  match p with
  | .single_po hpo =>
      obtain ⟨-, hr1Mem, htid⟩ := G.po_subset hpo
      have hrtid := executionGraphOf_reads_confined I hsol hr1Mem hr1rd
      rw [← htid, hloc1r.symm.trans hloc12] at hrtid
      rcases writeRead_selfthread_confined w2.tid w2.loc hw2confined hrtid with
        ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
      · exact htid2.1 ht
      · exact htid2.2.2.1 ht
      · exact htid2.2.1 ht
      · exact htid2.2.2.2 ht
  | .single_rf hrf2 =>
      exact htidne (congrArg Event.tid (G.rf_unique hrf2 hrf).symm)
  | .tail_rf (b := wl) p' hrf2 =>
      have hweq : wl = w1 := G.rf_unique hrf2 hrf
      subst hweq
      clear hi1 hi2 hrawEq h8 hraw
      have hstrict : G.index w2 < G.index wl :=
        executionGraphOf_hb_writes_increasing I hsol hw2wt hw1wt hloc12.symm p'.sound
      omega
  | .tail_po (b := rl) p' hpo =>
      clear hi1 hi2 hrawEq h8 hraw
      have hpCopy := hp
      obtain ⟨hp'alt, hp'lastrf⟩ := hpCopy
      cases p' with
      | single_po h' => exact absurd trivial hp'lastrf
      | tail_po q' h' => exact absurd trivial hp'lastrf
      | single_rf h' =>
          have hrlop : rl.op = .rd := (G.rf_subset h').2.2.2.1
          have hrlloc : rl.loc = w2.loc := (G.rf_subset h').2.2.2.2.symm
          have hidx : G.index w2 = G.index rl := executionGraphOf_rf_index_eq I hsol h'
          have hlt2 : G.index rl < G.index r1 :=
            executionGraphOf_index_lt_of_po_sameLocOp I hsol hpo
              (hrlloc.trans (hloc12.symm.trans hloc1r)) (hrlop.trans hr1rd.symm)
          omega
      | tail_rf q' h' =>
          rename_i wl
          have hrlop : rl.op = .rd := (G.rf_subset h').2.2.2.1
          have hwlop : wl.op = .wt := (G.rf_subset h').2.2.1
          have hwlrl_loc : wl.loc = rl.loc := (G.rf_subset h').2.2.2.2
          by_cases hloc2 : wl.loc = w2.loc
          · -- `loc(wℓ) = u`.
            have hstrict1 : G.index w2 < G.index wl :=
              executionGraphOf_hb_writes_increasing I hsol hw2wt hwlop hloc2.symm q'.sound
            have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
            have hrlr1loc : rl.loc = r1.loc :=
              hwlrl_loc.symm.trans (hloc2.trans (hloc12.symm.trans hloc1r))
            have hlt2 : G.index rl < G.index r1 :=
              executionGraphOf_index_lt_of_po_sameLocOp I hsol hpo hrlr1loc (hrlop.trans hr1rd.symm)
            omega
          · -- `loc(wℓ) ≠ u`: shared preamble, matching Lemma 3.13's
            -- own "hAllGuesserCase" setup exactly (`w2`/`r1` in place of its
            -- `wi`/`rj`).
            have hr1MemViaRf : r1 ∈ G.Events := (G.rf_subset hrf).2.1
            have hr1confAtR1 := executionGraphOf_reads_confined I hsol hr1MemViaRf hr1rd
            have hrtidR1 := hr1confAtR1
            rw [← hloc1r] at hrtidR1
            have hdom2 :=
              writeRead_diffThread_sameDom w2.tid r1.tid w1.loc hw2wt2 hw1nb hrtidR1
            have hnbAll := executionGraphOf_write_to_write_no_bridge I hsol hw2nb hr1nb hdom2 _
              hp hmin
            obtain ⟨hnbp', -⟩ := hnbAll
            obtain ⟨hnbq', hnbrl⟩ := hnbp'
            have hm := hmin
            simp only [Path.IsMinimal, Path.poThreads] at hm
            have hq'min : q'.poThreads.Nodup := (List.nodup_append.mp hm).1
            obtain ⟨hq'alt, -⟩ := hp'alt
            have hrltid : rl.tid = r1.tid := (G.po_subset hpo).2.2
            have hne : rl.loc ≠ r1.loc := by
              rw [← hwlrl_loc, ← (hloc12.symm.trans hloc1r)]; exact hloc2
            have hr1conf := executionGraphOf_reads_confined I hsol
              ((G.po_subset hpo).1) hrlop
            rw [hrltid] at hr1conf
            have hr1_verif := reads_two_nonbridge_locs_checker r1.tid rl.loc r1.loc hne hnbrl
              hr1nb hr1conf hr1confAtR1
            have hr1conf2w2' :=
              reads_confined_checker_filter r1.tid w1.loc hrtidR1 hr1_verif
            have hr1confwl := hr1conf
            rw [← hwlrl_loc] at hr1confwl
            have hr1confwl' :=
              reads_confined_checker_filter r1.tid wl.loc hr1confwl hr1_verif
            have htgloc := writeRead_guesser_crossing_loc w2.tid r1.tid w1.loc hw2wt2 hw1nb htid2
              hr1_verif hr1conf2w2'
            by_cases hwlv : wl.tid = Tid.checkX ∨ wl.tid = Tid.primeCheckX ∨
                wl.tid = Tid.checkY ∨ wl.tid = Tid.primeCheckY
            · -- `wℓ` is already a checker: trivial tid-mismatch gives a
              -- strict margin, and the closing edge is exact (no guesser can
              -- write `wℓ`, contradicting `hcon`).
              have hwitidne : w2.tid ≠ wl.tid := by
                rcases hwlv with h | h | h | h <;> rw [h]
                exacts [htid2.1, htid2.2.1, htid2.2.2.1, htid2.2.2.2]
              have hstrict1' : G.index w2 < G.index wl :=
                (executionGraphOf_write_to_write_no_bridge_increasing I hsol hw2wt hwlop q'
                  hq'alt hq'min hnbq').2 hwitidne
              have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
              have hrjrl : G.index rl ≤ G.index r1 := by
                by_contra hcon
                push Not at hcon
                obtain ⟨-, -, w1', hw1'rf, hgg⟩ :=
                  executionGraphOf_po_reads_decreasing I hsol hpo hrlop hr1rd hnbrl hr1nb hcon
                have hw1'eq : w1' = wl := G.rf_unique hw1'rf h'
                rw [hw1'eq] at hgg
                rcases hwlv with hwlv | hwlv | hwlv | hwlv <;> rw [hwlv] at hgg <;>
                  rcases hgg with hgg | hgg | hgg | hgg <;> exact Tid.noConfusion hgg
              omega
            · -- `wℓ` is still a guesser: the genuine crossing.
              push Not at hwlv
              obtain ⟨hwlv1, hwlv2, hwlv3, hwlv4⟩ := hwlv
              have hwlMem : wl ∈ G.Events := (G.rf_subset h').1
              have hwltid : wl.tid ∈ writerTids wl.loc :=
                executionGraphOf_writers_confined I hsol hwlMem hwlop
              have hwlnb : ¬ wl.IsBridge := by rw [Event.IsBridge, hwlrl_loc]; exact hnbrl
              have hwl8 := writeRead_guesser_crossing_loc wl.tid r1.tid wl.loc hwltid hwlnb
                ⟨hwlv1, hwlv2, hwlv3, hwlv4⟩ hr1_verif hr1confwl'
              have hwitidne : w2.tid ≠ wl.tid := by
                intro heqtid
                have hloceq := guesser_crossing_loc_functional wl.tid w1.loc wl.loc
                  (heqtid ▸ htgloc) hwl8
                exact hloc2 (hloceq.symm.trans hloc12)
              by_cases hprimed : w1.loc = Loc.xA' ∨ w1.loc = Loc.xB' ∨
                  w1.loc = Loc.yA' ∨ w1.loc = Loc.yB'
              · -- Primed `u`: need the sharper Lemma 3.11 margin, so
                -- `wℓ`'s thread must be pinned exactly, not just shown
                -- different from `w2`'s.
                have hw2AlphaOrBeta : w2.tid ∈ AlphaGuesserTids ∨ w2.tid ∈ BetaGuesserTids := by
                  rcases threadGroups_cover w2.tid with hg | hg | hg | hg
                  · exact Or.inl hg
                  · exact Or.inr hg
                  · exact absurd (Finset.mem_insert.mp hg)
                      (not_or.mpr ⟨htid2.1, fun h => htid2.2.1 (Finset.mem_singleton.mp h)⟩)
                  · exact absurd (Finset.mem_insert.mp hg)
                      (not_or.mpr ⟨htid2.2.2.1, fun h => htid2.2.2.2 (Finset.mem_singleton.mp h)⟩)
                have hwlAlphaOrBeta : wl.tid ∈ AlphaGuesserTids ∨ wl.tid ∈ BetaGuesserTids := by
                  rcases threadGroups_cover wl.tid with hg | hg | hg | hg
                  · exact Or.inl hg
                  · exact Or.inr hg
                  · exact absurd (Finset.mem_insert.mp hg)
                      (not_or.mpr ⟨hwlv1, fun h => hwlv2 (Finset.mem_singleton.mp h)⟩)
                  · exact absurd (Finset.mem_insert.mp hg)
                      (not_or.mpr ⟨hwlv3, fun h => hwlv4 (Finset.mem_singleton.mp h)⟩)
                have hwlSameGroup :
                    (w2.tid ∈ AlphaGuesserTids ∧ wl.tid ∈ AlphaGuesserTids) ∨
                    (w2.tid ∈ BetaGuesserTids ∧ wl.tid ∈ BetaGuesserTids) := by
                  rcases hw2AlphaOrBeta with hw2A | hw2B
                  · rcases hwlAlphaOrBeta with hwlA | hwlB
                    · exact Or.inl ⟨hw2A, hwlA⟩
                    · exact absurd q'.sound (executionGraphOf_alpha_not_hb_beta I hsol hw2A hwlB)
                  · rcases hwlAlphaOrBeta with hwlA | hwlB
                    · exact absurd q'.sound (executionGraphOf_beta_not_hb_alpha I hsol hw2B hwlA)
                    · exact Or.inr ⟨hw2B, hwlB⟩
                have hwlSameXY : (w2.tid ∈ ThreadDomX ∧ wl.tid ∈ ThreadDomX) ∨
                    (w2.tid ∈ ThreadDomY ∧ wl.tid ∈ ThreadDomY) := by
                  rcases hdomWW with ⟨-, hw2X⟩ | ⟨-, hw2Y⟩
                  · exact Or.inl ⟨hw2X, q'.allEventsSatisfy_right
                      (q'.allEventsSatisfy_of_step_closed
                        (executionGraphOf_threadDomX_step_closed I hsol) hw2X hnbq')⟩
                  · exact Or.inr ⟨hw2Y, q'.allEventsSatisfy_right
                      (q'.allEventsSatisfy_of_step_closed
                        (executionGraphOf_threadDomY_step_closed I hsol) hw2Y hnbq')⟩
                -- Combining group and side pins `wℓ.tid` to `w2.tid`'s own
                -- 2-element guesser/primed-guesser pair; `hwitidne` excludes
                -- `w2.tid` itself, leaving its unique partner.
                have hwlPair : (w2.tid = Tid.guessAX ∧ wl.tid = Tid.primeAX) ∨
                    (w2.tid = Tid.primeAX ∧ wl.tid = Tid.guessAX) ∨
                    (w2.tid = Tid.guessBX ∧ wl.tid = Tid.primeBX) ∨
                    (w2.tid = Tid.primeBX ∧ wl.tid = Tid.guessBX) ∨
                    (w2.tid = Tid.guessAY ∧ wl.tid = Tid.primeAY) ∨
                    (w2.tid = Tid.primeAY ∧ wl.tid = Tid.guessAY) ∨
                    (w2.tid = Tid.guessBY ∧ wl.tid = Tid.primeBY) ∨
                    (w2.tid = Tid.primeBY ∧ wl.tid = Tid.guessBY) :=
                  alphaBetaXY_pair_dispatch w2.tid wl.tid hwlSameGroup hwlSameXY hwitidne
                rcases hwlPair with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
                · -- `w2.tid = guessAX`: never writes a primed location, so
                  -- every `hprimed` branch is vacuous.
                  have hne4 := (writerTids_primed_dispatch w2.tid w1.loc hw2wt2).1 (Or.inl h1)
                  rcases hprimed with h | h | h | h
                  exacts [hne4.1 h, hne4.2.1 h, hne4.2.2.1 h, hne4.2.2.2 h]
                · -- `w2.tid = primeAX`: the real case, `u = xA'`.
                  have hw1loc : w1.loc = Loc.xA' :=
                    ((writerTids_primed_dispatch w2.tid w1.loc hw2wt2).2 hprimed).1 h1
                  have hw2loc : w2.loc = Loc.xA' := hloc12.symm.trans hw1loc
                  have hwlloc : wl.loc = Loc.xA := by
                    rw [h2] at hwltid
                    exact writerTids_guessAX_checker_loc r1.tid wl.loc hwltid hr1confwl'
                  have hgap : G.index w2 + 1 < G.index wl :=
                    executionGraphOf_hb_primeAX_guessAX_gap I hsol h1 hw2loc hw2wt h2 hwlloc
                      hwlop q'.sound
                  have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
                  have hle1 : G.index rl ≤ G.index r1 + 1 := by
                    rcases lt_trichotomy (G.index r1) (G.index rl) with hcon | heqidx | hgt
                    · obtain ⟨heqidx2, -, -⟩ :=
                        executionGraphOf_po_reads_decreasing I hsol hpo hrlop hr1rd hnbrl hr1nb hcon
                      have heqidx2' : G.index rl = G.index r1 + 1 := heqidx2
                      omega
                    · omega
                    · omega
                  omega
                · -- `w2.tid = guessBX`: vacuous, as above.
                  have hne4 := (writerTids_primed_dispatch w2.tid w1.loc hw2wt2).1
                    (Or.inr (Or.inl h1))
                  rcases hprimed with h | h | h | h
                  exacts [hne4.1 h, hne4.2.1 h, hne4.2.2.1 h, hne4.2.2.2 h]
                · -- `w2.tid = primeBX`: `u = xB'`.
                  have hw1loc : w1.loc = Loc.xB' :=
                    ((writerTids_primed_dispatch w2.tid w1.loc hw2wt2).2 hprimed).2.1 h1
                  have hw2loc : w2.loc = Loc.xB' := hloc12.symm.trans hw1loc
                  have hwlloc : wl.loc = Loc.xB := by
                    rw [h2] at hwltid
                    exact writerTids_guessBX_checker_loc r1.tid wl.loc hwltid hr1confwl'
                  have hgap : G.index w2 + 1 < G.index wl :=
                    executionGraphOf_hb_primeBX_guessBX_gap I hsol h1 hw2loc hw2wt h2 hwlloc
                      hwlop q'.sound
                  have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
                  have hle1 : G.index rl ≤ G.index r1 + 1 := by
                    rcases lt_trichotomy (G.index r1) (G.index rl) with hcon | heqidx | hgt
                    · obtain ⟨heqidx2, -, -⟩ :=
                        executionGraphOf_po_reads_decreasing I hsol hpo hrlop hr1rd hnbrl hr1nb hcon
                      have heqidx2' : G.index rl = G.index r1 + 1 := heqidx2
                      omega
                    · omega
                    · omega
                  omega
                · -- `w2.tid = guessAY`: vacuous, as above.
                  have hne4 := (writerTids_primed_dispatch w2.tid w1.loc hw2wt2).1
                    (Or.inr (Or.inr (Or.inl h1)))
                  rcases hprimed with h | h | h | h
                  exacts [hne4.1 h, hne4.2.1 h, hne4.2.2.1 h, hne4.2.2.2 h]
                · -- `w2.tid = primeAY`: `u = yA'`.
                  have hw1loc : w1.loc = Loc.yA' :=
                    ((writerTids_primed_dispatch w2.tid w1.loc hw2wt2).2 hprimed).2.2.1 h1
                  have hw2loc : w2.loc = Loc.yA' := hloc12.symm.trans hw1loc
                  have hwlloc : wl.loc = Loc.yA := by
                    rw [h2] at hwltid
                    exact writerTids_guessAY_checker_loc r1.tid wl.loc hwltid hr1confwl'
                  have hgap : G.index w2 + 1 < G.index wl :=
                    executionGraphOf_hb_primeAY_guessAY_gap I hsol h1 hw2loc hw2wt h2 hwlloc
                      hwlop q'.sound
                  have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
                  have hle1 : G.index rl ≤ G.index r1 + 1 := by
                    rcases lt_trichotomy (G.index r1) (G.index rl) with hcon | heqidx | hgt
                    · obtain ⟨heqidx2, -, -⟩ :=
                        executionGraphOf_po_reads_decreasing I hsol hpo hrlop hr1rd hnbrl hr1nb hcon
                      have heqidx2' : G.index rl = G.index r1 + 1 := heqidx2
                      omega
                    · omega
                    · omega
                  omega
                · -- `w2.tid = guessBY`: vacuous, as above.
                  have hne4 := (writerTids_primed_dispatch w2.tid w1.loc hw2wt2).1
                    (Or.inr (Or.inr (Or.inr h1)))
                  rcases hprimed with h | h | h | h
                  exacts [hne4.1 h, hne4.2.1 h, hne4.2.2.1 h, hne4.2.2.2 h]
                · -- `w2.tid = primeBY`: `u = yB'`.
                  have hw1loc : w1.loc = Loc.yB' :=
                    ((writerTids_primed_dispatch w2.tid w1.loc hw2wt2).2 hprimed).2.2.2 h1
                  have hw2loc : w2.loc = Loc.yB' := hloc12.symm.trans hw1loc
                  have hwlloc : wl.loc = Loc.yB := by
                    rw [h2] at hwltid
                    exact writerTids_guessBY_checker_loc r1.tid wl.loc hwltid hr1confwl'
                  have hgap : G.index w2 + 1 < G.index wl :=
                    executionGraphOf_hb_primeBY_guessBY_gap I hsol h1 hw2loc hw2wt h2 hwlloc
                      hwlop q'.sound
                  have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
                  have hle1 : G.index rl ≤ G.index r1 + 1 := by
                    rcases lt_trichotomy (G.index r1) (G.index rl) with hcon | heqidx | hgt
                    · obtain ⟨heqidx2, -, -⟩ :=
                        executionGraphOf_po_reads_decreasing I hsol hpo hrlop hr1rd hnbrl hr1nb hcon
                      have heqidx2' : G.index rl = G.index r1 + 1 := heqidx2
                      omega
                    · omega
                    · omega
                  omega
              · -- Non-primed `u`: the margin-1 strict bound plus the exact
                -- (non-decreasing) closing edge already suffice.
                have hstrict1'' : G.index w2 < G.index wl :=
                  (executionGraphOf_write_to_write_no_bridge_increasing I hsol hw2wt hwlop q'
                    hq'alt hq'min hnbq').2 hwitidne
                have hidx2 : G.index wl = G.index rl := executionGraphOf_rf_index_eq I hsol h'
                have hrjrl : G.index rl ≤ G.index r1 := by
                  by_contra hcon
                  push Not at hcon
                  obtain ⟨-, hcase, -⟩ :=
                    executionGraphOf_po_reads_decreasing I hsol hpo hrlop hr1rd hnbrl hr1nb hcon
                  have hcase' : r1.loc = Loc.xA' ∨ r1.loc = Loc.xB' ∨ r1.loc = Loc.yA' ∨
                      r1.loc = Loc.yB' := by
                    rcases hcase with hc | hc
                    · rcases hc with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
                      exacts [Or.inl h, Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inl h)]
                    · rcases hc with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
                      exacts [Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h)),
                        Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr h))]
                  exact hprimed (hloc1r ▸ hcase')
                omega

/-- **Paper:** §3.5, ¶ Proof of Lemma 3.3.

RA-consistency of `G`: `executionGraphOf` is RA-consistent, from Lemma 3.6
and the two coherence obligations. -/
theorem executionGraphOf_consistent (I : PCPInstance) (hsol : I.HasSolution) :
    (executionGraphOf I hsol).RAConsistent where
  irr_hb := executionGraphOf_hb_irrefl I hsol
  write_coherence := executionGraphOf_write_coherence I hsol
  read_coherence := executionGraphOf_read_coherence I hsol

end RAUndecidability
