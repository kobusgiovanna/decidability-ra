import RAUndecidability.Reduction.Soundness.NoSkipping

/-!
# Lemma 3.2

Lemma 3.2 of the paper, stated as in the paper: in every execution of
`ConcProg` in which all threads reach `term`, for each of the listed
`(writer, reader, location)` triples and every `i` such that the reader's
`i`-th read on the location exists, that read reads from the writer's `i`-th
write on the location.

`no_skipping_pairs` collects the 28 cases of Eq. (15)-(17), each proved in
`Soundness/NoSkipping.lean` in the form "an `rf`-edge from the writer's
`i`-th write to the reader's `k`-th read has `i = k`". What is added here is
the identification of the writer (`Soundness/NoSkipping.lean`): on the twelve
locations of Eq. (15) only the named thread writes at all
(`writer_of_single_writer`); on the eight two-writer locations of
Eq. (16)-(17), the value the read expects carries the writer's tag
(`writer_of_read_tag`).
-/

namespace RAUndecidability

/-- Eq. (15): the twelve `(writer, reader, location)`
triples, in the paper's order. Row 1: `w_i(g_α^{x'}, z_α^{x,x'}) ⟶rf
r_i(g_α^x, z_α^{x,x'})`, `w_i(g_α^x, z_α^{x',x}) ⟶rf r_i(g_α^{x'},
z_α^{x',x})`, and the same for `y`; row 2: the same for `β`; row 3: the
bridge locations `z^{x,y}` and `ℓ^{y,x}`. -/
def noSkipEdgesEq15 : List (Tid × Tid × Loc) :=
  [ (.primeAX, .guessAX, .zAxx'), (.guessAX, .primeAX, .zAx'x),
    (.primeAY, .guessAY, .zAyy'), (.guessAY, .primeAY, .zAy'y),
    (.primeBX, .guessBX, .zBxx'), (.guessBX, .primeBX, .zBx'x),
    (.primeBY, .guessBY, .zByy'), (.guessBY, .primeBY, .zBy'y),
    (.guessAX, .guessAY, .zAxy), (.guessAY, .guessAX, .ellAyx),
    (.guessBX, .guessBY, .zBxy), (.guessBY, .guessBX, .ellByx) ]

/-- Eq. (16): the eight triples between each checker
`c^x`, `c^y` and its primed partner, in the paper's order. -/
def noSkipEdgesEq16 : List (Tid × Tid × Loc) :=
  [ (.checkX, .primeCheckX, .xA), (.primeCheckX, .checkX, .xA'),
    (.checkX, .primeCheckX, .xB), (.primeCheckX, .checkX, .xB'),
    (.checkY, .primeCheckY, .yA), (.primeCheckY, .checkY, .yA'),
    (.checkY, .primeCheckY, .yB), (.primeCheckY, .checkY, .yB') ]

/-- Eq. (17): the eight triples from the guessers to the
checkers, in the paper's order. -/
def noSkipEdgesEq17 : List (Tid × Tid × Loc) :=
  [ (.guessAX, .checkX, .xA), (.primeAX, .primeCheckX, .xA'),
    (.guessBX, .checkX, .xB), (.primeBX, .primeCheckX, .xB'),
    (.guessAY, .checkY, .yA), (.primeAY, .primeCheckY, .yA'),
    (.guessBY, .checkY, .yB), (.primeBY, .primeCheckY, .yB') ]

/-- **Paper:** Lemma 3.2.

**Lemma 3.2**. Consider any
execution `G` of `ConcProg` where all threads reach `term`. For all `i` such
that the corresponding read event `r_i` exists in `G`, we have the `rf`-edges
`w_i(tw, x) ⟶rf r_i(tr, x)` for every `(tw, tr, x)` listed in Eq. (15)/(16) and Eq. (17). -/
theorem no_skipping_pairs (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) :
    (∀ c ∈ noSkipEdgesEq15, G.ReadsFromSameIndex c.1 c.2.1 c.2.2) ∧
    (∀ c ∈ noSkipEdgesEq16, G.ReadsFromSameIndex c.1 c.2.1 c.2.2) ∧
    (∀ c ∈ noSkipEdgesEq17, G.ReadsFromSameIndex c.1 c.2.1 c.2.2) := by
  have single : ∀ {tw tr : Tid} {x : Loc}, writerTids x = {tw} →
      (∀ {i k : ℕ} {ew er : Event (domainOf I)}, G.nthWrite tw x i = some ew →
        G.nthRead tr x k = some er → G.rf ew er → i = k) →
      G.ReadsFromSameIndex tw tr x := fun hx halign =>
    G.readsFromSameIndex_of (writer_of_single_writer I G hG hx) halign
  have hcX := checkX_run_of_reaches I G hG
  have hpX := primeCheckX_run_of_reaches I G hG
  have hcY := checkY_run_of_reaches I G hG
  have hpY := primeCheckY_run_of_reaches I G hG
  refine ⟨?_, ?_, ?_⟩
  · -- Eq. (15): single-writer locations.
    intro c hc
    simp only [noSkipEdgesEq15, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact single rfl (fun hew her hrf => no_skipping_guessAX_primeAX_zAxx' I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessAX_primeAX_zAx'x I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessAY_primeAY_zAyy' I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessAY_primeAY_zAy'y I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessBX_primeBX_zBxx' I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessBX_primeBX_zBx'x I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessBY_primeBY_zByy' I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessBY_primeBY_zBy'y I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessAX_guessAY_zAxy I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessAX_guessAY_ellAyx I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessBX_guessBY_zBxy I G hG _ _ hew her hrf)
    · exact single rfl (fun hew her hrf => no_skipping_guessBX_guessBY_ellByx I G hG _ _ hew her hrf)
  · -- Eq. (16): the writer is identified by the tag the read expects.
    intro c hc
    simp only [noSkipEdgesEq16, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hpX (fun e φ h => (PrimeCheckX.hasRead_writerTid I h φ).2.2.1 rfl))
        (fun hew her hrf => no_skipping_checkX_primeCheckX_xA I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hcX (fun e φ h => (CheckX.hasRead_writerTid I h φ).2.2.1 rfl))
        (fun hew her hrf => no_skipping_checkX_primeCheckX_xA' I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hpX (fun e φ h => (PrimeCheckX.hasRead_writerTid I h φ).2.2.2 rfl))
        (fun hew her hrf => no_skipping_checkX_primeCheckX_xB I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hcX (fun e φ h => (CheckX.hasRead_writerTid I h φ).2.2.2 rfl))
        (fun hew her hrf => no_skipping_checkX_primeCheckX_xB' I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hpY (fun e φ h => (PrimeCheckY.hasRead_writerTid I h φ).2.2.1 rfl))
        (fun hew her hrf => no_skipping_checkY_primeCheckY_yA I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hcY (fun e φ h => (CheckY.hasRead_writerTid I h φ).2.2.1 rfl))
        (fun hew her hrf => no_skipping_checkY_primeCheckY_yA' I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hpY (fun e φ h => (PrimeCheckY.hasRead_writerTid I h φ).2.2.2 rfl))
        (fun hew her hrf => no_skipping_checkY_primeCheckY_yB I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hcY (fun e φ h => (CheckY.hasRead_writerTid I h φ).2.2.2 rfl))
        (fun hew her hrf => no_skipping_checkY_primeCheckY_yB' I G hG _ _ hew her hrf)
  · -- Eq. (17): the writer is identified by the tag the read expects.
    intro c hc
    simp only [noSkipEdgesEq17, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hcX (fun e φ h => (CheckX.hasRead_writerTid I h φ).1 rfl))
        (fun hew her hrf => no_skipping_guessAX_checkX_xA I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hpX (fun e φ h => (PrimeCheckX.hasRead_writerTid I h φ).1 rfl))
        (fun hew her hrf => no_skipping_primeAX_primeCheckX_xA' I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hcX (fun e φ h => (CheckX.hasRead_writerTid I h φ).2.1 rfl))
        (fun hew her hrf => no_skipping_guessBX_checkX_xB I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hpX (fun e φ h => (PrimeCheckX.hasRead_writerTid I h φ).2.1 rfl))
        (fun hew her hrf => no_skipping_primeBX_primeCheckX_xB' I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hcY (fun e φ h => (CheckY.hasRead_writerTid I h φ).1 rfl))
        (fun hew her hrf => no_skipping_guessAY_checkY_yA I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hpY (fun e φ h => (PrimeCheckY.hasRead_writerTid I h φ).1 rfl))
        (fun hew her hrf => no_skipping_primeAY_primeCheckY_yA' I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hcY (fun e φ h => (CheckY.hasRead_writerTid I h φ).2.1 rfl))
        (fun hew her hrf => no_skipping_guessBY_checkY_yB I G hG _ _ hew her hrf)
    · exact G.readsFromSameIndex_of
        (writer_of_read_tag G hG hpY (fun e φ h => (PrimeCheckY.hasRead_writerTid I h φ).2.1 rfl))
        (fun hew her hrf => no_skipping_primeBY_primeCheckY_yB' I G hG _ _ hew her hrf)

end RAUndecidability
