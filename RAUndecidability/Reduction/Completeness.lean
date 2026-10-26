import RAUndecidability.Reduction.Completeness.Consistency

/-!
# Completeness

Lemma 3.3, assembled from Section 3.5's
ingredients in `Completeness/`: the construction of `G`, the monotonicity
lemmas, and its RA-consistency.
-/

namespace RAUndecidability

/-- **Paper:** Lemma 3.3.

Lemma 3.3: if `I` has a
solution, `ConcProg I` has an execution reaching its final state.
`executionGraphOf I hsol` is the witness: membership in `RASemantics` is
`executionGraphOf_consistent` (`RAConsistent`) and `executionGraphOf_isWord`
(`IsWord`); reaching `ConcProg I`'s final state is
`executionGraphOf_reaches_final`. Only the term-appended branch of
reachability (§2.2) applies, since `ConcurrentProgram.final` sends every thread
to its own `final` state. -/
theorem completeness (I : PCPInstance) (hsol : I.HasSolution) :
    (ConcProg I).ReachesFinal :=
  ⟨executionGraphOf I hsol,
    ⟨executionGraphOf_consistent I hsol, fun t => executionGraphOf_isWord I hsol t⟩,
    fun t => ⟨fun h => absurd rfl h, fun _ => executionGraphOf_reaches_final I hsol t⟩⟩

end RAUndecidability
