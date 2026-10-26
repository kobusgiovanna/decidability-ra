import RAUndecidability.Reduction.Soundness
import RAUndecidability.Reduction.Completeness

/-!
# The reduction

`ConcProg I` reaches its final state iff `I` has a solution: the reduction
from PCP to state reachability under RA. It combines

* completeness (`completeness`, Lemma 3.3): a solution of `I` yields an
  execution of `ConcProg I` in which every thread reaches `term`;
* soundness (`soundness`, Lemma 3.1): any execution of `ConcProg I` in which
  every thread reaches `term` yields a solution of `I`.

Undecidability of PCP is neither proved nor assumed here: `reduction` does not
need it. The further corollary that would combine it with `reduction` to
conclude undecidability of `ReachesFinal` is out of scope, since it also needs
effectiveness of `I ↦ ConcProg I`, not mechanized here.
-/

namespace RAUndecidability

/-- **Paper:** §3.3, ¶ Reduction (Lemmas 3.1 + 3.3).

The reduction: `I` has a PCP solution iff `ConcProg I` has an execution in
which every thread reaches `term`. `completeness` (Lemma 3.3) proves
the forward direction, `I.HasSolution → (ConcProg I).ReachesFinal`;
`soundness` (Lemma 3.1, Lemma 3.1) proves the reverse direction,
`(ConcProg I).ReachesFinal → I.HasSolution`. -/
theorem reduction (I : PCPInstance) : I.HasSolution ↔ (ConcProg I).ReachesFinal :=
  ⟨completeness I, soundness I⟩

end RAUndecidability
