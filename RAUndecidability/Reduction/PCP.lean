import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

/-!
# PCP instances

The "PCP" paragraph of Section 3: instances of Post's correspondence problem
and their solutions. -/

namespace RAUndecidability

/-- **Paper:** §3, ¶ Post's Correspondence Problem.

A PCP instance (§3): non-empty tuples `α`, `β` of non-empty words
over a finite alphabet `Γ`, indexed by `Fin n` (the paper's `[n] = {1,…,n}`,
0-indexed here as is standard in Lean). -/
structure PCPInstance where
  /-- The number of tile pairs. -/
  n : ℕ
  /-- `n > 0`: the tuples `α`, `β` are non-empty. -/
  hn : 0 < n
  /-- The tile alphabet. -/
  Γ : Type
  [ΓFintype : Fintype Γ]
  [ΓDecEq : DecidableEq Γ]
  /-- The top tiles. -/
  α : Fin n → List Γ
  /-- The bottom tiles. -/
  β : Fin n → List Γ
  /-- Every top tile is a non-empty word. -/
  hα : ∀ i, α i ≠ []
  /-- Every bottom tile is a non-empty word. -/
  hβ : ∀ i, β i ≠ []

attribute [instance] PCPInstance.ΓFintype
attribute [instance] PCPInstance.ΓDecEq

/-- `Fin I.n` is non-empty, given `hn`. -/
instance (I : PCPInstance) : Nonempty (Fin I.n) := ⟨⟨0, I.hn⟩⟩

/-- A solution of `I` (§3): a non-empty sequence `j_1, …, j_k ∈ [n]`
with `α_{j_1} ⋯ α_{j_k} = β_{j_1} ⋯ β_{j_k}`. -/
def PCPInstance.IsSolution (I : PCPInstance) (js : List (Fin I.n)) : Prop :=
  js ≠ [] ∧ (js.map I.α).flatten = (js.map I.β).flatten

/-- `I` has a solution (§3). -/
def PCPInstance.HasSolution (I : PCPInstance) : Prop :=
  ∃ js, I.IsSolution js

end RAUndecidability
