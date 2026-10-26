import RAUndecidability.ProgramSemantics.Syntax

/-!
# Derived forms

The "Derived forms" paragraph of the paper's Appendix A:

* App. A: the three derived command forms;
* App. A: the initial store.

Since `Vocabulary`'s `Expr`/`BExpr` are abstract, each derived form takes the
guards and expressions it needs (e.g. "`j ≤ N`", "`j + 1`") as parameters;
each docstring says what its parameters must denote.

`fstFalse` (`firstIt`) and `one` (`forLoop`) are `V.Expr`s, so `fst ← False`
and `j ← 1` are ordinary deterministic assignments; `ndetAssign` is used only
for genuine non-determinism (`NDet(X)`). -/

namespace RAUndecidability

variable {D : Domains} {V : Vocabulary D}

/-! ## The derived forms (App. A) -/

/-- **Paper:** App. A, ¶ Derived forms (`while NDet(X)`).

`while ndet(X) do C` (App. A): loop on a nondeterministic
choice from `X`, re-drawn each iteration.
`bGuard` must test whether `b` currently holds `True`. -/
def Command.whileNdet (b : V.LVar) (X : Finset V.LVal) (hX : X.Nonempty) (bGuard : V.BExpr)
    (C : Command D V) : Command D V :=
  .seq (.ndetAssign b X hX) (.whileLoop bGuard (.seq C (.ndetAssign b X hX)))

/-- **Paper:** App. A, ¶ Derived forms (`for`).

`for j ∈ 1,…,e do C` (App. A): bounded iteration, with the upper
bound evaluated once on entry.
`one` must evaluate to `1`, `leGuard` to "`j ≤ N`", and `incr` to "`j + 1`". -/
def Command.forLoop (j N : V.LVar) (e : V.Expr) (one : V.Expr) (leGuard : V.BExpr)
    (incr : V.Expr) (C : Command D V) : Command D V :=
  .seq (.assign j one)
    (.seq (.assign N e) (.whileLoop leGuard (.seq C (.assign j incr))))

/-- **Paper:** App. A, ¶ Derived forms (`First()`).

`if First() then C1 else C2` (App. A): `True` the first time this
syntactic occurrence executes, `False` thereafter.
`fst` is the fresh boolean of this occurrence of `First()` (one per syntactic
occurrence). `fstFalse` must evaluate to `False`, and `fstGuard` must read
`fst`'s current value. -/
def Command.firstIt (fst : V.LVar) (fstFalse : V.Expr) (fstGuard : V.BExpr)
    (C1 C2 : Command D V) : Command D V :=
  .ite fstGuard (.seq (.assign fst fstFalse) C1) C2

/-! ## The initial store (App. A) -/

/-- The initial store (App. A): every variable named in
`overrides` maps to its given value, every other variable maps to `default`.
The paper's choice (`vc`, `vcy` ↦ `0`, every `fst_ι` ↦ `True`) is supplied as
`overrides` when the twelve threads are built (`Reduction/ConcProg.lean`). -/
def Vocabulary.mkStore (V : Vocabulary D) (overrides : V.LVar → Option V.LVal)
    (default : V.LVal) : V.Store :=
  fun v => (overrides v).getD default

end RAUndecidability
