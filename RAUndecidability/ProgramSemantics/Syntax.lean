import RAUndecidability.Defs.Program
import Mathlib.Data.Fintype.Pi

/-!
# Syntax

The "Syntax" paragraph of the paper's Appendix A:

* App. A, Syntax: local variables, local values, stores, and expressions;
* App. A, Syntax: commands, including its closing sentence
  (`Command.IsProgram`, proved of each thread of Fig. 7 in
  `Reduction/Threads.lean`).
-/

namespace RAUndecidability

/-! ## Stores (App. A, Syntax) -/

/-- The local vocabulary of stores (App. A, Syntax): finite sets `LVar` of local
variables and `LVal` of local values, and three classes of pure expressions
over them, each with its own evaluation function.

`wt`/`rd` take expressions of their own class `VExpr`, evaluating into the
shared value domain `D.Val` (§2.1), while `Expr` (assignments)
evaluates into `LVal` and `BExpr` (guards) into `Bool`. -/
structure Vocabulary (D : Domains) where
  /-- The local variables. -/
  LVar : Type
  /-- The local values. -/
  LVal : Type
  [lvarFintype : Fintype LVar]
  [lvarDecEq : DecidableEq LVar]
  [lvalFintype : Fintype LVal]
  [lvalDecEq : DecidableEq LVal]
  /-- Expressions used in assignments, evaluating into `LVal`. -/
  Expr : Type
  eval : Expr → (LVar → LVal) → LVal
  /-- Guard expressions used in `if`/`while`, evaluating into `Bool`. -/
  BExpr : Type
  evalB : BExpr → (LVar → LVal) → Bool
  /-- Expressions used in `wt`/`rd`, evaluating into `D.Val`. -/
  VExpr : Type
  evalV : VExpr → (LVar → LVal) → D.Val

instance (D : Domains) (V : Vocabulary D) : Fintype V.LVar := V.lvarFintype
instance (D : Domains) (V : Vocabulary D) : DecidableEq V.LVar := V.lvarDecEq
instance (D : Domains) (V : Vocabulary D) : Fintype V.LVal := V.lvalFintype
instance (D : Domains) (V : Vocabulary D) : DecidableEq V.LVal := V.lvalDecEq

/-- A store (App. A, Syntax): a function from local variables to local
values. -/
def Vocabulary.Store (D : Domains) (V : Vocabulary D) : Type := V.LVar → V.LVal

/-- Stores are finite, since `LVar` and `LVal` are (`lvarFintype`,
`lvalFintype`) — the first half of the argument for finiteness of the induced LTS (App. A). -/
instance (D : Domains) (V : Vocabulary D) : Fintype (Vocabulary.Store D V) := by
  unfold Vocabulary.Store; infer_instance

/-! ## Commands (App. A, Syntax) -/

/-- **Paper:** App. A, ¶ Syntax.

Commands (App. A, Syntax). `loopSeq` is the runtime-only form
`C₁ ▷ C₂`: it does not occur in programs and arises only during execution,
marking the point at which a `break` is caught by its enclosing loop. -/
inductive Command (D : Domains) (V : Vocabulary D) : Type
  | skip
  | assign (v : V.LVar) (e : V.Expr)
  | ndetAssign (v : V.LVar) (X : Finset V.LVal) (hX : X.Nonempty)
  | write (u : D.Loc) (e : V.VExpr)
  | read (u : D.Loc) (e : V.VExpr)
  | seq (C1 C2 : Command D V)
  | ite (b : V.BExpr) (C1 C2 : Command D V)
  | whileLoop (b : V.BExpr) (C : Command D V)
  | brk
  | term
  | loopSeq (C1 C2 : Command D V)

/-- How many `term`s occur in `C`, counting `loopSeq`'s two children like
`seq`'s. `Command.IsProgram` requires it to be `1`. -/
def Command.TermCount {D : Domains} {V : Vocabulary D} : Command D V → ℕ
  | .skip => 0
  | .assign _ _ => 0
  | .ndetAssign _ _ _ => 0
  | .write _ _ => 0
  | .read _ _ => 0
  | .seq C1 C2 => C1.TermCount + C2.TermCount
  | .ite _ C1 C2 => C1.TermCount + C2.TermCount
  | .whileLoop _ C => C.TermCount
  | .brk => 0
  | .term => 1
  | .loopSeq C1 C2 => C1.TermCount + C2.TermCount

/-- Whether every `break` in `C` sits within the body of some `while`, and no
`loopSeq` occurs in `C` at all (`term`'s count is checked separately, by
`Command.TermCount`, since it recurs at a different position than these two).
`inWhile` records whether the walk is currently inside a `whileLoop`'s body;
it starts `false` at the top of `Command.IsProgram` and flips to `true` only
when recursing into a `whileLoop`'s body. -/
def Command.BreaksScopedNoLoopSeq {D : Domains} {V : Vocabulary D} (inWhile : Bool) :
    Command D V → Bool
  | .skip => true
  | .assign _ _ => true
  | .ndetAssign _ _ _ => true
  | .write _ _ => true
  | .read _ _ => true
  | .seq C1 C2 => C1.BreaksScopedNoLoopSeq inWhile && C2.BreaksScopedNoLoopSeq inWhile
  | .ite _ C1 C2 => C1.BreaksScopedNoLoopSeq inWhile && C2.BreaksScopedNoLoopSeq inWhile
  | .whileLoop _ C => C.BreaksScopedNoLoopSeq true
  | .brk => inWhile
  | .term => true
  | .loopSeq _ _ => false

/-- The closing sentence of App. A's "Syntax" paragraph: "a program of thread `t` is a
command of the form `C ; term` in which `term` occurs exactly once, and every
`break` occurs within the body of some `while`" — together with the
paragraph right after it, that `C₁ ▷ C₂` "does not appear in programs".
These are checked by `Command.TermCount` and `Command.BreaksScopedNoLoopSeq`. -/
def Command.IsProgram {D : Domains} {V : Vocabulary D} (C : Command D V) : Prop :=
  C.TermCount = 1 ∧ C.BreaksScopedNoLoopSeq false = true

instance {D : Domains} {V : Vocabulary D} :
    DecidablePred (Command.IsProgram (D := D) (V := V)) := fun C => by
  unfold Command.IsProgram
  infer_instance

end RAUndecidability
