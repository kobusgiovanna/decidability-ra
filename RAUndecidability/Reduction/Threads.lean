import RAUndecidability.Reduction.PCP
import RAUndecidability.ProgramSemantics.Sugar
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The twelve threads of Fig. 7

the program `ConcProg` (Fig. 7): the concurrent program `ConcProg` for a PCP instance `I`
(Fig. 7), written in the command language of commands (App. A, Syntax).

This file fixes the shared `Domains` (`Tid`: twelve threads; `Loc`: twenty
locations; `Val`: the value shapes occurring in the figure). Each thread gets
its own `Vocabulary` (App. A, Syntax) in its
own namespace: the guessers `GuessAX`/`GuessAY`/`GuessBX`/`GuessBY`
(`g_α^x`, `g_α^y`, `g_β^x`, `g_β^y`), their primed variants
`PrimeAX`/`PrimeAY`/`PrimeBX`/`PrimeBY` (`g_α^{x'}`, `g_α^{y'}`, `g_β^{x'}`,
`g_β^{y'}`), the checkers `CheckX`/`CheckY` (`c^x`, `c^y`) and their primed
variants `PrimeCheckX`/`PrimeCheckY` (`c^{x'}`, `c^{y'}`).

`Fintype` instances are given by hand (`Fintype.ofList` for enumerations,
`Fintype.ofEquiv` against a `Sum`/`Prod` encoding for `Val`).
-/

namespace RAUndecidability

/-! ## Layout of the thread definitions

Each thread's `Command` is laid out to be read side by side with its column of
Fig. 7: one Lean line per line of the figure, nested blocks indented as in the
figure, and the figure's line as a trailing comment. Sequential
composition `C₁; C₂` is written `C₁ ;; C₂` (Lean reserves `;`), a file-local
right-associative notation for `Command.seq`, so `a ;; b ;; c` is
`seq a (seq b c)`. It is pure notation: the terms are the same as when written
with nested `.seq`s, and no other file sees it.

The figure's lines with no command of their own (`α_⊥ ← ⊥`, `else`, `endif`,
`done`) appear as comment-only lines. `if First() then … else … endif` is
`Command.firstIt` applied to its two branches, and
`if aux = ⊥ then break endif` is `.ite .isBot .brk .skip`. -/

local infixr:10 " ;; " => Command.seq

/-! ## `Tid`, `Loc`, `Val` -/

/-- The twelve threads of Fig. 7: the guessers
`g_α^x, g_α^y, g_β^x, g_β^y`, their primed variants
`g_α^{x'}, g_α^{y'}, g_β^{x'}, g_β^{y'}`, the checkers `c^x, c^y`, and their primed
variants `c^{x'}, c^{y'}`. -/
inductive Tid
  | guessAX | guessAY | guessBX | guessBY
  | primeAX | primeAY | primeBX | primeBY
  | checkX | checkY
  | primeCheckX | primeCheckY
  deriving DecidableEq

instance : Fintype Tid :=
  Fintype.ofList
    [Tid.guessAX, .guessAY, .guessBX, .guessBY, .primeAX, .primeAY, .primeBX,
      .primeBY, .checkX, .checkY, .primeCheckX, .primeCheckY]
    (by intro x; cases x <;> simp)

instance : Nonempty Tid := ⟨.guessAX⟩

instance : Inhabited Tid := ⟨.guessAX⟩

/-- The twenty locations of the program `ConcProg` (Fig. 7): `x_α, x_β, y_α, y_β`;
`x'_α, x'_β, y'_α, y'_β`; `z_α^{x,x'}, z_α^{y,y'}, z_β^{x,x'}, z_β^{y,y'}`; the
bridge locations `z_α^{x,y}, z_β^{x,y}` (`zAxy`/`zBxy`) and
`ℓ_α^{y,x}, ℓ_β^{y,x}` (`ellAyx`/`ellByx`); and
`z_α^{x',x}, z_α^{y',y}, z_β^{x',x}, z_β^{y',y}`. -/
inductive Loc
  | xA | xB | yA | yB
  | xA' | xB' | yA' | yB'
  | zAxx' | zAyy' | zBxx' | zByy'
  | zAxy | zBxy
  | ellAyx | ellByx
  | zAx'x | zAy'y | zBx'x | zBy'y
  deriving DecidableEq

instance : Fintype Loc :=
  Fintype.ofList
    [Loc.xA, .xB, .yA, .yB, .xA', .xB', .yA', .yB', .zAxx', .zAyy', .zBxx', .zByy',
      .zAxy, .zBxy, .ellAyx, .ellByx, .zAx'x, .zAy'y, .zBx'x, .zBy'y]
    (by intro x; cases x <;> simp)

instance : Nonempty Loc := ⟨.xA⟩

/-- The values written in Fig. 7 (`ValueDom`, §2.1), one constructor
per tuple shape:
* `cnt`: bare counters (`z_α^{x,x'}`, `z_α^{y,y'}`, `z_α^{x',x}`, …);
* `xTag`/`yTag`: `⟨t, v⟩` or `⟨t̄, v⟩` at `x_α, x_β` (letters) and
  `y_α, y_β` (indices); the `Bool` is the overline, marking the first value
  written;
* `cntAux`: `⟨c_y, aux⟩` at the bridge locations `ℓ_α^{y,x}, ℓ_β^{y,x}`;
* `primeTag`: `⟨t, c⟩` at `x'_α, x'_β, y'_α, y'_β`, and the checkers' writes
  `⟨c^x, c⟩`/`⟨c^y, c⟩` at `x_α, x_β`/`y_α, y_β`.

Letters and indices are `Option _`, with `⊥` as `none`: `aux` can be `⊥`, so
the letter written, `α_aux[j]`, ranges over `Option Γ`. -/
inductive Val (I : PCPInstance)
  | cnt (v : Fin 4)
  | xTag (tag : Tid × Bool) (letter : Option I.Γ)
  | yTag (tag : Tid × Bool) (aux : Option (Fin I.n))
  | cntAux (cy : Fin 4) (aux : Option (Fin I.n))
  | primeTag (t : Tid) (v : Fin 4)
  deriving DecidableEq

/-- Encoding `Val I` into an equivalent `Sum`/`Prod` type, to get `Fintype`
via `Fintype.ofEquiv`. -/
def Val.toSum {I : PCPInstance} : Val I →
    Fin 4 ⊕ ((Tid × Bool) × Option I.Γ) ⊕ ((Tid × Bool) × Option (Fin I.n)) ⊕
      (Fin 4 × Option (Fin I.n)) ⊕ (Tid × Fin 4)
  | .cnt v => .inl v
  | .xTag tag letter => .inr (.inl (tag, letter))
  | .yTag tag aux => .inr (.inr (.inl (tag, aux)))
  | .cntAux cy aux => .inr (.inr (.inr (.inl (cy, aux))))
  | .primeTag t v => .inr (.inr (.inr (.inr (t, v))))

def Val.ofSum {I : PCPInstance} :
    Fin 4 ⊕ ((Tid × Bool) × Option I.Γ) ⊕ ((Tid × Bool) × Option (Fin I.n)) ⊕
      (Fin 4 × Option (Fin I.n)) ⊕ (Tid × Fin 4) → Val I
  | .inl v => .cnt v
  | .inr (.inl (tag, letter)) => .xTag tag letter
  | .inr (.inr (.inl (tag, aux))) => .yTag tag aux
  | .inr (.inr (.inr (.inl (cy, aux)))) => .cntAux cy aux
  | .inr (.inr (.inr (.inr (t, v)))) => .primeTag t v

instance (I : PCPInstance) : Fintype (Val I) :=
  Fintype.ofEquiv _ ⟨Val.ofSum, Val.toSum,
    by rintro (_ | _ | _ | _ | _) <;> rfl,
    by rintro (_ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩

instance (I : PCPInstance) : Nonempty (Val I) := ⟨.cnt 0⟩

/-- The shared `Domains` for all twelve threads of `ConcProg I`
(the domains (§2.1), instantiated per the program `ConcProg` (Fig. 7)). -/
def domainOf (I : PCPInstance) : Domains where
  Val := Val I
  Loc := Loc
  Tid := Tid

/-! ## Thread `g_α^{x'}` -/

-- Thread `g_α^{x'}`. `I` is unused by its logic; it only fixes the ambient
-- `Domains`.
namespace PrimeAX

/-- Local variables: `cnt`, and the fresh boolean `b` introduced by the
`while NDet({False,True}) do …` sugar (the first derived form of App. A). -/
inductive Vars | cnt | b
  deriving DecidableEq

instance : Fintype Vars := Fintype.ofList [Vars.cnt, .b] (by intro x; cases x <;> simp)

/-- Local values: `cnt`'s four values, and `b`'s two (one shared codomain,
stores (App. A, Syntax)). -/
abbrev Vals := Fin 4 ⊕ Bool

/-- `(cnt+1) mod 4` (`Fin 4`'s `+` wraps mod 4). -/
inductive Expr | nextCnt

/-- The `while NDet({False,True}) do …` guard: `b`'s current value. -/
inductive BExpr | isB

def eval : Expr → (Vars → Vals) → Vals
  | .nextCnt, φ => match φ .cnt with
      | .inl v => .inl (v + 1)
      | .inr _ => .inl 0

def evalB : BExpr → (Vars → Vals) → Bool
  | .isB, φ => match φ .b with
      | .inr v => v
      | .inl _ => false

variable (I : PCPInstance)

/-- `⟨g_α^{x'}, 0⟩`, the constant written to `x'_α`; and the current value of
`cnt`, both written to `z_α^{x,x'}` and expected when reading `z_α^{x',x}`. -/
inductive VExpr | xPrimeTag | cntVal

def evalV : VExpr → (Vars → Vals) → Val I
  | .xPrimeTag, _ => .primeTag .primeAX 0
  | .cntVal, φ => match φ .cnt with
      | .inl v => .cnt v
      | .inr _ => .cnt 0

/-- This thread's `Vocabulary` (App. A, Syntax). -/
def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals
  Expr := Expr
  eval := eval
  BExpr := BExpr
  evalB := evalB
  VExpr := VExpr
  evalV := evalV I

/-- The loop body of `g_α^{x'}`. -/
def body : Command (domainOf I) (Vocab I) :=
  .assign .cnt .nextCnt ;;       -- c ← (c + 1) mod 4;
  .write .xA' .xPrimeTag ;;      -- w(x'_α, ⟨g_α^{x'}, 0⟩);
  .write .zAxx' .cntVal ;;       -- w(z_α^{x,x'}, c);
  .read .zAx'x .cntVal           -- r(z_α^{x',x}, c);

/-- The choice set `{False, True}` of the outer `while NDet(⋯) do` loop. -/
def X : Finset Vals := {Sum.inr false, Sum.inr true}

theorem X_nonempty : X.Nonempty := ⟨Sum.inr false, by decide⟩

/-- **Paper:** Fig. 7, thread `g_α^{x'}`. -/
def program : Command (domainOf I) (Vocab I) :=
  Command.whileNdet .b X X_nonempty .isB    -- while NDet({False, True}) do
    (body I) ;;                             --   ⟨body⟩
                                            -- done
  .term                                     -- term

/-- `Command.IsProgram` (App. A, Syntax) for `g_α^{x'}`: one `term`, and no
`break`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end PrimeAX

/-! ## Thread `g_α^y` -/

-- Thread `g_α^y`: guesses `aux ∈ [n] ∪ {⊥}` and, each iteration, publishes it
-- at `y_α` and, paired with its counter, at the bridge location `ℓ_α^{y,x}`;
-- it synchronizes with `g_α^x` via `z_α^{x,y}` and with `g_α^{y'}` via
-- `z_α^{y,y'}`/`z_α^{y',y}`. `α_⊥ ← ⊥` is notation in the paper, not a
-- command.
namespace GuessAY

/-- Local variables: `aux` (the guessed tile index, or `⊥`), `cnt` (`c`),
`prev` (`c`'s value before the increment), and the fresh boolean `fst` of the
`First()` occurrence. -/
inductive Vars | aux | cnt | prev | fst
  deriving DecidableEq

instance : Fintype Vars :=
  Fintype.ofList [Vars.aux, .cnt, .prev, .fst] (by intro x; cases x <;> simp)

variable (I : PCPInstance)

/-- Local values: `aux` ranges over `Option (Fin I.n)` (`⊥` as `none`); `cnt`
and `prev` share `Fin 4`; `fst` is `Bool`. -/
abbrev Vals := Option (Fin I.n) ⊕ Fin 4 ⊕ Bool

/-- `prev ← c`; `c ← (c + 1) mod 4`; and `False`, for `First()`'s
`fst ← False`. -/
inductive Expr | readCnt | nextCnt | fstFalse

/-- The boolean guards: `True` (of `while True do`), `First()`'s guard
(`fst`'s current value), and `aux = ⊥`. -/
inductive BExpr | tt | isFirst | isBot

def eval : Expr → (Vars → Vals I) → Vals I
  | .readCnt, φ => φ .cnt
  | .nextCnt, φ => match φ .cnt with
      | .inr (.inl v) => .inr (.inl (v + 1))
      | _ => .inr (.inl 0)
  | .fstFalse, _ => Sum.inr (Sum.inr false)

def evalB : BExpr → (Vars → Vals I) → Bool
  | .tt, _ => true
  | .isFirst, φ => match φ .fst with
      | .inr (.inr b) => b
      | _ => false
  | .isBot, φ => match φ .aux with
      | .inl none => true
      | .inl (some _) => false
      | .inr _ => false

/-- `⟨ḡ_α^y, aux⟩` (first iteration) / `⟨g_α^y, aux⟩` (later), written to
`y_α`; `⟨c, aux⟩`, written to `ℓ_α^{y,x}`; `c`, written to `z_α^{y',y}`; and
`prev`, expected when reading `z_α^{x,y}` and `z_α^{y,y'}`. -/
inductive VExpr | yTagFirst | yTagRest | cntAuxVal | cntVal | prevVal

def auxOf (φ : Vars → Vals I) : Option (Fin I.n) :=
  match φ .aux with
  | .inl a => a
  | .inr _ => none

def cntOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .cnt with
  | .inr (.inl v) => v
  | _ => 0

def prevOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .prev with
  | .inr (.inl v) => v
  | _ => 0

def evalV : VExpr → (Vars → Vals I) → Val I
  | .yTagFirst, φ => .yTag (Tid.guessAY, true) (auxOf I φ)
  | .yTagRest, φ => .yTag (Tid.guessAY, false) (auxOf I φ)
  | .cntAuxVal, φ => .cntAux (cntOf I φ) (auxOf I φ)
  | .cntVal, φ => .cnt (cntOf I φ)
  | .prevVal, φ => .cnt (prevOf I φ)

/-- This thread's `Vocabulary` (App. A, Syntax). -/
def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals I
  Expr := Expr
  eval := eval I
  BExpr := BExpr
  evalB := evalB I
  VExpr := VExpr
  evalV := evalV I

/-- `{1,…,n}`, as `Vals` — `aux`'s first draw, `⊥` excluded. -/
def auxSet : Finset (Vals I) :=
  (Finset.univ : Finset (Fin I.n)).image (fun v => (Sum.inl (some v) : Vals I))

theorem auxSet_nonempty : (auxSet I).Nonempty :=
  (Finset.univ_nonempty (α := Fin I.n)).image _

/-- `{1,…,n,⊥}`, as `Vals` — every later draw of `aux`. -/
def auxSetBot : Finset (Vals I) :=
  (Finset.univ : Finset (Option (Fin I.n))).image (fun v => (Sum.inl v : Vals I))

theorem auxSetBot_nonempty : (auxSetBot I).Nonempty :=
  Finset.univ_nonempty.image _

/-- The body of `g_α^y`'s `while True do … done` loop. -/
def loopBody : Command (domainOf I) (Vocab I) :=
  .assign .prev .readCnt ;;                       -- prev ← c;
  .assign .cnt .nextCnt ;;                        -- c ← (c + 1) mod 4;
  Command.firstIt .fst .fstFalse .isFirst         -- if First() then
    (.write .yA .yTagFirst ;;                     --   w(y_α, ⟨ḡ_α^y, aux⟩);
     .write .ellAyx .cntAuxVal ;;                 --   w(ℓ_α^{y,x}, ⟨c, aux⟩);
     .write .zAy'y .cntVal)                       --   w(z_α^{y',y}, c);
                                                  -- else
    (.write .yA .yTagRest ;;                      --   w(y_α, ⟨g_α^y, aux⟩);
     .write .ellAyx .cntAuxVal ;;                 --   w(ℓ_α^{y,x}, ⟨c, aux⟩);
     .write .zAy'y .cntVal ;;                     --   w(z_α^{y',y}, c);
     .read .zAxy .prevVal ;;                      --   r(z_α^{x,y}, prev);
     .read .zAyy' .prevVal) ;;                    --   r(z_α^{y,y'}, prev);
                                                  -- endif
  .ite .isBot .brk .skip ;;                       -- if aux = ⊥ then break; endif
  .ndetAssign .aux (auxSetBot I) (auxSetBot_nonempty I)  -- aux ← NDet({1,…,n,⊥});

/-- **Paper:** Fig. 7, thread `g_α^y`. -/
def program : Command (domainOf I) (Vocab I) :=
                                                  -- α_⊥ ← ⊥;
  .ndetAssign .aux (auxSet I) (auxSet_nonempty I) ;;  -- aux ← NDet({1,…,n});
  Command.whileLoop .tt                           -- while True do
    (loopBody I) ;;                               --   ⟨loopBody⟩
                                                  -- done
  .term                                           -- term

/-- `Command.IsProgram` (App. A, Syntax) for `g_α^y`: one `term`, and its
`break` sits within the `whileLoop`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end GuessAY

/-! ## Thread `g_α^x` -/

-- Thread `g_α^x`: guesses `aux ∈ [n] ∪ {⊥}` and, each outer iteration,
-- publishes its counter `c_y` at the bridge location `z_α^{x,y}`, then writes
-- the guessed tile `α_aux`, letter by letter, to `x_α` (the inner `for` loop);
-- it synchronizes with `g_α^{x'}` via `z_α^{x,x'}`/`z_α^{x',x}` and with
-- `g_α^y` via `ℓ_α^{y,x}`.
namespace GuessAX

variable (I : PCPInstance)

/-- `max_i |α_i|`, the bound for the `for` loop's `j` and `N` (the semantics
appendix's finiteness discussion). -/
def maxLen : ℕ := Finset.univ.sup (fun i : Fin I.n => (I.α i).length)

theorem maxLen_pos : 0 < maxLen I := by
  have h := Finset.le_sup (f := fun i : Fin I.n => (I.α i).length)
    (Finset.mem_univ ⟨0, I.hn⟩)
  have hpos : 0 < (I.α ⟨0, I.hn⟩).length := List.length_pos_of_ne_nil (I.hα ⟨0, I.hn⟩)
  unfold maxLen
  omega

/-- `α`, extended to `aux = ⊥` as the one-letter word `⊥` (`α_⊥ = ⊥`); letters
are `Option I.Γ`, `⊥` as `none`. -/
def extAlpha (aux : Option (Fin I.n)) : List (Option I.Γ) :=
  match aux with
  | some i => (I.α i).map some
  | none => [none]

theorem extAlpha_length_le (aux : Option (Fin I.n)) : (extAlpha I aux).length ≤ maxLen I := by
  cases aux with
  | none =>
      have := maxLen_pos I
      simp only [extAlpha, List.length_singleton]
      omega
  | some i =>
      simp only [extAlpha, List.length_map]
      unfold maxLen
      exact Finset.le_sup (f := fun i : Fin I.n => (I.α i).length) (Finset.mem_univ i)

/-- Local variables: `aux`; `cntY` (`c_y`, the outer counter); `cnt`/`prev`
(`c`/`prev`, in the `for` loop); `j`/`N` (the `for` loop's index and upper
bound); `fst` (the `First()` occurrence). -/
inductive Vars | aux | cntY | cnt | prev | j | N | fst
  deriving DecidableEq

instance : Fintype Vars :=
  Fintype.ofList [Vars.aux, .cntY, .cnt, .prev, .j, .N, .fst]
    (by intro x; cases x <;> simp)

/-- Local values: `aux` over `Option (Fin I.n)`; `cntY`/`cnt`/`prev` share
`Fin 4`; `j`/`N` share `Fin (maxLen I + 2)`, one more than needed, so that the
`for` loop's final increment does not wrap; `fst` is `Bool`. -/
abbrev Vals := Option (Fin I.n) ⊕ Fin 4 ⊕ Fin (maxLen I + 2) ⊕ Bool

/-- `c_y ← (c_y + 1) mod 4`; `prev ← c`; `c ← (c + 1) mod 4`;
`N ← |α_aux|` (evaluated once on entry to the `for` loop); `j ← j + 1`;
`False`, for `First()`'s `fst ← False`; and `1`, for the `for` loop's
`j ← 1`. -/
inductive Expr | nextCntY | readCnt | nextCnt | alphaLen | jIncr | fstFalse | one

/-- The boolean guards: `True` (of `while True do`), the `for` loop's
`j ≤ N`, `First()`'s guard, and `aux = ⊥`. -/
inductive BExpr | tt | jLeN | isFirst | isBot

def auxOf (φ : Vars → Vals I) : Option (Fin I.n) :=
  match φ .aux with
  | .inl a => a
  | .inr _ => none

def cntYOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .cntY with
  | .inr (.inl v) => v
  | _ => 0

def cntOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .cnt with
  | .inr (.inl v) => v
  | _ => 0

def prevOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .prev with
  | .inr (.inl v) => v
  | _ => 0

def jOf (φ : Vars → Vals I) : Fin (maxLen I + 2) :=
  match φ .j with
  | .inr (.inr (.inl v)) => v
  | _ => 0

def NOf (φ : Vars → Vals I) : Fin (maxLen I + 2) :=
  match φ .N with
  | .inr (.inr (.inl v)) => v
  | _ => 0

def eval : Expr → (Vars → Vals I) → Vals I
  | .nextCntY, φ => .inr (.inl (cntYOf I φ + 1))
  | .readCnt, φ => φ .cnt
  | .nextCnt, φ => .inr (.inl (cntOf I φ + 1))
  | .alphaLen, φ =>
      .inr (.inr (.inl ⟨(extAlpha I (auxOf I φ)).length,
        by have := extAlpha_length_le I (auxOf I φ); omega⟩))
  | .jIncr, φ => .inr (.inr (.inl (jOf I φ + 1)))
  | .fstFalse, _ => .inr (.inr (.inr false))
  | .one, _ => .inr (.inr (.inl ⟨1, by have := maxLen_pos I; omega⟩))

def evalB : BExpr → (Vars → Vals I) → Bool
  | .tt, _ => true
  | .jLeN, φ => decide (jOf I φ ≤ NOf I φ)
  | .isFirst, φ => match φ .fst with
      | .inr (.inr (.inr b)) => b
      | _ => false
  | .isBot, φ => match φ .aux with
      | .inl none => true
      | .inl (some _) => false
      | .inr _ => false

/-- The `j`-th letter of `α_aux` (1-indexed, as in the paper), or `⊥` if `j` is
out of range (which does not happen while `1 ≤ j ≤ N`). -/
def jthLetter (aux : Option (Fin I.n)) (j : Fin (maxLen I + 2)) : Option I.Γ :=
  ((extAlpha I aux)[j.val - 1]?).getD none

/-- `c_y`, written to `z_α^{x,y}`; `⟨ḡ_α^x, α_aux[j]⟩` (first iteration)
/ `⟨g_α^x, α_aux[j]⟩` (later), written to `x_α`; `c`, written to `z_α^{x',x}`;
`prev`, expected when reading `z_α^{x,x'}`; and `⟨c_y, aux⟩`, expected when
reading `ℓ_α^{y,x}`. -/
inductive VExpr | cntYVal | xTagFirst | xTagRest | cntVal | prevVal | cntYAuxVal

def evalV : VExpr → (Vars → Vals I) → Val I
  | .cntYVal, φ => .cnt (cntYOf I φ)
  | .xTagFirst, φ => .xTag (Tid.guessAX, true) (jthLetter I (auxOf I φ) (jOf I φ))
  | .xTagRest, φ => .xTag (Tid.guessAX, false) (jthLetter I (auxOf I φ) (jOf I φ))
  | .cntVal, φ => .cnt (cntOf I φ)
  | .prevVal, φ => .cnt (prevOf I φ)
  | .cntYAuxVal, φ => .cntAux (cntYOf I φ) (auxOf I φ)

/-- This thread's `Vocabulary` (App. A, Syntax). -/
def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals I
  Expr := Expr
  eval := eval I
  BExpr := BExpr
  evalB := evalB I
  VExpr := VExpr
  evalV := evalV I

/-- `{1,…,n}`, as `Vals` — `aux`'s first draw, `⊥` excluded. -/
def auxSet : Finset (Vals I) :=
  (Finset.univ : Finset (Fin I.n)).image (fun v => (Sum.inl (some v) : Vals I))

theorem auxSet_nonempty : (auxSet I).Nonempty :=
  (Finset.univ_nonempty (α := Fin I.n)).image _

/-- `{1,…,n,⊥}`, as `Vals` — every later draw of `aux`. -/
def auxSetBot : Finset (Vals I) :=
  (Finset.univ : Finset (Option (Fin I.n))).image (fun v => (Sum.inl v : Vals I))

theorem auxSetBot_nonempty : (auxSetBot I).Nonempty :=
  Finset.univ_nonempty.image _

/-- The body of `g_α^x`'s `for` loop. -/
def innerBody : Command (domainOf I) (Vocab I) :=
  .assign .prev .readCnt ;;                       -- prev ← c;
  .assign .cnt .nextCnt ;;                        -- c ← (c + 1) mod 4;
  Command.firstIt .fst .fstFalse .isFirst         -- if First() then
    (.write .xA .xTagFirst ;;                     --   w(x_α, ⟨ḡ_α^x, α_aux[j]⟩);
     .write .zAx'x .cntVal)                       --   w(z_α^{x',x}, c);
                                                  -- else
    (.write .xA .xTagRest ;;                      --   w(x_α, ⟨g_α^x, α_aux[j]⟩);
     .write .zAx'x .cntVal ;;                     --   w(z_α^{x',x}, c);
     .read .zAxx' .prevVal)                       --   r(z_α^{x,x'}, prev);
                                                  -- endif

/-- The body of `g_α^x`'s `while True do … done` loop. -/
def outerBody : Command (domainOf I) (Vocab I) :=
  .assign .cntY .nextCntY ;;                      -- c_y ← (c_y + 1) mod 4;
  .write .zAxy .cntYVal ;;                        -- w(z_α^{x,y}, c_y);
  Command.forLoop .j .N .alphaLen .one .jLeN .jIncr  -- for j ∈ 1,…,|α_aux| do
    (innerBody I) ;;                              --   ⟨innerBody⟩
                                                  -- done
  .read .ellAyx .cntYAuxVal ;;                    -- r(ℓ_α^{y,x}, ⟨c_y, aux⟩);
  .ite .isBot .brk .skip ;;                       -- if aux = ⊥ then break; endif
  .ndetAssign .aux (auxSetBot I) (auxSetBot_nonempty I)  -- aux ← NDet({1,…,n,⊥});

/-- **Paper:** Fig. 7, thread `g_α^x`. -/
def program : Command (domainOf I) (Vocab I) :=
                                                  -- α_⊥ ← ⊥;
  .ndetAssign .aux (auxSet I) (auxSet_nonempty I) ;;  -- aux ← NDet({1,…,n});
  Command.whileLoop .tt                           -- while True do
    (outerBody I) ;;                              --   ⟨outerBody⟩
                                                  -- done
  .term                                           -- term

/-- `Command.IsProgram` (App. A, Syntax) for `g_α^x`: one `term`, and its
`break` (in `outerBody`) sits within the `whileLoop`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end GuessAX

/-! ## Thread `c^x` -/

-- Thread `c^x`: checks that the letters guessed by `g_α^x` and `g_β^x` agree,
-- letter by letter. Each iteration it writes its counter, tagged `c^x`, to
-- `x_α`/`x_β`, reads back the guessers' letters there, and (from the second
-- iteration on) reads `c^{x'}`'s writes at `x'_α`/`x'_β`.
namespace CheckX

/-- `Γ` is nonempty: the first tile word is nonempty (`I.hα`). Needed for
`aux`'s first draw, `NDet(Γ)`. -/
instance instNonemptyΓ (I : PCPInstance) : Nonempty I.Γ :=
  ⟨(I.α ⟨0, I.hn⟩).head (I.hα ⟨0, I.hn⟩)⟩

variable (I : PCPInstance)

/-- Local variables: `aux` (the guessed letter, or `⊥`), `cnt` (`c`), `prev`
(`c`'s value before the increment), and `fst` (the `First()` occurrence). -/
inductive Vars | aux | cnt | prev | fst
  deriving DecidableEq

instance : Fintype Vars :=
  Fintype.ofList [Vars.aux, .cnt, .prev, .fst] (by intro x; cases x <;> simp)

/-- Local values: `aux` over `Option I.Γ` (`⊥` as `none`); `cnt`/`prev` share
`Fin 4`; `fst` is `Bool`. -/
abbrev Vals := Option I.Γ ⊕ Fin 4 ⊕ Bool

/-- `prev ← c`; `c ← (c + 1) mod 4`; and `False`, for `First()`'s
`fst ← False`. -/
inductive Expr | readCnt | nextCnt | fstFalse

/-- The boolean guards: `True` (of `while True do`), `First()`'s guard, and
`aux = ⊥`. -/
inductive BExpr | tt | isFirst | isBot

def auxOf (φ : Vars → Vals I) : Option I.Γ :=
  match φ .aux with
  | .inl a => a
  | .inr _ => none

def cntOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .cnt with
  | .inr (.inl v) => v
  | _ => 0

def prevOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .prev with
  | .inr (.inl v) => v
  | _ => 0

def eval : Expr → (Vars → Vals I) → Vals I
  | .readCnt, φ => φ .cnt
  | .nextCnt, φ => .inr (.inl (cntOf I φ + 1))
  | .fstFalse, _ => .inr (.inr false)

def evalB : BExpr → (Vars → Vals I) → Bool
  | .tt, _ => true
  | .isFirst, φ => match φ .fst with
      | .inr (.inr b) => b
      | _ => false
  | .isBot, φ => match φ .aux with
      | .inl none => true
      | .inl (some _) => false
      | .inr _ => false

/-- `⟨c^x, c⟩`, written to both `x_α` and `x_β`; `⟨ḡ_α^x/g_α^x, aux⟩`
(resp. `g_β^x`), expected when reading `x_α` (resp. `x_β`); and
`⟨c^{x'}, prev⟩`, expected when reading `x'_α`/`x'_β`. -/
inductive VExpr | cntTagVal | xAFirst | xARest | xBFirst | xBRest | primeCheckVal

def evalV : VExpr → (Vars → Vals I) → Val I
  | .cntTagVal, φ => .primeTag Tid.checkX (cntOf I φ)
  | .xAFirst, φ => .xTag (Tid.guessAX, true) (auxOf I φ)
  | .xARest, φ => .xTag (Tid.guessAX, false) (auxOf I φ)
  | .xBFirst, φ => .xTag (Tid.guessBX, true) (auxOf I φ)
  | .xBRest, φ => .xTag (Tid.guessBX, false) (auxOf I φ)
  | .primeCheckVal, φ => .primeTag Tid.primeCheckX (prevOf I φ)

/-- This thread's `Vocabulary` (App. A, Syntax). -/
def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals I
  Expr := Expr
  eval := eval I
  BExpr := BExpr
  evalB := evalB I
  VExpr := VExpr
  evalV := evalV I

/-- `Γ`, as `Vals` — `aux`'s first draw, `⊥` excluded. -/
def auxSet : Finset (Vals I) :=
  (Finset.univ : Finset I.Γ).image (fun v => (Sum.inl (some v) : Vals I))

theorem auxSet_nonempty : (auxSet I).Nonempty :=
  (Finset.univ_nonempty (α := I.Γ)).image _

/-- `Γ ∪ {⊥}`, as `Vals` — every later draw of `aux`. -/
def auxSetBot : Finset (Vals I) :=
  (Finset.univ : Finset (Option I.Γ)).image (fun v => (Sum.inl v : Vals I))

theorem auxSetBot_nonempty : (auxSetBot I).Nonempty :=
  Finset.univ_nonempty.image _

/-- The body of `c^x`'s `while True do … done` loop. -/
def body : Command (domainOf I) (Vocab I) :=
  .assign .prev .readCnt ;;                       -- prev ← c;
  .assign .cnt .nextCnt ;;                        -- c ← (c + 1) mod 4;
  .write .xA .cntTagVal ;;                        -- w(x_α, ⟨c^x, c⟩);
  .write .xB .cntTagVal ;;                        -- w(x_β, ⟨c^x, c⟩);
  Command.firstIt .fst .fstFalse .isFirst         -- if First() then
    (.read .xA .xAFirst ;;                        --   r(x_α, ⟨ḡ_α^x, aux⟩);
     .read .xB .xBFirst)                          --   r(x_β, ⟨ḡ_β^x, aux⟩);
                                                  -- else
    (.read .xA .xARest ;;                         --   r(x_α, ⟨g_α^x, aux⟩);
     .read .xB .xBRest ;;                         --   r(x_β, ⟨g_β^x, aux⟩);
     .read .xA' .primeCheckVal ;;                 --   r(x'_α, ⟨c^{x'}, prev⟩);
     .read .xB' .primeCheckVal) ;;                --   r(x'_β, ⟨c^{x'}, prev⟩);
                                                  -- endif
  .ite .isBot .brk .skip ;;                       -- if aux = ⊥ then break; endif
  .ndetAssign .aux (auxSetBot I) (auxSetBot_nonempty I)  -- aux ← NDet(Γ ∪ {⊥});

/-- **Paper:** Fig. 7, thread `c^x`. -/
def program : Command (domainOf I) (Vocab I) :=
  .ndetAssign .aux (auxSet I) (auxSet_nonempty I) ;;  -- aux ← NDet(Γ);
  Command.whileLoop .tt                           -- while True do
    (body I) ;;                                   --   ⟨body⟩
                                                  -- done
  .term                                           -- term

/-- `Command.IsProgram` (App. A, Syntax) for `c^x`: one `term`, and its
`break` sits within the `whileLoop`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end CheckX

/-! ## Thread `c^{x'}` -/

-- Thread `c^{x'}`, running in lockstep with `c^x`. Each iteration it writes
-- its counter, tagged `c^{x'}`, to `x'_α`/`x'_β`, reads the primed guessers'
-- `⟨_, 0⟩` there, and reads `c^x`'s counter at `x_α`/`x_β`.
namespace PrimeCheckX

variable (I : PCPInstance)

/-- Local variables: `cnt` (`c`) and the fresh boolean `b` of
`while NDet({False,True}) do …`. -/
inductive Vars | cnt | b
  deriving DecidableEq

instance : Fintype Vars := Fintype.ofList [Vars.cnt, .b] (by intro x; cases x <;> simp)

/-- Local values: `cnt`'s four values, and `b`'s two. -/
abbrev Vals := Fin 4 ⊕ Bool

/-- `c ← (c + 1) mod 4`. -/
inductive Expr | nextCnt

/-- The `while NDet({False,True}) do …` guard. -/
inductive BExpr | isB

def cntOf (φ : Vars → Vals) : Fin 4 :=
  match φ .cnt with
  | .inl v => v
  | .inr _ => 0

def eval : Expr → (Vars → Vals) → Vals
  | .nextCnt, φ => .inl (cntOf φ + 1)

def evalB : BExpr → (Vars → Vals) → Bool
  | .isB, φ => match φ .b with
      | .inr v => v
      | .inl _ => false

/-- `⟨c^{x'}, c⟩`, written to both `x'_α` and `x'_β`; `⟨g_α^{x'}, 0⟩` (resp.
`⟨g_β^{x'}, 0⟩`), expected when reading `x'_α` (resp. `x'_β`); and `⟨c^x, c⟩`,
expected when reading `x_α`/`x_β`. -/
inductive VExpr | cntTagVal | xApExpect | xBpExpect | checkExpect

def evalV : VExpr → (Vars → Vals) → Val I
  | .cntTagVal, φ => .primeTag Tid.primeCheckX (cntOf φ)
  | .xApExpect, _ => .primeTag Tid.primeAX 0
  | .xBpExpect, _ => .primeTag Tid.primeBX 0
  | .checkExpect, φ => .primeTag Tid.checkX (cntOf φ)

/-- This thread's `Vocabulary` (App. A, Syntax). -/
def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals
  Expr := Expr
  eval := eval
  BExpr := BExpr
  evalB := evalB
  VExpr := VExpr
  evalV := evalV I

/-- The choice set `{False, True}` of the outer `while NDet(⋯) do` loop. -/
def X : Finset Vals := {Sum.inr false, Sum.inr true}

theorem X_nonempty : X.Nonempty := ⟨Sum.inr false, by decide⟩

/-- The loop body of `c^{x'}`. -/
def body : Command (domainOf I) (Vocab I) :=
  .assign .cnt .nextCnt ;;       -- c ← (c + 1) mod 4;
  .write .xA' .cntTagVal ;;      -- w(x'_α, ⟨c^{x'}, c⟩);
  .write .xB' .cntTagVal ;;      -- w(x'_β, ⟨c^{x'}, c⟩);
  .read .xA' .xApExpect ;;       -- r(x'_α, ⟨g_α^{x'}, 0⟩);
  .read .xB' .xBpExpect ;;       -- r(x'_β, ⟨g_β^{x'}, 0⟩);
  .read .xA .checkExpect ;;      -- r(x_α, ⟨c^x, c⟩);
  .read .xB .checkExpect         -- r(x_β, ⟨c^x, c⟩);

/-- **Paper:** Fig. 7, thread `c^{x'}`. -/
def program : Command (domainOf I) (Vocab I) :=
  Command.whileNdet .b X X_nonempty .isB    -- while NDet({False, True}) do
    (body I) ;;                             --   ⟨body⟩
                                            -- done
  .term                                     -- term

/-- `Command.IsProgram` (App. A, Syntax) for `c^{x'}`: one `term`, and no
`break`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end PrimeCheckX

/-! ## Threads `g_α^{y'}`, `g_β^{x'}`, `g_β^{y'}` -/

-- The remaining primed guessers, each `g_α^{x'}` with locations and tag
-- renamed as in Fig. 7.

namespace PrimeAY

/-- Local variables: `cnt`, and the fresh boolean `b` introduced by the
`while NDet({False,True}) do …` sugar. -/
inductive Vars | cnt | b
  deriving DecidableEq

instance : Fintype Vars := Fintype.ofList [Vars.cnt, .b] (by intro x; cases x <;> simp)

/-- Local values: `cnt`'s four values, and `b`'s two. -/
abbrev Vals := Fin 4 ⊕ Bool

/-- `(cnt+1) mod 4`. -/
inductive Expr | nextCnt

/-- The `while NDet({False,True}) do …` guard. -/
inductive BExpr | isB

def eval : Expr → (Vars → Vals) → Vals
  | .nextCnt, φ => match φ .cnt with
      | .inl v => .inl (v + 1)
      | .inr _ => .inl 0

def evalB : BExpr → (Vars → Vals) → Bool
  | .isB, φ => match φ .b with
      | .inr v => v
      | .inl _ => false

variable (I : PCPInstance)

/-- `⟨g_α^{y'}, 0⟩`, the constant written to `y'_α`; and the current value of
`cnt`, both written to `z_α^{y,y'}` and expected when reading `z_α^{y',y}`. -/
inductive VExpr | yPrimeTag | cntVal

def evalV : VExpr → (Vars → Vals) → Val I
  | .yPrimeTag, _ => .primeTag .primeAY 0
  | .cntVal, φ => match φ .cnt with
      | .inl v => .cnt v
      | .inr _ => .cnt 0

/-- This thread's `Vocabulary` (App. A, Syntax). -/
def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals
  Expr := Expr
  eval := eval
  BExpr := BExpr
  evalB := evalB
  VExpr := VExpr
  evalV := evalV I

/-- The loop body of `g_α^{y'}`. -/
def body : Command (domainOf I) (Vocab I) :=
  .assign .cnt .nextCnt ;;       -- c ← (c + 1) mod 4;
  .write .yA' .yPrimeTag ;;      -- w(y'_α, ⟨g_α^{y'}, 0⟩);
  .write .zAyy' .cntVal ;;       -- w(z_α^{y,y'}, c);
  .read .zAy'y .cntVal           -- r(z_α^{y',y}, c);

/-- The choice set `{False, True}` of the outer `while NDet(⋯) do` loop. -/
def X : Finset Vals := {Sum.inr false, Sum.inr true}

theorem X_nonempty : X.Nonempty := ⟨Sum.inr false, by decide⟩

/-- **Paper:** Fig. 7, thread `g_α^{y'}`. -/
def program : Command (domainOf I) (Vocab I) :=
  Command.whileNdet .b X X_nonempty .isB    -- while NDet({False, True}) do
    (body I) ;;                             --   ⟨body⟩
                                            -- done
  .term                                     -- term

/-- `Command.IsProgram` (App. A, Syntax) for `g_α^{y'}`: one `term`, and no
`break`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end PrimeAY

namespace PrimeBX

/-- Local variables: `cnt`, and the fresh boolean `b`. -/
inductive Vars | cnt | b
  deriving DecidableEq

instance : Fintype Vars := Fintype.ofList [Vars.cnt, .b] (by intro x; cases x <;> simp)

abbrev Vals := Fin 4 ⊕ Bool

inductive Expr | nextCnt
inductive BExpr | isB

def eval : Expr → (Vars → Vals) → Vals
  | .nextCnt, φ => match φ .cnt with
      | .inl v => .inl (v + 1)
      | .inr _ => .inl 0

def evalB : BExpr → (Vars → Vals) → Bool
  | .isB, φ => match φ .b with
      | .inr v => v
      | .inl _ => false

variable (I : PCPInstance)

/-- `⟨g_β^{x'}, 0⟩`, written to `x'_β`; and `cnt`, written to `z_β^{x,x'}` and
expected when reading `z_β^{x',x}`. -/
inductive VExpr | xPrimeTag | cntVal

def evalV : VExpr → (Vars → Vals) → Val I
  | .xPrimeTag, _ => .primeTag .primeBX 0
  | .cntVal, φ => match φ .cnt with
      | .inl v => .cnt v
      | .inr _ => .cnt 0

def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals
  Expr := Expr
  eval := eval
  BExpr := BExpr
  evalB := evalB
  VExpr := VExpr
  evalV := evalV I

/-- The loop body of `g_β^{x'}`. -/
def body : Command (domainOf I) (Vocab I) :=
  .assign .cnt .nextCnt ;;       -- c ← (c + 1) mod 4;
  .write .xB' .xPrimeTag ;;      -- w(x'_β, ⟨g_β^{x'}, 0⟩);
  .write .zBxx' .cntVal ;;       -- w(z_β^{x,x'}, c);
  .read .zBx'x .cntVal           -- r(z_β^{x',x}, c);

def X : Finset Vals := {Sum.inr false, Sum.inr true}

theorem X_nonempty : X.Nonempty := ⟨Sum.inr false, by decide⟩

/-- **Paper:** Fig. 7, thread `g_β^{x'}`. -/
def program : Command (domainOf I) (Vocab I) :=
  Command.whileNdet .b X X_nonempty .isB    -- while NDet({False, True}) do
    (body I) ;;                             --   ⟨body⟩
                                            -- done
  .term                                     -- term

/-- `Command.IsProgram` (App. A, Syntax) for `g_β^{x'}`: one `term`, and no
`break`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end PrimeBX

namespace PrimeBY

/-- Local variables: `cnt`, and the fresh boolean `b`. -/
inductive Vars | cnt | b
  deriving DecidableEq

instance : Fintype Vars := Fintype.ofList [Vars.cnt, .b] (by intro x; cases x <;> simp)

abbrev Vals := Fin 4 ⊕ Bool

inductive Expr | nextCnt
inductive BExpr | isB

def eval : Expr → (Vars → Vals) → Vals
  | .nextCnt, φ => match φ .cnt with
      | .inl v => .inl (v + 1)
      | .inr _ => .inl 0

def evalB : BExpr → (Vars → Vals) → Bool
  | .isB, φ => match φ .b with
      | .inr v => v
      | .inl _ => false

variable (I : PCPInstance)

/-- `⟨g_β^{y'}, 0⟩`, written to `y'_β`; and `cnt`, written to `z_β^{y,y'}` and
expected when reading `z_β^{y',y}`. -/
inductive VExpr | yPrimeTag | cntVal

def evalV : VExpr → (Vars → Vals) → Val I
  | .yPrimeTag, _ => .primeTag .primeBY 0
  | .cntVal, φ => match φ .cnt with
      | .inl v => .cnt v
      | .inr _ => .cnt 0

def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals
  Expr := Expr
  eval := eval
  BExpr := BExpr
  evalB := evalB
  VExpr := VExpr
  evalV := evalV I

/-- The loop body of `g_β^{y'}`. -/
def body : Command (domainOf I) (Vocab I) :=
  .assign .cnt .nextCnt ;;       -- c ← (c + 1) mod 4;
  .write .yB' .yPrimeTag ;;      -- w(y'_β, ⟨g_β^{y'}, 0⟩);
  .write .zByy' .cntVal ;;       -- w(z_β^{y,y'}, c);
  .read .zBy'y .cntVal           -- r(z_β^{y',y}, c);

def X : Finset Vals := {Sum.inr false, Sum.inr true}

theorem X_nonempty : X.Nonempty := ⟨Sum.inr false, by decide⟩

/-- **Paper:** Fig. 7, thread `g_β^{y'}`. -/
def program : Command (domainOf I) (Vocab I) :=
  Command.whileNdet .b X X_nonempty .isB    -- while NDet({False, True}) do
    (body I) ;;                             --   ⟨body⟩
                                            -- done
  .term                                     -- term

/-- `Command.IsProgram` (App. A, Syntax) for `g_β^{y'}`: one `term`, and no
`break`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end PrimeBY

/-! ## Threads `g_β^x`, `g_β^y` -/

-- `g_β^x` and `g_β^y`: `g_α^x` and `g_α^y` with `α` replaced by `β`, as in
-- Fig. 7.

namespace GuessBX

/-- `max_i |β_i|` — see `GuessAX.maxLen`. -/
def maxLen (I : PCPInstance) : ℕ := Finset.univ.sup (fun i : Fin I.n => (I.β i).length)

theorem maxLen_pos (I : PCPInstance) : 0 < maxLen I := by
  have h := Finset.le_sup (f := fun i : Fin I.n => (I.β i).length)
    (Finset.mem_univ ⟨0, I.hn⟩)
  have hpos : 0 < (I.β ⟨0, I.hn⟩).length := List.length_pos_of_ne_nil (I.hβ ⟨0, I.hn⟩)
  unfold maxLen
  omega

/-- `β`, extended to `aux = ⊥` as the one-letter word `⊥` — see
`GuessAX.extAlpha`. -/
def extBeta (I : PCPInstance) (aux : Option (Fin I.n)) : List (Option I.Γ) :=
  match aux with
  | some i => (I.β i).map some
  | none => [none]

theorem extBeta_length_le (I : PCPInstance) (aux : Option (Fin I.n)) :
    (extBeta I aux).length ≤ maxLen I := by
  cases aux with
  | none =>
      have := maxLen_pos I
      simp only [extBeta, List.length_singleton]
      omega
  | some i =>
      simp only [extBeta, List.length_map]
      unfold maxLen
      exact Finset.le_sup (f := fun i : Fin I.n => (I.β i).length) (Finset.mem_univ i)

variable (I : PCPInstance)

/-- Local variables — see `GuessAX.Vars`. -/
inductive Vars | aux | cntY | cnt | prev | j | N | fst
  deriving DecidableEq

instance : Fintype Vars :=
  Fintype.ofList [Vars.aux, .cntY, .cnt, .prev, .j, .N, .fst]
    (by intro x; cases x <;> simp)

/-- Local values — see `GuessAX.Vals`. -/
abbrev Vals := Option (Fin I.n) ⊕ Fin 4 ⊕ Fin (maxLen I + 2) ⊕ Bool

inductive Expr | nextCntY | readCnt | nextCnt | betaLen | jIncr | fstFalse | one
inductive BExpr | tt | jLeN | isFirst | isBot

def auxOf (φ : Vars → Vals I) : Option (Fin I.n) :=
  match φ .aux with
  | .inl a => a
  | .inr _ => none

def cntYOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .cntY with
  | .inr (.inl v) => v
  | _ => 0

def cntOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .cnt with
  | .inr (.inl v) => v
  | _ => 0

def prevOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .prev with
  | .inr (.inl v) => v
  | _ => 0

def jOf (φ : Vars → Vals I) : Fin (maxLen I + 2) :=
  match φ .j with
  | .inr (.inr (.inl v)) => v
  | _ => 0

def NOf (φ : Vars → Vals I) : Fin (maxLen I + 2) :=
  match φ .N with
  | .inr (.inr (.inl v)) => v
  | _ => 0

def eval : Expr → (Vars → Vals I) → Vals I
  | .nextCntY, φ => .inr (.inl (cntYOf I φ + 1))
  | .readCnt, φ => φ .cnt
  | .nextCnt, φ => .inr (.inl (cntOf I φ + 1))
  | .betaLen, φ =>
      .inr (.inr (.inl ⟨(extBeta I (auxOf I φ)).length,
        by have := extBeta_length_le I (auxOf I φ); omega⟩))
  | .jIncr, φ => .inr (.inr (.inl (jOf I φ + 1)))
  | .fstFalse, _ => .inr (.inr (.inr false))
  | .one, _ => .inr (.inr (.inl ⟨1, by have := maxLen_pos I; omega⟩))

def evalB : BExpr → (Vars → Vals I) → Bool
  | .tt, _ => true
  | .jLeN, φ => decide (jOf I φ ≤ NOf I φ)
  | .isFirst, φ => match φ .fst with
      | .inr (.inr (.inr b)) => b
      | _ => false
  | .isBot, φ => match φ .aux with
      | .inl none => true
      | .inl (some _) => false
      | .inr _ => false

/-- The `j`-th letter of `β_aux` — see `GuessAX.jthLetter`. -/
def jthLetter (aux : Option (Fin I.n)) (j : Fin (maxLen I + 2)) : Option I.Γ :=
  ((extBeta I aux)[j.val - 1]?).getD none

inductive VExpr | cntYVal | xTagFirst | xTagRest | cntVal | prevVal | cntYAuxVal

def evalV : VExpr → (Vars → Vals I) → Val I
  | .cntYVal, φ => .cnt (cntYOf I φ)
  | .xTagFirst, φ => .xTag (Tid.guessBX, true) (jthLetter I (auxOf I φ) (jOf I φ))
  | .xTagRest, φ => .xTag (Tid.guessBX, false) (jthLetter I (auxOf I φ) (jOf I φ))
  | .cntVal, φ => .cnt (cntOf I φ)
  | .prevVal, φ => .cnt (prevOf I φ)
  | .cntYAuxVal, φ => .cntAux (cntYOf I φ) (auxOf I φ)

def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals I
  Expr := Expr
  eval := eval I
  BExpr := BExpr
  evalB := evalB I
  VExpr := VExpr
  evalV := evalV I

def auxSet : Finset (Vals I) :=
  (Finset.univ : Finset (Fin I.n)).image (fun v => (Sum.inl (some v) : Vals I))

theorem auxSet_nonempty : (auxSet I).Nonempty :=
  (Finset.univ_nonempty (α := Fin I.n)).image _

def auxSetBot : Finset (Vals I) :=
  (Finset.univ : Finset (Option (Fin I.n))).image (fun v => (Sum.inl v : Vals I))

theorem auxSetBot_nonempty : (auxSetBot I).Nonempty :=
  Finset.univ_nonempty.image _

/-- The `for` loop's body — see `GuessAX.innerBody`. -/
def innerBody : Command (domainOf I) (Vocab I) :=
  .assign .prev .readCnt ;;                       -- prev ← c;
  .assign .cnt .nextCnt ;;                        -- c ← (c + 1) mod 4;
  Command.firstIt .fst .fstFalse .isFirst         -- if First() then
    (.write .xB .xTagFirst ;;                     --   w(x_β, ⟨ḡ_β^x, β_aux[j]⟩);
     .write .zBx'x .cntVal)                       --   w(z_β^{x',x}, c);
                                                  -- else
    (.write .xB .xTagRest ;;                      --   w(x_β, ⟨g_β^x, β_aux[j]⟩);
     .write .zBx'x .cntVal ;;                     --   w(z_β^{x',x}, c);
     .read .zBxx' .prevVal)                       --   r(z_β^{x,x'}, prev);
                                                  -- endif

/-- The `while True do … done` loop's body — see `GuessAX.outerBody`. -/
def outerBody : Command (domainOf I) (Vocab I) :=
  .assign .cntY .nextCntY ;;                      -- c_y ← (c_y + 1) mod 4;
  .write .zBxy .cntYVal ;;                        -- w(z_β^{x,y}, c_y);
  Command.forLoop .j .N .betaLen .one .jLeN .jIncr  -- for j ∈ 1,…,|β_aux| do
    (innerBody I) ;;                              --   ⟨innerBody⟩
                                                  -- done
  .read .ellByx .cntYAuxVal ;;                    -- r(ℓ_β^{y,x}, ⟨c_y, aux⟩);
  .ite .isBot .brk .skip ;;                       -- if aux = ⊥ then break; endif
  .ndetAssign .aux (auxSetBot I) (auxSetBot_nonempty I)  -- aux ← NDet({1,…,n,⊥});

/-- **Paper:** Fig. 7, thread `g_β^x`. -/
def program : Command (domainOf I) (Vocab I) :=
                                                  -- β_⊥ ← ⊥;
  .ndetAssign .aux (auxSet I) (auxSet_nonempty I) ;;  -- aux ← NDet({1,…,n});
  Command.whileLoop .tt                           -- while True do
    (outerBody I) ;;                              --   ⟨outerBody⟩
                                                  -- done
  .term                                           -- term

/-- `Command.IsProgram` (App. A, Syntax) for `g_β^x`: one `term`, and its
`break` (in `outerBody`) sits within the `whileLoop`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end GuessBX

namespace GuessBY

variable (I : PCPInstance)

/-- Local variables — see `GuessAY.Vars`. -/
inductive Vars | aux | cnt | prev | fst
  deriving DecidableEq

instance : Fintype Vars :=
  Fintype.ofList [Vars.aux, .cnt, .prev, .fst] (by intro x; cases x <;> simp)

/-- Local values — see `GuessAY.Vals`. -/
abbrev Vals := Option (Fin I.n) ⊕ Fin 4 ⊕ Bool

inductive Expr | readCnt | nextCnt | fstFalse
inductive BExpr | tt | isFirst | isBot

def eval : Expr → (Vars → Vals I) → Vals I
  | .readCnt, φ => φ .cnt
  | .nextCnt, φ => match φ .cnt with
      | .inr (.inl v) => .inr (.inl (v + 1))
      | _ => .inr (.inl 0)
  | .fstFalse, _ => .inr (.inr false)

def evalB : BExpr → (Vars → Vals I) → Bool
  | .tt, _ => true
  | .isFirst, φ => match φ .fst with
      | .inr (.inr b) => b
      | _ => false
  | .isBot, φ => match φ .aux with
      | .inl none => true
      | .inl (some _) => false
      | .inr _ => false

inductive VExpr | yTagFirst | yTagRest | cntAuxVal | cntVal | prevVal

def auxOf (φ : Vars → Vals I) : Option (Fin I.n) :=
  match φ .aux with
  | .inl a => a
  | .inr _ => none

def cntOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .cnt with
  | .inr (.inl v) => v
  | _ => 0

def prevOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .prev with
  | .inr (.inl v) => v
  | _ => 0

def evalV : VExpr → (Vars → Vals I) → Val I
  | .yTagFirst, φ => .yTag (Tid.guessBY, true) (auxOf I φ)
  | .yTagRest, φ => .yTag (Tid.guessBY, false) (auxOf I φ)
  | .cntAuxVal, φ => .cntAux (cntOf I φ) (auxOf I φ)
  | .cntVal, φ => .cnt (cntOf I φ)
  | .prevVal, φ => .cnt (prevOf I φ)

def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals I
  Expr := Expr
  eval := eval I
  BExpr := BExpr
  evalB := evalB I
  VExpr := VExpr
  evalV := evalV I

def auxSet : Finset (Vals I) :=
  (Finset.univ : Finset (Fin I.n)).image (fun v => (Sum.inl (some v) : Vals I))

theorem auxSet_nonempty : (auxSet I).Nonempty :=
  (Finset.univ_nonempty (α := Fin I.n)).image _

def auxSetBot : Finset (Vals I) :=
  (Finset.univ : Finset (Option (Fin I.n))).image (fun v => (Sum.inl v : Vals I))

theorem auxSetBot_nonempty : (auxSetBot I).Nonempty :=
  Finset.univ_nonempty.image _

/-- The `while True do … done` loop's body — see `GuessAY.loopBody`. -/
def loopBody : Command (domainOf I) (Vocab I) :=
  .assign .prev .readCnt ;;                       -- prev ← c;
  .assign .cnt .nextCnt ;;                        -- c ← (c + 1) mod 4;
  Command.firstIt .fst .fstFalse .isFirst         -- if First() then
    (.write .yB .yTagFirst ;;                     --   w(y_β, ⟨ḡ_β^y, aux⟩);
     .write .ellByx .cntAuxVal ;;                 --   w(ℓ_β^{y,x}, ⟨c, aux⟩);
     .write .zBy'y .cntVal)                       --   w(z_β^{y',y}, c);
                                                  -- else
    (.write .yB .yTagRest ;;                      --   w(y_β, ⟨g_β^y, aux⟩);
     .write .ellByx .cntAuxVal ;;                 --   w(ℓ_β^{y,x}, ⟨c, aux⟩);
     .write .zBy'y .cntVal ;;                     --   w(z_β^{y',y}, c);
     .read .zBxy .prevVal ;;                      --   r(z_β^{x,y}, prev);
     .read .zByy' .prevVal) ;;                    --   r(z_β^{y,y'}, prev);
                                                  -- endif
  .ite .isBot .brk .skip ;;                       -- if aux = ⊥ then break; endif
  .ndetAssign .aux (auxSetBot I) (auxSetBot_nonempty I)  -- aux ← NDet({1,…,n,⊥});

/-- **Paper:** Fig. 7, thread `g_β^y`. -/
def program : Command (domainOf I) (Vocab I) :=
                                                  -- β_⊥ ← ⊥;
  .ndetAssign .aux (auxSet I) (auxSet_nonempty I) ;;  -- aux ← NDet({1,…,n});
  Command.whileLoop .tt                           -- while True do
    (loopBody I) ;;                               --   ⟨loopBody⟩
                                                  -- done
  .term                                           -- term

/-- `Command.IsProgram` (App. A, Syntax) for `g_β^y`: one `term`, and its
`break` sits within the `whileLoop`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end GuessBY

/-! ## Thread `c^y` -/

-- Thread `c^y`: `c^x` with `x` replaced by `y`, except that `aux` ranges over
-- indices `{1,…,n}` (`Option (Fin I.n)`), not letters `Γ`.
namespace CheckY

variable (I : PCPInstance)

/-- Local variables — see `CheckX.Vars`. -/
inductive Vars | aux | cnt | prev | fst
  deriving DecidableEq

instance : Fintype Vars :=
  Fintype.ofList [Vars.aux, .cnt, .prev, .fst] (by intro x; cases x <;> simp)

/-- Local values: `aux` over `Option (Fin I.n)` (unlike `CheckX.Vals`);
`cnt`/`prev` share `Fin 4`; `fst` is `Bool`. -/
abbrev Vals := Option (Fin I.n) ⊕ Fin 4 ⊕ Bool

inductive Expr | readCnt | nextCnt | fstFalse
inductive BExpr | tt | isFirst | isBot

def auxOf (φ : Vars → Vals I) : Option (Fin I.n) :=
  match φ .aux with
  | .inl a => a
  | .inr _ => none

def cntOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .cnt with
  | .inr (.inl v) => v
  | _ => 0

def prevOf (φ : Vars → Vals I) : Fin 4 :=
  match φ .prev with
  | .inr (.inl v) => v
  | _ => 0

def eval : Expr → (Vars → Vals I) → Vals I
  | .readCnt, φ => φ .cnt
  | .nextCnt, φ => .inr (.inl (cntOf I φ + 1))
  | .fstFalse, _ => .inr (.inr false)

def evalB : BExpr → (Vars → Vals I) → Bool
  | .tt, _ => true
  | .isFirst, φ => match φ .fst with
      | .inr (.inr b) => b
      | _ => false
  | .isBot, φ => match φ .aux with
      | .inl none => true
      | .inl (some _) => false
      | .inr _ => false

/-- `⟨c^y, c⟩`, written to both `y_α` and `y_β`; `⟨ḡ_α^y/g_α^y, aux⟩`
(resp. `g_β^y`), expected when reading `y_α` (resp. `y_β`); and
`⟨c^{y'}, prev⟩`, expected when reading `y'_α`/`y'_β`. -/
inductive VExpr | cntTagVal | yAFirst | yARest | yBFirst | yBRest | primeCheckVal

def evalV : VExpr → (Vars → Vals I) → Val I
  | .cntTagVal, φ => .primeTag Tid.checkY (cntOf I φ)
  | .yAFirst, φ => .yTag (Tid.guessAY, true) (auxOf I φ)
  | .yARest, φ => .yTag (Tid.guessAY, false) (auxOf I φ)
  | .yBFirst, φ => .yTag (Tid.guessBY, true) (auxOf I φ)
  | .yBRest, φ => .yTag (Tid.guessBY, false) (auxOf I φ)
  | .primeCheckVal, φ => .primeTag Tid.primeCheckY (prevOf I φ)

def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals I
  Expr := Expr
  eval := eval I
  BExpr := BExpr
  evalB := evalB I
  VExpr := VExpr
  evalV := evalV I

/-- `{1,…,n}`, as `Vals` — `aux`'s first draw, `⊥` excluded. -/
def auxSet : Finset (Vals I) :=
  (Finset.univ : Finset (Fin I.n)).image (fun v => (Sum.inl (some v) : Vals I))

theorem auxSet_nonempty : (auxSet I).Nonempty :=
  (Finset.univ_nonempty (α := Fin I.n)).image _

/-- `{1,…,n,⊥}`, as `Vals` — every later draw of `aux`. -/
def auxSetBot : Finset (Vals I) :=
  (Finset.univ : Finset (Option (Fin I.n))).image (fun v => (Sum.inl v : Vals I))

theorem auxSetBot_nonempty : (auxSetBot I).Nonempty :=
  Finset.univ_nonempty.image _

/-- The `while True do … done` loop's body — see `CheckX.body`. -/
def body : Command (domainOf I) (Vocab I) :=
  .assign .prev .readCnt ;;                       -- prev ← c;
  .assign .cnt .nextCnt ;;                        -- c ← (c + 1) mod 4;
  .write .yA .cntTagVal ;;                        -- w(y_α, ⟨c^y, c⟩);
  .write .yB .cntTagVal ;;                        -- w(y_β, ⟨c^y, c⟩);
  Command.firstIt .fst .fstFalse .isFirst         -- if First() then
    (.read .yA .yAFirst ;;                        --   r(y_α, ⟨ḡ_α^y, aux⟩);
     .read .yB .yBFirst)                          --   r(y_β, ⟨ḡ_β^y, aux⟩);
                                                  -- else
    (.read .yA .yARest ;;                         --   r(y_α, ⟨g_α^y, aux⟩);
     .read .yB .yBRest ;;                         --   r(y_β, ⟨g_β^y, aux⟩);
     .read .yA' .primeCheckVal ;;                 --   r(y'_α, ⟨c^{y'}, prev⟩);
     .read .yB' .primeCheckVal) ;;                --   r(y'_β, ⟨c^{y'}, prev⟩);
                                                  -- endif
  .ite .isBot .brk .skip ;;                       -- if aux = ⊥ then break; endif
  .ndetAssign .aux (auxSetBot I) (auxSetBot_nonempty I)  -- aux ← NDet({1,…,n,⊥});

/-- **Paper:** Fig. 7, thread `c^y`. -/
def program : Command (domainOf I) (Vocab I) :=
  .ndetAssign .aux (auxSet I) (auxSet_nonempty I) ;;  -- aux ← NDet({1,…,n});
  Command.whileLoop .tt                           -- while True do
    (body I) ;;                                   --   ⟨body⟩
                                                  -- done
  .term                                           -- term

/-- `Command.IsProgram` (App. A, Syntax) for `c^y`: one `term`, and its
`break` sits within the `whileLoop`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end CheckY

/-! ## Thread `c^{y'}` -/

-- Thread `c^{y'}`: `c^{x'}` with `x` replaced by `y`.
namespace PrimeCheckY

variable (I : PCPInstance)

/-- Local variables — see `PrimeCheckX.Vars`. -/
inductive Vars | cnt | b
  deriving DecidableEq

instance : Fintype Vars := Fintype.ofList [Vars.cnt, .b] (by intro x; cases x <;> simp)

abbrev Vals := Fin 4 ⊕ Bool

inductive Expr | nextCnt
inductive BExpr | isB

def cntOf (φ : Vars → Vals) : Fin 4 :=
  match φ .cnt with
  | .inl v => v
  | .inr _ => 0

def eval : Expr → (Vars → Vals) → Vals
  | .nextCnt, φ => .inl (cntOf φ + 1)

def evalB : BExpr → (Vars → Vals) → Bool
  | .isB, φ => match φ .b with
      | .inr v => v
      | .inl _ => false

/-- `⟨c^{y'}, c⟩`, written to both `y'_α` and `y'_β`; `⟨g_α^{y'}, 0⟩` (resp.
`⟨g_β^{y'}, 0⟩`), expected when reading `y'_α` (resp. `y'_β`); and
`⟨c^y, c⟩`, expected when reading `y_α`/`y_β`. -/
inductive VExpr | cntTagVal | yApExpect | yBpExpect | checkExpect

def evalV : VExpr → (Vars → Vals) → Val I
  | .cntTagVal, φ => .primeTag Tid.primeCheckY (cntOf φ)
  | .yApExpect, _ => .primeTag Tid.primeAY 0
  | .yBpExpect, _ => .primeTag Tid.primeBY 0
  | .checkExpect, φ => .primeTag Tid.checkY (cntOf φ)

def Vocab : Vocabulary (domainOf I) where
  LVar := Vars
  LVal := Vals
  Expr := Expr
  eval := eval
  BExpr := BExpr
  evalB := evalB
  VExpr := VExpr
  evalV := evalV I

def X : Finset Vals := {Sum.inr false, Sum.inr true}

theorem X_nonempty : X.Nonempty := ⟨Sum.inr false, by decide⟩

/-- The loop body — see `PrimeCheckX.body`. -/
def body : Command (domainOf I) (Vocab I) :=
  .assign .cnt .nextCnt ;;       -- c ← (c + 1) mod 4;
  .write .yA' .cntTagVal ;;      -- w(y'_α, ⟨c^{y'}, c⟩);
  .write .yB' .cntTagVal ;;      -- w(y'_β, ⟨c^{y'}, c⟩);
  .read .yA' .yApExpect ;;       -- r(y'_α, ⟨g_α^{y'}, 0⟩);
  .read .yB' .yBpExpect ;;       -- r(y'_β, ⟨g_β^{y'}, 0⟩);
  .read .yA .checkExpect ;;      -- r(y_α, ⟨c^y, c⟩);
  .read .yB .checkExpect         -- r(y_β, ⟨c^y, c⟩);

/-- **Paper:** Fig. 7, thread `c^{y'}`. -/
def program : Command (domainOf I) (Vocab I) :=
  Command.whileNdet .b X X_nonempty .isB    -- while NDet({False, True}) do
    (body I) ;;                             --   ⟨body⟩
                                            -- done
  .term                                     -- term

/-- `Command.IsProgram` (App. A, Syntax) for `c^{y'}`: one `term`, and no
`break`. -/
theorem program_isProgram (I : PCPInstance) : (program I).IsProgram := ⟨rfl, rfl⟩

end PrimeCheckY

end RAUndecidability
