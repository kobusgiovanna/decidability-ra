import Mathlib.Data.Fintype.Basic

/-!
# Programs

Section 2 (preliminaries and programs):

* §2.1: the domains of values, locations and thread identifiers,
  fixed once for the whole development;
* §2.1: labeled transition systems;
* §2.1: words over an alphabet, independently of any LTS;
* §2.1: words of an LTS, and reaching a state;
* §2.1: event labels, their thread/location/operation/value
  projections, and the thread-indexed label sets `LabelDom^t`;
* §2.1: sequential programs;
* §2.1: concurrent programs, and their global states.
-/

namespace RAUndecidability

/-! ## The domains (§2.1) -/

/-- The domains (§2.1): `Val`, `Loc` and `Tid` are finite,
non-empty types of values, shared memory locations and thread identifiers,
respectively, each with decidable equality. Values are opaque: nothing beyond
equality is assumed of them.

Section 3 supplies one concrete instance, `domainOf I`. -/
structure Domains where
  /-- The domain of values. -/
  Val : Type
  /-- The domain of shared memory locations. -/
  Loc : Type
  /-- The domain of thread identifiers. -/
  Tid : Type
  [valFintype : Fintype Val]
  [valNonempty : Nonempty Val]
  [valDecEq : DecidableEq Val]
  [locFintype : Fintype Loc]
  [locNonempty : Nonempty Loc]
  [locDecEq : DecidableEq Loc]
  [tidFintype : Fintype Tid]
  [tidNonempty : Nonempty Tid]
  [tidDecEq : DecidableEq Tid]

instance (D : Domains) : Fintype D.Val := D.valFintype
instance (D : Domains) : Nonempty D.Val := D.valNonempty
instance (D : Domains) : DecidableEq D.Val := D.valDecEq
instance (D : Domains) : Fintype D.Loc := D.locFintype
instance (D : Domains) : Nonempty D.Loc := D.locNonempty
instance (D : Domains) : DecidableEq D.Loc := D.locDecEq
instance (D : Domains) : Fintype D.Tid := D.tidFintype
instance (D : Domains) : Nonempty D.Tid := D.tidNonempty
instance (D : Domains) : DecidableEq D.Tid := D.tidDecEq

/-! ## LTSs (§2.1) -/

/-- **Paper:** §2.1, ¶ Labeled Transition Systems.

A labeled transition system (LTS) over an alphabet `Letter`, with state
type `State` (§2.1). `trans p a q` records that `(p, a, q)` is a
transition, written `p ⟶[a] q` in the paper.

Item (i) of LTSs (§2.1), finiteness of the state set, is required by
`SequentialProgram` instead, since for the induced LTS of a command it is a
theorem (App. A). -/
structure LTS (Letter State : Type) where
  /-- The transition relation. -/
  trans : State → Letter → State → Prop
  /-- The initial state. -/
  init : State
  /-- The final state. -/
  final : State

/-! ## Words (§2.1) -/

/-- **Paper:** §2.1, ¶ Labeled Transition Systems (words).

A word over `Letter` (§2.1): a finite sequence of symbols. A word
is an object in its own right, independent of any LTS. Concatenation of words
is list append (`++`).

The alphabet's finiteness and non-emptiness is not needed here; the concrete
alphabets `LabelDom^t ∪ {term}` inherit it from `Domains`. -/
abbrev Word (Letter : Type) := List Letter

/-! ## Words of an LTS (§2.1) -/

variable {Letter State : Type} (lts : LTS Letter State)

/-- `lts.Steps p σ q` holds if the word `σ` drives `lts` from `p` to `q`. -/
inductive LTS.Steps : State → Word Letter → State → Prop
  | nil {p} : LTS.Steps p [] p
  | cons {p q r a σ} : lts.trans p a q → LTS.Steps q σ r → LTS.Steps p (a :: σ) r

/-- `lts.Reaches σ q` holds if the word `σ` drives `lts` from its initial
state to `q` (§2.1). In particular `lts.Reaches [] lts.init` holds
immediately, by `LTS.Steps.nil`. -/
def LTS.Reaches (σ : Word Letter) (q : State) : Prop :=
  lts.Steps lts.init σ q

/-- A word `σ` is a word of `lts` if it reaches some state of `lts`
(§2.1). In particular the empty word is a word of every LTS. -/
def LTS.IsWord (σ : Word Letter) : Prop :=
  ∃ q, lts.Reaches σ q

/-- Extending `lts.Steps` by one more transition on the right. -/
theorem LTS.Steps.snoc {p q r : State} {w : Word Letter} {a : Letter}
    (h : lts.Steps p w q) (hstep : lts.trans q a r) : lts.Steps p (w ++ [a]) r := by
  induction h with
  | nil => exact LTS.Steps.cons hstep LTS.Steps.nil
  | cons htrans _ ih => exact LTS.Steps.cons htrans (ih hstep)

/-- The converse of `LTS.Steps.snoc`: a path ending in one more transition
inverts to a shorter path plus that final transition. -/
theorem LTS.Steps.snoc_inv {p r : State} (w : Word Letter) (a : Letter)
    (h : lts.Steps p (w ++ [a]) r) : ∃ q, lts.Steps p w q ∧ lts.trans q a r := by
  induction w generalizing p with
  | nil =>
      simp only [List.nil_append] at h
      cases h with
      | cons htrans hrest =>
          cases hrest with
          | nil => exact ⟨p, LTS.Steps.nil, htrans⟩
  | cons b w' ih =>
      simp only [List.cons_append] at h
      cases h with
      | cons htrans hrest =>
          obtain ⟨q, hq1, hq2⟩ := ih hrest
          exact ⟨q, LTS.Steps.cons htrans hq1, hq2⟩

/-! ## Event labels (§2.1) -/

variable {D : Domains}

/-- **Paper:** §2.1, ¶ Event labels.

An event label (§2.1): a read label `r(t, x, v)` (`EventLabel.rd t x v`) or a
write label `w(t, x, v)` (`EventLabel.wt t x v`), where `t : D.Tid`, `x : D.Loc` and `v : D.Val`. `LabelDom`
of the paper is `EventLabel D`. The paper also has read-modify-write
labels `rmw t x v_r v_w`; they are omitted, since the reduction concerns
RMW-free programs. -/
inductive EventLabel (D : Domains) : Type
  | rd (t : D.Tid) (x : D.Loc) (v : D.Val)
  | wt (t : D.Tid) (x : D.Loc) (v : D.Val)
  deriving DecidableEq

/-- The thread identifier of an event label. -/
def EventLabel.tid : EventLabel D → D.Tid
  | .rd t _ _ => t
  | .wt t _ _ => t

/-- The location of an event label. -/
def EventLabel.loc : EventLabel D → D.Loc
  | .rd _ x _ => x
  | .wt _ x _ => x

/-- The operation of an event label: read or write (§2.2). There is no
`rmw` operation: the reduction concerns RMW-free programs, so the paper's
general definitions are taken with no RMW events (its atomicity axiom is
then vacuous, and `rf`'s endpoints are distinct automatically). -/
inductive OpType
  | rd
  | wt
  deriving DecidableEq

/-- The operation of an event label. -/
def EventLabel.op : EventLabel D → OpType
  | .rd _ _ _ => .rd
  | .wt _ _ _ => .wt

/-- The value carried by an event label: the value read, for a read label, or
the value written, for a write label (the paper's `val_rd`/`val_wt` (§2.2), which
coincide here — each label carries exactly one value, so there is only one
function to extract it, not two). -/
def EventLabel.val : EventLabel D → D.Val
  | .rd _ _ v => v
  | .wt _ _ v => v

/-- `LabelDom^t` (§2.1): the event labels with thread identifier
`t`. -/
abbrev ThreadLabel (D : Domains) (t : D.Tid) : Type :=
  {l : EventLabel D // l.tid = t}

/-! ## Sequential programs (§2.1) -/

/-- **Paper:** §2.1, ¶ Sequential programs.

A sequential program of thread `t` (§2.1): an LTS
over `LabelDom^t ∪ {term}` — encoded as `Option (ThreadLabel D t)`, `term`
represented by `none` and event labels by `some l`, so `term ∉ LabelDom^t`
holds by construction — with finite states, such that a transition is
labeled `term` iff its target is `final`, and `final` has no outgoing
transitions.

This is the definition of an earlier version of the paper. The paper
takes a sequential program to be an LTS over `LabelDom^t` alone, with no
`term` symbol; this development keeps the `term`-based version (see the
README). -/
structure SequentialProgram (D : Domains) (t : D.Tid) (State : Type)
    extends LTS (Option (ThreadLabel D t)) State where
  /-- The state set is finite. -/
  stateFinite : Finite State
  /-- A transition is labeled `term` (`none`) iff its target is `final`. -/
  term_iff_final : ∀ {p a q}, trans p a q → (a = none ↔ q = final)
  /-- `final` has no outgoing transitions. -/
  final_no_outgoing : ∀ {a q}, ¬ trans final a q

/-! ## Concurrent programs (§2.1) -/

/-- **Paper:** §2.1, ¶ Concurrent programs.

A concurrent program (§2.1): one sequential program
per thread, threads possibly having different state types. `D.Tid` is finite
but not literally `Fin n`, so this is the dependent-function generalization
of the paper's tuple `⟨Prog_{t_1}, …, Prog_{t_n}⟩`. -/
structure ConcurrentProgram (D : Domains) where
  /-- The state type of each thread's sequential program. -/
  LocalState : D.Tid → Type
  /-- The sequential program of each thread. -/
  prog : (t : D.Tid) → SequentialProgram D t (LocalState t)

/-- A state of a concurrent program (§2.1): one local
state per thread. -/
def ConcurrentProgram.GlobalState (C : ConcurrentProgram D) : Type :=
  ∀ t, C.LocalState t

/-- The initial state of a concurrent program (§2.1). -/
def ConcurrentProgram.init (C : ConcurrentProgram D) : C.GlobalState :=
  fun t => (C.prog t).init

/-- The final state of a concurrent program (§2.1). -/
def ConcurrentProgram.final (C : ConcurrentProgram D) : C.GlobalState :=
  fun t => (C.prog t).final

end RAUndecidability
