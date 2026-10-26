import RAUndecidability.Defs.Program
import Mathlib.Logic.Relation
import Mathlib.Order.RelClasses
import Mathlib.Data.Finset.Sort

/-!
# Execution graphs

Section 2 (executions):

* §2.2: events (over the event labels of event labels (§2.1),
  `Defs/Program.lean`), and the read/write subsets of the event domain;
* §2.2: execution graphs (`po`, `rf`, `mo`);
* §2.2: happens-before;
* §2.2: Release/Acquire consistency;
* §2.2: the thread word of an execution;
* §2.2: the Release/Acquire semantics of a concurrent program;
* §2.2: reaching a state, and the reachability problem.

Definitions only, except for `ExecutionGraph.hb_mem_events` and
`ExecutionGraph.hb_mem_events_left`: small, general facts about `hb` — that an
`hb`-edge's target (resp. source) is always one of `G`'s own events — needed
by Lemma 3.10 and Lemma 3.12 respectively, and
general enough to belong here rather than in `Completeness/Consistency.lean`.
-/

namespace RAUndecidability

variable {D : Domains}

/-! ## Events (§2.2) -/

/-- **Paper:** §2.2, ¶ Events.

An event (§2.2): an identifier paired with an event label. -/
structure Event (D : Domains) where
  /-- The event's identifier. -/
  id : ℕ
  /-- The event's label, `llab(event)` in the paper. -/
  lab : EventLabel D

/-- The thread of an event. -/
def Event.tid (e : Event D) : D.Tid := e.lab.tid

/-- The location of an event. -/
def Event.loc (e : Event D) : D.Loc := e.lab.loc

/-- The operation of an event. -/
def Event.op (e : Event D) : OpType := e.lab.op

/-- The value carried by an event: read, for a reading event, or written, for
a writing event. See `EventLabel.val`. -/
def Event.val (e : Event D) : D.Val := e.lab.val

/-- An event is writing if its operation is `wt` (§2.2). -/
abbrev Event.IsWriting (e : Event D) : Prop := e.op = .wt

/-- An event is reading if its operation is `rd` (§2.2). No event is
both writing and reading, since `OpType.rd ≠ OpType.wt`. -/
abbrev Event.IsReading (e : Event D) : Prop := e.op = .rd

/-- `EventDom` (§2.2): the domain of events. -/
abbrev EventDom (D : Domains) := Event D

/-- `ReadDom` (§2.2): the reading events. -/
def ReadDom (D : Domains) : Set (Event D) := {e | e.IsReading}

/-- `WriteDom` (§2.2): the writing events. -/
def WriteDom (D : Domains) : Set (Event D) := {e | e.IsWriting}

/-! ## Execution graphs (§2.2) -/

/-- **Paper:** §2.2, ¶ Execution graphs.

An execution graph (§2.2): a finite set of events, with
unique identifiers, carrying a program order `po`, reads-from relation `rf`,
and modification order `mo`. Finiteness follows an earlier version of
the paper; the paper does not state it, but an execution reaching a state of a
program is finite anyway, and the thread word of an execution (§2.2) needs it. -/
structure ExecutionGraph (D : Domains) where
  /-- The finite set of events participating in the execution. -/
  Events : Finset (Event D)
  /-- The program order. -/
  po : Event D → Event D → Prop
  /-- The reads-from relation. -/
  rf : Event D → Event D → Prop
  /-- The modification order. -/
  mo : Event D → Event D → Prop
  /-- `po` only relates events of `Events` on the same thread. -/
  po_subset : ∀ {e1 e2}, po e1 e2 → e1 ∈ Events ∧ e2 ∈ Events ∧ e1.tid = e2.tid
  /-- `po` is a total order on the events of each thread. -/
  po_total : ∀ t, IsStrictTotalOrder {e // e ∈ Events.filter (fun e => e.tid = t)}
      (fun a b => po a.1 b.1)
  /-- `rf` only relates a writing event of `Events` to a reading event of
  `Events` on the same location. -/
  rf_subset : ∀ {ew er}, rf ew er → ew ∈ Events ∧ er ∈ Events ∧
      ew ∈ WriteDom D ∧ er ∈ ReadDom D ∧ ew.loc = er.loc
  /-- The connected events agree on the value. -/
  rf_matches : ∀ {ew er}, rf ew er → ew.val = er.val
  /-- A reading event has at most one incoming `rf`-edge. -/
  rf_unique : ∀ {ew1 ew2 er}, rf ew1 er → rf ew2 er → ew1 = ew2
  /-- Every reading event of `Events` has an incoming `rf`-edge. -/
  rf_total : ∀ {er}, er ∈ Events → er ∈ ReadDom D → ∃ ew, rf ew er
  /-- `mo` only relates writing events of `Events` on the same location. -/
  mo_subset : ∀ {e1 e2}, mo e1 e2 → e1 ∈ Events ∧ e2 ∈ Events ∧
      e1 ∈ WriteDom D ∧ e2 ∈ WriteDom D ∧ e1.loc = e2.loc
  /-- `mo` is a total order on the writing events of `Events` on each
  location. -/
  mo_total : ∀ x, IsStrictTotalOrder
      {e // e ∈ Events.filter (fun e => e.IsWriting ∧ e.loc = x)} (fun a b => mo a.1 b.1)
  /-- Events are attached to "some arbitrary unique identifier" (§2.2,
  the "Events" paragraph): an event of `Events` is
  determined by its `id` alone, among `Events`. -/
  ids_unique : ∀ {e1 e2}, e1 ∈ Events → e2 ∈ Events → e1.id = e2.id → e1 = e2

/-! ## Happens-before (§2.2) -/

/-- **Paper:** §2.2, ¶ Release/Acquire semantics (hb).

Happens-before (§2.2): `hb ≜ (po ∪ rf)⁺`. -/
def ExecutionGraph.hb (G : ExecutionGraph D) : Event D → Event D → Prop :=
  Relation.TransGen (fun e1 e2 => G.po e1 e2 ∨ G.rf e1 e2)

/-- An `hb`-edge's target is one of `G`'s events. -/
theorem ExecutionGraph.hb_mem_events {G : ExecutionGraph D} {a b : Event D} (h : G.hb a b) :
    b ∈ G.Events := by
  induction h with
  | single hab => rcases hab with h | h; exacts [(G.po_subset h).2.1, (G.rf_subset h).2.1]
  | tail _ hbc _ => rcases hbc with h | h; exacts [(G.po_subset h).2.1, (G.rf_subset h).2.1]

/-- An `hb`-edge's source is one of `G`'s events. -/
theorem ExecutionGraph.hb_mem_events_left {G : ExecutionGraph D} {a b : Event D}
    (h : G.hb a b) : a ∈ G.Events := by
  induction h using Relation.TransGen.head_induction_on with
  | single hab => rcases hab with h | h; exacts [(G.po_subset h).1, (G.rf_subset h).1]
  | head hac _ _ => rcases hac with h | h; exacts [(G.po_subset h).1, (G.rf_subset h).1]

/-! ## RA-consistency (§2.2) -/

/-- **Paper:** §2.2, ¶ Release/Acquire semantics; Fig. 1.

Release/Acquire consistency (§2.2). -/
structure ExecutionGraph.RAConsistent (G : ExecutionGraph D) : Prop where
  /-- `hb` is irreflexive. -/
  irr_hb : ∀ e, ¬ G.hb e e
  /-- `mo;hb` is irreflexive. -/
  write_coherence : ∀ e, ¬ Relation.Comp G.mo G.hb e e
  /-- `mo;hb;rf⁻¹` is irreflexive. -/
  read_coherence : ∀ e, ¬ Relation.Comp (Relation.Comp G.mo G.hb) (flip G.rf) e e

/-! ## The thread word of an execution (§2.2) -/

/-- The `po`-sorted thread-`t` events of `G` (the paper's
`e_1, …, e_n`, §2.2). By `po_total` this is the unique
list conforming to `po`; it is computed by `Finset.sort` against the
`LinearOrder` that `po_total` induces. -/
noncomputable def ExecutionGraph.threadEvents (G : ExecutionGraph D) (t : D.Tid) :
    List {e : Event D // e ∈ G.Events.filter (fun e => e.tid = t)} :=
  haveI := G.po_total t
  haveI : DecidableRel
      (fun a b : {e : Event D // e ∈ G.Events.filter (fun e => e.tid = t)} => G.po a.1 b.1) :=
    Classical.decRel _
  haveI : LinearOrder {e : Event D // e ∈ G.Events.filter (fun e => e.tid = t)} :=
    linearOrderOfSTO fun a b => G.po a.1 b.1
  Finset.univ.sort (· ≤ ·)

/-- `Word{G}{t}` (§2.2): the labels of the thread-`t` events of
`G`, in `po`-order, as a word over `LabelDom^t ∪ {term}`. Never contains
`term`: every element is wrapped in `some`. -/
noncomputable def ExecutionGraph.threadWord (G : ExecutionGraph D) (t : D.Tid) :
    Word (Option (ThreadLabel D t)) :=
  (G.threadEvents t).map
    fun (e : {x // x ∈ G.Events.filter (fun e => e.tid = t)}) =>
      let he : e.1.tid = t := (Finset.mem_filter.mp e.2).2
      (some ⟨e.1.lab, he⟩ : Option (ThreadLabel D t))

/-! ## The RA semantics (§2.2) -/

/-- **Paper:** §2.2, ¶ Release/Acquire program semantics.

`⟦P⟧_RA` (§2.2): the
RA-consistent execution graphs whose thread words are words of the
corresponding sequential programs. -/
def ConcurrentProgram.RASemantics (C : ConcurrentProgram D) : Set (ExecutionGraph D) :=
  {G | G.RAConsistent ∧ ∀ t, (C.prog t).IsWord (G.threadWord t)}

/-! ## Reachability (§2.2) -/

/-- `G` reaches the global state `p` of `C` (§2.2): `G` is in
`C`'s Release/Acquire semantics, and, for every thread `t`, `Word{G}{t}`
reaches `p t` in `Prog_t` when `p t ≠ Prog_t.final`, and `Word{G}{t}` with
`term` (`none`) appended reaches `p t` otherwise. This is the
definition of an earlier version of the paper, matching the `term`-based
`SequentialProgram`; the paper, having no `term`, asks only that
`Word{G}{t}` reach `p t` (see the README). -/
def ExecutionGraph.Reaches (G : ExecutionGraph D) (C : ConcurrentProgram D)
    (p : C.GlobalState) : Prop :=
  G ∈ C.RASemantics ∧
    ∀ t, (p t ≠ (C.prog t).final → (C.prog t).Reaches (G.threadWord t) (p t)) ∧
         (p t = (C.prog t).final →
           (C.prog t).Reaches (G.threadWord t ++ [none]) (p t))

/-- **Paper:** §2.2, ¶ Release/Acquire reachability.

The reachability problem (§2.2): does some execution graph
in `C`'s Release/Acquire semantics reach `C`'s final state? -/
def ConcurrentProgram.ReachesFinal (C : ConcurrentProgram D) : Prop :=
  ∃ G : ExecutionGraph D, G.Reaches C C.final

end RAUndecidability
