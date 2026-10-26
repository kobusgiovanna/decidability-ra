import RAUndecidability.Defs.Execution
import Mathlib.Data.List.Chain

/-!
# hb-paths

Section 3.5's `hb`-path machinery and its proofs in Appendix B:

* §3.5: the `Path` datatype and its length;
* `Path.sound`, `Path.complete`: `Path` and `hb` agree;
* §3.5: alternating, minimal and bridge-free paths;
* `Path.exists_alternating`: every `hb`-connected pair has an alternating path;
* Lemma 3.7: alternating paths can be taken minimal;
* the path-level parts of Lemma 3.6.
-/

namespace RAUndecidability

variable {D : Domains}

/-! ## Hb-paths (§3.5) -/

/-- **Paper:** §3.5, ¶ Alternating and minimal hb-paths (hb-paths).

hb-paths (§3.5): an explicit sequence of `po`- and `rf`-edges, built like
`Relation.TransGen` (`single`/`tail`) but recording each edge's kind. `hb`
itself stays `(po ∪ rf)⁺` (`ExecutionGraph.hb`).

A `Type`, not a `Prop`, so that `Path.length` can be defined by recursion. -/
inductive Path (G : ExecutionGraph D) : Event D → Event D → Type
  /-- A single `po`-edge. -/
  | single_po {a b : Event D} (h : G.po a b) : Path G a b
  /-- A single `rf`-edge. -/
  | single_rf {a b : Event D} (h : G.rf a b) : Path G a b
  /-- Extending a path by one more `po`-edge at its end. -/
  | tail_po {a b c : Event D} (p : Path G a b) (h : G.po b c) : Path G a c
  /-- Extending a path by one more `rf`-edge at its end. -/
  | tail_rf {a b c : Event D} (p : Path G a b) (h : G.rf b c) : Path G a c

/-- The length of an hb-path (§3.5): the number of `po`-edges the path contains (the
quantity the shortening argument for minimal paths decreases). -/
def Path.length {G : ExecutionGraph D} {a b : Event D} : Path G a b → ℕ
  | .single_po _ => 1
  | .single_rf _ => 0
  | .tail_po p _ => p.length + 1
  | .tail_rf p _ => p.length

/-! ## `Path.sound`, `Path.complete` -/

/-- `Path.sound`: a path from `a` to `b` gives `a ⟶hb b`. Induction on
the path. -/
theorem Path.sound {G : ExecutionGraph D} {a b : Event D} : Path G a b → G.hb a b
  | .single_po h => Relation.TransGen.single (Or.inl h)
  | .single_rf h => Relation.TransGen.single (Or.inr h)
  | .tail_po p h => Relation.TransGen.tail p.sound (Or.inl h)
  | .tail_rf p h => Relation.TransGen.tail p.sound (Or.inr h)

/-- `Path.complete`: `a ⟶hb b` gives a path from `a` to `b`. Induction on
the `Relation.TransGen` derivation. Concludes `Nonempty (Path G a b)`, since a
`Prop` cannot be eliminated into the `Type`-valued `Path`. -/
theorem Path.complete {G : ExecutionGraph D} {a b : Event D} (h : G.hb a b) :
    Nonempty (Path G a b) := by
  induction h with
  | single hab =>
      rcases hab with hpo | hrf
      · exact ⟨.single_po hpo⟩
      · exact ⟨.single_rf hrf⟩
  | tail _ hbc ih =>
      rcases hbc with hpo | hrf
      · exact ⟨.tail_po ih.some hpo⟩
      · exact ⟨.tail_rf ih.some hrf⟩

/-! ## Alternating paths (§3.5) -/

/-- Whether a path's final edge is a `po`-edge. -/
def Path.lastIsPo {G : ExecutionGraph D} {a b : Event D} : Path G a b → Prop
  | .single_po _ => True
  | .single_rf _ => False
  | .tail_po _ _ => True
  | .tail_rf _ _ => False

/-- Whether a path's final edge is an `rf`-edge. -/
def Path.lastIsRf {G : ExecutionGraph D} {a b : Event D} (p : Path G a b) : Prop :=
  ¬ p.lastIsPo

/-- **Paper:** §3.5, ¶ Alternating and minimal hb-paths (alternating).

"alternating" (§3.5): no two consecutive edges are of
the same kind, i.e. the shape `a ⟶po^? w ⟶rf r ⟶po
⋯ ⟶rf r ⟶po^? b`.

Each `rf`-edge relates an arbitrary write to an arbitrary read: the shared
index in the paper's `w_{i_1} ⟶rf r_{i_1}` is a property of the
constructed `G`, not of a general execution. -/
def Path.IsAlternating {G : ExecutionGraph D} {a b : Event D} : Path G a b → Prop
  | .single_po _ => True
  | .single_rf _ => True
  | .tail_po p _ => p.IsAlternating ∧ p.lastIsRf
  | .tail_rf p _ => p.IsAlternating ∧ p.lastIsPo

/-! ## Facts about `po`/`rf` needed for `Path.exists_alternating` -/

/-- `po` is transitive: two consecutive `po`-edges compose into one. -/
theorem ExecutionGraph.po_trans (G : ExecutionGraph D) {e1 e2 e3 : Event D}
    (h12 : G.po e1 e2) (h23 : G.po e2 e3) : G.po e1 e3 := by
  obtain ⟨he1, he2, ht12⟩ := G.po_subset h12
  obtain ⟨-, he3, ht23⟩ := G.po_subset h23
  have hSTO := G.po_total e1.tid
  have hmem1 : e1 ∈ G.Events.filter (fun e => e.tid = e1.tid) :=
    Finset.mem_filter.mpr ⟨he1, rfl⟩
  have hmem2 : e2 ∈ G.Events.filter (fun e => e.tid = e1.tid) :=
    Finset.mem_filter.mpr ⟨he2, ht12.symm⟩
  have hmem3 : e3 ∈ G.Events.filter (fun e => e.tid = e1.tid) :=
    Finset.mem_filter.mpr ⟨he3, ht23.symm.trans ht12.symm⟩
  have := @IsTrans.trans _ (fun a b : {e // e ∈ G.Events.filter (fun e => e.tid = e1.tid)} =>
    G.po a.1 b.1) hSTO.toIsTrans ⟨e1, hmem1⟩ ⟨e2, hmem2⟩ ⟨e3, hmem3⟩ h12 h23
  exact this

/-- No event is both an `rf`-edge's source (a write) and another `rf`-edge's
target (a read), so two consecutive `rf`-edges cannot occur. -/
theorem ExecutionGraph.no_consecutive_rf (G : ExecutionGraph D) {a b c : Event D}
    (h1 : G.rf a b) (h2 : G.rf b c) : False := by
  have hrd : b.op = OpType.rd := (G.rf_subset h1).2.2.2.1
  have hwt : b.op = OpType.wt := (G.rf_subset h2).2.2.1
  rw [hrd] at hwt
  exact absurd hwt (by decide)

/-! ## `Path.exists_alternating` -/

/-- The merging half of `Path.exists_alternating`: every path can be normalized
into an alternating one with the same endpoints, by collapsing consecutive
`po`-edges (`ExecutionGraph.po_trans`) and ruling out consecutive `rf`-edges
(`ExecutionGraph.no_consecutive_rf`). By structural recursion on `p`. -/
theorem Path.exists_alternating {G : ExecutionGraph D} {a b : Event D} (p : Path G a b) :
    ∃ p' : Path G a b, p'.IsAlternating := by
  induction p with
  | single_po h => exact ⟨.single_po h, trivial⟩
  | single_rf h => exact ⟨.single_rf h, trivial⟩
  | tail_po p h ih =>
      obtain ⟨p', hp'⟩ := ih
      by_cases hpo : p'.lastIsPo
      · cases p' with
        | single_po h' => exact ⟨.single_po (G.po_trans h' h), trivial⟩
        | tail_po p'' h' => exact ⟨.tail_po p'' (G.po_trans h' h), hp'⟩
        | single_rf _ => simp [Path.lastIsPo] at hpo
        | tail_rf _ _ => simp [Path.lastIsPo] at hpo
      · exact ⟨.tail_po p' h, hp', hpo⟩
  | tail_rf p h ih =>
      obtain ⟨p', hp'⟩ := ih
      cases p' with
      | single_po h' => exact ⟨.tail_rf (.single_po h') h, trivial, trivial⟩
      | tail_po p'' h' => exact ⟨.tail_rf (.tail_po p'' h') h, hp', trivial⟩
      | single_rf h' => exact (G.no_consecutive_rf h' h).elim
      | tail_rf _ h' => exact (G.no_consecutive_rf h' h).elim

/-- `Path.exists_alternating`: if `a ⟶hb b` then there is an alternating path
from `a` to `b` (`Path.complete`, then `Path.exists_alternating`). -/
theorem Path.exists_alternating_of_hb {G : ExecutionGraph D} {a b : Event D}
    (h : G.hb a b) : ∃ p : Path G a b, p.IsAlternating := by
  obtain ⟨p⟩ := Path.complete h
  exact p.exists_alternating

/-! ## Lemma 3.7 (§3.5) -/

/-- The threads the path's `po`-edges lie on, one per `po`-edge, in path
order. -/
def Path.poThreads {G : ExecutionGraph D} {a b : Event D} : Path G a b → List D.Tid
  | .single_po _ => [b.tid]
  | .single_rf _ => []
  | .tail_po p _ => p.poThreads ++ [b.tid]
  | .tail_rf p _ => p.poThreads

/-- **Paper:** §3.5, ¶ Alternating and minimal hb-paths (minimal).

"minimal" (§3.5): every `po`-edge of the path is on a
distinct thread, i.e. `poThreads` has no repeats. -/
def Path.IsMinimal {G : ExecutionGraph D} {a b : Event D} (p : Path G a b) : Prop :=
  p.poThreads.Nodup

/-- Every event the path touches (its endpoints and every intermediate event)
satisfies `P`. "bridge-free" and "contained in a
thread set" (§3.5) are instances. -/
def Path.AllEventsSatisfy {G : ExecutionGraph D} {a b : Event D} (P : Event D → Prop) :
    Path G a b → Prop
  | .single_po _ => P a ∧ P b
  | .single_rf _ => P a ∧ P b
  | .tail_po p _ => p.AllEventsSatisfy P ∧ P b
  | .tail_rf p _ => p.AllEventsSatisfy P ∧ P b

theorem Path.allEventsSatisfy_right {G : ExecutionGraph D} {a b : Event D} {P : Event D → Prop} :
    ∀ (p : Path G a b), p.AllEventsSatisfy P → P b
  | .single_po _, h => h.2
  | .single_rf _, h => h.2
  | .tail_po _ _, h => h.2
  | .tail_rf _ _, h => h.2

/-- `AllEventsSatisfy` is monotone in its predicate. -/
theorem Path.allEventsSatisfy_mono {G : ExecutionGraph D} {a b : Event D} {P Q : Event D → Prop}
    (h : ∀ e, P e → Q e) : ∀ (p : Path G a b), p.AllEventsSatisfy P → p.AllEventsSatisfy Q
  | .single_po _, hp => ⟨h _ hp.1, h _ hp.2⟩
  | .single_rf _, hp => ⟨h _ hp.1, h _ hp.2⟩
  | .tail_po p _, hp => ⟨p.allEventsSatisfy_mono h hp.1, h _ hp.2⟩
  | .tail_rf p _, hp => ⟨p.allEventsSatisfy_mono h hp.1, h _ hp.2⟩

/-- If a set `S` of events is closed under a single `hb`-step and contains the
path's source, every event the path touches is in `S`. -/
theorem Path.allEventsSatisfy_of_hb_closed {G : ExecutionGraph D} {a b : Event D}
    {S : Event D → Prop} (hS : ∀ ⦃x y⦄, S x → G.hb x y → S y) (ha : S a) :
    ∀ (p : Path G a b), p.AllEventsSatisfy S
  | .single_po h => ⟨ha, hS ha (Relation.TransGen.single (Or.inl h))⟩
  | .single_rf h => ⟨ha, hS ha (Relation.TransGen.single (Or.inr h))⟩
  | .tail_po p h =>
      ⟨p.allEventsSatisfy_of_hb_closed hS ha, hS ha (Relation.TransGen.tail p.sound (Or.inl h))⟩
  | .tail_rf p h =>
      ⟨p.allEventsSatisfy_of_hb_closed hS ha, hS ha (Relation.TransGen.tail p.sound (Or.inr h))⟩

/-- If `S` is closed under a single `hb`-step and the path's target is not in
`S`, then no event the path touches is in `S`. -/
theorem Path.allEventsSatisfy_not_of_hb_closed_end {G : ExecutionGraph D} {a b : Event D}
    {S : Event D → Prop} (hS : ∀ ⦃x y⦄, S x → G.hb x y → S y) :
    ∀ (p : Path G a b), ¬ S b → p.AllEventsSatisfy (fun e => ¬ S e)
  | .single_po h, hb => ⟨fun ha => hb (hS ha (Relation.TransGen.single (Or.inl h))), hb⟩
  | .single_rf h, hb => ⟨fun ha => hb (hS ha (Relation.TransGen.single (Or.inr h))), hb⟩
  | .tail_po p h, hb =>
      have hb' : ¬ S _ := fun hSb' => hb (hS hSb' (Relation.TransGen.single (Or.inl h)))
      ⟨p.allEventsSatisfy_not_of_hb_closed_end hS hb', hb⟩
  | .tail_rf p h, hb =>
      have hb' : ¬ S _ := fun hSb' => hb (hS hSb' (Relation.TransGen.single (Or.inr h)))
      ⟨p.allEventsSatisfy_not_of_hb_closed_end hS hb', hb⟩

/-- Forward propagation of a set `S` closed under single `po`/`rf`-edges
between events satisfying a second path-wide predicate `P` (e.g.
bridge-freeness): if the path's source is in `S` and every event satisfies
`P`, every event is in `S`. -/
theorem Path.allEventsSatisfy_of_step_closed {G : ExecutionGraph D} {a b : Event D}
    {P S : Event D → Prop}
    (hstep : ∀ x y : Event D, S x → P x → P y → (G.po x y ∨ G.rf x y) → S y) (ha : S a) :
    ∀ (p : Path G a b), p.AllEventsSatisfy P → p.AllEventsSatisfy S
  | .single_po h, hp => ⟨ha, hstep a b ha hp.1 hp.2 (Or.inl h)⟩
  | .single_rf h, hp => ⟨ha, hstep a b ha hp.1 hp.2 (Or.inr h)⟩
  | .tail_po p h, hp =>
      have hprev := p.allEventsSatisfy_of_step_closed hstep ha hp.1
      ⟨hprev, hstep _ _ (p.allEventsSatisfy_right hprev) (p.allEventsSatisfy_right hp.1) hp.2
        (Or.inl h)⟩
  | .tail_rf p h, hp =>
      have hprev := p.allEventsSatisfy_of_step_closed hstep ha hp.1
      ⟨hprev, hstep _ _ (p.allEventsSatisfy_right hprev) (p.allEventsSatisfy_right hp.1) hp.2
        (Or.inr h)⟩

/-- `AllEventsSatisfy` combines pointwise. -/
theorem Path.allEventsSatisfy_and {G : ExecutionGraph D} {a b : Event D} {P Q : Event D → Prop} :
    ∀ (p : Path G a b), p.AllEventsSatisfy P → p.AllEventsSatisfy Q →
      p.AllEventsSatisfy (fun e => P e ∧ Q e)
  | .single_po _, hp, hq => ⟨⟨hp.1, hq.1⟩, ⟨hp.2, hq.2⟩⟩
  | .single_rf _, hp, hq => ⟨⟨hp.1, hq.1⟩, ⟨hp.2, hq.2⟩⟩
  | .tail_po p _, hp, hq => ⟨p.allEventsSatisfy_and hp.1 hq.1, ⟨hp.2, hq.2⟩⟩
  | .tail_rf p _, hp, hq => ⟨p.allEventsSatisfy_and hp.1 hq.1, ⟨hp.2, hq.2⟩⟩

/-! ## Machinery for Lemma 3.7

Shortening replaces the sub-path between two same-thread `po`-edges by one
edge. The pieces before and after may be empty, which `Path0` (a possibly
empty path) represents. -/

/-- A path from `a` to `b`, or nothing at all if `a = b`; used for fragments
of a `Path`. -/
inductive Path0 (G : ExecutionGraph D) : Event D → Event D → Type
  | refl (a : Event D) : Path0 G a a
  | ofPath {a b : Event D} (p : Path G a b) : Path0 G a b

/-- `Path0`'s length, matching `Path.length`: `refl` contributes none. -/
def Path0.length {G : ExecutionGraph D} {a b : Event D} : Path0 G a b → ℕ
  | .refl _ => 0
  | .ofPath p => p.length

/-- `Path0`'s analogue of `Path.sound`: a fragment gives `a ⟶hb b` or
`a = b`. -/
theorem Path0.sound {G : ExecutionGraph D} {a b : Event D} : Path0 G a b → G.hb a b ∨ a = b
  | .refl _ => Or.inr rfl
  | .ofPath p => Or.inl p.sound

/-- `Path0`'s `poThreads`, matching `Path.poThreads`. -/
def Path0.poThreads {G : ExecutionGraph D} {a b : Event D} : Path0 G a b → List D.Tid
  | .refl _ => []
  | .ofPath p => p.poThreads

/-- Extending a (possibly-empty) `Path0` by one `po`-edge always yields a
genuine, nonempty `Path`. -/
def Path0.tail_po {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.po b c) : Path G a c :=
  match p0 with
  | .refl _ => .single_po h
  | .ofPath p => .tail_po p h

/-- Extending a (possibly-empty) `Path0` by one `rf`-edge always yields a
genuine, nonempty `Path`. -/
def Path0.tail_rf {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.rf b c) : Path G a c :=
  match p0 with
  | .refl _ => .single_rf h
  | .ofPath p => .tail_rf p h

theorem Path0.poThreads_tail_po {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.po b c) : (p0.tail_po h).poThreads = p0.poThreads ++ [c.tid] := by
  cases p0 <;> rfl

theorem Path0.poThreads_tail_rf {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.rf b c) : (p0.tail_rf h).poThreads = p0.poThreads := by
  cases p0 <;> rfl

/-- Extending a `Path0` by a `po`-edge, staying `Path0`-valued. -/
def Path0.extend_po {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.po b c) : Path0 G a c :=
  .ofPath (p0.tail_po h)

/-- `Path0.extend_po`'s `rf` analogue. -/
def Path0.extend_rf {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.rf b c) : Path0 G a c :=
  .ofPath (p0.tail_rf h)

theorem Path0.poThreads_extend_po {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.po b c) : (p0.extend_po h).poThreads = p0.poThreads ++ [c.tid] :=
  Path0.poThreads_tail_po p0 h

theorem Path0.poThreads_extend_rf {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.rf b c) : (p0.extend_rf h).poThreads = p0.poThreads :=
  Path0.poThreads_tail_rf p0 h

/-- Prepending one `po`-edge to the front of a `Path`. -/
def Path.cons_po {G : ExecutionGraph D} {a x b : Event D} (h : G.po a x) :
    Path G x b → Path G a b
  | .single_po h' => .tail_po (.single_po h) h'
  | .single_rf h' => .tail_rf (.single_po h) h'
  | .tail_po p h' => .tail_po (p.cons_po h) h'
  | .tail_rf p h' => .tail_rf (p.cons_po h) h'

/-- `Path.cons_po` for a `Path0` continuation: prepending a `po`-edge to a
(possibly-empty) `Path0` always yields a genuine `Path`. -/
def Path0.cons_po {G : ExecutionGraph D} {a x b : Event D} (h : G.po a x) :
    Path0 G x b → Path G a b
  | .refl _ => .single_po h
  | .ofPath p => p.cons_po h

/-- If thread `t` occurs among `p`'s `po`-edges, `p` decomposes as a prefix
`pre`, the `po`-edge `s →po d` on `t`, and a suffix `post`, with
`p.poThreads` splitting the same way. -/
theorem Path.extractThread {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b) (t : D.Tid), t ∈ p.poThreads →
    ∃ (s d : Event D) (_ : G.po s d) (pre : Path0 G a s) (post : Path0 G d b),
      s.tid = t ∧ p.poThreads = pre.poThreads ++ [t] ++ post.poThreads
  | .single_po h, t, ht => by
      simp only [Path.poThreads, List.mem_singleton] at ht
      subst ht
      exact ⟨a, b, h, .refl a, .refl b, (G.po_subset h).2.2, by
        simp [Path.poThreads, Path0.poThreads]⟩
  | .single_rf _, t, ht => by simp [Path.poThreads] at ht
  | .tail_po p h, t, ht => by
      simp only [Path.poThreads, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | ht
      · obtain ⟨s, d, hsd, pre, post, hstid, heq⟩ := p.extractThread t ht
        refine ⟨s, d, hsd, pre, post.extend_po h, hstid, ?_⟩
        rw [Path0.poThreads_extend_po, Path.poThreads, heq, List.append_assoc]
      · subst ht
        exact ⟨_, b, h, .ofPath p, .refl b, (G.po_subset h).2.2, by
          simp [Path.poThreads, Path0.poThreads]⟩
  | .tail_rf p h, t, ht => by
      simp only [Path.poThreads] at ht
      obtain ⟨s, d, hsd, pre, post, hstid, heq⟩ := p.extractThread t ht
      refine ⟨s, d, hsd, pre, post.extend_rf h, hstid, ?_⟩
      rw [Path0.poThreads_extend_rf, Path.poThreads]
      exact heq

/-! ## Lemma 3.7 -/

/-- Lemma 3.7's shortening step, for a single `po`-edge appended to
a minimal prefix `q`: either appending keeps minimality, or the new edge's
thread already occurs in `q` and the segment from there on is spliced out.
The two bad trichotomy outcomes (`c = f` or `f ⟶po c`, in the notation
of the paper's proof) each give an `hb`-cycle, ruled out by `hirr`. -/
theorem Path.exists_minimal {G : ExecutionGraph D} (hirr : ∀ e : Event D, ¬ G.hb e e) :
    ∀ {a b : Event D}, Path G a b → ∃ q : Path G a b, q.IsMinimal
  | _, _, .single_po h => ⟨.single_po h, by simp [Path.IsMinimal, Path.poThreads]⟩
  | _, _, .single_rf h => ⟨.single_rf h, by simp [Path.IsMinimal, Path.poThreads]⟩
  | _, _, .tail_rf p h => by
      obtain ⟨q, hq⟩ := Path.exists_minimal hirr p
      exact ⟨.tail_rf q h, by simpa [Path.IsMinimal, Path.poThreads] using hq⟩
  | a, c, .tail_po (b := mid) p h => by
      obtain ⟨q, hq⟩ := Path.exists_minimal hirr p
      unfold Path.IsMinimal at hq
      by_cases hconf : mid.tid ∈ q.poThreads
      · -- the new edge's thread already occurs in q: locate it and merge
        obtain ⟨s, d, hsd, pre, post, hstid, heq⟩ := q.extractThread mid.tid hconf
        have hsc_tid : s.tid = c.tid := hstid.trans (G.po_subset h).2.2
        have hSTO := G.po_total s.tid
        have hmemS : s ∈ G.Events.filter (fun e => e.tid = s.tid) :=
          Finset.mem_filter.mpr ⟨(G.po_subset hsd).1, rfl⟩
        have hmemC : c ∈ G.Events.filter (fun e => e.tid = s.tid) :=
          Finset.mem_filter.mpr ⟨(G.po_subset h).2.1, hsc_tid.symm⟩
        by_cases h1 : G.po s c
        · -- s →po c directly: replace the whole segment by this one edge
          have hct : c.tid = mid.tid := hsc_tid.symm.trans hstid
          refine ⟨pre.tail_po h1, ?_⟩
          unfold Path.IsMinimal
          rw [Path0.poThreads_tail_po, hct]
          exact List.Nodup.of_append_left (heq ▸ hq)
        · by_cases h2 : G.po c s
          · -- f →po c (bad): c →po s →po d ⇝ mid →po c is an hb-cycle
            exact absurd (((post.cons_po hsd).cons_po h2).tail_po h).sound (hirr c)
          · -- c = f (bad): s →po d ⇝ mid →po c = s is an hb-cycle
            have hsc : s = c := congrArg Subtype.val
              (hSTO.toTrichotomous.trichotomous ⟨s, hmemS⟩ ⟨c, hmemC⟩ h1 h2)
            refine absurd (((post.cons_po hsd).tail_po h : Path G s c).sound) ?_
            rw [hsc]
            exact hirr c
      · -- no conflict: append directly
        refine ⟨.tail_po q h, ?_⟩
        unfold Path.IsMinimal
        rw [Path.poThreads, ← (G.po_subset h).2.2]
        refine List.Nodup.append hq (List.nodup_singleton _) ?_
        intro x hx hx'
        rw [List.mem_singleton] at hx'
        exact hconf (hx' ▸ hx)

/-! ## Lemma 3.6, part 2: hb-cycles can be taken minimal

Lemma 3.6's shortening compares the two colliding `po`-edges' *sources*,
and may rebase the cycle at a different event; it is proved by strong
induction on `Path.length`, locating both colliding edges at once
(`Path.extractDuplicateThread`). -/

/-- Whether a path's first edge is a `po`-edge. -/
def Path.firstIsPo {G : ExecutionGraph D} {a b : Event D} : Path G a b → Prop
  | .single_po _ => True
  | .single_rf _ => False
  | .tail_po p _ => p.firstIsPo
  | .tail_rf p _ => p.firstIsPo

/-- The complement of `Path.firstIsPo`, definitionally, matching
`Path.lastIsRf`. -/
def Path.firstIsRf {G : ExecutionGraph D} {a b : Event D} (p : Path G a b) : Prop :=
  ¬ p.firstIsPo

/-- `Path0.lastIsPo`, matching `Path.lastIsPo`; `False` for `refl`. -/
def Path0.lastIsPo {G : ExecutionGraph D} {a b : Event D} : Path0 G a b → Prop
  | .refl _ => False
  | .ofPath p => p.lastIsPo

def Path0.lastIsRf {G : ExecutionGraph D} {a b : Event D} (p0 : Path0 G a b) : Prop :=
  ¬ p0.lastIsPo

/-- `Path0.firstIsPo`, matching `Path.firstIsPo`; `refl` is vacuously
`False`, for the same reason as `Path0.lastIsPo`. -/
def Path0.firstIsPo {G : ExecutionGraph D} {a b : Event D} : Path0 G a b → Prop
  | .refl _ => False
  | .ofPath p => p.firstIsPo

def Path0.firstIsRf {G : ExecutionGraph D} {a b : Event D} (p0 : Path0 G a b) : Prop :=
  ¬ p0.firstIsPo

/-- `Path0.IsAlternating`, matching `Path.IsAlternating`; `refl` is vacuously
alternating (it has no edges to violate alternation). -/
def Path0.IsAlternating {G : ExecutionGraph D} {a b : Event D} : Path0 G a b → Prop
  | .refl _ => True
  | .ofPath p => p.IsAlternating

/-- `Path0.AllEventsSatisfy`, matching `Path.AllEventsSatisfy`; `refl` touches
only `a`. -/
def Path0.AllEventsSatisfy {G : ExecutionGraph D} {a b : Event D} (P : Event D → Prop)
    (p0 : Path0 G a b) : Prop := by
  cases p0 with
  | refl => exact P a
  | ofPath p => exact p.AllEventsSatisfy P

/-- Concatenating two paths. The join is not assumed compatible with
alternation here — see `Path.append_isAlternating` for the condition under
which it is. -/
def Path.append {G : ExecutionGraph D} {a b c : Event D} (p : Path G a b) :
    Path G b c → Path G a c
  | .single_po h => p.tail_po h
  | .single_rf h => p.tail_rf h
  | .tail_po q h => (p.append q).tail_po h
  | .tail_rf q h => (p.append q).tail_rf h

/-- `p.append q` ends with `q`'s last edge. -/
theorem Path.append_lastIsPo {G : ExecutionGraph D} {a b c : Event D} (p : Path G a b) :
    ∀ (q : Path G b c), (p.append q).lastIsPo ↔ q.lastIsPo
  | .single_po _ => Iff.rfl
  | .single_rf _ => Iff.rfl
  | .tail_po _ _ => Iff.rfl
  | .tail_rf _ _ => Iff.rfl

/-- `p.append q` is alternating exactly when both pieces are and the join
does not put two edges of the same kind next to each other — i.e., `p`'s
last edge and `q`'s first edge are of different kinds. -/
theorem Path.append_isAlternating {G : ExecutionGraph D} {a b c : Event D} (p : Path G a b) :
    ∀ (q : Path G b c), p.IsAlternating → q.IsAlternating →
      (p.lastIsPo ↔ q.firstIsRf) → (p.append q).IsAlternating
  | .single_po h, hp, _, hjoin => by
      have : p.lastIsRf := by
        simp only [Path.firstIsPo, Path.firstIsRf, not_true_eq_false, iff_false] at hjoin
        exact hjoin
      exact ⟨hp, this⟩
  | .single_rf h, hp, _, hjoin => by
      have : p.lastIsPo := by
        simp only [Path.firstIsPo, Path.firstIsRf, not_false_eq_true, iff_true] at hjoin
        exact hjoin
      exact ⟨hp, this⟩
  | .tail_po q h, hp, hq, hjoin => by
      obtain ⟨hqalt, hqlast⟩ := hq
      have hjoin' : p.lastIsPo ↔ q.firstIsRf := by
        simpa [Path.firstIsPo, Path.firstIsRf] using hjoin
      have hstep := p.append_isAlternating q hp hqalt hjoin'
      have hlast : (p.append q).lastIsRf :=
        (not_congr (Path.append_lastIsPo p q)).mpr hqlast
      exact ⟨hstep, hlast⟩
  | .tail_rf q h, hp, hq, hjoin => by
      obtain ⟨hqalt, hqlast⟩ := hq
      have hjoin' : p.lastIsPo ↔ q.firstIsRf := by
        simpa [Path.firstIsPo, Path.firstIsRf] using hjoin
      have hstep := p.append_isAlternating q hp hqalt hjoin'
      have hlast : (p.append q).lastIsPo := by
        rw [Path.append_lastIsPo]
        exact hqlast
      exact ⟨hstep, hlast⟩

/-- `Path.append` for a `Path0` continuation: appending a (possibly-empty)
`Path0` to an existing `Path` always yields a genuine `Path`. -/
def Path.append_path0 {G : ExecutionGraph D} {a b c : Event D} (p : Path G a b) :
    Path0 G b c → Path G a c
  | .refl _ => p
  | .ofPath q => p.append q

theorem Path.append_path0_isAlternating {G : ExecutionGraph D} {a b c : Event D}
    (p : Path G a b) (q0 : Path0 G b c) (hp : p.IsAlternating) (hq0 : q0.IsAlternating)
    (hjoin : p.lastIsPo ↔ q0.firstIsRf) : (p.append_path0 q0).IsAlternating := by
  cases q0 with
  | refl => exact hp
  | ofPath q =>
      simp only [Path0.firstIsRf, Path0.firstIsPo] at hjoin
      exact p.append_isAlternating q hp hq0 hjoin

/-- Whether a `Path0` is the empty fragment. -/
def Path0.IsRefl {G : ExecutionGraph D} {a b : Event D} : Path0 G a b → Prop
  | .refl _ => True
  | .ofPath _ => False

/-- Extending a `Path0` by a `po`-edge always ends in `po`, regardless of
what the fragment being extended was. -/
theorem Path0.lastIsPo_extend_po {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.po b c) : (p0.extend_po h).lastIsPo := by
  cases p0 <;> trivial

/-- Extending a `Path0` by an `rf`-edge always ends in `rf`. -/
theorem Path0.lastIsPo_extend_rf {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.rf b c) : ¬ (p0.extend_rf h).lastIsPo := by
  cases p0 <;> exact fun hc => hc

/-- Extending a `Path0` by one edge (either kind) never leaves it empty. -/
theorem Path0.not_isRefl_extend_po {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.po b c) : ¬ (p0.extend_po h).IsRefl := by
  cases p0 <;> simp [Path0.IsRefl, Path0.extend_po]

theorem Path0.not_isRefl_extend_rf {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.rf b c) : ¬ (p0.extend_rf h).IsRefl := by
  cases p0 <;> simp [Path0.IsRefl, Path0.extend_rf]

/-- `Path.extractThread`, strengthened with alternation: for `p` alternating,
the prefix and suffix are alternating and compatible at both seams (`pre`
ends in `rf`, `post` starts with `rf`). The extra clauses relate how `pre`
starts and `post` ends to how `p` starts and ends. -/
theorem Path.extractThreadAlt {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.IsAlternating → ∀ (t : D.Tid), t ∈ p.poThreads →
    ∃ (s d : Event D) (_ : G.po s d) (pre : Path0 G a s) (post : Path0 G d b),
      s.tid = t ∧
      p.poThreads = pre.poThreads ++ [t] ++ post.poThreads ∧
      pre.IsAlternating ∧ post.IsAlternating ∧
      pre.lastIsRf ∧ post.firstIsRf ∧
      (post.IsRefl → p.lastIsPo) ∧
      (¬ post.IsRefl → (post.lastIsPo ↔ p.lastIsPo)) ∧
      (pre.IsRefl → p.firstIsPo) ∧
      (¬ pre.IsRefl → (pre.firstIsPo ↔ p.firstIsPo))
  | .single_po h, _, t, ht => by
      simp only [Path.poThreads, List.mem_singleton] at ht
      subst ht
      refine ⟨a, b, h, .refl a, .refl b, (G.po_subset h).2.2, ?_, trivial, trivial, ?_, ?_, ?_, ?_,
        ?_, ?_⟩
      · simp [Path.poThreads, Path0.poThreads]
      · simp [Path0.lastIsRf, Path0.lastIsPo]
      · simp [Path0.firstIsRf, Path0.firstIsPo]
      · intro _; trivial
      · intro hr; exact absurd trivial hr
      · intro _; trivial
      · intro hr; exact absurd trivial hr
  | .single_rf _, _, t, ht => by simp [Path.poThreads] at ht
  | .tail_po p h, hp, t, ht => by
      obtain ⟨hpalt, hplast⟩ := hp
      simp only [Path.poThreads, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | ht
      · obtain ⟨s, d, hsd, pre, post, hstid, heq, hprealt, hpostalt, hprelast, hpostfirst,
            hrefl, hrelate, hprefirstrefl, hprefirstrelate⟩ := p.extractThreadAlt hpalt t ht
        have hpostNotRefl : ¬ post.IsRefl := fun hr => hplast (hrefl hr)
        have hpostLastRf : post.lastIsRf :=
          (not_congr (hrelate hpostNotRefl)).mpr hplast
        refine ⟨s, d, hsd, pre, post.extend_po h, hstid, ?_, hprealt, ?_, hprelast, ?_, ?_, ?_, ?_,
          ?_⟩
        · rw [Path0.poThreads_extend_po, Path.poThreads, heq, List.append_assoc]
        · cases post with
          | refl => exact absurd trivial hpostNotRefl
          | ofPath q => exact ⟨hpostalt, hpostLastRf⟩
        · cases post with
          | refl => exact absurd trivial hpostNotRefl
          | ofPath q =>
              simpa [Path0.firstIsRf, Path0.firstIsPo, Path0.extend_po, Path0.tail_po,
                Path.firstIsPo] using hpostfirst
        · exact fun hr => absurd hr (post.not_isRefl_extend_po h)
        · exact fun _ => iff_of_true (post.lastIsPo_extend_po h) trivial
        · exact hprefirstrefl
        · exact hprefirstrelate
      · subst ht
        refine ⟨_, b, h, .ofPath p, .refl b, (G.po_subset h).2.2, ?_, hpalt, trivial, hplast,
          ?_, ?_, ?_, ?_, ?_⟩
        · simp [Path.poThreads, Path0.poThreads]
        · simp [Path0.firstIsRf, Path0.firstIsPo]
        · intro _; trivial
        · intro hr; exact absurd trivial hr
        · intro hr; exact absurd hr (by simp [Path0.IsRefl])
        · intro _; rfl
  | .tail_rf p h, hp, t, ht => by
      obtain ⟨hpalt, hplast⟩ := hp
      simp only [Path.poThreads] at ht
      obtain ⟨s, d, hsd, pre, post, hstid, heq, hprealt, hpostalt, hprelast, hpostfirst,
          hrefl, hrelate, hprefirstrefl, hprefirstrelate⟩ := p.extractThreadAlt hpalt t ht
      refine ⟨s, d, hsd, pre, post.extend_rf h, hstid, ?_, hprealt, ?_, hprelast, ?_, ?_, ?_, ?_,
        ?_⟩
      · rw [Path0.poThreads_extend_rf, Path.poThreads]; exact heq
      · by_cases hpostRefl : post.IsRefl
        · cases post with
          | refl => trivial
          | ofPath q => exact absurd hpostRefl (by simp [Path0.IsRefl])
        · have hpostLastPo : post.lastIsPo := (hrelate hpostRefl).mpr hplast
          cases post with
          | refl => exact absurd trivial hpostRefl
          | ofPath q => exact ⟨hpostalt, hpostLastPo⟩
      · cases post with
        | refl => trivial
        | ofPath q =>
            simpa [Path0.firstIsRf, Path0.firstIsPo, Path0.extend_rf, Path0.tail_rf,
              Path.firstIsPo] using hpostfirst
      · exact fun hr => absurd hr (post.not_isRefl_extend_rf h)
      · exact fun _ => iff_of_false (post.lastIsPo_extend_rf h) (fun hc => hc)
      · exact hprefirstrefl
      · exact hprefirstrelate

/-- `Path.extractThreadAlt`, with the extracted prefix also satisfying any
`AllEventsSatisfy` predicate `p` satisfies. -/
theorem Path.extractThreadAlt_pre_allEventsSatisfy {G : ExecutionGraph D} {a b : Event D}
    (P : Event D → Prop) :
    ∀ (p : Path G a b), p.IsAlternating → p.AllEventsSatisfy P → ∀ (t : D.Tid),
      t ∈ p.poThreads →
    ∃ (s d : Event D) (_ : G.po s d) (pre : Path0 G a s) (post : Path0 G d b),
      s.tid = t ∧
      p.poThreads = pre.poThreads ++ [t] ++ post.poThreads ∧
      pre.IsAlternating ∧ post.IsAlternating ∧
      pre.lastIsRf ∧ post.firstIsRf ∧
      (post.IsRefl → p.lastIsPo) ∧
      (¬ post.IsRefl → (post.lastIsPo ↔ p.lastIsPo)) ∧
      (pre.IsRefl → p.firstIsPo) ∧
      (¬ pre.IsRefl → (pre.firstIsPo ↔ p.firstIsPo)) ∧
      (pre.IsRefl ∨ pre.AllEventsSatisfy P)
  | .single_po h, _, hP, t, ht => by
      simp only [Path.poThreads, List.mem_singleton] at ht
      subst ht
      refine ⟨a, b, h, .refl a, .refl b, (G.po_subset h).2.2, ?_, trivial, trivial, ?_, ?_, ?_, ?_,
        ?_, ?_, Or.inl trivial⟩
      · simp [Path.poThreads, Path0.poThreads]
      · simp [Path0.lastIsRf, Path0.lastIsPo]
      · simp [Path0.firstIsRf, Path0.firstIsPo]
      · intro _; trivial
      · intro hr; exact absurd trivial hr
      · intro _; trivial
      · intro hr; exact absurd trivial hr
  | .single_rf _, _, _, t, ht => by simp [Path.poThreads] at ht
  | .tail_po p h, hp, hP, t, ht => by
      obtain ⟨hpalt, hplast⟩ := hp
      obtain ⟨hpAES, hbAES⟩ := hP
      simp only [Path.poThreads, List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | ht
      · obtain ⟨s, d, hsd, pre, post, hstid, heq, hprealt, hpostalt, hprelast, hpostfirst,
            hrefl, hrelate, hprefirstrefl, hprefirstrelate, hpreAES⟩ :=
          p.extractThreadAlt_pre_allEventsSatisfy P hpalt hpAES t ht
        have hpostNotRefl : ¬ post.IsRefl := fun hr => hplast (hrefl hr)
        have hpostLastRf : post.lastIsRf :=
          (not_congr (hrelate hpostNotRefl)).mpr hplast
        refine ⟨s, d, hsd, pre, post.extend_po h, hstid, ?_, hprealt, ?_, hprelast, ?_, ?_, ?_, ?_,
          ?_, hpreAES⟩
        · rw [Path0.poThreads_extend_po, Path.poThreads, heq, List.append_assoc]
        · cases post with
          | refl => exact absurd trivial hpostNotRefl
          | ofPath q => exact ⟨hpostalt, hpostLastRf⟩
        · cases post with
          | refl => exact absurd trivial hpostNotRefl
          | ofPath q =>
              simpa [Path0.firstIsRf, Path0.firstIsPo, Path0.extend_po, Path0.tail_po,
                Path.firstIsPo] using hpostfirst
        · exact fun hr => absurd hr (post.not_isRefl_extend_po h)
        · exact fun _ => iff_of_true (post.lastIsPo_extend_po h) trivial
        · exact hprefirstrefl
        · exact hprefirstrelate
      · subst ht
        refine ⟨_, b, h, .ofPath p, .refl b, (G.po_subset h).2.2, ?_, hpalt, trivial, hplast,
          ?_, ?_, ?_, ?_, ?_, Or.inr hpAES⟩
        · simp [Path.poThreads, Path0.poThreads]
        · simp [Path0.firstIsRf, Path0.firstIsPo]
        · intro _; trivial
        · intro hr; exact absurd trivial hr
        · intro hr; exact absurd hr (by simp [Path0.IsRefl])
        · intro _; rfl
  | .tail_rf p h, hp, hP, t, ht => by
      obtain ⟨hpalt, hplast⟩ := hp
      obtain ⟨hpAES, hbAES⟩ := hP
      simp only [Path.poThreads] at ht
      obtain ⟨s, d, hsd, pre, post, hstid, heq, hprealt, hpostalt, hprelast, hpostfirst,
          hrefl, hrelate, hprefirstrefl, hprefirstrelate, hpreAES⟩ :=
        p.extractThreadAlt_pre_allEventsSatisfy P hpalt hpAES t ht
      refine ⟨s, d, hsd, pre, post.extend_rf h, hstid, ?_, hprealt, ?_, hprelast, ?_, ?_, ?_, ?_,
        ?_, hpreAES⟩
      · rw [Path0.poThreads_extend_rf, Path.poThreads]; exact heq
      · by_cases hpostRefl : post.IsRefl
        · cases post with
          | refl => trivial
          | ofPath q => exact absurd hpostRefl (by simp [Path0.IsRefl])
        · have hpostLastPo : post.lastIsPo := (hrelate hpostRefl).mpr hplast
          cases post with
          | refl => exact absurd trivial hpostRefl
          | ofPath q => exact ⟨hpostalt, hpostLastPo⟩
      · cases post with
        | refl => trivial
        | ofPath q =>
            simpa [Path0.firstIsRf, Path0.firstIsPo, Path0.extend_rf, Path0.tail_rf,
              Path.firstIsPo] using hpostfirst
      · exact fun hr => absurd hr (post.not_isRefl_extend_rf h)
      · exact fun _ => iff_of_false (post.lastIsPo_extend_rf h) (fun hc => hc)
      · exact hprefirstrefl
      · exact hprefirstrelate

/-- `Path.extractThreadAlt` for a `Path0` continuation: delegates to
`Path.extractThreadAlt` when nonempty, and is vacuous (no `po`-edges at all)
when `refl`. -/
theorem Path0.extractThreadAlt {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p0 : Path0 G a b), p0.IsAlternating → ∀ (t : D.Tid), t ∈ p0.poThreads →
    ∃ (s d : Event D) (_ : G.po s d) (pre : Path0 G a s) (post : Path0 G d b),
      s.tid = t ∧
      p0.poThreads = pre.poThreads ++ [t] ++ post.poThreads ∧
      pre.IsAlternating ∧ post.IsAlternating ∧
      pre.lastIsRf ∧ post.firstIsRf ∧
      (post.IsRefl → p0.lastIsPo) ∧
      (¬ post.IsRefl → (post.lastIsPo ↔ p0.lastIsPo)) ∧
      (pre.IsRefl → p0.firstIsPo) ∧
      (¬ pre.IsRefl → (pre.firstIsPo ↔ p0.firstIsPo))
  | .refl _, _, t, ht => by simp [Path0.poThreads] at ht
  | .ofPath p, hp, t, ht => p.extractThreadAlt hp t ht

/-- If `p` is not minimal, two of its `po`-edges share a thread, and `p`
decomposes around both of them: `pre`, the first edge, `mid`, the second
edge, `post`. -/
theorem Path.extractDuplicateThread {G : ExecutionGraph D} {a b : Event D} (p : Path G a b)
    (hp : p.IsAlternating) (hdup : ¬ p.poThreads.Nodup) :
    ∃ (s1 d1 s2 d2 : Event D) (_ : G.po s1 d1) (_ : G.po s2 d2)
      (pre : Path0 G a s1) (mid : Path0 G d1 s2) (post : Path0 G d2 b),
      s1.tid = s2.tid ∧
      p.poThreads = pre.poThreads ++ [s1.tid] ++ mid.poThreads ++ [s2.tid] ++ post.poThreads ∧
      pre.IsAlternating ∧ mid.IsAlternating ∧ post.IsAlternating ∧
      pre.lastIsRf ∧ mid.lastIsRf ∧ post.firstIsRf := by
  obtain ⟨t, htdup⟩ := List.exists_duplicate_iff_not_nodup.mpr hdup
  have hcount : 2 ≤ p.poThreads.count t := List.duplicate_iff_two_le_count.mp htdup
  have ht1 : t ∈ p.poThreads := List.count_pos_iff.mp (by omega)
  obtain ⟨s, d, h, pre1, post1, hstid, heq, hpre1alt, hpost1alt, hpre1last, hpost1first, _, _, _,
      _⟩ := p.extractThreadAlt hp t ht1
  by_cases hin : t ∈ post1.poThreads
  · obtain ⟨s2, d2, h2, mid, post2, hstid2, heq2, hmidalt, hpost2alt, hmidlast, hpost2first,
        _, _, _, _⟩ := post1.extractThreadAlt hpost1alt t hin
    refine ⟨s, d, s2, d2, h, h2, pre1, mid, post2, hstid.trans hstid2.symm, ?_,
      hpre1alt, hmidalt, hpost2alt, hpre1last, hmidlast, hpost2first⟩
    rw [heq, heq2, hstid, hstid2]
    simp only [List.append_assoc]
  · have hin' : t ∈ pre1.poThreads := by
      have h0 : post1.poThreads.count t = 0 := List.count_eq_zero.mpr hin
      have heqcount : p.poThreads.count t
          = pre1.poThreads.count t + 1 + post1.poThreads.count t := by
        rw [heq, ← hstid]
        simp only [List.count_append, List.count_singleton_self]
      rw [h0] at heqcount
      exact List.count_pos_iff.mp (by omega)
    obtain ⟨s0, d0, h0, pre0, mid0, hstid0, heq0, hpre0alt, hmid0alt, hpre0last, hmid0first,
        hrefl0, hrelate0, _, _⟩ := pre1.extractThreadAlt hpre1alt t hin'
    have hmid0NotRefl : ¬ mid0.IsRefl := fun hr => hpre1last (hrefl0 hr)
    have hmid0LastRf : mid0.lastIsRf := (not_congr (hrelate0 hmid0NotRefl)).mpr hpre1last
    refine ⟨s0, d0, s, d, h0, h, pre0, mid0, post1, hstid0.trans hstid.symm, ?_,
      hpre0alt, hmid0alt, hpost1alt, hpre0last, hmid0LastRf, hpost1first⟩
    rw [heq, heq0, hstid0, hstid]

/-- `Path0.tail_po` always ends in `po`. -/
theorem Path0.tail_po_lastIsPo {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.po b c) : (p0.tail_po h).lastIsPo := by
  cases p0 <;> trivial

/-- Extending an alternating, `rf`-ending `Path0` by a `po`-edge is
alternating. -/
theorem Path0.tail_po_isAlternating {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (hp0 : p0.IsAlternating) (hlast : p0.lastIsRf) (h : G.po b c) :
    (p0.tail_po h).IsAlternating := by
  cases p0 with
  | refl => trivial
  | ofPath q => exact ⟨hp0, hlast⟩

/-- `Path.length` counts exactly the elements of `Path.poThreads`: both count
`po`-edges, and nothing else. -/
theorem Path.length_eq_poThreads_length {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.length = p.poThreads.length
  | .single_po _ => rfl
  | .single_rf _ => rfl
  | .tail_po p _ => by simp [Path.length, Path.poThreads, p.length_eq_poThreads_length]
  | .tail_rf p _ => by simp [Path.length, Path.poThreads, p.length_eq_poThreads_length]

theorem Path0.length_eq_poThreads_length {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p0 : Path0 G a b), p0.length = p0.poThreads.length
  | .refl _ => rfl
  | .ofPath p => p.length_eq_poThreads_length

theorem Path.append_length {G : ExecutionGraph D} {a b c : Event D} (p : Path G a b) :
    ∀ (q : Path G b c), (p.append q).length = p.length + q.length
  | .single_po _ => by simp [Path.append, Path.length]
  | .single_rf _ => by simp [Path.append, Path.length]
  | .tail_po q _ => by simp [Path.append, Path.length, p.append_length q]; omega
  | .tail_rf q _ => by simp [Path.append, Path.length, p.append_length q]

theorem Path.append_path0_length {G : ExecutionGraph D} {a b c : Event D} (p : Path G a b) :
    ∀ (q0 : Path0 G b c), (p.append_path0 q0).length = p.length + q0.length
  | .refl _ => rfl
  | .ofPath q => p.append_length q

theorem Path0.tail_po_length {G : ExecutionGraph D} {a b c : Event D} (p0 : Path0 G a b)
    (h : G.po b c) : (p0.tail_po h).length = p0.length + 1 := by
  cases p0 <;> rfl

/-- Lemma 3.6, part 2: every alternating `hb`-cycle can be shortened to a
minimal one, possibly based at a different event. Strong induction on
`p.length`: `Path.extractDuplicateThread` locates a colliding pair, and
trichotomy of their sources yields a strictly shorter alternating cycle in
every case. -/
theorem Path.exists_minimal_alternating_cycle {G : ExecutionGraph D} :
    ∀ (n : ℕ) (e : Event D) (p : Path G e e), p.IsAlternating → p.length = n →
      ∃ (e' : Event D) (p' : Path G e' e'), p'.IsAlternating ∧ p'.IsMinimal := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro e p hp hlen
    by_cases hmin : p.IsMinimal
    · exact ⟨e, p, hp, hmin⟩
    · obtain ⟨s1, d1, s2, d2, h1, h2, pre, mid, post, hst, heq, hprealt, hmidalt, hpostalt,
        hprelast, hmidlast, hpostfirst⟩ := p.extractDuplicateThread hp hmin
      have hSTO := G.po_total s1.tid
      have hmemS1 : s1 ∈ G.Events.filter (fun e => e.tid = s1.tid) :=
        Finset.mem_filter.mpr ⟨(G.po_subset h1).1, rfl⟩
      have hmemS2 : s2 ∈ G.Events.filter (fun e => e.tid = s1.tid) :=
        Finset.mem_filter.mpr ⟨(G.po_subset h2).1, hst.symm⟩
      have hplen : p.length = pre.length + mid.length + post.length + 2 := by
        rw [Path.length_eq_poThreads_length, heq]
        simp [List.length_append, Path0.length_eq_poThreads_length]
        omega
      by_cases hd1 : G.po s1 s2
      · -- s1 →po s2 →po d2: transitivity merges the whole segment into one edge
        have hmerge : G.po s1 d2 := G.po_trans hd1 h2
        refine ih (pre.length + 1 + post.length) (by omega) e
          ((pre.tail_po hmerge).append_path0 post)
          (Path.append_path0_isAlternating _ post
            (Path0.tail_po_isAlternating pre hprealt hprelast hmerge) hpostalt
            (iff_of_true (Path0.tail_po_lastIsPo pre hmerge) hpostfirst))
          ?_
        rw [Path.append_path0_length, Path0.tail_po_length]
      · by_cases hd2 : G.po s2 s1
        · -- s2 →po s1 →po d1: transitivity gives a shorter cycle based at d1 instead
          have hmerge : G.po s2 d1 := G.po_trans hd2 h1
          refine ih (mid.length + 1) (by omega) d1 (mid.tail_po hmerge)
            (Path0.tail_po_isAlternating mid hmidalt hmidlast hmerge) ?_
          rw [Path0.tail_po_length]
        · -- s1 = s2: the second edge already reaches d2 from s1
          have hs12 : s1 = s2 := congrArg Subtype.val
            (hSTO.toTrichotomous.trichotomous ⟨s1, hmemS1⟩ ⟨s2, hmemS2⟩ hd1 hd2)
          have hmerge : G.po s1 d2 := hs12 ▸ h2
          refine ih (pre.length + 1 + post.length) (by omega) e
            ((pre.tail_po hmerge).append_path0 post)
            (Path.append_path0_isAlternating _ post
              (Path0.tail_po_isAlternating pre hprealt hprelast hmerge) hpostalt
              (iff_of_true (Path0.tail_po_lastIsPo pre hmerge) hpostfirst))
            ?_
          rw [Path.append_path0_length, Path0.tail_po_length]

/-! ## Lemma 3.6, parts 3–4: the topology of a minimal alternating cycle

The threads of a minimal cycle's `po`-edges, read cyclically, form a chain
linked by `rf`-edges, to which the thread-level `rf` topology (Fig. 4) applies.

A cycle based at `e` cannot have both ends `po` (that would repeat `e.tid` in
`poThreads`) nor both ends `rf` (that would make `e` both a write and a read),
so exactly one end is `po`, and the wraparound is witnessed by the edge
touching `e` on the `rf` side. -/

/-- Two threads are connected by `G.rf` if some `rf`-edge runs from an event
of one to an event of the other. -/
def ExecutionGraph.ThreadRf (G : ExecutionGraph D) (t t' : D.Tid) : Prop :=
  ∃ ew er, G.rf ew er ∧ ew.tid = t ∧ er.tid = t'

/-- A path ending in a `po`-edge has that edge's (shared) thread as the
last entry of `poThreads`, regardless of what precedes it. -/
theorem Path.lastIsPo_getLast {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.lastIsPo → ∀ (hne : p.poThreads ≠ []),
      p.poThreads.getLast hne = b.tid
  | .single_po _, _, _ => by simp [Path.poThreads]
  | .single_rf _, hlast, _ => hlast.elim
  | .tail_po _ _, _, _ => by simp [Path.poThreads]
  | .tail_rf _ _, hlast, _ => hlast.elim

/-- A path ending in a `po`-edge always has a nonempty `poThreads`: the edge
itself contributes an entry. -/
theorem Path.lastIsPo_poThreads_ne_nil {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.lastIsPo → p.poThreads ≠ []
  | .single_po _, _ => by simp [Path.poThreads]
  | .single_rf _, hlast => hlast.elim
  | .tail_po _ _, _ => by simp [Path.poThreads]
  | .tail_rf _ _, hlast => hlast.elim

/-- A path starting with a `po`-edge has a nonempty `poThreads`, whose head
(`Path.firstIsPo_head`) is that edge's thread. -/
theorem Path.firstIsPo_poThreads_ne_nil {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.firstIsPo → p.poThreads ≠ []
  | .single_po _, _ => by simp [Path.poThreads]
  | .single_rf _, hfirst => hfirst.elim
  | .tail_po _ _, _ => by simp [Path.poThreads]
  | .tail_rf p _, hfirst => p.firstIsPo_poThreads_ne_nil hfirst

theorem Path.firstIsPo_head {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.firstIsPo → ∀ (hne : p.poThreads ≠ []),
      p.poThreads.head hne = a.tid
  | .single_po h, _, _ => by simp [Path.poThreads, (G.po_subset h).2.2]
  | .single_rf _, hfirst, _ => hfirst.elim
  | .tail_po p h, hfirst, hne => by
      have hpe : p.poThreads ≠ [] := p.firstIsPo_poThreads_ne_nil hfirst
      simp only [Path.poThreads, List.head_append_of_ne_nil hpe]
      exact p.firstIsPo_head hfirst hpe
  | .tail_rf p h, hfirst, hne => by
      simp only [Path.poThreads] at hne ⊢
      exact p.firstIsPo_head hfirst hne

/-- If `q` has no `po`-edges at all and starts with an `rf`-edge, `q` is
exactly that one `rf`-edge: alternation forbids a second edge from following
it without an intervening `po`-edge, and `Path` has no empty constructor. -/
theorem Path.rf_of_poThreads_nil {G : ExecutionGraph D} {a c : Event D} :
    ∀ (q : Path G a c), q.IsAlternating → q.poThreads = [] → q.firstIsRf → G.rf a c
  | .single_po _, _, hpt, _ => by simp [Path.poThreads] at hpt
  | .single_rf h, _, _, _ => h
  | .tail_po _ _, _, hpt, _ => by simp [Path.poThreads] at hpt
  | .tail_rf q _, hq, hpt, _ =>
      absurd (show q.poThreads = [] by simpa [Path.poThreads] using hpt)
        (q.lastIsPo_poThreads_ne_nil hq.2)

/-- If a path's last edge is an `rf`-edge, that edge itself witnesses
`G.ThreadRf` between the thread of the preceding `po`-edge (the last entry
of `poThreads`) and the path's endpoint. -/
theorem Path.lastEdge_threadRf {G : ExecutionGraph D} {a c : Event D} :
    ∀ (p : Path G a c), p.IsAlternating → p.lastIsRf → ∀ (hne : p.poThreads ≠ []),
      G.ThreadRf (p.poThreads.getLast hne) c.tid
  | .single_po _, _, hlast, _ => (hlast trivial).elim
  | .single_rf _, _, _, hne => absurd rfl hne
  | .tail_po _ _, _, hlast, _ => (hlast trivial).elim
  | .tail_rf p h, hp, _, hne => by
      simp only [Path.poThreads] at hne ⊢
      rw [p.lastIsPo_getLast hp.2 hne]
      exact ⟨_, _, h, rfl, rfl⟩

/-- The symmetric fact for a path's first edge. -/
theorem Path.firstEdge_threadRf {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.IsAlternating → p.firstIsRf → ∀ (hne : p.poThreads ≠ []),
      G.ThreadRf a.tid (p.poThreads.head hne)
  | .single_po _, _, hfirst, _ => (hfirst trivial).elim
  | .single_rf _, _, _, hne => absurd rfl hne
  | .tail_po (b := m) p h, hp, hfirst, hne => by
      by_cases hpe : p.poThreads = []
      · have hrf : G.rf a m := p.rf_of_poThreads_nil hp.1 hpe hfirst
        simp only [Path.poThreads, hpe, List.nil_append, List.head_cons]
        exact (G.po_subset h).2.2 ▸ ⟨a, m, hrf, rfl, rfl⟩
      · simp only [Path.poThreads, List.head_append_of_ne_nil hpe]
        exact p.firstEdge_threadRf hp.1 hfirst hpe
  | .tail_rf p h, hp, hfirst, hne => by
      simp only [Path.poThreads] at hne ⊢
      exact p.firstEdge_threadRf hp.1 hfirst hne

/-- Every alternating path's `poThreads` forms an `rf`-chain: consecutive
`po`-edges are separated by exactly one `rf`-edge. -/
theorem Path.poThreads_isChain {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.IsAlternating → List.IsChain G.ThreadRf p.poThreads
  | .single_po _, _ => List.isChain_singleton _
  | .single_rf _, _ => List.isChain_nil
  | .tail_po (b := m) p h, hp => by
      obtain ⟨hpalt, hplast⟩ := hp
      rw [Path.poThreads]
      refine (p.poThreads_isChain hpalt).append (List.isChain_singleton b.tid) ?_
      intro x hx y hy
      simp only [List.head?_singleton, Option.mem_some_iff] at hy
      subst hy
      obtain ⟨hne, hxeq⟩ := List.mem_getLast?_eq_getLast hx
      subst hxeq
      have hthreadrf := p.lastEdge_threadRf hpalt hplast hne
      rwa [(G.po_subset h).2.2] at hthreadrf
  | .tail_rf p h, hp => by
      simp only [Path.poThreads]
      exact p.poThreads_isChain hp.1

/-- Whether a path contains at least one `rf`-edge. -/
def Path.HasRf {G : ExecutionGraph D} {a b : Event D} : Path G a b → Prop
  | .single_po _ => False
  | .single_rf _ => True
  | .tail_po p _ => p.HasRf
  | .tail_rf _ _ => True

/-- A path with no `rf`-edge at all is entirely `po`-edges, which compose
(`ExecutionGraph.po_trans`) into a single `po`-edge from start to end. -/
theorem Path.po_of_not_hasRf {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), ¬ p.HasRf → G.po a b
  | .single_po h, _ => h
  | .single_rf _, hrf => (hrf trivial).elim
  | .tail_po p h, hrf => G.po_trans (p.po_of_not_hasRf hrf) h
  | .tail_rf _ _, hrf => (hrf trivial).elim

/-- The single-thread case of Lemma 3.6: an alternating `hb`-cycle always contains at
least one `rf`-edge, since a purely-`po` cycle would witness `G.po e e`,
contradicting `po`'s irreflexivity on `e`'s thread. -/
theorem Path.hasRf_of_cyclic {G : ExecutionGraph D} {e : Event D} (p : Path G e e) : p.HasRf := by
  by_contra hrf
  have hpo : G.po e e := p.po_of_not_hasRf hrf
  have hmem : e ∈ G.Events.filter (fun x => x.tid = e.tid) :=
    Finset.mem_filter.mpr ⟨(G.po_subset hpo).1, rfl⟩
  exact (G.po_total e.tid).irrefl ⟨e, hmem⟩ hpo

/-- A cyclic path starting and ending with a `po`-edge and containing an
`rf`-edge has at least two entries in `poThreads`. -/
theorem Path.firstIsPo_lastIsPo_length_two_le {G : ExecutionGraph D} {e : Event D} :
    ∀ (p : Path G e e), p.HasRf → p.firstIsPo → p.lastIsPo → 2 ≤ p.poThreads.length
  | .single_po _, hrf, _, _ => hrf.elim
  | .single_rf _, _, hfirst, _ => hfirst.elim
  | .tail_po p h, _, hfirst, _ => by
      have hlen : 1 ≤ p.poThreads.length :=
        List.length_pos_of_ne_nil (p.firstIsPo_poThreads_ne_nil hfirst)
      simp only [Path.poThreads, List.length_append, List.length_cons, List.length_nil]
      omega
  | .tail_rf _ _, _, _, hlast => hlast.elim

/-- A minimal alternating cyclic path cannot have both ends `po`: the head
and last entry of `poThreads` would coincide, contradicting `Nodup`. -/
theorem Path.not_firstIsPo_and_lastIsPo {G : ExecutionGraph D} {e : Event D} (p : Path G e e)
    (hrf : p.HasRf) (hmin : p.IsMinimal) : ¬ (p.firstIsPo ∧ p.lastIsPo) := by
  rintro ⟨hfirst, hlast⟩
  have hne : p.poThreads ≠ [] := p.firstIsPo_poThreads_ne_nil hfirst
  have hlen : 2 ≤ p.poThreads.length := p.firstIsPo_lastIsPo_length_two_le hrf hfirst hlast
  have heq : p.poThreads.head hne = p.poThreads.getLast hne :=
    (p.firstIsPo_head hfirst hne).trans (p.lastIsPo_getLast hlast hne).symm
  obtain ⟨x, hx⟩ := (List.Nodup.head_eq_getLast_iff hne hmin).mp heq
  rw [hx] at hlen
  simp at hlen

/-- If a path's first edge is `rf`, that edge itself is available directly. -/
theorem Path.firstIsRf_rf {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.firstIsRf → ∃ x, G.rf a x
  | .single_po _, hfirst => (hfirst trivial).elim
  | .single_rf h, _ => ⟨b, h⟩
  | .tail_po p _, hfirst => p.firstIsRf_rf hfirst
  | .tail_rf p _, hfirst => p.firstIsRf_rf hfirst

/-- The symmetric fact for a path's last edge. -/
theorem Path.lastIsRf_rf {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.lastIsRf → ∃ x, G.rf x b
  | .single_po _, hlast => (hlast trivial).elim
  | .single_rf h, _ => ⟨a, h⟩
  | .tail_po _ _, hlast => (hlast trivial).elim
  | .tail_rf _ h, _ => ⟨_, h⟩

/-- A path ending at a write ends in a `po`-edge, since `rf`'s target is a
read. -/
theorem Path.lastIsPo_of_wt {G : ExecutionGraph D} {a b : Event D} (p : Path G a b)
    (hb : b.op = .wt) : p.lastIsPo := by
  by_contra hlast
  obtain ⟨x, hrf⟩ := p.lastIsRf_rf hlast
  have hrd : b.op = .rd := (G.rf_subset hrf).2.2.2.1
  rw [hb] at hrd
  exact absurd hrd (by decide)

/-- A path starting at a read starts with a `po`-edge, since `rf`'s source is
a write. -/
theorem Path.firstIsPo_of_rd {G : ExecutionGraph D} {a b : Event D} (p : Path G a b)
    (ha : a.op = .rd) : p.firstIsPo := by
  by_contra hfirst
  obtain ⟨x, hrf⟩ := p.firstIsRf_rf hfirst
  have hwt : a.op = .wt := (G.rf_subset hrf).2.2.1
  rw [ha] at hwt
  exact absurd hwt (by decide)

/-- Every minimal path is alternating: two consecutive `po`-edges would repeat
a thread in `poThreads`, and two consecutive `rf`-edges cannot occur
(`ExecutionGraph.no_consecutive_rf`). -/
theorem Path.isAlternating_of_isMinimal {G : ExecutionGraph D} {a b : Event D} :
    ∀ (p : Path G a b), p.IsMinimal → p.IsAlternating
  | .single_po _, _ => trivial
  | .single_rf _, _ => trivial
  | .tail_po p' h, hmin => by
      have hminp : (p'.poThreads ++ [b.tid]).Nodup := hmin
      have hmin' : p'.poThreads.Nodup := hminp.of_append_left
      have hp'lastrf : p'.lastIsRf := by
        intro hp'lastpo
        have hne' : p'.poThreads ≠ [] := p'.lastIsPo_poThreads_ne_nil hp'lastpo
        have hget : p'.poThreads.getLast hne' = b.tid :=
          (p'.lastIsPo_getLast hp'lastpo hne').trans (G.po_subset h).2.2
        have hmem : b.tid ∈ p'.poThreads := hget ▸ List.getLast_mem hne'
        rw [List.nodup_append] at hminp
        exact (hminp.2.2 b.tid hmem b.tid (List.mem_singleton_self _)) rfl
      exact ⟨p'.isAlternating_of_isMinimal hmin', hp'lastrf⟩
  | .tail_rf p' h, hmin => by
      have hmin' : p'.poThreads.Nodup := hmin
      have hp'lastpo : p'.lastIsPo := by
        by_contra hp'lastrf
        obtain ⟨x, hrf⟩ := p'.lastIsRf_rf hp'lastrf
        exact G.no_consecutive_rf hrf h
      exact ⟨p'.isAlternating_of_isMinimal hmin', hp'lastpo⟩

/-- A cyclic path cannot have both ends `rf`: its base event would be both a
write and a read. -/
theorem Path.not_firstIsRf_and_lastIsRf {G : ExecutionGraph D} {e : Event D} (p : Path G e e) :
    ¬ (p.firstIsRf ∧ p.lastIsRf) := by
  rintro ⟨hfirst, hlast⟩
  obtain ⟨x, hx⟩ := p.firstIsRf_rf hfirst
  obtain ⟨y, hy⟩ := p.lastIsRf_rf hlast
  exact G.no_consecutive_rf hy hx

/-- Lemma 3.6's topology step (parts 3–4): a minimal alternating `hb`-cycle's
`poThreads`, closed cyclically, forms an `rf`-chain of pairwise distinct
threads. -/
theorem Path.poThreads_cyclic_chain {G : ExecutionGraph D} {e : Event D} (p : Path G e e)
    (hp : p.IsAlternating) (hmin : p.IsMinimal) (hne : p.poThreads ≠ []) :
    List.IsChain G.ThreadRf (p.poThreads ++ [p.poThreads.head hne]) := by
  have hrf : p.HasRf := p.hasRf_of_cyclic
  refine (p.poThreads_isChain hp).append (List.isChain_singleton _) ?_
  intro x hx y hy
  simp only [List.head?_singleton, Option.mem_some_iff] at hy
  subst hy
  obtain ⟨hne', hxeq⟩ := List.mem_getLast?_eq_getLast hx
  subst hxeq
  by_cases hlast : p.lastIsPo
  · by_cases hfirst : p.firstIsPo
    · exact absurd ⟨hfirst, hlast⟩ (p.not_firstIsPo_and_lastIsPo hrf hmin)
    · have hwrap := p.firstEdge_threadRf hp hfirst hne
      rwa [p.lastIsPo_getLast hlast hne']
  · by_cases hfirst : p.firstIsPo
    · have hwrap := p.lastEdge_threadRf hp hlast hne'
      rwa [p.firstIsPo_head hfirst hne]
    · exact absurd ⟨hfirst, hlast⟩ (p.not_firstIsRf_and_lastIsRf)

/-- An alternating cyclic path has at least one `po`-edge: otherwise it would
be a single `rf`-edge from `e` to itself. -/
theorem Path.poThreads_ne_nil_of_cyclic {G : ExecutionGraph D} {e : Event D} (p : Path G e e)
    (hp : p.IsAlternating) : p.poThreads ≠ [] := by
  intro hpt
  have hfp : ¬ p.firstIsPo := fun hfp => absurd hpt (p.firstIsPo_poThreads_ne_nil hfp)
  have hrf : G.rf e e := p.rf_of_poThreads_nil hp hpt hfp
  have hwt : e.op = OpType.wt := (G.rf_subset hrf).2.2.1
  have hrd : e.op = OpType.rd := (G.rf_subset hrf).2.2.2.1
  rw [hwt] at hrd
  exact absurd hrd (by simp)

/-- The 4-event cycle shape of a minimal alternating cycle with exactly two
`po`-edges: Lemma 3.6's displayed cycle
`w_1 →rf r_1 →po w_2 →rf r_2 →po w_1`. The two `po`-edges are located by
`Path.extractThreadAlt`, and every fragment between them is a single
`rf`-edge. -/
theorem Path.exists_cycle_shape {G : ExecutionGraph D} {e : Event D} (p : Path G e e)
    (hp : p.IsAlternating) (hmin : p.IsMinimal) (hlen : p.poThreads.length = 2) :
    ∃ (w1 r1 w2 r2 : Event D), G.rf w1 r1 ∧ G.po r1 w2 ∧ G.rf w2 r2 ∧ G.po r2 w1 ∧
      r1.tid ≠ r2.tid := by
  obtain ⟨t1, t2, hpeq⟩ := List.length_eq_two.mp hlen
  have hlnodup : ([t1, t2] : List D.Tid).Nodup := hpeq ▸ hmin
  have ht1ne2 : t1 ≠ t2 := by
    have := (List.nodup_cons.mp hlnodup).1
    simpa using this
  have ht2mem : t2 ∈ p.poThreads := by rw [hpeq]; simp
  obtain ⟨s2, d2, h2, pre, post, hstid2, heq, hprealt, hpostalt, hprelast, hpostfirst,
      hrefl, hrelate, hprefirstrefl, hprefirstrelate⟩ := p.extractThreadAlt hp t2 ht2mem
  have heq' : ([t1, t2] : List D.Tid) = pre.poThreads ++ [t2] ++ post.poThreads := hpeq ▸ heq
  have hlensum : pre.poThreads.length + post.poThreads.length = 1 := by
    have hl := congrArg List.length heq'
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega
  have hpostnil : post.poThreads = [] := by
    rcases Nat.eq_zero_or_pos pre.poThreads.length with hpre0 | hpre0
    · exfalso
      have hprenil : pre.poThreads = [] := List.length_eq_zero_iff.mp hpre0
      rw [hprenil, List.nil_append] at heq'
      injection heq' with heqt1t2 _
      exact ht1ne2 heqt1t2
    · exact List.length_eq_zero_iff.mp (by omega)
  have hprelen1 : pre.poThreads.length = 1 := by
    have : post.poThreads.length = 0 := by rw [hpostnil]; rfl
    omega
  obtain ⟨x, hxeq⟩ := List.length_eq_one_iff.mp hprelen1
  have hxt1 : x = t1 := by
    rw [hxeq, hpostnil, List.append_nil] at heq'
    injection heq' with hh _
    exact hh.symm
  have ht1eq : pre.poThreads = [t1] := hxt1 ▸ hxeq
  have ht1mem : t1 ∈ pre.poThreads := ht1eq ▸ List.mem_singleton_self t1
  have hprenotrefl : ¬ pre.IsRefl := by
    cases pre with
    | refl => simp [Path0.poThreads] at ht1eq
    | ofPath q => simp [Path0.IsRefl]
  obtain ⟨s1, d1, h1, pre1, post1, hstid1, heq1, hpre1alt, hpost1alt, hpre1last, hpost1first,
      hrefl1, hrelate1, hprefirstrefl1, hprefirstrelate1⟩ := pre.extractThreadAlt hprealt t1 ht1mem
  have hlensum1 : pre1.poThreads.length + post1.poThreads.length = 0 := by
    have hl := congrArg List.length heq1
    rw [ht1eq] at hl
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega
  have hpre1nil : pre1.poThreads = [] := List.length_eq_zero_iff.mp (by omega)
  have hpost1nil : post1.poThreads = [] := List.length_eq_zero_iff.mp (by omega)
  have hrf : p.HasRf := p.hasRf_of_cyclic
  have htid : t1 ≠ s2.tid := hstid2 ▸ ht1ne2
  -- post1 : Path0 G d1 s2, no po-edges, always nonempty (pre.lastIsRf forbids it collapsing
  -- into d1 → s2 being an extra po-edge already counted).
  have hpost1notrefl : ¬ post1.IsRefl := fun hcon => hprelast (hrefl1 hcon)
  have hrf1 : G.rf d1 s2 := by
    cases post1 with
    | refl => exact absurd trivial hpost1notrefl
    | ofPath q => exact q.rf_of_poThreads_nil hpost1alt hpost1nil hpost1first
  by_cases hlast : p.lastIsPo
  · -- p.lastIsPo: post is refl (d2 = e); p.firstIsRf, so pre1 is nonempty (e -rf-> s1)
    have hpostrefl : post.IsRefl := by
      by_contra hcon
      have hlp : post.lastIsPo := (hrelate hcon).mpr hlast
      cases post with
      | refl => exact hcon trivial
      | ofPath q => exact absurd hpostnil (q.lastIsPo_poThreads_ne_nil hlp)
    have hd2e : d2 = e := by
      cases post with
      | refl => rfl
      | ofPath q => exact absurd hpostrefl (by simp [Path0.IsRefl])
    have hfirstRf : p.firstIsRf := fun hfp => p.not_firstIsPo_and_lastIsPo hrf hmin ⟨hfp, hlast⟩
    have hprefirstpo : ¬ pre.firstIsPo := (hprefirstrelate hprenotrefl).not.mpr hfirstRf
    have hpre1notrefl : ¬ pre1.IsRefl := fun hcon => hprefirstpo (hprefirstrefl1 hcon)
    have hrf0 : G.rf e s1 := by
      cases pre1 with
      | refl => exact absurd trivial hpre1notrefl
      | ofPath q =>
          exact q.rf_of_poThreads_nil hpre1alt hpre1nil
            ((hprefirstrelate1 hpre1notrefl).not.mpr hprefirstpo)
    refine ⟨e, s1, d1, s2, hrf0, h1, hrf1, ?_, ?_⟩
    · rw [← hd2e]; exact h2
    · rw [hstid1]; exact htid
  · -- p.lastIsRf: post is nonempty (d2 -rf-> e); p.firstIsPo, so pre1 is refl (e = s1)
    have hpostnotrefl : ¬ post.IsRefl := fun hcon => hlast (hrefl hcon)
    have hrf2 : G.rf d2 e := by
      cases post with
      | refl => exact absurd trivial hpostnotrefl
      | ofPath q => exact q.rf_of_poThreads_nil hpostalt hpostnil hpostfirst
    have hfirstpo : p.firstIsPo := by
      by_contra hc
      exact p.not_firstIsRf_and_lastIsRf ⟨hc, hlast⟩
    have hpreiff : pre.firstIsPo := (hprefirstrelate hprenotrefl).mpr hfirstpo
    have hpre1refl : pre1.IsRefl := by
      by_contra hcon
      have hq : pre1.firstIsPo := (hprefirstrelate1 hcon).mpr hpreiff
      cases pre1 with
      | refl => exact hcon trivial
      | ofPath q => exact absurd hpre1nil (q.firstIsPo_poThreads_ne_nil hq)
    have hs1e : s1 = e := by
      cases pre1 with
      | refl => rfl
      | ofPath q => exact absurd hpre1refl (by simp [Path0.IsRefl])
    refine ⟨d1, s2, d2, e, hrf1, h2, hrf2, ?_, ?_⟩
    · rw [← hs1e]; exact h1
    · have hetid : e.tid = t1 := by rw [← hs1e]; exact hstid1
      rw [hetid]; exact Ne.symm htid

end RAUndecidability
