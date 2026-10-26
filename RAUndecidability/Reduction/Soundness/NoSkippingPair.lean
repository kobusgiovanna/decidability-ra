import RAUndecidability.Reduction.Soundness.Bridge

/-!
# The shared arguments behind Lemma 3.2

Eq. (15) and Eq. (16) of Lemma 3.2 consist of ten pairs of `rf`-edge
families, and the paper's proof of them (Appendix B) argues only the
first pair, stating that "the proof of each pair has identical structure, and
is based on the fact that each of the involved threads alternates between
writing to one of the involved locations and reading from the other".

This file is that one argument, stated once, over an arbitrary
RA-consistent execution graph. A pair is two threads `A`, `B` and two
locations `p`, `q`: `B` writes `p` and `A` reads it; `A` writes `q` and `B`
reads it. `ExecutionGraph.NoSkipPair` collects the facts about the two
threads' own words that the paper's argument actually uses — value
residues, writer identification, the alternation (as `po`-edges between
indexed events) and existence of earlier events — and
`ExecutionGraph.NoSkipPair.no_skipping` derives both families of the pair
from them, by the paper's joint induction on the read index.

Each concrete pair (`Soundness/NoSkipping.lean`) has its own statement and
discharges `NoSkipPair`'s fields from its threads' closed forms. The structure is symmetric under
swapping `(A, p)` with `(B, q)` (`NoSkipPair.swap`), which is how a single
step lemma, `NoSkipPair.step`, proves both families — matching the paper's
own "symmetric reasoning on `r_i(g_α^{x'}, z_α^{x',x})`".

Eq. (17) has four pairs, each linking a guesser and its primed copy to a
checker and its primed copy. The paper again argues one of them;
`ExecutionGraph.CrossPair` is the interface of that argument and
`ExecutionGraph.CrossPair.no_skipping` the argument, by the same kind of joint
induction. Its proof uses Eq. (15)/(16) for the pairs involved, as the
paper's does.
-/

namespace RAUndecidability

variable {D : Domains}

/-- A `po`-edge between two same-location writes is an `mo`-edge, via
`mo_total`'s trichotomy and `write_coherence` excluding the reverse (a
`po`-edge the wrong way around combined with the trichotomy's `mo`-edge
would make a `mo;hb` cycle) and the diagonal (`w1 = w2` would make `po`
reflexive, contradicting `po_total`'s irreflexivity). -/
theorem ExecutionGraph.mo_of_po_sameLoc (G : ExecutionGraph D)
    (hcons : G.RAConsistent) {w1 w2 : Event D} (hpo : G.po w1 w2)
    (hw1 : w1.IsWriting) (hw2 : w2.IsWriting) (hloc : w1.loc = w2.loc) :
    G.mo w1 w2 := by
  have hmem1 := (G.po_subset hpo).1
  have hmem2 := (G.po_subset hpo).2.1
  have hSTO := G.mo_total w1.loc
  have hmemS : w1 ∈ G.Events.filter (fun e => e.IsWriting ∧ e.loc = w1.loc) :=
    Finset.mem_filter.mpr ⟨hmem1, hw1, rfl⟩
  have hmemC : w2 ∈ G.Events.filter (fun e => e.IsWriting ∧ e.loc = w1.loc) :=
    Finset.mem_filter.mpr ⟨hmem2, hw2, hloc.symm⟩
  by_cases h1 : G.mo w1 w2
  · exact h1
  · exfalso
    by_cases h2 : G.mo w2 w1
    · exact hcons.write_coherence w2 ⟨w1, h2, Relation.TransGen.single (Or.inl hpo)⟩
    · have heq : w1 = w2 := congrArg Subtype.val
        (hSTO.toTrichotomous.trichotomous ⟨w1, hmemS⟩ ⟨w2, hmemC⟩ h1 h2)
      subst heq
      exact (G.po_total w1.tid).irrefl
        ⟨w1, Finset.mem_filter.mpr ⟨(G.po_subset hpo).1, rfl⟩⟩ hpo

/-- Filtered-index monotonicity against `po` within one thread: of two
events of the same thread, location and operation, the one with the smaller
index is `po`-before the other (`opEvents` is a filtered sublist of the
`po`-sorted `threadEvents`). -/
theorem ExecutionGraph.nthEvent_po_of_lt (G : ExecutionGraph D) {t : D.Tid}
    {x : D.Loc} {op : OpType} {i1 i2 : ℕ} {e1 e2 : Event D}
    (h1 : G.nthEvent t x op i1 = some e1) (h2 : G.nthEvent t x op i2 = some e2)
    (hlt : i1 < i2) : G.po e1 e2 := by
  have hpw := G.threadEvents_pairwise_po t
  have hpw2 : ((G.threadEvents t).filter (fun e => e.1.loc = x ∧ e.1.op = op)).Pairwise
      (fun a b => G.po a.1 b.1) := hpw.filter _
  have hpw3 : (G.opEvents t x op).Pairwise G.po := by
    unfold ExecutionGraph.opEvents
    rw [List.pairwise_map]
    exact hpw2
  rw [List.pairwise_iff_getElem] at hpw3
  have h1' : (G.opEvents t x op)[i1]? = some e1 := h1
  have h2' : (G.opEvents t x op)[i2]? = some e2 := h2
  have hlt1 := (List.getElem?_eq_some_iff.mp h1').1
  have hlt2 := (List.getElem?_eq_some_iff.mp h2').1
  have heq1 := (List.getElem?_eq_some_iff.mp h1').2
  have heq2 := (List.getElem?_eq_some_iff.mp h2').2
  have h := hpw3 i1 i2 hlt1 hlt2 hlt
  rwa [heq1, heq2] at h

/-- If the `k`-th event of a thread/location/operation triple exists, so
does every earlier one. -/
theorem ExecutionGraph.nthEvent_of_le (G : ExecutionGraph D) {t : D.Tid}
    {x : D.Loc} {op : OpType} {j k : ℕ} {e : Event D}
    (h : G.nthEvent t x op k = some e) (hjk : j ≤ k) :
    ∃ e', G.nthEvent t x op j = some e' := by
  have h' : (G.opEvents t x op)[k]? = some e := h
  have hk := (List.getElem?_eq_some_iff.mp h').1
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- An `rf`-edge's writer, once its thread is known, is one of that thread's
own indexed writes on the read's location. -/
theorem ExecutionGraph.exists_nthWrite_of_rf (G : ExecutionGraph D)
    {w r : Event D} {t : D.Tid} {x : D.Loc}
    (hrf : G.rf w r) (htid : w.tid = t) (hloc : r.loc = x) :
    ∃ i, G.nthWrite t x i = some w := by
  obtain ⟨hmem, -, hwt, -, hwloc⟩ := G.rf_subset hrf
  have hop : w.op = OpType.wt := hwt
  have h := G.index_nthEvent hmem
  rw [htid, hwloc, hloc, hop] at h
  exact ⟨_, h⟩

/-- The facts about a pair of threads `A`, `B` and locations `p`, `q` (`B`
writes `p`, read by `A`; `A` writes `q`, read by `B`) that
the paper's proof of Eq. (15)/(16) (Appendix B) uses
about the two threads' own words, phrased over `G`'s indexed events
(event indexing (§3), 0-indexed):

* `match_p`/`match_q`: "`r_i(g_α^x, z_α^{x,x'})` must read value `i mod 4`" — a
  write and a read on the pair's location carry the same value only when
  their indices agree mod 4;
* `writer_p`/`writer_q`: every read of `A` on `p` reads from some write of `B`
  (resp. of `A` on `q` for `B`'s reads), i.e. "any later write that writes
  this value is of the form `w_j(g_α^{x'}, z_α^{x,x'})`";
* `po_A`/`po_B`: "each of the involved threads alternates between writing to
  one of the involved locations and reading from the other", in the form the
  argument uses it — the `i`-th read of a thread precedes its own `ℓ`-th
  write on the other location once `i + 2 ≤ ℓ`;
* `ex_A`/`ex_B`: an event preceded in that alternation exists whenever the
  later one does ("any such `w_j(g_α^{x'}, z_α^{x,x'})`, if it exists, is preceded by
  `r_{i+2}(g_α^{x'}, z_α^{x',x})`"). -/
structure ExecutionGraph.NoSkipPair (G : ExecutionGraph D) (A B : D.Tid) (p q : D.Loc) :
    Prop where
  match_p : ∀ {i j : ℕ} {w r : Event D}, G.nthWrite B p i = some w →
    G.nthRead A p j = some r → w.val = r.val → i % 4 = j % 4
  match_q : ∀ {i j : ℕ} {w r : Event D}, G.nthWrite A q i = some w →
    G.nthRead B q j = some r → w.val = r.val → i % 4 = j % 4
  writer_p : ∀ {j : ℕ} {w r : Event D}, G.nthRead A p j = some r → G.rf w r →
    ∃ i, G.nthWrite B p i = some w
  writer_q : ∀ {j : ℕ} {w r : Event D}, G.nthRead B q j = some r → G.rf w r →
    ∃ i, G.nthWrite A q i = some w
  po_A : ∀ {i ℓ : ℕ} {r w : Event D}, G.nthRead A p i = some r →
    G.nthWrite A q ℓ = some w → i + 2 ≤ ℓ → G.po r w
  po_B : ∀ {i ℓ : ℕ} {r w : Event D}, G.nthRead B q i = some r →
    G.nthWrite B p ℓ = some w → i + 2 ≤ ℓ → G.po r w
  ex_A : ∀ {i ℓ : ℕ} {w : Event D}, G.nthWrite A q ℓ = some w → i + 2 ≤ ℓ →
    ∃ r, G.nthRead A p i = some r
  ex_B : ∀ {i ℓ : ℕ} {w : Event D}, G.nthWrite B p ℓ = some w → i + 2 ≤ ℓ →
    ∃ r, G.nthRead B q i = some r

/-- The pair seen from the other side: `(A, p)` and `(B, q)` swapped. -/
theorem ExecutionGraph.NoSkipPair.swap {G : ExecutionGraph D} {A B : D.Tid} {p q : D.Loc}
    (h : G.NoSkipPair A B p q) : G.NoSkipPair B A q p where
  match_p := h.match_q
  match_q := h.match_p
  writer_p := h.writer_q
  writer_q := h.writer_p
  po_A := h.po_B
  po_B := h.po_A
  ex_A := h.ex_B
  ex_B := h.ex_A

/-- One step of the paper's induction: `r_k(A, p)` reads from `w_k(B, p)`,
given both families of the pair at every smaller index. Follows
the two exclusions of the paper's proof (Appendix B):

* `i < k` violates `read_coherence`: `w_{k-1}(B, p) ⟶rf r_{k-1}(A, p)` by
  the induction hypothesis, so `w_i(B, p) ⟶mo w_{k-1}(B, p) ⟶hb r_k(A, p)`
  (the paper's (i)-(iii); here `i ≤ k - 4` by `match_p`, so (iii) is not
  needed);
* `i > k` (so `i ≥ k + 4` by `match_p`) gives an `hb`-cycle through the
  anchor `r_{k+2}(B, q)`, whose own writer `w_ℓ(A, q)` has `ℓ ≥ k + 2`:
  `ℓ ≡ k + 2 (mod 4)` by `match_q`, and `ℓ < k - 1` would violate
  `read_coherence` against `w_{k-1}(A, q) ⟶rf r_{k-1}(B, q)`, the other
  family's induction hypothesis. -/
theorem ExecutionGraph.NoSkipPair.step {G : ExecutionGraph D} {A B : D.Tid} {p q : D.Loc}
    (hcons : G.RAConsistent) (h : G.NoSkipPair A B p q) (k : ℕ)
    (IHp : ∀ k' < k, ∀ {i : ℕ} {ew er : Event D}, G.nthWrite B p i = some ew →
      G.nthRead A p k' = some er → G.rf ew er → i = k')
    (IHq : ∀ k' < k, ∀ {n : ℕ} {ew er : Event D}, G.nthWrite A q n = some ew →
      G.nthRead B q k' = some er → G.rf ew er → n = k') :
    ∀ {i : ℕ} {ew er : Event D}, G.nthWrite B p i = some ew →
      G.nthRead A p k = some er → G.rf ew er → i = k := by
  intro i ew er hew her hrf
  have hres : i % 4 = k % 4 := h.match_p hew her (G.rf_matches hrf)
  obtain ⟨-, -, hewloc, hewop⟩ := G.nthEvent_index hew
  rcases Nat.lt_trichotomy i k with hlt | heq | hgt
  · -- `i < k`: `read_coherence` against `w_{k-1}(B, p) ⟶rf r_{k-1}(A, p)`.
    exfalso
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨er', her'⟩ := G.nthEvent_of_le her (Nat.le_succ k')
    have her'mem := (G.mem_opEvents_iff.mp (List.mem_of_getElem? her')).1
    obtain ⟨-, -, -, her'op⟩ := G.nthEvent_index her'
    obtain ⟨w0, hw0⟩ := G.rf_total her'mem her'op
    obtain ⟨j0, hj0⟩ := h.writer_p her' hw0
    have hj0eq : j0 = k' := IHp k' (by omega) hj0 her' hw0
    rw [hj0eq] at hj0
    obtain ⟨-, -, hw0loc, hw0op⟩ := G.nthEvent_index hj0
    have hpo : G.po ew w0 := G.nthEvent_po_of_lt hew hj0 (by omega)
    have hmo : G.mo ew w0 := G.mo_of_po_sameLoc hcons hpo hewop hw0op (hewloc.trans hw0loc.symm)
    have hhb : G.hb w0 er :=
      Relation.TransGen.tail (Relation.TransGen.single (Or.inr hw0))
        (Or.inl (G.nthEvent_po_of_lt her' her (Nat.lt_succ_self k')))
    exact hcons.read_coherence ew ⟨er, ⟨w0, hmo, hhb⟩, hrf⟩
  · exact heq
  · -- `i > k`: an `hb`-cycle through the anchor `r_{k+2}(B, q)`.
    exfalso
    obtain ⟨r2, hr2⟩ := h.ex_B hew (i := k + 2) (by omega)
    have hr2mem := (G.mem_opEvents_iff.mp (List.mem_of_getElem? hr2)).1
    obtain ⟨-, -, -, hr2op⟩ := G.nthEvent_index hr2
    obtain ⟨w2, hw2⟩ := G.rf_total hr2mem hr2op
    obtain ⟨ℓ, hℓ⟩ := h.writer_q hr2 hw2
    have hresℓ : ℓ % 4 = (k + 2) % 4 := h.match_q hℓ hr2 (G.rf_matches hw2)
    have hℓge : k + 2 ≤ ℓ := by
      by_contra hℓlt
      -- `ℓ ≤ k - 2`: `read_coherence` against `w_{k-1}(A, q) ⟶rf r_{k-1}(B, q)`.
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      obtain ⟨r3, hr3⟩ := G.nthEvent_of_le hr2 (j := k') (by omega)
      have hr3mem := (G.mem_opEvents_iff.mp (List.mem_of_getElem? hr3)).1
      obtain ⟨-, -, -, hr3op⟩ := G.nthEvent_index hr3
      obtain ⟨w3, hw3⟩ := G.rf_total hr3mem hr3op
      obtain ⟨n, hn⟩ := h.writer_q hr3 hw3
      have hneq : n = k' := IHq k' (by omega) hn hr3 hw3
      rw [hneq] at hn
      obtain ⟨-, -, hℓloc, hℓop⟩ := G.nthEvent_index hℓ
      obtain ⟨-, -, hnloc, hnop⟩ := G.nthEvent_index hn
      have hmo : G.mo w2 w3 :=
        G.mo_of_po_sameLoc hcons (G.nthEvent_po_of_lt hℓ hn (by omega)) hℓop hnop
          (hℓloc.trans hnloc.symm)
      have hhb : G.hb w3 r2 :=
        Relation.TransGen.tail (Relation.TransGen.single (Or.inr hw3))
          (Or.inl (G.nthEvent_po_of_lt hr3 hr2 (by omega)))
      exact hcons.read_coherence w2 ⟨r2, ⟨w3, hmo, hhb⟩, hw2⟩
    have hcycle : G.hb er er :=
      Relation.TransGen.tail
        (Relation.TransGen.tail
          (Relation.TransGen.tail
            (Relation.TransGen.single (Or.inl (h.po_A her hℓ hℓge)))
            (Or.inr hw2))
          (Or.inl (h.po_B hr2 hew (by omega))))
        (Or.inr hrf)
    exact hcons.irr_hb er hcycle

/-- Eq. (15)/(16) for one pair: at every index `k`, the
`k`-th read of each thread on the pair's location reads from the
partner thread's `k`-th write. Joint strong induction on `k`, both
families at once, each step by `NoSkipPair.step` — the second family via
`NoSkipPair.swap`. -/
theorem ExecutionGraph.NoSkipPair.no_skipping {G : ExecutionGraph D} {A B : D.Tid}
    {p q : D.Loc} (hcons : G.RAConsistent) (h : G.NoSkipPair A B p q) (k : ℕ) :
    (∀ {i : ℕ} {ew er : Event D}, G.nthWrite B p i = some ew →
      G.nthRead A p k = some er → G.rf ew er → i = k) ∧
    (∀ {n : ℕ} {ew er : Event D}, G.nthWrite A q n = some ew →
      G.nthRead B q k = some er → G.rf ew er → n = k) := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    exact ⟨h.step hcons k (fun k' hk' => (IH k' hk').1) (fun k' hk' => (IH k' hk').2),
      h.swap.step hcons k (fun k' hk' => (IH k' hk').2) (fun k' hk' => (IH k' hk').1)⟩

/-! ## Same-location `mo` facts, for Eq. (17)

Consequences of `read_coherence`/`write_coherence`. -/

/-- If `w1 ⟶rf r`, and `w2 ≠ w1` is a write to the same location with
`w2 ⟶hb r`, then `w2 ⟶mo w1` (otherwise `w1 ⟶mo w2` would violate
`read_coherence`). -/
theorem ExecutionGraph.mo_of_rf_hb {D : Domains} (G : ExecutionGraph D)
    (hcons : G.RAConsistent) {w1 w2 r : Event D} (hrf : G.rf w1 r) (hhb : G.hb w2 r)
    (hw1 : w1.IsWriting) (hw2 : w2.IsWriting) (hloc : w1.loc = w2.loc) (hne : w1 ≠ w2) :
    G.mo w2 w1 := by
  have hmem1 : w1 ∈ G.Events := (G.rf_subset hrf).1
  have hmem2 : w2 ∈ G.Events := G.hb_mem_events_left hhb
  have hSTO := G.mo_total w1.loc
  have hmemS1 : w1 ∈ G.Events.filter (fun e => e.IsWriting ∧ e.loc = w1.loc) :=
    Finset.mem_filter.mpr ⟨hmem1, hw1, rfl⟩
  have hmemS2 : w2 ∈ G.Events.filter (fun e => e.IsWriting ∧ e.loc = w1.loc) :=
    Finset.mem_filter.mpr ⟨hmem2, hw2, hloc.symm⟩
  by_cases h1 : G.mo w2 w1
  · exact h1
  · exfalso
    by_cases h2 : G.mo w1 w2
    · exact hcons.read_coherence w1 ⟨r, ⟨w2, h2, hhb⟩, hrf⟩
    · exact hne (congrArg Subtype.val
        (hSTO.toTrichotomous.trichotomous ⟨w1, hmemS1⟩ ⟨w2, hmemS2⟩ h2 h1))

/-- An `hb`-edge between two distinct same-location writes is an `mo`-edge
(`mo_total`, with `write_coherence` excluding the reverse). -/
theorem ExecutionGraph.mo_of_hb_sameLoc {D : Domains} (G : ExecutionGraph D)
    (hcons : G.RAConsistent) {w1 w2 : Event D} (hhb : G.hb w1 w2)
    (hw1 : w1.IsWriting) (hw2 : w2.IsWriting) (hloc : w1.loc = w2.loc) (hne : w1 ≠ w2) :
    G.mo w1 w2 := by
  have hmem1 := G.hb_mem_events_left hhb
  have hmem2 := G.hb_mem_events hhb
  have hSTO := G.mo_total w1.loc
  have hmemS1 : w1 ∈ G.Events.filter (fun e => e.IsWriting ∧ e.loc = w1.loc) :=
    Finset.mem_filter.mpr ⟨hmem1, hw1, rfl⟩
  have hmemS2 : w2 ∈ G.Events.filter (fun e => e.IsWriting ∧ e.loc = w1.loc) :=
    Finset.mem_filter.mpr ⟨hmem2, hw2, hloc.symm⟩
  by_cases h1 : G.mo w1 w2
  · exact h1
  · exfalso
    by_cases h2 : G.mo w2 w1
    · exact hcons.write_coherence w2 ⟨w1, h2, hhb⟩
    · exact hne (congrArg Subtype.val
        (hSTO.toTrichotomous.trichotomous ⟨w1, hmemS1⟩ ⟨w2, hmemS2⟩ h1 h2))

/-! ## From index alignment to the paper's statement -/

section Generic

variable {D : Domains}

/-- One `rf`-edge family of Lemma 3.2, as in the paper: for every `i` such that
the `i`-th read `r_i(tr, x)` exists, `w_i(tw, x) ⟶rf r_i(tr, x)`. -/
def ExecutionGraph.ReadsFromSameIndex (G : ExecutionGraph D) (tw tr : D.Tid) (x : D.Loc) :
    Prop :=
  ∀ (i : ℕ) (er : Event D), G.nthRead tr x i = some er →
    ∃ ew, G.nthWrite tw x i = some ew ∧ G.rf ew er

/-- The paper's form of an `rf`-edge family, from (i) every write read by
`tr` on `x` belongs to `tw` and (ii) an `rf`-edge from `tw`'s `i`-th write to
`tr`'s `k`-th read on `x` has `i = k`. -/
theorem ExecutionGraph.readsFromSameIndex_of {G : ExecutionGraph D} {tw tr : D.Tid} {x : D.Loc}
    (hwriter : ∀ {i : ℕ} {er w : Event D}, G.nthRead tr x i = some er → G.rf w er → w.tid = tw)
    (halign : ∀ {i k : ℕ} {ew er : Event D}, G.nthWrite tw x i = some ew →
      G.nthRead tr x k = some er → G.rf ew er → i = k) :
    G.ReadsFromSameIndex tw tr x := by
  intro i er her
  obtain ⟨-, -, hloc, hop⟩ := G.nthEvent_index her
  have hmem := (G.mem_opEvents_iff.mp (List.mem_of_getElem? her)).1
  obtain ⟨w, hrf⟩ := G.rf_total hmem hop
  obtain ⟨j, hj⟩ := G.exists_nthWrite_of_rf hrf (hwriter her hrf) hloc
  obtain rfl := halign hj her hrf
  exact ⟨w, hj, hrf⟩

end Generic


/-! ## Eq. (17): the shared argument

The paper proves Eq. (17) for the pair `w_i(g_α^x, x_α) ⟶rf r_i(c^x, x_α)`,
`w_i(g_α^{x'}, x'_α) ⟶rf r_i(c^{x'}, x'_α)` and states that the remaining pairs
follow the same argument. `ExecutionGraph.CrossPair` collects what that argument
uses about the four threads involved, a guesser `g`, its primed copy `p`, a
checker `c` and its primed copy `q`, and the locations `a` (written by `g` and
`c`, read by `c` and `q`), `a'` (written by `p` and `q`, read by `q` and `c`), `z`
(written by `p`, read by `g`) and `z'` (written by `g`, read by `p`);
`CrossPair.no_skipping` is the argument itself. Indices are 0-based: the
paper's `r_i` is `nthRead … (i - 1)`. -/

section Cross

variable {D : Domains}

/-- The facts about the four threads of one pair of Eq. (17) that the paper's
proof uses, over `G`'s indexed events.

* `tag_ca`, `tag_qa'`: "`r_i(c^x, x_α)` must read value `⟨ḡ_α^x, _⟩`", i.e. the
  writes read by `c` on `a` are `g`'s, and those read by `q` on `a'` are `p`'s;
* `hgc`, `hpq`: the guesser and the checker are different threads, and so are
  their primed copies;
* `base`: the base case, "`r_1(c^x, x_α)` must read value `⟨ḡ_α^x, _⟩`, which
  can only be written by `w_1(g_α^x, x_α)`";
* `rs_qa`, `rs_ca'`: Eq. (16) for the checker pair (`c` to `q` on `a`, `q` to `c`
  on `a'`); `rs_gz`, `rs_pz'`: Eq. (15) for the guesser pair (`p` to `g` on `z`,
  `g` to `p` on `z'`);
* the remaining fields are the facts "by the construction shown in Fig. 7":
  - `c_wr`, `c_ex`: in iteration `k`, `c` writes `a` and then reads it;
  - `c_rw`: `c`'s reads of `a` in earlier iterations precede its later writes;
  - `c_rr`: in iteration `k + 1`, `c` reads `a` and then `a'` (`c` reads `a'` only
    from its second iteration on, so its `k`-th read of `a'` is in iteration
    `k + 1`);
  - `q_wr`, `q_ex`, `q_rw`: the same for `q` on `a'`;
  - `q_rr`: in iteration `k`, `q` reads `a'` and then `a`;
  - `g_za`: "if `w_j(g, a) ∈ E` for `j > i`, then `r_{i-1}(g, z) ∈ E`", before it;
  - `g_az'`: in each call, `g` writes `a` and then `z'`;
  - `p_a'z`: in each iteration, `p` writes `a'` and then `z`;
  - `p_z'a'`: "if `w_j(p, a') ∈ E` for `j > i`, then `r_i(p, z') ∈ E`", before it. -/
structure ExecutionGraph.CrossPair (G : ExecutionGraph D) (g p c q : D.Tid)
    (a a' z z' : D.Loc) : Prop where
  tag_ca : ∀ {k : ℕ} {r w : Event D}, G.nthRead c a k = some r → G.rf w r → w.tid = g
  tag_qa' : ∀ {k : ℕ} {r w : Event D}, G.nthRead q a' k = some r → G.rf w r → w.tid = p
  hgc : g ≠ c
  hpq : p ≠ q
  base : ∀ {i : ℕ} {ew er : Event D}, G.nthWrite g a i = some ew →
    G.nthRead c a 0 = some er → G.rf ew er → i = 0
  rs_qa : G.ReadsFromSameIndex c q a
  rs_ca' : G.ReadsFromSameIndex q c a'
  rs_gz : G.ReadsFromSameIndex p g z
  rs_pz' : G.ReadsFromSameIndex g p z'
  c_wr : ∀ {k : ℕ} {r : Event D}, G.nthRead c a k = some r →
    ∃ w, G.nthWrite c a k = some w ∧ G.po w r
  c_ex : ∀ {k : ℕ} {w : Event D}, G.nthWrite c a k = some w → ∃ r, G.nthRead c a k = some r
  c_rw : ∀ {j k : ℕ} {r w : Event D}, G.nthRead c a j = some r → G.nthWrite c a k = some w →
    j < k → G.po r w
  c_rr : ∀ {k : ℕ} {r : Event D}, G.nthRead c a (k + 1) = some r →
    ∃ r', G.nthRead c a' k = some r' ∧ G.po r r'
  q_wr : ∀ {k : ℕ} {r : Event D}, G.nthRead q a' k = some r →
    ∃ w, G.nthWrite q a' k = some w ∧ G.po w r
  q_ex : ∀ {k : ℕ} {w : Event D}, G.nthWrite q a' k = some w → ∃ r, G.nthRead q a' k = some r
  q_rw : ∀ {j k : ℕ} {r w : Event D}, G.nthRead q a' j = some r → G.nthWrite q a' k = some w →
    j < k → G.po r w
  q_rr : ∀ {k : ℕ} {r : Event D}, G.nthRead q a' k = some r →
    ∃ r', G.nthRead q a k = some r' ∧ G.po r r'
  g_za : ∀ {m j : ℕ} {w : Event D}, G.nthWrite g a j = some w → m + 2 ≤ j →
    ∃ r, G.nthRead g z m = some r ∧ G.po r w
  g_az' : ∀ {k : ℕ} {w : Event D}, G.nthWrite g a k = some w →
    ∃ w', G.nthWrite g z' k = some w' ∧ G.po w w'
  p_a'z : ∀ {k : ℕ} {w : Event D}, G.nthWrite p a' k = some w →
    ∃ w', G.nthWrite p z k = some w' ∧ G.po w w'
  p_z'a' : ∀ {m j : ℕ} {w : Event D}, G.nthWrite p a' j = some w → m + 1 ≤ j →
    ∃ r, G.nthRead p z' m = some r ∧ G.po r w

namespace ExecutionGraph.CrossPair

variable {G : ExecutionGraph D} {g p c q : D.Tid} {a a' z z' : D.Loc}

private theorem hb_of_po {x y : Event D} (h : G.po x y) : G.hb x y :=
  Relation.TransGen.single (Or.inl h)

private theorem hb_of_rf {x y : Event D} (h : G.rf x y) : G.hb x y :=
  Relation.TransGen.single (Or.inr h)

/-- A read's incoming `rf`-edge, given that its writer is `t`'s, comes from
`t`'s write of the same index when the alignment `halign` holds. -/
private theorem aligned_writer {t tr : D.Tid} {x : D.Loc} {k : ℕ} {er : Event D}
    (her : G.nthRead tr x k = some er)
    (hwriter : ∀ {w : Event D}, G.rf w er → w.tid = t)
    (halign : ∀ {i : ℕ} {ew : Event D}, G.nthWrite t x i = some ew → G.rf ew er → i = k) :
    ∃ ew, G.nthWrite t x k = some ew ∧ G.rf ew er := by
  obtain ⟨-, -, hloc, hop⟩ := G.nthEvent_index her
  have hmem := (G.mem_opEvents_iff.mp (List.mem_of_getElem? her)).1
  obtain ⟨w, hrf⟩ := G.rf_total hmem hop
  obtain ⟨j, hj⟩ := G.exists_nthWrite_of_rf hrf (hwriter hrf) hloc
  obtain rfl := halign hj hrf
  exact ⟨w, hj, hrf⟩

private theorem isWriting_of_nthWrite {t : D.Tid} {x : D.Loc} {i : ℕ} {w : Event D}
    (h : G.nthWrite t x i = some w) : w.IsWriting := (G.nthEvent_index h).2.2.2

private theorem loc_of_nthEvent {t : D.Tid} {x : D.Loc} {op : OpType} {i : ℕ} {e : Event D}
    (h : G.nthEvent t x op i = some e) : e.loc = x := (G.nthEvent_index h).2.2.1

private theorem tid_of_nthEvent {t : D.Tid} {x : D.Loc} {op : OpType} {i : ℕ} {e : Event D}
    (h : G.nthEvent t x op i = some e) : e.tid = t := (G.nthEvent_index h).2.1

/-- Read-coherence, in the shape the paper's proof uses it: if `e ⟶rf r`,
`e ⟶mo w2` and `w2 ⟶hb r`, contradiction. -/
private theorem rc {e r w2 : Event D} (hcons : G.RAConsistent) (hrf : G.rf e r)
    (hmo : G.mo e w2) (hhb : G.hb w2 r) : False :=
  hcons.read_coherence e ⟨r, ⟨w2, hmo, hhb⟩, hrf⟩

/-- The "`j < i`" exclusion, shared by both families: if `w_j(t, x)` is read by
`r_j(tr, x)` and by `r_k(tr, x)`, and `tr` writes `x` between the two reads,
read-coherence is violated. -/
private theorem lt_exclusion (hcons : G.RAConsistent) {t tr : D.Tid} {x : D.Loc}
    {j k : ℕ} {ew er erj wk : Event D}
    (hew : G.nthWrite t x j = some ew) (hrfj : G.rf ew erj) (hrf : G.rf ew er)
    (hwk : G.nthWrite tr x k = some wk)
    (hpo1 : G.po erj wk) (hpo2 : G.po wk er) (hne : ew ≠ wk) : False := by
  have hmo : G.mo ew wk :=
    G.mo_of_hb_sameLoc hcons (Relation.TransGen.head (Or.inr hrfj) (hb_of_po hpo1))
      (isWriting_of_nthWrite hew) (isWriting_of_nthWrite hwk)
      ((loc_of_nthEvent hew).trans (loc_of_nthEvent hwk).symm) hne
  exact rc hcons hrf hmo (hb_of_po hpo2)

/-- The first family of the pair at index `k`, given both families below `k`:
an `rf`-edge from `w_i(g, a)` into `r_k(c, a)` has `i = k`. -/
theorem step_ca (hcons : G.RAConsistent) (h : G.CrossPair g p c q a a' z z') (k : ℕ)
    (IHca : ∀ k' < k, ∀ {i : ℕ} {ew er : Event D}, G.nthWrite g a i = some ew →
      G.nthRead c a k' = some er → G.rf ew er → i = k')
    (IHqa' : ∀ k' < k, ∀ {n : ℕ} {ew er : Event D}, G.nthWrite p a' n = some ew →
      G.nthRead q a' k' = some er → G.rf ew er → n = k') :
    ∀ {i : ℕ} {ew er : Event D}, G.nthWrite g a i = some ew →
      G.nthRead c a k = some er → G.rf ew er → i = k := by
  intro i ew er hew her hrf
  rcases Nat.lt_trichotomy i k with hlt | heq | hgt
  · -- `i < k`: `r_i(c, a)` also reads from `w_i(g, a)`, while `c` writes `a`
    -- between `r_i(c, a)` and `r_k(c, a)`.
    exfalso
    obtain ⟨eri, heri⟩ := G.nthEvent_of_le her hlt.le
    obtain ⟨ew', hew', hrf'⟩ := aligned_writer heri (fun hw => h.tag_ca heri hw)
      (fun hj hr => IHca i hlt hj heri hr)
    obtain rfl : ew' = ew := Option.some.inj (hew'.symm.trans hew)
    obtain ⟨wk, hwk, hpo2⟩ := h.c_wr her
    have hne : ew' ≠ wk := fun he =>
      h.hgc ((tid_of_nthEvent hew').symm.trans (he ▸ tid_of_nthEvent hwk))
    exact lt_exclusion hcons hew' hrf' hrf hwk (h.c_rw heri hwk hlt) hpo2 hne
  · exact heq
  · -- `i > k`: for `k = 0` this is the base case; otherwise, with `k = k' + 1`,
    -- `w_{k'}(q, a') ⟶rf r_{k'}(c, a')`, `w_{k'}(q, a') ⟶mo w_{k'}(p, a')`, and
    -- `w_{k'}(p, a') ⟶hb r_{k'}(c, a')` violate read-coherence.
    exfalso
    rcases k with _ | k
    · exact absurd (h.base hew her hrf) (by omega)
    obtain ⟨er', her', hpo3⟩ := h.c_rr her
    obtain ⟨wq, hwq, hrfq⟩ := h.rs_ca' k er' her'
    obtain ⟨erq, herq⟩ := h.q_ex hwq
    obtain ⟨ep, hep, hrfp⟩ := aligned_writer herq (fun hw => h.tag_qa' herq hw)
      (fun hj hr => IHqa' k (Nat.lt_succ_self k) hj herq hr)
    obtain ⟨wq', hwq', hpoq⟩ := h.q_wr herq
    obtain rfl : wq' = wq := Option.some.inj (hwq'.symm.trans hwq)
    have hne : ep ≠ wq' := fun he =>
      h.hpq ((tid_of_nthEvent hep).symm.trans (he ▸ tid_of_nthEvent hwq'))
    have hmo : G.mo wq' ep :=
      G.mo_of_rf_hb hcons hrfp (hb_of_po hpoq) (isWriting_of_nthWrite hep)
        (isWriting_of_nthWrite hwq') ((loc_of_nthEvent hep).trans (loc_of_nthEvent hwq').symm) hne
    obtain ⟨wz, hwz, hpo4⟩ := h.p_a'z hep
    obtain ⟨rz, hrz, hpo5⟩ := h.g_za hew (m := k) (by omega)
    obtain ⟨wz', hwz', hrfz⟩ := h.rs_gz k rz hrz
    obtain rfl : wz' = wz := Option.some.inj (hwz'.symm.trans hwz)
    have hhb : G.hb ep er' :=
      Relation.TransGen.head (Or.inl hpo4) <| Relation.TransGen.head (Or.inr hrfz) <|
        Relation.TransGen.head (Or.inl hpo5) <| Relation.TransGen.head (Or.inr hrf) <|
          hb_of_po hpo3
    exact rc hcons hrfq hmo hhb

/-- The second family of the pair at index `k`, given the second family below
`k` and the first at `k`: an `rf`-edge from `w_n(p, a')` into `r_k(q, a')` has
`n = k`. -/
theorem step_qa' (hcons : G.RAConsistent) (h : G.CrossPair g p c q a a' z z') (k : ℕ)
    (IHqa' : ∀ k' < k, ∀ {n : ℕ} {ew er : Event D}, G.nthWrite p a' n = some ew →
      G.nthRead q a' k' = some er → G.rf ew er → n = k')
    (Hca : ∀ {i : ℕ} {ew er : Event D}, G.nthWrite g a i = some ew →
      G.nthRead c a k = some er → G.rf ew er → i = k) :
    ∀ {n : ℕ} {ew er : Event D}, G.nthWrite p a' n = some ew →
      G.nthRead q a' k = some er → G.rf ew er → n = k := by
  intro n ew er hew her hrf
  rcases Nat.lt_trichotomy n k with hlt | heq | hgt
  · -- `n < k`: `r_n(q, a')` also reads from `w_n(p, a')`, while `q` writes `a'`
    -- between `r_n(q, a')` and `r_k(q, a')`.
    exfalso
    obtain ⟨ern, hern⟩ := G.nthEvent_of_le her hlt.le
    obtain ⟨ew', hew', hrf'⟩ := aligned_writer hern (fun hw => h.tag_qa' hern hw)
      (fun hj hr => IHqa' n hlt hj hern hr)
    obtain rfl : ew' = ew := Option.some.inj (hew'.symm.trans hew)
    obtain ⟨wk, hwk, hpo2⟩ := h.q_wr her
    have hne : ew' ≠ wk := fun he =>
      h.hpq ((tid_of_nthEvent hew').symm.trans (he ▸ tid_of_nthEvent hwk))
    exact lt_exclusion hcons hew' hrf' hrf hwk (h.q_rw hern hwk hlt) hpo2 hne
  · exact heq
  · -- `n > k`: `w_k(c, a) ⟶rf r_k(q, a)`, `w_k(c, a) ⟶mo w_k(g, a)`, and
    -- `w_k(g, a) ⟶hb r_k(q, a)` violate read-coherence.
    exfalso
    obtain ⟨erqa, herqa, hpo3⟩ := h.q_rr her
    obtain ⟨wc, hwc, hrfc⟩ := h.rs_qa k erqa herqa
    obtain ⟨erc, herc⟩ := h.c_ex hwc
    obtain ⟨eg, heg, hrfg⟩ := aligned_writer herc (fun hw => h.tag_ca herc hw)
      (fun hj hr => Hca hj herc hr)
    obtain ⟨wc', hwc', hpoc⟩ := h.c_wr herc
    obtain rfl : wc' = wc := Option.some.inj (hwc'.symm.trans hwc)
    have hne : eg ≠ wc' := fun he =>
      h.hgc ((tid_of_nthEvent heg).symm.trans (he ▸ tid_of_nthEvent hwc'))
    have hmo : G.mo wc' eg :=
      G.mo_of_rf_hb hcons hrfg (hb_of_po hpoc) (isWriting_of_nthWrite heg)
        (isWriting_of_nthWrite hwc') ((loc_of_nthEvent heg).trans (loc_of_nthEvent hwc').symm) hne
    obtain ⟨wz, hwz, hpo4⟩ := h.g_az' heg
    obtain ⟨rz, hrz, hpo5⟩ := h.p_z'a' hew (m := k) (by omega)
    obtain ⟨wz', hwz', hrfz⟩ := h.rs_pz' k rz hrz
    obtain rfl : wz' = wz := Option.some.inj (hwz'.symm.trans hwz)
    have hhb : G.hb eg erqa :=
      Relation.TransGen.head (Or.inl hpo4) <| Relation.TransGen.head (Or.inr hrfz) <|
        Relation.TransGen.head (Or.inl hpo5) <| Relation.TransGen.head (Or.inr hrf) <|
          hb_of_po hpo3
    exact rc hcons hrfc hmo hhb

/-- Eq. (17) for one pair: at every index `k`, an `rf`-edge from `g`'s `i`-th
write on `a` into `c`'s `k`-th read on `a` has `i = k`, and an `rf`-edge from
`p`'s `n`-th write on `a'` into `q`'s `k`-th read on `a'` has `n = k`. By strong
induction on `k`, both families at once, as in the paper. -/
theorem no_skipping (hcons : G.RAConsistent) (h : G.CrossPair g p c q a a' z z') (k : ℕ) :
    (∀ {i : ℕ} {ew er : Event D}, G.nthWrite g a i = some ew →
      G.nthRead c a k = some er → G.rf ew er → i = k) ∧
    (∀ {n : ℕ} {ew er : Event D}, G.nthWrite p a' n = some ew →
      G.nthRead q a' k = some er → G.rf ew er → n = k) := by
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    have hca : ∀ {i : ℕ} {ew er : Event D}, G.nthWrite g a i = some ew →
        G.nthRead c a k = some er → G.rf ew er → i = k := fun hew her hrf =>
      h.step_ca hcons k (fun k' hk' => (IH k' hk').1) (fun k' hk' => (IH k' hk').2) hew her hrf
    exact ⟨hca, fun hew her hrf =>
      h.step_qa' hcons k (fun k' hk' => (IH k' hk').2) hca hew her hrf⟩

end ExecutionGraph.CrossPair

end Cross

end RAUndecidability
