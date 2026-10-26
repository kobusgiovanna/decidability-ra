import RAUndecidability.Defs.Execution

/-!
# Event indexing

The "notational convenience" paragraph of Section 3 (§3):
for an execution `G`, `w_i(t, x)` and `r_i(t, x)` are the `i`-th write and
read event of thread `t` on location `x` in `G`, and conversely an event `e`
of `G` has an index relative to its own thread/location/operation triple.

* `G` is an explicit argument throughout: soundness quantifies over an
  arbitrary `G`, completeness instantiates one constructed `G`.
* Indices are relative to the `(thread, location, operation)` triple, so
  `w_i(t, x)` and `r_i(t, x)` are each the `i`-th event of their own kind.
* `nthWrite`/`nthRead` (index → event) are partial (`Option`), since `G`
  need not contain a given event; `index` (event → index) is total, with junk
  value `(G.opEvents e.tid e.loc e.op).length` off `G`'s events.
  `index_nthEvent` and `nthEvent_index` relate the two directions.
* `opEvents` filters the po-sorted `threadEvents`, so it inherits po-order.
-/

namespace RAUndecidability

variable {D : Domains} (G : ExecutionGraph D)

/-! ## Event indexing (§3) -/

/-- The po-sorted events of thread `t` on location `x` with operation `op`
(the sequence `w_1(t,x), w_2(t,x), …` or `r_1(t,x), r_2(t,x), …` of the
paper, in order): a sublist of `threadEvents t`. -/
noncomputable def ExecutionGraph.opEvents (t : D.Tid) (x : D.Loc) (op : OpType) :
    List (Event D) :=
  ((G.threadEvents t).filter fun e => e.1.loc = x ∧ e.1.op = op).map Subtype.val

/-- Membership in `opEvents` unfolds to exactly the defining conditions: `e`
is one of `G`'s events, on the right thread, location and operation. -/
theorem ExecutionGraph.mem_opEvents_iff {t : D.Tid} {x : D.Loc} {op : OpType} {e : Event D} :
    e ∈ G.opEvents t x op ↔ e ∈ G.Events ∧ e.tid = t ∧ e.loc = x ∧ e.op = op := by
  unfold ExecutionGraph.opEvents
  constructor
  · intro hmem
    simp only [List.mem_map] at hmem
    obtain ⟨b, hb, rfl⟩ := hmem
    simp only [List.mem_filter] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have hbtid : b.1 ∈ G.Events.filter (fun e' => e'.tid = t) := b.2
    simp only [Finset.mem_filter] at hbtid
    simp only [decide_eq_true_eq] at hb2
    exact ⟨hbtid.1, hbtid.2, hb2.1, hb2.2⟩
  · rintro ⟨hmem, htid, hloc, hop⟩
    have hsub : (⟨e, Finset.mem_filter.mpr ⟨hmem, htid⟩⟩ :
        {e' : Event D // e' ∈ G.Events.filter (fun e' => e'.tid = t)}) ∈ G.threadEvents t := by
      rw [ExecutionGraph.threadEvents, Finset.mem_sort]
      exact Finset.mem_univ _
    have hfilt : (⟨e, Finset.mem_filter.mpr ⟨hmem, htid⟩⟩ :
        {e' : Event D // e' ∈ G.Events.filter (fun e' => e'.tid = t)}) ∈
        (G.threadEvents t).filter (fun e' => e'.1.loc = x ∧ e'.1.op = op) := by
      simp [List.mem_filter, hsub, hloc, hop]
    exact List.mem_map.mpr ⟨_, hfilt, rfl⟩

/-- Every one of `G`'s events is among its own thread/location/operation
events. -/
theorem ExecutionGraph.mem_opEvents_self {e : Event D} (he : e ∈ G.Events) :
    e ∈ G.opEvents e.tid e.loc e.op :=
  G.mem_opEvents_iff.mpr ⟨he, rfl, rfl, rfl⟩

/-- `opEvents` has no repeats: it is a filtered image of `threadEvents`,
itself `Finset.sort` of a `Finset`, through the injective `Subtype.val`. -/
theorem ExecutionGraph.opEvents_nodup (t : D.Tid) (x : D.Loc) (op : OpType) :
    (G.opEvents t x op).Nodup := by
  unfold ExecutionGraph.opEvents
  apply List.Nodup.map Subtype.val_injective
  apply List.Nodup.filter
  unfold ExecutionGraph.threadEvents
  exact Finset.sort_nodup _ _

/-- The `i`-th event of thread `t` on location `x` with operation `op`
(0-indexed), or `none` if `G` has fewer than `i + 1` such events. The shared
implementation behind `nthWrite`/`nthRead`. -/
noncomputable def ExecutionGraph.nthEvent (t : D.Tid) (x : D.Loc) (op : OpType) (i : ℕ) :
    Option (Event D) :=
  (G.opEvents t x op)[i]?

/-- **Paper:** §3, ¶ Event indexing (`w_i(t, x)`).

`w_i(t, x)` (§3), 0-indexed: the `i`-th write of thread
`t` on location `x` in `G`, or `none` if it doesn't exist. -/
noncomputable def ExecutionGraph.nthWrite (t : D.Tid) (x : D.Loc) (i : ℕ) : Option (Event D) :=
  G.nthEvent t x .wt i

/-- **Paper:** §3, ¶ Event indexing (`r_i(t, x)`).

`r_i(t, x)` (§3), 0-indexed: the `i`-th read of thread
`t` on location `x` in `G`, or `none` if it doesn't exist. -/
noncomputable def ExecutionGraph.nthRead (t : D.Tid) (x : D.Loc) (i : ℕ) : Option (Event D) :=
  G.nthEvent t x .rd i

/-- The index of `e` (the paper's `e_i` (event indexing, §3), read in the other
direction): the position of `e` among `G`'s events sharing its own thread,
location and operation, in po-order. Total on `Event D`, with junk value
the relevant list's length when `e` is not among `G`'s matching events (see
`index_lt_length_iff`). -/
noncomputable def ExecutionGraph.index (e : Event D) : ℕ :=
  haveI := Classical.decEq (Event D)
  (G.opEvents e.tid e.loc e.op).idxOf e

/-- `index`'s junk value is detectable: it is always `< length`, but exactly
when `e` occurs among its own thread/location/operation events. -/
theorem ExecutionGraph.index_lt_length_iff (e : Event D) :
    haveI := Classical.decEq (Event D)
    G.index e < (G.opEvents e.tid e.loc e.op).length ↔ e ∈ G.opEvents e.tid e.loc e.op := by
  classical
  unfold ExecutionGraph.index
  exact List.idxOf_lt_length_iff

/-- "Mutual inverse where defined", direction one: an event recovered from
its own index is itself. -/
theorem ExecutionGraph.index_nthEvent {e : Event D} (he : e ∈ G.Events) :
    G.nthEvent e.tid e.loc e.op (G.index e) = some e := by
  classical
  have hmem := G.mem_opEvents_self he
  have hlt : G.index e < (G.opEvents e.tid e.loc e.op).length :=
    (G.index_lt_length_iff e).2 hmem
  change (G.opEvents e.tid e.loc e.op)[G.index e]? = some e
  rw [List.getElem?_eq_getElem hlt]
  congr 1
  exact List.getElem_idxOf hlt

/-- "Mutual inverse where defined", direction two: an event returned by
`nthEvent` (hence by `nthWrite`/`nthRead`) at position `i` has index exactly
`i`, and its own thread/location/operation are the ones asked for. -/
theorem ExecutionGraph.nthEvent_index {t : D.Tid} {x : D.Loc} {op : OpType} {i : ℕ} {e : Event D}
    (h : G.nthEvent t x op i = some e) :
    G.index e = i ∧ e.tid = t ∧ e.loc = x ∧ e.op = op := by
  classical
  have hlt_eq : (G.opEvents t x op)[i]? = some e := h
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hlt_eq
  have hmem : e ∈ G.opEvents t x op := heq ▸ List.getElem_mem hlt
  obtain ⟨_, htid, hloc, hop⟩ := G.mem_opEvents_iff.mp hmem
  refine ⟨?_, htid, hloc, hop⟩
  have heq2 : G.opEvents t x op = G.opEvents e.tid e.loc e.op := by rw [htid, hloc, hop]
  rw [heq2] at hlt_eq hlt
  have hidx_lt : G.index e < (G.opEvents e.tid e.loc e.op).length :=
    (G.index_lt_length_iff e).2 (heq2 ▸ hmem)
  have hidx_eq : (G.opEvents e.tid e.loc e.op)[G.index e]? = some e := by
    rw [List.getElem?_eq_getElem hidx_lt]
    congr 1
    exact List.getElem_idxOf hidx_lt
  exact (List.getElem?_inj hidx_lt (G.opEvents_nodup e.tid e.loc e.op)).mp
    (hidx_eq.trans hlt_eq.symm)

/-! ## Monotonicity (§3.5) -/

/-- An `R`-edge `e_i ⟶[R] e_j` is non-decreasing if `i ≤ j` (§3.5);
`R` is non-decreasing if all its edges are. -/
def ExecutionGraph.NonDecreasing (R : Event D → Event D → Prop) : Prop :=
  ∀ {e1 e2}, R e1 e2 → G.index e1 ≤ G.index e2

/-- An `R`-edge `e_i ⟶[R] e_j` is increasing if `i < j` (§3.5);
`R` is increasing if all its edges are. -/
def ExecutionGraph.Increasing (R : Event D → Event D → Prop) : Prop :=
  ∀ {e1 e2}, R e1 e2 → G.index e1 < G.index e2


end RAUndecidability
