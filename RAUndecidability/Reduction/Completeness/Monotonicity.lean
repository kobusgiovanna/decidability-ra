import RAUndecidability.Reduction.Completeness.Construction

/-!
# Monotonicity of po-indices

Section 3.5's monotonicity lemmas (Lemmas 3.4 and 3.5) for the traces of
the twelve threads, from which the execution graph `G` is built
(`Completeness/Graph.lean`): the index arithmetic of the nested guessers
`GuessAX`/`GuessBX`, and the assembly over all twelve threads
(`po_monotone_of_traceShapes`, `po_reads_decreasing_of_traceShapes`).

The arithmetic quantities `nestedCallLen`, `nestedGap`, `nestedInnerStart`,
`nestedOuterLen`, `nestedOuterStart` mention no thread or location and are
shared by `GuessAX` and `GuessBX`, whose loops have the same shape.
-/

namespace RAUndecidability

/-! ## Index formulas for the nested guessers

In `GuessAX`/`GuessBX`, the inner calls have uniform length (`nestedCallLen`:
`3`, except `2` for the thread's first call), but the calls of one outer
iteration sit between two bridge events (`z_α^{x,y}`'s write, `ℓ_α^{y,x}`'s
read), a gap of two events. `nestedInnerStart` follows the recurrence
`blockStart (n + 1) = blockStart n + blockLen n` of `blockIndex_po_monotone`,
with `blockLen k := nestedCallLen k + nestedGap ks k`.

**The `ks` convention.** `ks[m] + 1` is the number of inner calls of outer
iteration `m`. `ks` covers iterations `0, …, N` (`ks.length = N + 1`); the
last iteration `N + 1`, whose `aux ← NDet` drew `⊥`, always makes exactly one
call (`extAlpha I none = [none]`). Iteration `0` corresponds to `inner0Rest`
(`ks[0] = inner0Rest.length`), and iteration `m` for `1 ≤ m ≤ N` to
`outerRest`'s entry `m - 1`. -/

/-- The length (in events) of global inner call `k`: `2` for `k = 0`, `3`
otherwise. `k = 0` is the thread's first call ever: `fst` is never reset, so
`First()` holds for exactly one call of the whole run. -/
def nestedCallLen (k : ℕ) : ℕ := if k = 0 then 2 else 3

/-- The gap after global inner call `k`: `2` (`ℓ_α^{y,x}`'s read closing its
outer iteration, then `z_α^{x,y}`'s write opening the next) if `k` is the last
call of its outer iteration, `0` otherwise. Computed by walking `ks` one
iteration at a time. Meaningful for `k < ksPrefix ks ks.length`. -/
def nestedGap : List ℕ → ℕ → ℕ
  | [], _ => 0
  | k0 :: ks', k => if k < k0 then 0 else if k = k0 then 2 else nestedGap ks' (k - (k0 + 1))

/-- The position of global inner call `k`'s first event, with
`blockLen k := nestedCallLen k + nestedGap ks k`. `nestedInnerStart ks 0 = 1`:
call `0` begins right after the thread's first event, a `z_α^{x,y}` write. -/
def nestedInnerStart (ks : List ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => nestedInnerStart ks k + nestedCallLen k + nestedGap ks k

/-- `nestedInnerStart`'s defining recurrence. -/
theorem nestedInnerStart_succ (ks : List ℕ) (k : ℕ) :
    nestedInnerStart ks (k + 1) =
      nestedInnerStart ks k + (nestedCallLen k + nestedGap ks k) := by
  simp only [nestedInnerStart, Nat.add_assoc]

/-- `nestedInnerStart ks` is strictly monotone, since every
`nestedCallLen k` is positive. -/
theorem nestedInnerStart_strictMono (ks : List ℕ) : StrictMono (nestedInnerStart ks) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := nestedInnerStart_succ ks n
  have hpos : 0 < nestedCallLen n := by unfold nestedCallLen; split <;> omega
  omega

theorem nestedInnerStart_lt_iff (ks : List ℕ) (k k' : ℕ) :
    nestedInnerStart ks k < nestedInnerStart ks k' ↔ k < k' :=
  (nestedInnerStart_strictMono ks).lt_iff_lt

/-- The length (in events) of outer iteration `m`: `3 * ks[0] + 4` for
iteration `0` (`z_α^{x,y}`'s write, the two-event first call, `ks[0]`
three-event calls, `ℓ_α^{y,x}`'s read), `5` for the last iteration
`m = N + 1` (bridge write, one three-event call, bridge read), and
`3 * (ks[m] + 1) + 2` in between. -/
def nestedOuterLen (ks : List ℕ) (N m : ℕ) : ℕ :=
  if m = N + 1 then 5
  else if m = 0 then 3 * ks.getD 0 0 + 4
  else 3 * (ks.getD m 0 + 1) + 2

/-- The position of outer iteration `m`'s `z_α^{x,y}` write.
`nestedOuterStart _ _ 0 = 0`. -/
def nestedOuterStart (ks : List ℕ) (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => nestedOuterStart ks N m + nestedOuterLen ks N m

/-- `nestedOuterStart`'s defining recurrence. -/
theorem nestedOuterStart_succ (ks : List ℕ) (N m : ℕ) :
    nestedOuterStart ks N (m + 1) = nestedOuterStart ks N m + nestedOuterLen ks N m := rfl

theorem nestedOuterStart_mono (ks : List ℕ) (N : ℕ) : Monotone (nestedOuterStart ks N) := by
  apply monotone_nat_of_le_succ
  intro n
  change nestedOuterStart ks N n ≤ nestedOuterStart ks N n + nestedOuterLen ks N n
  omega

theorem nestedOuterStart_ge (ks : List ℕ) (N m : ℕ) :
    nestedOuterStart ks N (m + 1) ≥ 3 * ks.getD 0 0 + 4 := by
  have h1 : nestedOuterStart ks N 1 = 3 * ks.getD 0 0 + 4 := by
    simp [nestedOuterStart, nestedOuterLen]
  have h2 : nestedOuterStart ks N 1 ≤ nestedOuterStart ks N (m + 1) :=
    nestedOuterStart_mono ks N (by omega)
  omega

/-- `nestedGap` within outer iteration `M`'s group (global calls
`ksPrefix ks M` through `ksPrefix ks M + ks[M]`): `2` at the group's last
call (`r = ks[M]`), `0` before. By induction on `M`. -/
theorem nestedGap_group_add : ∀ (M : ℕ) (ks : List ℕ) (hM : M < ks.length) (r : ℕ),
    r ≤ ks[M]'hM →
    nestedGap ks (ksPrefix ks M + r) = if r = ks[M]'hM then 2 else 0
  | 0, ks, hM, r, hr => by
      match ks, hM with
      | k0 :: ks', hM =>
          simp only [ksPrefix, Nat.zero_add]
          have hk0 : (k0 :: ks')[0]'hM = k0 := rfl
          rw [hk0] at hr ⊢
          show nestedGap (k0 :: ks') r = if r = k0 then 2 else 0
          unfold nestedGap
          split_ifs <;> omega
  | M + 1, ks, hM, r, hr => by
      match ks, hM with
      | k0 :: ks', hM =>
          have hM' : M < ks'.length := by simpa using hM
          have hMeq : (k0 :: ks')[M + 1]'hM = ks'[M]'hM' := rfl
          rw [hMeq] at hr ⊢
          have ih := nestedGap_group_add M ks' hM' r hr
          rw [ksPrefix_cons]
          show nestedGap (k0 :: ks') (k0 + 1 + ksPrefix ks' M + r) =
            if r = ks'[M]'hM' then 2 else 0
          unfold nestedGap
          rw [if_neg (by omega), if_neg (by omega)]
          have heq : k0 + 1 + ksPrefix ks' M + r - (k0 + 1) = ksPrefix ks' M + r := by omega
          rw [heq]
          exact ih

/-- Advancing `nestedInnerStart` by `r` calls within outer iteration `M`'s
group: `3 * r` events (`3 * r - 1` for `M = 0`, whose first call has length
`2`), plus `2` when `r` reaches the end of the group (`r = ks[M] + 1`). By
induction on `r`. -/
theorem nestedInnerStart_group_add (ks : List ℕ) (M : ℕ) (hM : M < ks.length) : ∀ r,
    r ≤ ks[M]'hM + 1 →
    nestedInnerStart ks (ksPrefix ks M + r) =
      nestedInnerStart ks (ksPrefix ks M) +
        (if M = 0 then 3 * r - 1 else 3 * r) +
        (if r = ks[M]'hM + 1 then 2 else 0) := by
  intro r hr
  induction r with
  | zero => simp
  | succ r ihr =>
      -- `hr : r + 1 ≤ ks[M] + 1` gives `r ≤ ks[M]`, within the range of
      -- `nestedGap_group_add`.
      have hrle : r ≤ ks[M]'hM := by omega
      have ihr' := ihr (by omega)
      have hrec : nestedInnerStart ks (ksPrefix ks M + (r + 1))
          = nestedInnerStart ks (ksPrefix ks M + r)
              + (nestedCallLen (ksPrefix ks M + r) + nestedGap ks (ksPrefix ks M + r)) := by
        have hshift : ksPrefix ks M + (r + 1) = (ksPrefix ks M + r) + 1 := by omega
        rw [hshift]
        exact nestedInnerStart_succ ks (ksPrefix ks M + r)
      have hzero_iff : ksPrefix ks M + r = 0 ↔ M = 0 ∧ r = 0 := by
        rw [Nat.add_eq_zero_iff, ksPrefix_eq_zero_iff]
      have hcalllen : nestedCallLen (ksPrefix ks M + r) = if M = 0 ∧ r = 0 then 2 else 3 := by
        unfold nestedCallLen
        by_cases hMr : M = 0 ∧ r = 0
        · rw [if_pos hMr, if_pos (hzero_iff.mpr hMr)]
        · rw [if_neg hMr, if_neg (fun h => hMr (hzero_iff.mp h))]
      have hgap := nestedGap_group_add M ks hM r hrle
      rw [hrec, ihr', hcalllen, hgap]
      split_ifs <;> omega

/-- The start of call `n + 1` (the `n`-th call of `inner0Rest`, `n < ks[0]`):
`3 * (n + 1)`. -/
theorem nestedInnerStart_inner0Rest (ks : List ℕ) (hks : 0 < ks.length) (n : ℕ)
    (hn : n < ks[0]'hks) :
    nestedInnerStart ks (n + 1) = 3 * (n + 1) := by
  have h := nestedInnerStart_group_add ks 0 hks (n + 1) (by omega)
  simp only [ksPrefix, Nat.zero_add, if_true] at h
  rw [if_neg (by omega)] at h
  have h0 : nestedInnerStart ks 0 = 1 := rfl
  omega

/-- The start of call `ksPrefix ks (m + 1) + n`, for `n ≤ ks[m + 1]`. -/
theorem nestedInnerStart_outerRest_add (ks : List ℕ) (m : ℕ) (hm : m + 1 < ks.length) (n : ℕ)
    (hn : n ≤ ks[m + 1]'hm) :
    nestedInnerStart ks (ksPrefix ks (m + 1) + n)
      = nestedInnerStart ks (ksPrefix ks (m + 1)) + 3 * n := by
  have h := nestedInnerStart_group_add ks (m + 1) hm n (by omega)
  rw [if_neg (by omega), if_neg (by omega)] at h
  exact h

/-- Outer iteration `M`'s start (its `z_α^{x,y}` write) is one position before
the start of the first call of its group, `ksPrefix ks M`, for `M ≤ N + 1`.
By induction on `M`, via `nestedInnerStart_group_add`. -/
theorem nestedOuterStart_succ_eq_innerStart (ks : List ℕ) (N M : ℕ) (hks : ks.length = N + 1)
    (hM : M ≤ N + 1) :
    nestedOuterStart ks N M + 1 = nestedInnerStart ks (ksPrefix ks M) := by
  induction M with
  | zero => simp [nestedOuterStart, nestedInnerStart, ksPrefix]
  | succ M ih =>
      have hM' : M ≤ N + 1 := by omega
      have ihM := ih hM'
      have hMlt : M < ks.length := by omega
      have hgetEq : ks.getD M 0 = ks[M]'hMlt := by
        show (ks[M]?).getD 0 = ks[M]'hMlt
        rw [List.getElem?_eq_getElem hMlt]
        rfl
      have h1 := nestedInnerStart_group_add ks M hMlt (ks[M]'hMlt + 1) (le_refl _)
      have hshift2 : ksPrefix ks (M + 1) = ksPrefix ks M + (ks.getD M 0 + 1) := rfl
      have hsucc : nestedOuterStart ks N (M + 1) = nestedOuterStart ks N M + nestedOuterLen ks N M :=
        nestedOuterStart_succ ks N M
      by_cases hM0 : M = 0
      · subst hM0
        have hlen : nestedOuterLen ks N 0 = 3 * ks[0]'hMlt + 4 := by
          unfold nestedOuterLen
          rw [if_neg (show (0 : ℕ) ≠ N + 1 by omega), if_pos rfl, hgetEq]
        rw [hsucc, hlen, hshift2, hgetEq, h1]
        split_ifs <;> omega
      · have hMne : M ≠ N + 1 := by omega
        have hlen : nestedOuterLen ks N M = 3 * (ks[M]'hMlt + 1) + 2 := by
          unfold nestedOuterLen
          rw [if_neg hMne, if_neg hM0, hgetEq]
        rw [hsucc, hlen, hshift2, hgetEq, h1]
        split_ifs <;> omega

theorem guessAXInnerBlockElems_length (I : PCPInstance) (vs : Val I × Val I × Val I) :
    (guessAXInnerBlockElems I vs).length = 3 := rfl

/-- One outer iteration's emitted length is `3` events per inner call,
plus the two bridge events. -/
theorem guessAXOuterBlockElems_length (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) :
    (guessAXOuterBlockElems I b vs).length = 3 * vs.length + 2 := by
  have h1 : (vs.flatMap (guessAXInnerBlockElems I)).length = 3 * vs.length := by
    rw [List.length_flatMap]
    simp [guessAXInnerBlockElems_length, mul_comm]
  simp [guessAXOuterBlockElems, h1]

/-- Filtering a flatMap of `guessAXInnerBlockElems` blocks by a predicate
matching exactly one position `p0` of every block gives the per-block
matches, in order. -/
theorem guessAXInnerBlockElems_filter (I : PCPInstance)
    (pred : ThreadLabel (domainOf I) Tid.guessAX → Bool) (p0 : ℕ)
    (bval : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX)
    (h0 : ∀ a, (guessAXInnerBlockElems I a)[p0]? = some (bval a))
    (htrue : ∀ a, pred (bval a) = true)
    (hfalse : ∀ a q b, q ≠ p0 → (guessAXInnerBlockElems I a)[q]? = some b → pred b = false) :
    ∀ vs : List (Val I × Val I × Val I),
      (vs.flatMap (guessAXInnerBlockElems I)).filter pred = vs.map bval := by
  intro vs
  induction vs with
  | nil => simp
  | cons a vs ih =>
      have hsingle := list_filter_singleton_of_unique' (guessAXInnerBlockElems I a) pred p0
        (bval a) (h0 a) (htrue a) (hfalse a)
      rw [List.flatMap_cons, List.filter_append, hsingle, ih, List.map_cons, List.singleton_append]

/-- `guessAXInnerBlockElems_filter` across one outer iteration: the leading
`z_α^{x,y}` write and trailing `ℓ_α^{y,x}` read are bridge events and do not
match `pred`. -/
theorem guessAXOuterBlockElems_filter (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I))
    (pred : ThreadLabel (domainOf I) Tid.guessAX → Bool) (p0 : ℕ)
    (bval : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX)
    (h0 : ∀ a, (guessAXInnerBlockElems I a)[p0]? = some (bval a))
    (htrue : ∀ a, pred (bval a) = true)
    (hfalse : ∀ a q b0, q ≠ p0 → (guessAXInnerBlockElems I a)[q]? = some b0 → pred b0 = false)
    (hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
      pred b0 = false) :
    (guessAXOuterBlockElems I b vs).filter pred = vs.map bval := by
  have hz : pred (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    hpredNonBridge _ (by decide : Loc.zAxy ∈ BridgeLoc)
  have he : pred (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    hpredNonBridge _ (by decide : Loc.ellAyx ∈ BridgeLoc)
  unfold guessAXOuterBlockElems
  rw [List.filter_cons_of_neg (by simp [hz]), List.filter_append,
    guessAXInnerBlockElems_filter I pred p0 bval h0 htrue hfalse vs,
    List.filter_cons_of_neg (by simp [he]), List.filter_nil, List.append_nil]

/-- The number of `pred`-matches among the words of `outerRest`'s first `m`
entries is `ksPrefix ks (m + 1) - ksPrefix ks 1` (entry `j` being iteration
`j + 1`, with `ks[j + 1] + 1` matches). -/
theorem guessAXOuterRest_prefix_matchCount (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (_ : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (pred : ThreadLabel (domainOf I) Tid.guessAX → Bool) (p0 : ℕ)
    (bval : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX)
    (h0 : ∀ a, (guessAXInnerBlockElems I a)[p0]? = some (bval a))
    (htrue : ∀ a, pred (bval a) = true)
    (hfalse : ∀ a q b, q ≠ p0 → (guessAXInnerBlockElems I a)[q]? = some b → pred b = false)
    (hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
      pred b0 = false) :
    ∀ m ≤ N,
      (((outerRest.take m).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)).filter pred).length
        = ksPrefix ks (m + 1) - ksPrefix ks 1 := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN' : m ≤ N := by omega
      have ihm := ih hmN'
      have hmN : m < N := by omega
      obtain ⟨b, vs, km, hjbv, hksm, hlen⟩ := houter m hmN
      rw [List.take_add_one, hjbv]
      simp only [Option.toList_some, List.flatMap_append, List.filter_append, List.length_append]
      rw [ihm]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [guessAXOuterBlockElems_filter I b vs pred p0 bval h0 htrue hfalse hpredNonBridge,
        List.length_map, hlen]
      have hgd : ks.getD (m + 1) 0 = km := by
        show (ks[m + 1]?).getD 0 = km
        rw [hksm]; rfl
      have hpre : ksPrefix ks (m + 1 + 1) = ksPrefix ks (m + 1) + (km + 1) := by
        show ksPrefix ks (m + 1) + (ks.getD (m + 1) 0 + 1) = ksPrefix ks (m + 1) + (km + 1)
        rw [hgd]
      have hge : ksPrefix ks 1 ≤ ksPrefix ks (m + 1) := ksPrefix_mono ks (by omega)
      omega

/-- The total length of the words of `outerRest`'s first `m` entries is
`nestedOuterStart ks N (m + 1) - nestedOuterStart ks N 1` (the head,
iteration `0`, precedes `outerRest`). -/
theorem guessAXOuterRest_prefix_length (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (_ : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    ∀ m ≤ N + 1,
      ((outerRest.take m).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)).length
        = nestedOuterStart ks N (m + 1) - nestedOuterStart ks N 1 := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN : m ≤ N + 1 := by omega
      have ihm := ih hmN
      have hmlt : m < outerRest.length := by omega
      have hget : outerRest[m]? = some (outerRest[m]'hmlt) := List.getElem?_eq_getElem hmlt
      rw [List.take_add_one, hget]
      simp only [Option.toList_some, List.flatMap_append, List.length_append]
      rw [ihm]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hge1 : nestedOuterStart ks N 1 ≤ nestedOuterStart ks N (m + 1) :=
        nestedOuterStart_mono ks N (by omega)
      rcases Nat.lt_or_ge m N with hmn | hmn
      · obtain ⟨b, vs, km, hjbv, hksm, hlen⟩ := houter m hmn
        rw [hjbv] at hget
        have hbveq : outerRest[m]'hmlt = (b, vs) := by
          have h := hget.symm; simpa using h
        rw [hbveq]
        have hblen : (guessAXOuterBlockElems I b vs).length = 3 * (km + 1) + 2 := by
          rw [guessAXOuterBlockElems_length, hlen]
        rw [hblen]
        have hstartsucc : nestedOuterStart ks N (m + 2)
            = nestedOuterStart ks N (m + 1) + nestedOuterLen ks N (m + 1) := rfl
        have hgd : ks.getD (m + 1) 0 = km := by
          show (ks[m + 1]?).getD 0 = km
          rw [hksm]; rfl
        have htestlen : nestedOuterLen ks N (m + 1) = 3 * (km + 1) + 2 := by
          have h1 : m + 1 ≠ N + 1 := by omega
          have h2 : m + 1 ≠ 0 := by omega
          unfold nestedOuterLen
          rw [if_neg h1, if_neg h2, hgd]
        rw [show m + 1 + 1 = m + 2 from rfl, hstartsucc, htestlen]
        omega
      · have hmeqN : m = N := by omega
        obtain ⟨b, vs, hjbv, hlen⟩ := houterLast
        have hjbv' : outerRest[m]? = some (b, vs) := by rw [hmeqN]; exact hjbv
        rw [hjbv'] at hget
        have hbveq : outerRest[m]'hmlt = (b, vs) := by
          have h := hget.symm; simpa using h
        rw [hbveq]
        have hblen : (guessAXOuterBlockElems I b vs).length = 5 := by
          rw [guessAXOuterBlockElems_length, hlen]
        rw [hblen]
        have hstartsucc : nestedOuterStart ks N (m + 2)
            = nestedOuterStart ks N (m + 1) + nestedOuterLen ks N (m + 1) := rfl
        have htestlen : nestedOuterLen ks N (m + 1) = 5 := by
          have h2 : m + 1 = N + 1 := by omega
          unfold nestedOuterLen
          rw [if_pos h2]
        rw [show m + 1 + 1 = m + 2 from rfl, hstartsucc, htestlen]
        omega


/-! ## The `zAxx'` count at an arbitrary position

The number of `zAxx'`-reads before an arbitrary position: `m` whole outer
iterations (`guessAXOuterRest_prefix_matchCount`) plus a partial one
(`flatMap_uniform_take_count` on its inner calls), split by
`list_take_flatMap_offset`. -/

/-- The number of `zAxx'`-reads within a possibly partial outer block: the
bridge events do not match, so this is `flatMap_uniform_take_count` on the
inner calls. -/
theorem guessAXOuterBlockElems_zAxx'_take_count (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((guessAXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false)).length
      = n + (if 2 < p then 1 else 0) := by
  have hstep : ((guessAXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) =
      ((vs.flatMap (guessAXInnerBlockElems I)).take (n * 3 + p)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) := by
    unfold guessAXOuterBlockElems
    rw [List.take_succ_cons, List.filter_cons_of_neg (fun h => Bool.noConfusion h),
      List.take_append, List.filter_append]
    have hnil : (([⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩] :
        List (ThreadLabel (domainOf I) Tid.guessAX)).take
          (n * 3 + p - (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hxmem : x ∈ ([⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩] :
          List (ThreadLabel (domainOf I) Tid.guessAX)) := List.mem_of_mem_take hx
      simp only [List.mem_singleton] at hxmem
      subst hxmem
      exact fun h => Bool.noConfusion h
    rw [hnil, List.append_nil]
  rw [hstep]
  exact flatMap_uniform_take_count (guessAXInnerBlockElems I) 3 (fun _ => rfl)
    (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) 2 (by norm_num)
    (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun _ => rfl) (fun _ => rfl)
    (fun a q b hq hqb => by
      unfold guessAXInnerBlockElems at hqb
      rcases q with _ | _ | _ | q <;> simp_all only [ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.some.injEq, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
    vs n a hva p hp

/-- The number of `zAxx'`-reads before an arbitrary position of `outerRest`'s
flatMap, `M` whole outer iterations plus `n * 3 + p + 1` events into
iteration `M`. -/
theorem guessAXOuterRest_zAxx'_take_count (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (hks : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (hpredNonBridge :
      ∀ b0 : ThreadLabel (domainOf I) Tid.guessAX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) = false)
    (M : ℕ) (hM : M ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hMbv : outerRest[M]? = some (b, vs)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((outerRest.flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take M).flatMap (fun q => guessAXOuterBlockElems I q.1 q.2)).length +
          (n * 3 + p + 1))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false)).length
      = (ksPrefix ks (M + 1) - ksPrefix ks 1) + (n + (if 2 < p then 1 else 0)) := by
  have hqbound : n * 3 + p + 1 ≤ (guessAXOuterBlockElems I b vs).length := by
    have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
    rw [guessAXOuterBlockElems_length]
    omega
  rw [list_take_flatMap_offset (fun q => guessAXOuterBlockElems I q.1 q.2) outerRest M
    (n * 3 + p + 1) (b, vs) hMbv hqbound, List.filter_append, List.length_append,
    guessAXOuterRest_prefix_matchCount I ks N hks outerRest houter
      (fun l => match l.1.loc, l.1.op with | Loc.zAxx', OpType.rd => true | _, _ => false) 2
      (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessAXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [add_lt_add_iff_right, getElem?_pos, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, Subtype.forall, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, List.getElem_cons_zero, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      hpredNonBridge M hM,
    guessAXOuterBlockElems_zAxx'_take_count I b vs n p a hva hp]

theorem guessBXInnerBlockElems_length (I : PCPInstance) (vs : Val I × Val I × Val I) :
    (guessBXInnerBlockElems I vs).length = 3 := rfl

/-- One outer iteration's emitted length is `3` events per inner call,
plus the two bridge events. -/
theorem guessBXOuterBlockElems_length (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) :
    (guessBXOuterBlockElems I b vs).length = 3 * vs.length + 2 := by
  have h1 : (vs.flatMap (guessBXInnerBlockElems I)).length = 3 * vs.length := by
    rw [List.length_flatMap]
    simp [guessBXInnerBlockElems_length, mul_comm]
  simp [guessBXOuterBlockElems, h1]

/-- Filtering a flatMap of `guessBXInnerBlockElems` blocks by a predicate
matching exactly one position `p0` of every block gives the per-block
matches, in order. -/
theorem guessBXInnerBlockElems_filter (I : PCPInstance)
    (pred : ThreadLabel (domainOf I) Tid.guessBX → Bool) (p0 : ℕ)
    (bval : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX)
    (h0 : ∀ a, (guessBXInnerBlockElems I a)[p0]? = some (bval a))
    (htrue : ∀ a, pred (bval a) = true)
    (hfalse : ∀ a q b, q ≠ p0 → (guessBXInnerBlockElems I a)[q]? = some b → pred b = false) :
    ∀ vs : List (Val I × Val I × Val I),
      (vs.flatMap (guessBXInnerBlockElems I)).filter pred = vs.map bval := by
  intro vs
  induction vs with
  | nil => simp
  | cons a vs ih =>
      have hsingle := list_filter_singleton_of_unique' (guessBXInnerBlockElems I a) pred p0
        (bval a) (h0 a) (htrue a) (hfalse a)
      rw [List.flatMap_cons, List.filter_append, hsingle, ih, List.map_cons, List.singleton_append]

/-- `guessBXInnerBlockElems_filter` across one outer iteration: the leading
`z_β^{x,y}` write and trailing `ℓ_β^{y,x}` read are bridge events and do not
match `pred`. -/
theorem guessBXOuterBlockElems_filter (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I))
    (pred : ThreadLabel (domainOf I) Tid.guessBX → Bool) (p0 : ℕ)
    (bval : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX)
    (h0 : ∀ a, (guessBXInnerBlockElems I a)[p0]? = some (bval a))
    (htrue : ∀ a, pred (bval a) = true)
    (hfalse : ∀ a q b0, q ≠ p0 → (guessBXInnerBlockElems I a)[q]? = some b0 → pred b0 = false)
    (hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
      pred b0 = false) :
    (guessBXOuterBlockElems I b vs).filter pred = vs.map bval := by
  have hz : pred (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    hpredNonBridge _ (by decide : Loc.zBxy ∈ BridgeLoc)
  have he : pred (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    hpredNonBridge _ (by decide : Loc.ellByx ∈ BridgeLoc)
  unfold guessBXOuterBlockElems
  rw [List.filter_cons_of_neg (by simp [hz]), List.filter_append,
    guessBXInnerBlockElems_filter I pred p0 bval h0 htrue hfalse vs,
    List.filter_cons_of_neg (by simp [he]), List.filter_nil, List.append_nil]

/-- The number of `pred`-matches among the words of `outerRest`'s first `m`
entries is `ksPrefix ks (m + 1) - ksPrefix ks 1`. -/
theorem guessBXOuterRest_prefix_matchCount (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (_ : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (pred : ThreadLabel (domainOf I) Tid.guessBX → Bool) (p0 : ℕ)
    (bval : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX)
    (h0 : ∀ a, (guessBXInnerBlockElems I a)[p0]? = some (bval a))
    (htrue : ∀ a, pred (bval a) = true)
    (hfalse : ∀ a q b, q ≠ p0 → (guessBXInnerBlockElems I a)[q]? = some b → pred b = false)
    (hpredNonBridge : ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
      pred b0 = false) :
    ∀ m ≤ N,
      (((outerRest.take m).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)).filter pred).length
        = ksPrefix ks (m + 1) - ksPrefix ks 1 := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN' : m ≤ N := by omega
      have ihm := ih hmN'
      have hmN : m < N := by omega
      obtain ⟨b, vs, km, hjbv, hksm, hlen⟩ := houter m hmN
      rw [List.take_add_one, hjbv]
      simp only [Option.toList_some, List.flatMap_append, List.filter_append, List.length_append]
      rw [ihm]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [guessBXOuterBlockElems_filter I b vs pred p0 bval h0 htrue hfalse hpredNonBridge,
        List.length_map, hlen]
      have hgd : ks.getD (m + 1) 0 = km := by
        show (ks[m + 1]?).getD 0 = km
        rw [hksm]; rfl
      have hpre : ksPrefix ks (m + 1 + 1) = ksPrefix ks (m + 1) + (km + 1) := by
        show ksPrefix ks (m + 1) + (ks.getD (m + 1) 0 + 1) = ksPrefix ks (m + 1) + (km + 1)
        rw [hgd]
      have hge : ksPrefix ks 1 ≤ ksPrefix ks (m + 1) := ksPrefix_mono ks (by omega)
      omega

/-- The total length of the words of `outerRest`'s first `m` entries is
`nestedOuterStart ks N (m + 1) - nestedOuterStart ks N 1`. -/
theorem guessBXOuterRest_prefix_length (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (_ : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) :
    ∀ m ≤ N + 1,
      ((outerRest.take m).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)).length
        = nestedOuterStart ks N (m + 1) - nestedOuterStart ks N 1 := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN : m ≤ N + 1 := by omega
      have ihm := ih hmN
      have hmlt : m < outerRest.length := by omega
      have hget : outerRest[m]? = some (outerRest[m]'hmlt) := List.getElem?_eq_getElem hmlt
      rw [List.take_add_one, hget]
      simp only [Option.toList_some, List.flatMap_append, List.length_append]
      rw [ihm]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hge1 : nestedOuterStart ks N 1 ≤ nestedOuterStart ks N (m + 1) :=
        nestedOuterStart_mono ks N (by omega)
      rcases Nat.lt_or_ge m N with hmn | hmn
      · obtain ⟨b, vs, km, hjbv, hksm, hlen⟩ := houter m hmn
        rw [hjbv] at hget
        have hbveq : outerRest[m]'hmlt = (b, vs) := by
          have h := hget.symm; simpa using h
        rw [hbveq]
        have hblen : (guessBXOuterBlockElems I b vs).length = 3 * (km + 1) + 2 := by
          rw [guessBXOuterBlockElems_length, hlen]
        rw [hblen]
        have hstartsucc : nestedOuterStart ks N (m + 2)
            = nestedOuterStart ks N (m + 1) + nestedOuterLen ks N (m + 1) := rfl
        have hgd : ks.getD (m + 1) 0 = km := by
          show (ks[m + 1]?).getD 0 = km
          rw [hksm]; rfl
        have htestlen : nestedOuterLen ks N (m + 1) = 3 * (km + 1) + 2 := by
          have h1 : m + 1 ≠ N + 1 := by omega
          have h2 : m + 1 ≠ 0 := by omega
          unfold nestedOuterLen
          rw [if_neg h1, if_neg h2, hgd]
        rw [show m + 1 + 1 = m + 2 from rfl, hstartsucc, htestlen]
        omega
      · have hmeqN : m = N := by omega
        obtain ⟨b, vs, hjbv, hlen⟩ := houterLast
        have hjbv' : outerRest[m]? = some (b, vs) := by rw [hmeqN]; exact hjbv
        rw [hjbv'] at hget
        have hbveq : outerRest[m]'hmlt = (b, vs) := by
          have h := hget.symm; simpa using h
        rw [hbveq]
        have hblen : (guessBXOuterBlockElems I b vs).length = 5 := by
          rw [guessBXOuterBlockElems_length, hlen]
        rw [hblen]
        have hstartsucc : nestedOuterStart ks N (m + 2)
            = nestedOuterStart ks N (m + 1) + nestedOuterLen ks N (m + 1) := rfl
        have htestlen : nestedOuterLen ks N (m + 1) = 5 := by
          have h2 : m + 1 = N + 1 := by omega
          unfold nestedOuterLen
          rw [if_pos h2]
        rw [show m + 1 + 1 = m + 2 from rfl, hstartsucc, htestlen]
        omega

/-! ## The `zBxx'` count at an arbitrary position

As for `zAxx'` above. -/

/-- The number of `zBxx'`-reads within a possibly partial outer block. -/
theorem guessBXOuterBlockElems_zBxx'_take_count (I : PCPInstance) (b : Val I × Val I)
    (vs : List (Val I × Val I × Val I)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((guessBXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false)).length
      = n + (if 2 < p then 1 else 0) := by
  have hstep : ((guessBXOuterBlockElems I b vs).take (n * 3 + p + 1)).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) =
      ((vs.flatMap (guessBXInnerBlockElems I)).take (n * 3 + p)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) := by
    unfold guessBXOuterBlockElems
    rw [List.take_succ_cons, List.filter_cons_of_neg (fun h => Bool.noConfusion h),
      List.take_append, List.filter_append]
    have hnil : (([⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩] :
        List (ThreadLabel (domainOf I) Tid.guessBX)).take
          (n * 3 + p - (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
        (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro x hx
      have hxmem : x ∈ ([⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩] :
          List (ThreadLabel (domainOf I) Tid.guessBX)) := List.mem_of_mem_take hx
      simp only [List.mem_singleton] at hxmem
      subst hxmem
      exact fun h => Bool.noConfusion h
    rw [hnil, List.append_nil]
  rw [hstep]
  exact flatMap_uniform_take_count (guessBXInnerBlockElems I) 3 (fun _ => rfl)
    (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) 2 (by norm_num)
    (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun _ => rfl) (fun _ => rfl)
    (fun a q b hq hqb => by
      unfold guessBXInnerBlockElems at hqb
      rcases q with _ | _ | _ | q <;> simp_all only [ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos, List.getElem_cons_zero, Option.some.injEq, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
    vs n a hva p hp

/-- The number of `zBxx'`-reads before an arbitrary position of `outerRest`'s
flatMap. -/
theorem guessBXOuterRest_zBxx'_take_count (I : PCPInstance) (ks : List ℕ) (N : ℕ)
    (hks : ks.length = N + 1)
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (houter : ∀ j, j < N →
      ∃ b vs km, outerRest[j]? = some (b, vs) ∧ ks[j + 1]? = some km ∧ vs.length = km + 1)
    (hpredNonBridge :
      ∀ b0 : ThreadLabel (domainOf I) Tid.guessBX, b0.1.loc ∈ BridgeLoc →
        (match b0.1.loc, b0.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) = false)
    (M : ℕ) (hM : M ≤ N) (b : Val I × Val I) (vs : List (Val I × Val I × Val I))
    (hMbv : outerRest[M]? = some (b, vs)) (n p : ℕ) (a : Val I × Val I × Val I)
    (hva : vs[n]? = some a) (hp : p ≤ 3) :
    (((outerRest.flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).take
        (((outerRest.take M).flatMap (fun q => guessBXOuterBlockElems I q.1 q.2)).length +
          (n * 3 + p + 1))).filter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false)).length
      = (ksPrefix ks (M + 1) - ksPrefix ks 1) + (n + (if 2 < p then 1 else 0)) := by
  have hqbound : n * 3 + p + 1 ≤ (guessBXOuterBlockElems I b vs).length := by
    have hnlen : n < vs.length := (List.getElem?_eq_some_iff.mp hva).1
    rw [guessBXOuterBlockElems_length]
    omega
  rw [list_take_flatMap_offset (fun q => guessBXOuterBlockElems I q.1 q.2) outerRest M
    (n * 3 + p + 1) (b, vs) hMbv hqbound, List.filter_append, List.length_append,
    guessBXOuterRest_prefix_matchCount I ks N hks outerRest houter
      (fun l => match l.1.loc, l.1.op with | Loc.zBxx', OpType.rd => true | _, _ => false) 2
      (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX))
      (fun _ => rfl) (fun _ => rfl)
      (fun a q b hq hqb => by
        unfold guessBXInnerBlockElems at hqb
        rcases q with _ | _ | _ | q <;> simp_all only [add_lt_add_iff_right, getElem?_pos, Option.some.injEq, exists_and_left, ↓existsAndEq, true_and, Prod.exists, Subtype.forall, ne_eq, OfNat.zero_ne_ofNat, not_false_eq_true, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, List.getElem_cons_zero, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, List.getElem_cons_succ, not_true_eq_false, Nat.reduceEqDiff, not_lt, le_add_iff_nonneg_left, zero_le, getElem?_neg, reduceCtorEq] <;> (subst hqb; rfl))
      hpredNonBridge M hM,
    guessBXOuterBlockElems_zBxx'_take_count I b vs n p a hva hp]

/-- Position and index of the bridge events of `GuessAX`'s trace: each belongs
to an outer iteration `M ≤ N + 1` and is either its `zAxy` write, at
`nestedOuterStart K0 N M`, or its `ellAyx` read, one position before
`nestedOuterStart K0 N M + nestedOuterLen K0 N M`; its `rawIndex` is `M`
either way. Every other position of the word is inside an inner call and so
not a bridge event (`guessAXInnerBlockShape_no_bridge`). -/
theorem guessAXOuter_idPos_rawIndex (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.guessAX) (hb : e.IsBridge) :
    ∃ M, M ≤ N + 1 ∧ rawIndex trace e = M ∧
      ((e.loc = Loc.zAxy ∧ e.op = OpType.wt ∧ idPos e = nestedOuterStart ks N M) ∨
       (e.loc = Loc.ellAyx ∧ e.op = OpType.rd ∧
         idPos e + 1 = nestedOuterStart ks N M + nestedOuterLen ks N M)) := by
  obtain ⟨K0, hks0, hinner0⟩ := hinner0
  have hgd0 : ks.getD 0 0 = K0 := by
    show (ks[0]?).getD 0 = K0
    rw [hks0]; rfl
  obtain ⟨i, l, hget, hee⟩ := mem_traceEventsOf_iff'.mp he
  have hidPos : idPos e = i := by rw [hee]; unfold idPos traceEventId; simp [Nat.unpair_pair]
  have hloce : e.loc = l.1.loc := by rw [hee]; rfl
  have hope : e.op = l.1.op := by rw [hee]; rfl
  have hgetT : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]? = some l := by
    rw [← htrace]; exact hget
  have hFlatLen : ∀ vals : List (Val I × Val I × Val I),
      (vals.flatMap (guessAXInnerBlockElems I)).length = 3 * vals.length := by
    intro vals
    rw [List.length_flatMap]
    have heq : vals.map (fun a => (guessAXInnerBlockElems I a).length) = vals.map (fun _ => 3) :=
      List.map_congr_left (fun a _ => guessAXInnerBlockElems_length I a)
    rw [heq, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hBlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
    rw [hFlatLen, hinner0]
  have hHeadLen :
      (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX)
          , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessAXInnerBlockElems I) ++
          [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX) ])).length = 3 * K0 + 4 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hBlen]
    omega
  -- Any position inside a `guessAXInnerBlockElems`-flatMap is non-bridge.
  have hInnerNonBridge : ∀ (vals : List (Val I × Val I × Val I)) (q : ℕ)
      (l' : ThreadLabel (domainOf I) Tid.guessAX),
      (vals.flatMap (guessAXInnerBlockElems I))[q]? = some l' → l'.1.loc ∉ BridgeLoc := by
    intro vals q l' hq
    have hqlt : q < (vals.flatMap (guessAXInnerBlockElems I)).length :=
      (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨n0, p0, a0, hp0L, hva0, hoff0, heqget0⟩ :=
      flatMap_getElem_of_lengths (guessAXInnerBlockElems I) vals q hqlt
    rw [guessAXInnerBlockElems_length] at hp0L
    have hgetblk : (guessAXInnerBlockElems I a0)[p0]? = some l' := by rw [← heqget0]; exact hq
    have hshapep0 : guessAXInnerBlockShape[p0]? = some (l'.1.loc, l'.1.op) := by
      have h1 : guessAXInnerBlockShape[p0]? =
          ((guessAXInnerBlockElems I a0).map (fun ev => (ev.1.loc, ev.1.op)))[p0]? := by
        rw [guessAXInnerBlockElems_shape I a0]
        rfl
      rw [h1, List.getElem?_map, hgetblk]
      rfl
    have hmem : (l'.1.loc, l'.1.op) ∈ guessAXInnerBlockShape :=
      List.mem_iff_getElem?.mpr ⟨p0, hshapep0⟩
    exact guessAXInnerBlockShape_no_bridge _ hmem
  -- A middle position (neither the leading `zAxy` nor the trailing `ellAyx`) of one outer
  -- iteration's block is also non-bridge.
  have hOuterBlockMid : ∀ (b : Val I × Val I) (vs : List (Val I × Val I × Val I)) (q : ℕ)
      (l' : ThreadLabel (domainOf I) Tid.guessAX),
      1 ≤ q → q ≤ 3 * vs.length → (guessAXOuterBlockElems I b vs)[q]? = some l' →
      l'.1.loc ∉ BridgeLoc := by
    intro b vs q l' hq1 hq2 hqget
    unfold guessAXOuterBlockElems at hqget
    rw [show q = (q - 1) + 1 from by omega, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hFlatLen]; omega)] at hqget
    exact hInnerNonBridge vs (q - 1) l' hqget
  -- The trailing `ellAyx` of one outer iteration's block.
  have hOuterBlockLast : ∀ (b : Val I × Val I) (vs : List (Val I × Val I × Val I)),
      (guessAXOuterBlockElems I b vs)[3 * vs.length + 1]?
        = some (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX) := by
    intro b vs
    unfold guessAXOuterBlockElems
    rw [show 3 * vs.length + 1 = (3 * vs.length) + 1 from rfl, List.getElem?_cons_succ,
      List.getElem?_append_right (by rw [hFlatLen]), hFlatLen]
    simp
  -- The `hrawop` unfolding of `rawOpEvents` to a `zipIdx`/`filter`/`map` computation.
  have hrawop : ∀ (x : Loc) (op : OpType), rawOpEvents trace Tid.guessAX x op =
      (((trace Tid.guessAX).zipIdx).filter
          (fun p' => decide (p'.1.1.loc = x ∧ p'.1.1.op = op))).map
        (fun p' => (⟨traceEventId (D := domainOf I) Tid.guessAX p'.2, p'.1.1⟩ :
            Event (domainOf I))) := by
    intro x op
    unfold rawOpEvents traceEventsOf
    rw [List.filter_map]
    congr 1
  -- `inner0Rest`'s flatMap never matches a bridge-location predicate.
  have hBEmpty : ∀ (x : Loc) (op : OpType) (k : ℕ), x ∈ BridgeLoc →
      ((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx k).filter
        (fun p' => decide (p'.1.1.loc = x ∧ p'.1.1.op = op)) = [] := by
    intro x op k hxbridge
    rw [List.filter_eq_nil_iff]
    rintro ⟨l', j⟩ hmem
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hmem
    rw [List.getElem?_zipIdx] at hq
    rcases hcase : (inner0Rest.flatMap (guessAXInnerBlockElems I))[q]? with _ | l0
    · rw [hcase] at hq; simp at hq
    · rw [hcase] at hq
      simp only [Option.map_some, Option.some.injEq] at hq
      have hnb := hInnerNonBridge inner0Rest q l0 hcase
      have hql : l0 = l' := congrArg Prod.fst hq
      simp only [decide_eq_true_eq]
      rintro ⟨hloc, -⟩
      rw [← hql] at hloc
      exact hnb (hloc ▸ hxbridge)
  -- The head's filtered singleton, for each of the two bridge predicates.
  have hHeadFilterZAxy :
      (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX)
          , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessAXInnerBlockElems I) ++
          [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX) ]).zipIdx 0).filter
        (fun p' => decide (p'.1.1.loc = Loc.zAxy ∧ p'.1.1.op = OpType.wt))
        = [(⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩, 0)] := by
    rw [List.zipIdx_append, List.zipIdx_append, List.filter_append, List.filter_append]
    have hA :
        (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessAX)
            , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
            , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
          (fun p' => decide (p'.1.1.loc = Loc.zAxy ∧ p'.1.1.op = OpType.wt))
          = [(⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩, 0)] := by rfl
    have hC :
        (([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX) ]).zipIdx (3 + 3 * K0)).filter
          (fun p' => decide (p'.1.1.loc = Loc.zAxy ∧ p'.1.1.op = OpType.wt)) = [] := by rfl
    simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.zero_add,
      hA, hBEmpty Loc.zAxy OpType.wt _ (by decide : Loc.zAxy ∈ BridgeLoc), hC, List.nil_append, List.append_nil]
  have hHeadFilterEllA :
      (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX)
          , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessAXInnerBlockElems I) ++
          [ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX) ]).zipIdx 0).filter
        (fun p' => decide (p'.1.1.loc = Loc.ellAyx ∧ p'.1.1.op = OpType.rd))
        = [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩, 3 + 3 * K0)] := by
    rw [List.zipIdx_append, List.zipIdx_append, List.filter_append, List.filter_append]
    have hA :
        (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessAX)
            , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
            , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
          (fun p' => decide (p'.1.1.loc = Loc.ellAyx ∧ p'.1.1.op = OpType.rd)) = [] := by rfl
    have hC :
        (([ (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessAX) ]).zipIdx (3 + 3 * K0)).filter
          (fun p' => decide (p'.1.1.loc = Loc.ellAyx ∧ p'.1.1.op = OpType.rd))
          = [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩, 3 + 3 * K0)] := by rfl
    simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.zero_add,
      hA, hBEmpty Loc.ellAyx OpType.rd _ (by decide : Loc.ellAyx ∈ BridgeLoc), hC, List.nil_append, List.append_nil]
  -- `flatMap_filter_getElem_of_lengths`'s hypotheses for the `zAxy` predicate over `outerRest`.
  have hp0Z : ∀ p : (Val I × Val I) × List (Val I × Val I × Val I),
      (guessAXOuterBlockElems I p.1 p.2)[(0 : ℕ)]?
        = some (⟨EventLabel.wt Tid.guessAX Loc.zAxy p.1.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX) := by
    rintro ⟨⟨b', b2⟩, vs'⟩; rfl
  have hfalseZ : ∀ (p : (Val I × Val I) × List (Val I × Val I × Val I)) (q : ℕ)
      (b0 : ThreadLabel (domainOf I) Tid.guessAX), q ≠ 0 →
      (guessAXOuterBlockElems I p.1 p.2)[q]? = some b0 →
      @decide (b0.1.loc = Loc.zAxy ∧ b0.1.op = OpType.wt)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b0.1.loc Loc.zAxy) inferInstance) = false := by
    rintro ⟨a1, a2⟩ q b0 hq0 hqget
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    by_cases hqle : q ≤ 3 * a2.length
    · have hmem : b0.1.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.zAxy ∈ BridgeLoc)
      exact (hOuterBlockMid a1 a2 q b0 (by omega) hqle hqget) hmem
    · have hqeq : q = 3 * a2.length + 1 := by
        have hqlt2 : q < (guessAXOuterBlockElems I a1 a2).length :=
          (List.getElem?_eq_some_iff.mp hqget).1
        rw [guessAXOuterBlockElems_length] at hqlt2
        omega
      rw [hqeq, hOuterBlockLast a1 a2] at hqget
      simp only [Option.some.injEq] at hqget
      rw [← hqget] at hloc
      change Loc.ellAyx = Loc.zAxy at hloc
      exact absurd hloc (by decide : Loc.ellAyx ≠ Loc.zAxy)
  -- Likewise for the `ellAyx` predicate.
  have hp0E : ∀ p : (Val I × Val I) × List (Val I × Val I × Val I),
      (guessAXOuterBlockElems I p.1 p.2)[3 * p.2.length + 1]?
        = some (⟨EventLabel.rd Tid.guessAX Loc.ellAyx p.1.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX) :=
    fun p => hOuterBlockLast p.1 p.2
  have hfalseE : ∀ (p : (Val I × Val I) × List (Val I × Val I × Val I)) (q : ℕ)
      (b0 : ThreadLabel (domainOf I) Tid.guessAX), q ≠ 3 * p.2.length + 1 →
      (guessAXOuterBlockElems I p.1 p.2)[q]? = some b0 →
      @decide (b0.1.loc = Loc.ellAyx ∧ b0.1.op = OpType.rd)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b0.1.loc Loc.ellAyx) inferInstance) = false := by
    rintro ⟨a1, a2⟩ q b0 hq0 hqget
    have hq0' : q ≠ 3 * a2.length + 1 := hq0
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    rcases Nat.eq_zero_or_pos q with hqz | hqpos
    · subst hqz
      have := hp0Z (a1, a2)
      rw [hqget] at this
      simp only [Option.some.injEq] at this
      rw [this] at hloc
      change Loc.zAxy = Loc.ellAyx at hloc
      exact absurd hloc (by decide : Loc.zAxy ≠ Loc.ellAyx)
    · have hqlt2 : q < (guessAXOuterBlockElems I a1 a2).length :=
        (List.getElem?_eq_some_iff.mp hqget).1
      rw [guessAXOuterBlockElems_length] at hqlt2
      have hmem : b0.1.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.ellAyx ∈ BridgeLoc)
      exact (hOuterBlockMid a1 a2 q b0 hqpos (by omega)) hqget hmem
  rcases Nat.lt_or_ge i (3 * K0 + 4) with hi | hi
  · -- HEAD case: iteration `0`.
    have hget1 : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]?
        = (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessAX)
            , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
            , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
            inner0Rest.flatMap (guessAXInnerBlockElems I) ++
            [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]))[i]? := by
      unfold guessAXBlockWord
      rw [List.getElem?_append_left
        (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)]
    rw [hget1] at hgetT
    rcases Nat.lt_or_ge i (3 + 3 * K0) with hi2 | hi2
    · rw [List.getElem?_append_left
          (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)] at hgetT
      rcases Nat.lt_or_ge i 3 with hi3 | hi3
      · rw [List.getElem?_append_left (by simpa using hi3)] at hgetT
        have hi012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi012 with rfl | rfl | rfl
        · -- position 0: `zAxy`
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have heloc : e.loc = Loc.zAxy := by rw [hloce, ← hgetT]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetT]; rfl
          refine ⟨0, by omega, ?_, Or.inl ⟨heloc, heop, ?_⟩⟩
          · have hnth : rawNthEvent trace Tid.guessAX Loc.zAxy OpType.wt 0 = some e := by
              unfold rawNthEvent
              rw [hrawop, htrace]
              unfold guessAXBlockWord
              rw [List.zipIdx_append, List.filter_append, hHeadFilterZAxy]
              simp only [List.getElem?_map, List.getElem?_append_left, List.length_cons,
                List.length_nil, Nat.zero_lt_succ, List.getElem?_cons_zero, Option.map_some]
              rw [hee, ← hgetT]
            exact rawNthEvent_rawIndex hnth
          · rw [hidPos]; simp [nestedOuterStart]
        · -- position 1: `xA`, non-bridge — contradicts `hb`.
          exfalso
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have hloc : e.loc = Loc.xA := by rw [hloce, ← hgetT]; rfl
          change e.loc ∈ BridgeLoc at hb
          rw [hloc] at hb
          exact absurd hb (by decide : Loc.xA ∉ BridgeLoc)
        · -- position 2: `zAx'x`, non-bridge — contradicts `hb`.
          exfalso
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have hloc : e.loc = Loc.zAx'x := by rw [hloce, ← hgetT]; rfl
          change e.loc ∈ BridgeLoc at hb
          rw [hloc] at hb
          exact absurd hb (by decide : Loc.zAx'x ∉ BridgeLoc)
      · -- `3 ≤ i < 3 + 3 * K0`: within `inner0Rest`'s flatMap — non-bridge, contradicts `hb`.
        exfalso
        rw [List.getElem?_append_right (by simpa using hi3)] at hgetT
        have hmem : l.1.loc ∈ BridgeLoc := by rw [← hloce]; exact hb
        exact hInnerNonBridge inner0Rest (i - 3) l hgetT hmem
    · -- `i = 3 + 3 * K0`: `ellAyx`.
      have hieq : i = 3 + 3 * K0 := by omega
      rw [List.getElem?_append_right
          (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)] at hgetT
      simp only [List.length_append, List.length_cons, List.length_nil, hBlen] at hgetT
      have hzero : i - (3 + 3 * K0) = 0 := by omega
      rw [hzero] at hgetT
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetT
      have heloc : e.loc = Loc.ellAyx := by rw [hloce, ← hgetT]; rfl
      have heop : e.op = OpType.rd := by rw [hope, ← hgetT]; rfl
      refine ⟨0, by omega, ?_, Or.inr ⟨heloc, heop, ?_⟩⟩
      · have hnth : rawNthEvent trace Tid.guessAX Loc.ellAyx OpType.rd 0 = some e := by
          unfold rawNthEvent
          rw [hrawop, htrace]
          unfold guessAXBlockWord
          rw [List.zipIdx_append, List.filter_append, hHeadFilterEllA]
          simp only [List.getElem?_map, List.getElem?_append_left, List.length_cons,
            List.length_nil, Nat.zero_lt_succ, List.getElem?_cons_zero, Option.map_some]
          rw [hee, hieq, ← hgetT]
        exact rawNthEvent_rawIndex hnth
      · rw [show nestedOuterStart ks N 0 = 0 from rfl]
        have htestlen0 : nestedOuterLen ks N 0 = 3 * K0 + 4 := by
          unfold nestedOuterLen
          rw [if_neg (show (0 : ℕ) ≠ N + 1 by omega), if_pos rfl, hgd0]
        rw [htestlen0, hidPos, hieq]
        omega
  · -- TAIL case: some `outerRest[n]`, `M := n + 1`.
    have hget2 : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]?
        = (outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2))[i - (3 * K0 + 4)]? := by
      unfold guessAXBlockWord
      rw [List.getElem?_append_right]
      · congr 1
        simp [List.length_append, List.length_cons, hBlen]
      · simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega
    rw [hget2] at hgetT
    have hqlt : i - (3 * K0 + 4) <
        (outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)).length :=
      (List.getElem?_eq_some_iff.mp hgetT).1
    obtain ⟨n, p2, ⟨b, vs⟩, hp2L, hvan, hoffn, heqgetn⟩ :=
      flatMap_getElem_of_lengths (fun p => guessAXOuterBlockElems I p.1 p.2) outerRest
        (i - (3 * K0 + 4)) hqlt
    rw [guessAXOuterBlockElems_length] at hp2L
    have hgetblkn : (guessAXOuterBlockElems I b vs)[p2]? = some l := by
      rw [← heqgetn]; exact hgetT
    have hoffidPos : idPos e = (3 * K0 + 4) + (((outerRest.take n).flatMap
        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + p2) := by
      rw [hidPos]; omega
    have hnlt : n < outerRest.length := (List.getElem?_eq_some_iff.mp hvan).1
    have hstartrel : nestedOuterStart ks N (n + 1)
        = (3 * K0 + 4) + ((outerRest.take n).flatMap
            (fun p => guessAXOuterBlockElems I p.1 p.2)).length := by
      have hp := guessAXOuterRest_prefix_length I ks N hks outerRest houterLen houter houterLast n
        (by omega)
      have hge1 : nestedOuterStart ks N 1 ≤ nestedOuterStart ks N (n + 1) :=
        nestedOuterStart_mono ks N (by omega)
      have hns1 : nestedOuterStart ks N 1 = 3 * K0 + 4 := by
        show nestedOuterStart ks N 0 + nestedOuterLen ks N 0 = 3 * K0 + 4
        rw [show nestedOuterStart ks N 0 = 0 from rfl]
        unfold nestedOuterLen
        rw [if_neg (show (0 : ℕ) ≠ N + 1 by omega), if_pos rfl, hgd0]
        omega
      omega
    rcases Nat.eq_zero_or_pos p2 with hp2z | hp2pos
    · -- position `0` of the block: `zAxy` — iteration `n + 1`'s start.
      subst hp2z
      have hgetblkn' := hgetblkn
      rw [hp0Z (b, vs)] at hgetblkn'
      simp only [Option.some.injEq] at hgetblkn'
      have heloc : e.loc = Loc.zAxy := by rw [hloce, ← hgetblkn']; rfl
      have heop : e.op = OpType.wt := by rw [hope, ← hgetblkn']; rfl
      refine ⟨n + 1, by omega, ?_, Or.inl ⟨heloc, heop, ?_⟩⟩
      · have hnth : rawNthEvent trace Tid.guessAX Loc.zAxy OpType.wt (n + 1) = some e := by
          unfold rawNthEvent
          rw [hrawop, htrace]
          unfold guessAXBlockWord
          rw [List.zipIdx_append, List.filter_append, hHeadFilterZAxy]
          have hmain := flatMap_filter_getElem_of_lengths
            (fun p => guessAXOuterBlockElems I p.1 p.2)
            (fun (_ : (Val I × Val I) × List (Val I × Val I × Val I)) => (0 : ℕ))
            (fun p' => @decide (p'.1.loc = Loc.zAxy ∧ p'.1.op = OpType.wt)
              (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.zAxy) inferInstance))
            (fun p => (⟨EventLabel.wt Tid.guessAX Loc.zAxy p.1.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessAX))
            hp0Z (fun _ => rfl) hfalseZ
            outerRest (3 * K0 + 4) n (b, vs) hvan
          rw [Nat.zero_add, hHeadLen]
          rw [List.getElem?_map]
          simp only [List.getElem?_append_right, List.length_cons, List.length_nil,
            Nat.le_add_left, Nat.add_sub_cancel_left]
          rw [show n + 1 - 1 = n from by omega]
          have hmapped := congrArg (Option.map (fun p' =>
            (⟨traceEventId (D := domainOf I) Tid.guessAX p'.2, p'.1.1⟩ : Event (domainOf I)))) hmain
          rw [Option.map_some] at hmapped
          refine hmapped.trans ?_
          have hival : (3 * K0 + 4 + ((List.take n outerRest).flatMap
              (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 0) = i := by omega
          have hlab : EventLabel.wt Tid.guessAX Loc.zAxy b.1 = (l.1 : EventLabel (domainOf I)) :=
            congrArg Subtype.val hgetblkn'
          simp only [hival, hlab]
          exact congrArg some hee.symm
        exact rawNthEvent_rawIndex hnth
      · rw [hstartrel]; omega
    · -- `1 ≤ p2 < 3 * vs.length + 2`: either middle (non-bridge) or the block's last (`ellAyx`).
      by_cases hp2le : p2 ≤ 3 * vs.length
      · exfalso
        have hmem : l.1.loc ∈ BridgeLoc := by rw [← hloce]; exact hb
        exact hOuterBlockMid b vs p2 l hp2pos hp2le hgetblkn hmem
      · have hp2L' : p2 < 3 * vs.length + 2 := hp2L
        have hp2eq : p2 = 3 * vs.length + 1 := by omega
        have hgetblkn' := hgetblkn
        rw [hp2eq, hp0E (b, vs)] at hgetblkn'
        simp only [Option.some.injEq] at hgetblkn'
        have heloc : e.loc = Loc.ellAyx := by rw [hloce, ← hgetblkn']; rfl
        have heop : e.op = OpType.rd := by rw [hope, ← hgetblkn']; rfl
        refine ⟨n + 1, by omega, ?_, Or.inr ⟨heloc, heop, ?_⟩⟩
        · have hnth : rawNthEvent trace Tid.guessAX Loc.ellAyx OpType.rd (n + 1) = some e := by
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessAXBlockWord
            rw [List.zipIdx_append, List.filter_append, hHeadFilterEllA]
            have hmain := flatMap_filter_getElem_of_lengths
              (fun p => guessAXOuterBlockElems I p.1 p.2)
              (fun p : (Val I × Val I) × List (Val I × Val I × Val I) => 3 * p.2.length + 1)
              (fun p' => @decide (p'.1.loc = Loc.ellAyx ∧ p'.1.op = OpType.rd)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.ellAyx) inferInstance))
              (fun p => (⟨EventLabel.rd Tid.guessAX Loc.ellAyx p.1.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX))
              hp0E (fun _ => rfl) hfalseE
              outerRest (3 * K0 + 4) n (b, vs) hvan
            rw [Nat.zero_add, hHeadLen]
            rw [List.getElem?_map]
            simp only [List.getElem?_append_right, List.length_cons, List.length_nil,
              Nat.le_add_left, Nat.add_sub_cancel_left]
            rw [show n + 1 - 1 = n from by omega]
            have hmapped := congrArg (Option.map (fun p' =>
              (⟨traceEventId (D := domainOf I) Tid.guessAX p'.2, p'.1.1⟩ : Event (domainOf I)))) hmain
            rw [Option.map_some] at hmapped
            refine hmapped.trans ?_
            have hival : (3 * K0 + 4 + ((List.take n outerRest).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).length + (3 * vs.length + 1)) = i := by
              omega
            have hlab : EventLabel.rd Tid.guessAX Loc.ellAyx b.2 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblkn'
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · rw [hstartrel]
          rcases Nat.lt_or_ge n N with hnN | hnN
          · obtain ⟨b', vs', km, hb'vs', hksm, hlen'⟩ := houter n hnN
            rw [hvan] at hb'vs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'vs'
            have hvslen : vs.length = km + 1 := by rw [hb'vs'.2]; exact hlen'
            have hgdn : ks.getD (n + 1) 0 = km := by
              show (ks[n + 1]?).getD 0 = km
              rw [hksm]; rfl
            have hlenne : n + 1 ≠ N + 1 := by omega
            have hne0 : n + 1 ≠ 0 := by omega
            unfold nestedOuterLen
            rw [if_neg hlenne, if_neg hne0, hgdn]
            omega
          · have hnN' : n = N := by omega
            obtain ⟨b', vs', hb'vs', hlen'⟩ := houterLast
            rw [hnN'] at hvan
            rw [hvan] at hb'vs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'vs'
            have hvslen : vs.length = 1 := by rw [hb'vs'.2]; exact hlen'
            have hlenne : n + 1 = N + 1 := by omega
            unfold nestedOuterLen
            rw [if_pos hlenne]
            omega


/-- Position and index of the bridge events of `GuessBX`'s trace, as
`guessAXOuter_idPos_rawIndex`. -/
theorem guessBXOuter_idPos_rawIndex (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.guessBX) (hb : e.IsBridge) :
    ∃ M, M ≤ N + 1 ∧ rawIndex trace e = M ∧
      ((e.loc = Loc.zBxy ∧ e.op = OpType.wt ∧ idPos e = nestedOuterStart ks N M) ∨
       (e.loc = Loc.ellByx ∧ e.op = OpType.rd ∧
         idPos e + 1 = nestedOuterStart ks N M + nestedOuterLen ks N M)) := by
  obtain ⟨K0, hks0, hinner0⟩ := hinner0
  have hgd0 : ks.getD 0 0 = K0 := by
    show (ks[0]?).getD 0 = K0
    rw [hks0]; rfl
  obtain ⟨i, l, hget, hee⟩ := mem_traceEventsOf_iff'.mp he
  have hidPos : idPos e = i := by rw [hee]; unfold idPos traceEventId; simp [Nat.unpair_pair]
  have hloce : e.loc = l.1.loc := by rw [hee]; rfl
  have hope : e.op = l.1.op := by rw [hee]; rfl
  have hgetT : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]? = some l := by
    rw [← htrace]; exact hget
  have hFlatLen : ∀ vals : List (Val I × Val I × Val I),
      (vals.flatMap (guessBXInnerBlockElems I)).length = 3 * vals.length := by
    intro vals
    rw [List.length_flatMap]
    have heq : vals.map (fun a => (guessBXInnerBlockElems I a).length) = vals.map (fun _ => 3) :=
      List.map_congr_left (fun a _ => guessBXInnerBlockElems_length I a)
    rw [heq, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hBlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
    rw [hFlatLen, hinner0]
  have hHeadLen :
      (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX)
          , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessBXInnerBlockElems I) ++
          [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX) ])).length = 3 * K0 + 4 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hBlen]
    omega
  -- Any position inside a `guessBXInnerBlockElems`-flatMap is non-bridge.
  have hInnerNonBridge : ∀ (vals : List (Val I × Val I × Val I)) (q : ℕ)
      (l' : ThreadLabel (domainOf I) Tid.guessBX),
      (vals.flatMap (guessBXInnerBlockElems I))[q]? = some l' → l'.1.loc ∉ BridgeLoc := by
    intro vals q l' hq
    have hqlt : q < (vals.flatMap (guessBXInnerBlockElems I)).length :=
      (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨n0, p0, a0, hp0L, hva0, hoff0, heqget0⟩ :=
      flatMap_getElem_of_lengths (guessBXInnerBlockElems I) vals q hqlt
    rw [guessBXInnerBlockElems_length] at hp0L
    have hgetblk : (guessBXInnerBlockElems I a0)[p0]? = some l' := by rw [← heqget0]; exact hq
    have hshapep0 : guessBXInnerBlockShape[p0]? = some (l'.1.loc, l'.1.op) := by
      have h1 : guessBXInnerBlockShape[p0]? =
          ((guessBXInnerBlockElems I a0).map (fun ev => (ev.1.loc, ev.1.op)))[p0]? := by
        rw [guessBXInnerBlockElems_shape I a0]
        rfl
      rw [h1, List.getElem?_map, hgetblk]
      rfl
    have hmem : (l'.1.loc, l'.1.op) ∈ guessBXInnerBlockShape :=
      List.mem_iff_getElem?.mpr ⟨p0, hshapep0⟩
    exact guessBXInnerBlockShape_no_bridge _ hmem
  -- A middle position (neither the leading `zBxy` nor the trailing `ellByx`) of one outer
  -- iteration's block is also non-bridge.
  have hOuterBlockMid : ∀ (b : Val I × Val I) (vs : List (Val I × Val I × Val I)) (q : ℕ)
      (l' : ThreadLabel (domainOf I) Tid.guessBX),
      1 ≤ q → q ≤ 3 * vs.length → (guessBXOuterBlockElems I b vs)[q]? = some l' →
      l'.1.loc ∉ BridgeLoc := by
    intro b vs q l' hq1 hq2 hqget
    unfold guessBXOuterBlockElems at hqget
    rw [show q = (q - 1) + 1 from by omega, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hFlatLen]; omega)] at hqget
    exact hInnerNonBridge vs (q - 1) l' hqget
  -- The trailing `ellByx` of one outer iteration's block.
  have hOuterBlockLast : ∀ (b : Val I × Val I) (vs : List (Val I × Val I × Val I)),
      (guessBXOuterBlockElems I b vs)[3 * vs.length + 1]?
        = some (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX) := by
    intro b vs
    unfold guessBXOuterBlockElems
    rw [show 3 * vs.length + 1 = (3 * vs.length) + 1 from rfl, List.getElem?_cons_succ,
      List.getElem?_append_right (by rw [hFlatLen]), hFlatLen]
    simp
  -- The `hrawop` unfolding of `rawOpEvents` to a `zipIdx`/`filter`/`map` computation.
  have hrawop : ∀ (x : Loc) (op : OpType), rawOpEvents trace Tid.guessBX x op =
      (((trace Tid.guessBX).zipIdx).filter
          (fun p' => decide (p'.1.1.loc = x ∧ p'.1.1.op = op))).map
        (fun p' => (⟨traceEventId (D := domainOf I) Tid.guessBX p'.2, p'.1.1⟩ :
            Event (domainOf I))) := by
    intro x op
    unfold rawOpEvents traceEventsOf
    rw [List.filter_map]
    congr 1
  -- `inner0Rest`'s flatMap never matches a bridge-location predicate.
  have hBEmpty : ∀ (x : Loc) (op : OpType) (k : ℕ), x ∈ BridgeLoc →
      ((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx k).filter
        (fun p' => decide (p'.1.1.loc = x ∧ p'.1.1.op = op)) = [] := by
    intro x op k hxbridge
    rw [List.filter_eq_nil_iff]
    rintro ⟨l', j⟩ hmem
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hmem
    rw [List.getElem?_zipIdx] at hq
    rcases hcase : (inner0Rest.flatMap (guessBXInnerBlockElems I))[q]? with _ | l0
    · rw [hcase] at hq; simp at hq
    · rw [hcase] at hq
      simp only [Option.map_some, Option.some.injEq] at hq
      have hnb := hInnerNonBridge inner0Rest q l0 hcase
      have hql : l0 = l' := congrArg Prod.fst hq
      simp only [decide_eq_true_eq]
      rintro ⟨hloc, -⟩
      rw [← hql] at hloc
      exact hnb (hloc ▸ hxbridge)
  -- The head's filtered singleton, for each of the two bridge predicates.
  have hHeadFilterZAxy :
      (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX)
          , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessBXInnerBlockElems I) ++
          [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX) ]).zipIdx 0).filter
        (fun p' => decide (p'.1.1.loc = Loc.zBxy ∧ p'.1.1.op = OpType.wt))
        = [(⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩, 0)] := by
    rw [List.zipIdx_append, List.zipIdx_append, List.filter_append, List.filter_append]
    have hA :
        (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessBX)
            , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
            , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
          (fun p' => decide (p'.1.1.loc = Loc.zBxy ∧ p'.1.1.op = OpType.wt))
          = [(⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩, 0)] := by rfl
    have hC :
        (([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX) ]).zipIdx (3 + 3 * K0)).filter
          (fun p' => decide (p'.1.1.loc = Loc.zBxy ∧ p'.1.1.op = OpType.wt)) = [] := by rfl
    simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.zero_add,
      hA, hBEmpty Loc.zBxy OpType.wt _ (by decide : Loc.zBxy ∈ BridgeLoc), hC, List.nil_append, List.append_nil]
  have hHeadFilterEllA :
      (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX)
          , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
          , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
          inner0Rest.flatMap (guessBXInnerBlockElems I) ++
          [ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX) ]).zipIdx 0).filter
        (fun p' => decide (p'.1.1.loc = Loc.ellByx ∧ p'.1.1.op = OpType.rd))
        = [(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩, 3 + 3 * K0)] := by
    rw [List.zipIdx_append, List.zipIdx_append, List.filter_append, List.filter_append]
    have hA :
        (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessBX)
            , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
            , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
          (fun p' => decide (p'.1.1.loc = Loc.ellByx ∧ p'.1.1.op = OpType.rd)) = [] := by rfl
    have hC :
        (([ (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
              ThreadLabel (domainOf I) Tid.guessBX) ]).zipIdx (3 + 3 * K0)).filter
          (fun p' => decide (p'.1.1.loc = Loc.ellByx ∧ p'.1.1.op = OpType.rd))
          = [(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩, 3 + 3 * K0)] := by rfl
    simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.zero_add,
      hA, hBEmpty Loc.ellByx OpType.rd _ (by decide : Loc.ellByx ∈ BridgeLoc), hC, List.nil_append, List.append_nil]
  -- `flatMap_filter_getElem_of_lengths`'s hypotheses for the `zBxy` predicate over `outerRest`.
  have hp0Z : ∀ p : (Val I × Val I) × List (Val I × Val I × Val I),
      (guessBXOuterBlockElems I p.1 p.2)[(0 : ℕ)]?
        = some (⟨EventLabel.wt Tid.guessBX Loc.zBxy p.1.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX) := by
    rintro ⟨⟨b', b2⟩, vs'⟩; rfl
  have hfalseZ : ∀ (p : (Val I × Val I) × List (Val I × Val I × Val I)) (q : ℕ)
      (b0 : ThreadLabel (domainOf I) Tid.guessBX), q ≠ 0 →
      (guessBXOuterBlockElems I p.1 p.2)[q]? = some b0 →
      @decide (b0.1.loc = Loc.zBxy ∧ b0.1.op = OpType.wt)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b0.1.loc Loc.zBxy) inferInstance) = false := by
    rintro ⟨a1, a2⟩ q b0 hq0 hqget
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    by_cases hqle : q ≤ 3 * a2.length
    · have hmem : b0.1.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.zBxy ∈ BridgeLoc)
      exact (hOuterBlockMid a1 a2 q b0 (by omega) hqle hqget) hmem
    · have hqeq : q = 3 * a2.length + 1 := by
        have hqlt2 : q < (guessBXOuterBlockElems I a1 a2).length :=
          (List.getElem?_eq_some_iff.mp hqget).1
        rw [guessBXOuterBlockElems_length] at hqlt2
        omega
      rw [hqeq, hOuterBlockLast a1 a2] at hqget
      simp only [Option.some.injEq] at hqget
      rw [← hqget] at hloc
      change Loc.ellByx = Loc.zBxy at hloc
      exact absurd hloc (by decide : Loc.ellByx ≠ Loc.zBxy)
  -- Likewise for the `ellByx` predicate.
  have hp0E : ∀ p : (Val I × Val I) × List (Val I × Val I × Val I),
      (guessBXOuterBlockElems I p.1 p.2)[3 * p.2.length + 1]?
        = some (⟨EventLabel.rd Tid.guessBX Loc.ellByx p.1.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX) :=
    fun p => hOuterBlockLast p.1 p.2
  have hfalseE : ∀ (p : (Val I × Val I) × List (Val I × Val I × Val I)) (q : ℕ)
      (b0 : ThreadLabel (domainOf I) Tid.guessBX), q ≠ 3 * p.2.length + 1 →
      (guessBXOuterBlockElems I p.1 p.2)[q]? = some b0 →
      @decide (b0.1.loc = Loc.ellByx ∧ b0.1.op = OpType.rd)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b0.1.loc Loc.ellByx) inferInstance) = false := by
    rintro ⟨a1, a2⟩ q b0 hq0 hqget
    have hq0' : q ≠ 3 * a2.length + 1 := hq0
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    rcases Nat.eq_zero_or_pos q with hqz | hqpos
    · subst hqz
      have := hp0Z (a1, a2)
      rw [hqget] at this
      simp only [Option.some.injEq] at this
      rw [this] at hloc
      change Loc.zBxy = Loc.ellByx at hloc
      exact absurd hloc (by decide : Loc.zBxy ≠ Loc.ellByx)
    · have hqlt2 : q < (guessBXOuterBlockElems I a1 a2).length :=
        (List.getElem?_eq_some_iff.mp hqget).1
      rw [guessBXOuterBlockElems_length] at hqlt2
      have hmem : b0.1.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.ellByx ∈ BridgeLoc)
      exact (hOuterBlockMid a1 a2 q b0 hqpos (by omega)) hqget hmem
  rcases Nat.lt_or_ge i (3 * K0 + 4) with hi | hi
  · -- HEAD case: iteration `0`.
    have hget1 : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]?
        = (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessBX)
            , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
            , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
            inner0Rest.flatMap (guessBXInnerBlockElems I) ++
            [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]))[i]? := by
      unfold guessBXBlockWord
      rw [List.getElem?_append_left
        (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)]
    rw [hget1] at hgetT
    rcases Nat.lt_or_ge i (3 + 3 * K0) with hi2 | hi2
    · rw [List.getElem?_append_left
          (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)] at hgetT
      rcases Nat.lt_or_ge i 3 with hi3 | hi3
      · rw [List.getElem?_append_left (by simpa using hi3)] at hgetT
        have hi012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi012 with rfl | rfl | rfl
        · -- position 0: `zBxy`
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have heloc : e.loc = Loc.zBxy := by rw [hloce, ← hgetT]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetT]; rfl
          refine ⟨0, by omega, ?_, Or.inl ⟨heloc, heop, ?_⟩⟩
          · have hnth : rawNthEvent trace Tid.guessBX Loc.zBxy OpType.wt 0 = some e := by
              unfold rawNthEvent
              rw [hrawop, htrace]
              unfold guessBXBlockWord
              rw [List.zipIdx_append, List.filter_append, hHeadFilterZAxy]
              simp only [List.getElem?_map, List.getElem?_append_left, List.length_cons,
                List.length_nil, Nat.zero_lt_succ, List.getElem?_cons_zero, Option.map_some]
              rw [hee, ← hgetT]
            exact rawNthEvent_rawIndex hnth
          · rw [hidPos]; simp [nestedOuterStart]
        · -- position 1: `xB`, non-bridge — contradicts `hb`.
          exfalso
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have hloc : e.loc = Loc.xB := by rw [hloce, ← hgetT]; rfl
          change e.loc ∈ BridgeLoc at hb
          rw [hloc] at hb
          exact absurd hb (by decide : Loc.xB ∉ BridgeLoc)
        · -- position 2: `zBx'x`, non-bridge — contradicts `hb`.
          exfalso
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have hloc : e.loc = Loc.zBx'x := by rw [hloce, ← hgetT]; rfl
          change e.loc ∈ BridgeLoc at hb
          rw [hloc] at hb
          exact absurd hb (by decide : Loc.zBx'x ∉ BridgeLoc)
      · -- `3 ≤ i < 3 + 3 * K0`: within `inner0Rest`'s flatMap — non-bridge, contradicts `hb`.
        exfalso
        rw [List.getElem?_append_right (by simpa using hi3)] at hgetT
        have hmem : l.1.loc ∈ BridgeLoc := by rw [← hloce]; exact hb
        exact hInnerNonBridge inner0Rest (i - 3) l hgetT hmem
    · -- `i = 3 + 3 * K0`: `ellByx`.
      have hieq : i = 3 + 3 * K0 := by omega
      rw [List.getElem?_append_right
          (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)] at hgetT
      simp only [List.length_append, List.length_cons, List.length_nil, hBlen] at hgetT
      have hzero : i - (3 + 3 * K0) = 0 := by omega
      rw [hzero] at hgetT
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetT
      have heloc : e.loc = Loc.ellByx := by rw [hloce, ← hgetT]; rfl
      have heop : e.op = OpType.rd := by rw [hope, ← hgetT]; rfl
      refine ⟨0, by omega, ?_, Or.inr ⟨heloc, heop, ?_⟩⟩
      · have hnth : rawNthEvent trace Tid.guessBX Loc.ellByx OpType.rd 0 = some e := by
          unfold rawNthEvent
          rw [hrawop, htrace]
          unfold guessBXBlockWord
          rw [List.zipIdx_append, List.filter_append, hHeadFilterEllA]
          simp only [List.getElem?_map, List.getElem?_append_left, List.length_cons,
            List.length_nil, Nat.zero_lt_succ, List.getElem?_cons_zero, Option.map_some]
          rw [hee, hieq, ← hgetT]
        exact rawNthEvent_rawIndex hnth
      · rw [show nestedOuterStart ks N 0 = 0 from rfl]
        have htestlen0 : nestedOuterLen ks N 0 = 3 * K0 + 4 := by
          unfold nestedOuterLen
          rw [if_neg (show (0 : ℕ) ≠ N + 1 by omega), if_pos rfl, hgd0]
        rw [htestlen0, hidPos, hieq]
        omega
  · -- TAIL case: some `outerRest[n]`, `M := n + 1`.
    have hget2 : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]?
        = (outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2))[i - (3 * K0 + 4)]? := by
      unfold guessBXBlockWord
      rw [List.getElem?_append_right]
      · congr 1
        simp [List.length_append, List.length_cons, hBlen]
      · simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega
    rw [hget2] at hgetT
    have hqlt : i - (3 * K0 + 4) <
        (outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)).length :=
      (List.getElem?_eq_some_iff.mp hgetT).1
    obtain ⟨n, p2, ⟨b, vs⟩, hp2L, hvan, hoffn, heqgetn⟩ :=
      flatMap_getElem_of_lengths (fun p => guessBXOuterBlockElems I p.1 p.2) outerRest
        (i - (3 * K0 + 4)) hqlt
    rw [guessBXOuterBlockElems_length] at hp2L
    have hgetblkn : (guessBXOuterBlockElems I b vs)[p2]? = some l := by
      rw [← heqgetn]; exact hgetT
    have hoffidPos : idPos e = (3 * K0 + 4) + (((outerRest.take n).flatMap
        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + p2) := by
      rw [hidPos]; omega
    have hnlt : n < outerRest.length := (List.getElem?_eq_some_iff.mp hvan).1
    have hstartrel : nestedOuterStart ks N (n + 1)
        = (3 * K0 + 4) + ((outerRest.take n).flatMap
            (fun p => guessBXOuterBlockElems I p.1 p.2)).length := by
      have hp := guessBXOuterRest_prefix_length I ks N hks outerRest houterLen houter houterLast n
        (by omega)
      have hge1 : nestedOuterStart ks N 1 ≤ nestedOuterStart ks N (n + 1) :=
        nestedOuterStart_mono ks N (by omega)
      have hns1 : nestedOuterStart ks N 1 = 3 * K0 + 4 := by
        show nestedOuterStart ks N 0 + nestedOuterLen ks N 0 = 3 * K0 + 4
        rw [show nestedOuterStart ks N 0 = 0 from rfl]
        unfold nestedOuterLen
        rw [if_neg (show (0 : ℕ) ≠ N + 1 by omega), if_pos rfl, hgd0]
        omega
      omega
    rcases Nat.eq_zero_or_pos p2 with hp2z | hp2pos
    · -- position `0` of the block: `zBxy` — iteration `n + 1`'s start.
      subst hp2z
      have hgetblkn' := hgetblkn
      rw [hp0Z (b, vs)] at hgetblkn'
      simp only [Option.some.injEq] at hgetblkn'
      have heloc : e.loc = Loc.zBxy := by rw [hloce, ← hgetblkn']; rfl
      have heop : e.op = OpType.wt := by rw [hope, ← hgetblkn']; rfl
      refine ⟨n + 1, by omega, ?_, Or.inl ⟨heloc, heop, ?_⟩⟩
      · have hnth : rawNthEvent trace Tid.guessBX Loc.zBxy OpType.wt (n + 1) = some e := by
          unfold rawNthEvent
          rw [hrawop, htrace]
          unfold guessBXBlockWord
          rw [List.zipIdx_append, List.filter_append, hHeadFilterZAxy]
          have hmain := flatMap_filter_getElem_of_lengths
            (fun p => guessBXOuterBlockElems I p.1 p.2)
            (fun (_ : (Val I × Val I) × List (Val I × Val I × Val I)) => (0 : ℕ))
            (fun p' => @decide (p'.1.loc = Loc.zBxy ∧ p'.1.op = OpType.wt)
              (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.zBxy) inferInstance))
            (fun p => (⟨EventLabel.wt Tid.guessBX Loc.zBxy p.1.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessBX))
            hp0Z (fun _ => rfl) hfalseZ
            outerRest (3 * K0 + 4) n (b, vs) hvan
          rw [Nat.zero_add, hHeadLen]
          rw [List.getElem?_map]
          simp only [List.getElem?_append_right, List.length_cons, List.length_nil,
            Nat.le_add_left, Nat.add_sub_cancel_left]
          rw [show n + 1 - 1 = n from by omega]
          have hmapped := congrArg (Option.map (fun p' =>
            (⟨traceEventId (D := domainOf I) Tid.guessBX p'.2, p'.1.1⟩ : Event (domainOf I)))) hmain
          rw [Option.map_some] at hmapped
          refine hmapped.trans ?_
          have hival : (3 * K0 + 4 + ((List.take n outerRest).flatMap
              (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 0) = i := by omega
          have hlab : EventLabel.wt Tid.guessBX Loc.zBxy b.1 = (l.1 : EventLabel (domainOf I)) :=
            congrArg Subtype.val hgetblkn'
          simp only [hival, hlab]
          exact congrArg some hee.symm
        exact rawNthEvent_rawIndex hnth
      · rw [hstartrel]; omega
    · -- `1 ≤ p2 < 3 * vs.length + 2`: either middle (non-bridge) or the block's last (`ellByx`).
      by_cases hp2le : p2 ≤ 3 * vs.length
      · exfalso
        have hmem : l.1.loc ∈ BridgeLoc := by rw [← hloce]; exact hb
        exact hOuterBlockMid b vs p2 l hp2pos hp2le hgetblkn hmem
      · have hp2L' : p2 < 3 * vs.length + 2 := hp2L
        have hp2eq : p2 = 3 * vs.length + 1 := by omega
        have hgetblkn' := hgetblkn
        rw [hp2eq, hp0E (b, vs)] at hgetblkn'
        simp only [Option.some.injEq] at hgetblkn'
        have heloc : e.loc = Loc.ellByx := by rw [hloce, ← hgetblkn']; rfl
        have heop : e.op = OpType.rd := by rw [hope, ← hgetblkn']; rfl
        refine ⟨n + 1, by omega, ?_, Or.inr ⟨heloc, heop, ?_⟩⟩
        · have hnth : rawNthEvent trace Tid.guessBX Loc.ellByx OpType.rd (n + 1) = some e := by
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessBXBlockWord
            rw [List.zipIdx_append, List.filter_append, hHeadFilterEllA]
            have hmain := flatMap_filter_getElem_of_lengths
              (fun p => guessBXOuterBlockElems I p.1 p.2)
              (fun p : (Val I × Val I) × List (Val I × Val I × Val I) => 3 * p.2.length + 1)
              (fun p' => @decide (p'.1.loc = Loc.ellByx ∧ p'.1.op = OpType.rd)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.ellByx) inferInstance))
              (fun p => (⟨EventLabel.rd Tid.guessBX Loc.ellByx p.1.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX))
              hp0E (fun _ => rfl) hfalseE
              outerRest (3 * K0 + 4) n (b, vs) hvan
            rw [Nat.zero_add, hHeadLen]
            rw [List.getElem?_map]
            simp only [List.getElem?_append_right, List.length_cons, List.length_nil,
              Nat.le_add_left, Nat.add_sub_cancel_left]
            rw [show n + 1 - 1 = n from by omega]
            have hmapped := congrArg (Option.map (fun p' =>
              (⟨traceEventId (D := domainOf I) Tid.guessBX p'.2, p'.1.1⟩ : Event (domainOf I)))) hmain
            rw [Option.map_some] at hmapped
            refine hmapped.trans ?_
            have hival : (3 * K0 + 4 + ((List.take n outerRest).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).length + (3 * vs.length + 1)) = i := by
              omega
            have hlab : EventLabel.rd Tid.guessBX Loc.ellByx b.2 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblkn'
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · rw [hstartrel]
          rcases Nat.lt_or_ge n N with hnN | hnN
          · obtain ⟨b', vs', km, hb'vs', hksm, hlen'⟩ := houter n hnN
            rw [hvan] at hb'vs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'vs'
            have hvslen : vs.length = km + 1 := by rw [hb'vs'.2]; exact hlen'
            have hgdn : ks.getD (n + 1) 0 = km := by
              show (ks[n + 1]?).getD 0 = km
              rw [hksm]; rfl
            have hlenne : n + 1 ≠ N + 1 := by omega
            have hne0 : n + 1 ≠ 0 := by omega
            unfold nestedOuterLen
            rw [if_neg hlenne, if_neg hne0, hgdn]
            omega
          · have hnN' : n = N := by omega
            obtain ⟨b', vs', hb'vs', hlen'⟩ := houterLast
            rw [hnN'] at hvan
            rw [hvan] at hb'vs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'vs'
            have hvslen : vs.length = 1 := by rw [hb'vs'.2]; exact hlen'
            have hlenne : n + 1 = N + 1 := by omega
            unfold nestedOuterLen
            rw [if_pos hlenne]
            omega
/-- Position and index of the non-bridge events of `GuessAX`'s trace: each sits
at global inner call `k`, position `p` of `guessAXInnerBlockShape`, and its
`rawIndex` is `k` for the two writes and `k - 1` for the read (call `0` skips
its `zAxx'`-read). -/
theorem guessAXInner_idPos_rawIndex (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.guessAX)
    (hnb : ¬ e.IsBridge) :
    ∃ k p, idPos e = nestedInnerStart ks k + p ∧ p < nestedCallLen k ∧
      guessAXInnerBlockShape[p]? = some (e.loc, e.op) ∧
      rawIndex trace e = if p < 2 then k else k - 1 := by
  obtain ⟨K0, hks0, hinner0⟩ := hinner0
  have hgd0 : ks.getD 0 0 = K0 := by
    show (ks[0]?).getD 0 = K0
    rw [hks0]; rfl
  obtain ⟨i, l, hget, hee⟩ := mem_traceEventsOf_iff'.mp he
  have hidPos : idPos e = i := by rw [hee]; unfold idPos traceEventId; simp [Nat.unpair_pair]
  have hloce : e.loc = l.1.loc := by rw [hee]; rfl
  have hope : e.op = l.1.op := by rw [hee]; rfl
  have hgetT : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]? = some l := by
    rw [← htrace]; exact hget
  have hFlatLen : ∀ vals : List (Val I × Val I × Val I),
      (vals.flatMap (guessAXInnerBlockElems I)).length = 3 * vals.length := by
    intro vals
    rw [List.length_flatMap]
    have heq : vals.map (fun a => (guessAXInnerBlockElems I a).length) = vals.map (fun _ => 3) :=
      List.map_congr_left (fun a _ => guessAXInnerBlockElems_length I a)
    rw [heq, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hBlen : (inner0Rest.flatMap (guessAXInnerBlockElems I)).length = 3 * K0 := by
    rw [hFlatLen, hinner0]
  have hrawop : ∀ (x : Loc) (op : OpType), rawOpEvents trace Tid.guessAX x op =
      (((trace Tid.guessAX).zipIdx).filter
          (fun p' => decide (p'.1.1.loc = x ∧ p'.1.1.op = op))).map
        (fun p' => (⟨traceEventId (D := domainOf I) Tid.guessAX p'.2, p'.1.1⟩ :
            Event (domainOf I))) := by
    intro x op
    unfold rawOpEvents traceEventsOf
    rw [List.filter_map]
    congr 1
  have hpredNonBridgeGen : ∀ (y : Loc), y ∉ BridgeLoc →
      ∀ (b0 : ThreadLabel (domainOf I) Tid.guessAX) (op0 : OpType),
      b0.1.loc ∈ BridgeLoc →
      @decide (b0.1.loc = y ∧ b0.1.op = op0)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b0.1.loc y) inferInstance) = false := by
    intro y hy b0 op0 hmem
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    rw [hloc] at hmem
    exact hy hmem
  -- `guessAXInnerBlockElems`'s three marked positions, for each of the three inner
  -- predicates: the position itself (`h0_X`) and the fact no other position matches (`hfalse_X`).
  -- Shared by the `inner0Rest` branch below and the `outerRest` (TAIL) branch.
  have h0_xA : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a)[(0 : ℕ)]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) :=
    fun _ => rfl
  have hfalse_xA : ∀ (a : Val I × Val I × Val I) (q : ℕ) (b : ThreadLabel (domainOf I) Tid.guessAX),
      q ≠ 0 → (guessAXInnerBlockElems I a)[q]? = some b →
      @decide (b.1.loc = Loc.xA ∧ b.1.op = OpType.wt)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b.1.loc Loc.xA) inferInstance) = false := by
    rintro ⟨a1, a2, a3⟩ q b hq0 hqget
    have hqlt : q < 3 := by
      have := (List.getElem?_eq_some_iff.mp hqget).1
      simpa [guessAXInnerBlockElems_length] using this
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    have hq12 : q = 1 ∨ q = 2 := by omega
    rcases hq12 with rfl | rfl
    · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.zAx'x ≠ Loc.xA)
    · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.zAxx' ≠ Loc.xA)
  have h0_zAx'x : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a)[(1 : ℕ)]? =
      some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) :=
    fun _ => rfl
  have hfalse_zAx'x : ∀ (a : Val I × Val I × Val I) (q : ℕ) (b : ThreadLabel (domainOf I) Tid.guessAX),
      q ≠ 1 → (guessAXInnerBlockElems I a)[q]? = some b →
      @decide (b.1.loc = Loc.zAx'x ∧ b.1.op = OpType.wt)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b.1.loc Loc.zAx'x) inferInstance) = false := by
    rintro ⟨a1, a2, a3⟩ q b hq1 hqget
    have hqlt : q < 3 := by
      have := (List.getElem?_eq_some_iff.mp hqget).1
      simpa [guessAXInnerBlockElems_length] using this
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    have hq02 : q = 0 ∨ q = 2 := by omega
    rcases hq02 with rfl | rfl
    · simp only [guessAXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.xA ≠ Loc.zAx'x)
    · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.zAxx' ≠ Loc.zAx'x)
  have h0_zAxx' : ∀ a : Val I × Val I × Val I, (guessAXInnerBlockElems I a)[(2 : ℕ)]? =
      some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX) :=
    fun _ => rfl
  have hfalse_zAxx' : ∀ (a : Val I × Val I × Val I) (q : ℕ) (b : ThreadLabel (domainOf I) Tid.guessAX),
      q ≠ 2 → (guessAXInnerBlockElems I a)[q]? = some b →
      @decide (b.1.loc = Loc.zAxx' ∧ b.1.op = OpType.rd)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b.1.loc Loc.zAxx') inferInstance) = false := by
    rintro ⟨a1, a2, a3⟩ q b hq2 hqget
    have hqlt : q < 3 := by
      have := (List.getElem?_eq_some_iff.mp hqget).1
      simpa [guessAXInnerBlockElems_length] using this
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    have hq01 : q = 0 ∨ q = 1 := by omega
    rcases hq01 with rfl | rfl
    · simp only [guessAXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.xA ≠ Loc.zAxx')
    · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.zAx'x ≠ Loc.zAxx')
  rcases Nat.lt_or_ge i (3 * K0 + 4) with hi | hi
  · -- HEAD case: `e` sits among the head's three literal events or `inner0Rest`.
    have hget1 : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]?
        = (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessAX)
            , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
            , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ] ++
            inner0Rest.flatMap (guessAXInnerBlockElems I) ++
            [ ⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ ]))[i]? := by
      unfold guessAXBlockWord
      rw [List.getElem?_append_left
        (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)]
    rw [hget1] at hgetT
    rcases Nat.lt_or_ge i (3 + 3 * K0) with hi2 | hi2
    · rw [List.getElem?_append_left
          (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)] at hgetT
      rcases Nat.lt_or_ge i 3 with hi3 | hi3
      · rw [List.getElem?_append_left (by simpa using hi3)] at hgetT
        have hi012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi012 with rfl | rfl | rfl
        · -- position 0: `zAxy`, bridge — contradicts `hnb`.
          exfalso
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have hloc : e.loc = Loc.zAxy := by rw [hloce, ← hgetT]; rfl
          have hmem : e.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.zAxy ∈ BridgeLoc)
          exact hnb hmem
        · -- position 1: `xA`, call `0`, `p = 0`.
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have heloc : e.loc = Loc.xA := by rw [hloce, ← hgetT]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetT]; rfl
          refine ⟨0, 0, ?_, by norm_num [nestedCallLen], ?_, ?_⟩
          · rw [hidPos]; simp [nestedInnerStart]
          · rw [heloc, heop]; rfl
          · have hnth : rawNthEvent trace Tid.guessAX Loc.xA OpType.wt 0 = some e := by
              unfold rawNthEvent
              rw [hrawop, htrace]
              unfold guessAXBlockWord
              simp only [List.zipIdx_append, List.filter_append]
              have hHead3 :
                  (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessAX)
                      , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                      , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                    (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))
                    = [(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩, 1)] := by rfl
              rw [hHead3]
              simp only [List.cons_append, List.map_cons, List.getElem?_cons_zero]
              rw [hee, ← hgetT]
            exact rawNthEvent_rawIndex hnth
        · -- position 2: `zAx'x`, call `0`, `p = 1`.
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have heloc : e.loc = Loc.zAx'x := by rw [hloce, ← hgetT]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetT]; rfl
          refine ⟨0, 1, ?_, by norm_num [nestedCallLen], ?_, ?_⟩
          · rw [hidPos]; simp [nestedInnerStart]
          · rw [heloc, heop]; rfl
          · have hnth : rawNthEvent trace Tid.guessAX Loc.zAx'x OpType.wt 0 = some e := by
              unfold rawNthEvent
              rw [hrawop, htrace]
              unfold guessAXBlockWord
              simp only [List.zipIdx_append, List.filter_append]
              have hHead3 :
                  (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessAX)
                      , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                      , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))
                    = [(⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩, 2)] := by rfl
              rw [hHead3]
              simp only [List.cons_append, List.map_cons, List.getElem?_cons_zero]
              rw [hee, ← hgetT]
            exact rawNthEvent_rawIndex hnth
      · -- `3 ≤ i < 3 + 3 * K0`: within `inner0Rest`'s flatMap.
        rw [List.getElem?_append_right (by simpa using hi3)] at hgetT
        simp only [List.length_cons, List.length_nil, show 1 + 1 + 1 = 3 from rfl] at hgetT
        have hilt : i - 3 < inner0Rest.length * 3 := by rw [hinner0]; omega
        obtain ⟨n, p, a, hpL, hoffnp, hvan, heqget⟩ :=
          flatMap_uniform_getElem (guessAXInnerBlockElems I) 3
            (fun a => guessAXInnerBlockElems_length I a) inner0Rest (i - 3) hilt
        rw [heqget] at hgetT
        have hgetblk : (guessAXInnerBlockElems I a)[p]? = some l := hgetT
        have hnlt : n < inner0Rest.length := (List.getElem?_eq_some_iff.mp hvan).1
        have hnK0 : n < K0 := by rw [← hinner0]; exact hnlt
        have h0lt : 0 < ks.length := by omega
        have hk0eq : ks[0]'h0lt = K0 :=
          Option.some.inj ((List.getElem?_eq_getElem h0lt).symm.trans hks0)
        have hstart : nestedInnerStart ks (n + 1) = 3 * (n + 1) :=
          nestedInnerStart_inner0Rest ks h0lt n (by rw [hk0eq]; exact hnK0)
        have hoffidPos : idPos e = nestedInnerStart ks (n + 1) + p := by
          rw [hidPos, hstart]; omega
        have hcalllen : nestedCallLen (n + 1) = 3 := by
          unfold nestedCallLen; rw [if_neg (by omega)]
        have hplt3 : p < nestedCallLen (n + 1) := by rw [hcalllen]; exact hpL
        have hp012 : p = 0 ∨ p = 1 ∨ p = 2 := by omega
        rcases hp012 with rfl | rfl | rfl
        · -- `p = 0`: `xA`, target rawIndex `n + 1`.
          have hgetblk0 := hgetblk
          rw [h0_xA a] at hgetblk0
          simp only [Option.some.injEq] at hgetblk0
          have heloc : e.loc = Loc.xA := by rw [hloce, ← hgetblk0]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetblk0]; rfl
          refine ⟨n + 1, 0, hoffidPos, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show (0 : ℕ) < 2 from by omega, if_true]
          have hnth : rawNthEvent trace Tid.guessAX Loc.xA OpType.wt (n + 1) = some e := by
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessAXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))
                  = [(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩, 1)] := by rfl
            have hInnerMatch := zipIdx_flatMap_filter_getElem (guessAXInnerBlockElems I) 3 0
              (fun a => guessAXInnerBlockElems_length I a)
              (fun p' => @decide (p'.1.loc = Loc.xA ∧ p'.1.op = OpType.wt)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.xA) inferInstance))
              (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX))
              h0_xA (fun _ => rfl) hfalse_xA
              inner0Rest 3 n a hvan
            have hInnerMatch' : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)))[n]?
                = some (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩, 3 + n * 3 + 0) := hInnerMatch
            rw [hHead3]
            simp only [List.cons_append, List.map_cons, List.getElem?_cons_succ, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            have hmapped := congrArg (Option.map (fun p' =>
              (⟨traceEventId (D := domainOf I) Tid.guessAX p'.2, p'.1.1⟩ : Event (domainOf I))))
              hInnerMatch'
            rw [Option.map_some] at hmapped
            rw [List.getElem?_map,
              List.getElem?_append_left (by
                rw [List.length_append]
                have := (List.getElem?_eq_some_iff.mp hInnerMatch').1
                omega),
              List.getElem?_append_left (List.getElem?_eq_some_iff.mp hInnerMatch').1]
            refine hmapped.trans ?_
            have hival : 3 + n * 3 + 0 = i := by omega
            have hlab : EventLabel.wt Tid.guessAX Loc.xA a.1 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk0
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · -- `p = 1`: `zAx'x`, target rawIndex `n + 1`.
          have hgetblk1 := hgetblk
          rw [h0_zAx'x a] at hgetblk1
          simp only [Option.some.injEq] at hgetblk1
          have heloc : e.loc = Loc.zAx'x := by rw [hloce, ← hgetblk1]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetblk1]; rfl
          refine ⟨n + 1, 1, hoffidPos, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show (1 : ℕ) < 2 from by omega, if_true]
          have hnth : rawNthEvent trace Tid.guessAX Loc.zAx'x OpType.wt (n + 1) = some e := by
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessAXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))
                  = [(⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩, 2)] := by rfl
            have hInnerMatch := zipIdx_flatMap_filter_getElem (guessAXInnerBlockElems I) 3 1
              (fun a => guessAXInnerBlockElems_length I a)
              (fun p' => @decide (p'.1.loc = Loc.zAx'x ∧ p'.1.op = OpType.wt)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.zAx'x) inferInstance))
              (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX))
              h0_zAx'x (fun _ => rfl) hfalse_zAx'x
              inner0Rest 3 n a hvan
            have hInnerMatch' : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)))[n]?
                = some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩, 3 + n * 3 + 1) := hInnerMatch
            rw [hHead3]
            simp only [List.cons_append, List.map_cons, List.getElem?_cons_succ, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            have hmapped := congrArg (Option.map (fun p' =>
              (⟨traceEventId (D := domainOf I) Tid.guessAX p'.2, p'.1.1⟩ : Event (domainOf I))))
              hInnerMatch'
            rw [Option.map_some] at hmapped
            rw [List.getElem?_map,
              List.getElem?_append_left (by
                rw [List.length_append]
                have := (List.getElem?_eq_some_iff.mp hInnerMatch').1
                omega),
              List.getElem?_append_left (List.getElem?_eq_some_iff.mp hInnerMatch').1]
            refine hmapped.trans ?_
            have hival : 3 + n * 3 + 1 = i := by omega
            have hlab : EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk1
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · -- `p = 2`: `zAxx'`, target rawIndex `n` (call `0`'s skipped read).
          have hgetblk2 := hgetblk
          rw [h0_zAxx' a] at hgetblk2
          simp only [Option.some.injEq] at hgetblk2
          have heloc : e.loc = Loc.zAxx' := by rw [hloce, ← hgetblk2]; rfl
          have heop : e.op = OpType.rd := by rw [hope, ← hgetblk2]; rfl
          refine ⟨n + 1, 2, hoffidPos, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show ¬ (2 : ℕ) < 2 from by omega, if_false]
          have hnth : rawNthEvent trace Tid.guessAX Loc.zAxx' OpType.rd n = some e := by
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessAXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))
                  = [] := by rfl
            have hInnerMatch := zipIdx_flatMap_filter_getElem (guessAXInnerBlockElems I) 3 2
              (fun a => guessAXInnerBlockElems_length I a)
              (fun p' => @decide (p'.1.loc = Loc.zAxx' ∧ p'.1.op = OpType.rd)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.zAxx') inferInstance))
              (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX))
              h0_zAxx' (fun _ => rfl) hfalse_zAxx'
              inner0Rest 3 n a hvan
            have hInnerMatch' : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)))[n]?
                = some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩, 3 + n * 3 + 2) := hInnerMatch
            rw [hHead3, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            have hmapped := congrArg (Option.map (fun p' =>
              (⟨traceEventId (D := domainOf I) Tid.guessAX p'.2, p'.1.1⟩ : Event (domainOf I))))
              hInnerMatch'
            rw [Option.map_some] at hmapped
            rw [List.getElem?_map,
              List.getElem?_append_left (by
                rw [List.length_append]
                have := (List.getElem?_eq_some_iff.mp hInnerMatch').1
                omega),
              List.getElem?_append_left (List.getElem?_eq_some_iff.mp hInnerMatch').1]
            refine hmapped.trans ?_
            have hival : 3 + n * 3 + 2 = i := by omega
            have hlab : EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk2
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
    · -- `i = 3 + 3 * K0`: `ellAyx`, bridge — contradicts `hnb`.
      exfalso
      have hieq : i = 3 + 3 * K0 := by omega
      rw [List.getElem?_append_right
          (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)] at hgetT
      simp only [List.length_append, List.length_cons, List.length_nil, hBlen] at hgetT
      have hzero : i - (3 + 3 * K0) = 0 := by omega
      rw [hzero] at hgetT
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetT
      have hloc : e.loc = Loc.ellAyx := by rw [hloce, ← hgetT]; rfl
      have hmem : e.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.ellAyx ∈ BridgeLoc)
      exact hnb hmem
  · -- TAIL case: some `outerRest[m]`, outer iteration `M := m + 1`.
    have hget2 : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]?
        = (outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2))[i - (3 * K0 + 4)]? := by
      unfold guessAXBlockWord
      rw [List.getElem?_append_right]
      · congr 1
        simp [List.length_append, List.length_cons, hBlen]
      · simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega
    rw [hget2] at hgetT
    have hqlt : i - (3 * K0 + 4) <
        (outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)).length :=
      (List.getElem?_eq_some_iff.mp hgetT).1
    obtain ⟨m, p2, ⟨b, vs⟩, hp2L, hvan, hoffn, heqgetn⟩ :=
      flatMap_getElem_of_lengths (fun p => guessAXOuterBlockElems I p.1 p.2) outerRest
        (i - (3 * K0 + 4)) hqlt
    rw [guessAXOuterBlockElems_length] at hp2L
    have hgetblkn : (guessAXOuterBlockElems I b vs)[p2]? = some l := by
      rw [← heqgetn]; exact hgetT
    have hoffidPos : idPos e = (3 * K0 + 4) + (((outerRest.take m).flatMap
        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + p2) := by
      rw [hidPos]; omega
    have hmlt : m < outerRest.length := (List.getElem?_eq_some_iff.mp hvan).1
    have hstartrel : nestedOuterStart ks N (m + 1)
        = (3 * K0 + 4) + ((outerRest.take m).flatMap
            (fun p => guessAXOuterBlockElems I p.1 p.2)).length := by
      have hp := guessAXOuterRest_prefix_length I ks N hks outerRest houterLen houter houterLast m
        (by omega)
      have hge1 : nestedOuterStart ks N 1 ≤ nestedOuterStart ks N (m + 1) :=
        nestedOuterStart_mono ks N (by omega)
      have hns1 : nestedOuterStart ks N 1 = 3 * K0 + 4 := by
        show nestedOuterStart ks N 0 + nestedOuterLen ks N 0 = 3 * K0 + 4
        rw [show nestedOuterStart ks N 0 = 0 from rfl]
        unfold nestedOuterLen
        rw [if_neg (show (0 : ℕ) ≠ N + 1 by omega), if_pos rfl, hgd0]
        omega
      omega
    have hp0Z' : (guessAXOuterBlockElems I b vs)[(0 : ℕ)]?
        = some (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX) := rfl
    have hOuterBlockLast' : (guessAXOuterBlockElems I b vs)[3 * vs.length + 1]?
        = some (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX) := by
      unfold guessAXOuterBlockElems
      rw [show 3 * vs.length + 1 = (3 * vs.length) + 1 from rfl, List.getElem?_cons_succ,
        List.getElem?_append_right (by rw [hFlatLen]), hFlatLen]
      simp
    rcases Nat.eq_zero_or_pos p2 with hp2z | hp2pos
    · -- `p2 = 0`: `zAxy`, bridge — contradicts `hnb`.
      exfalso
      subst hp2z
      rw [hp0Z'] at hgetblkn
      simp only [Option.some.injEq] at hgetblkn
      have hloc : e.loc = Loc.zAxy := by rw [hloce, ← hgetblkn]; rfl
      have hmem : e.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.zAxy ∈ BridgeLoc)
      exact hnb hmem
    · by_cases hp2le : p2 ≤ 3 * vs.length
      · -- `1 ≤ p2 ≤ 3 * vs.length`: an inner call within outer iteration `m + 1`.
        have hp2sub : p2 - 1 < vs.length * 3 := by omega
        obtain ⟨j, p, a', hpL', hoffjp, hvaj, heqgetj⟩ :=
          flatMap_uniform_getElem (guessAXInnerBlockElems I) 3
            (fun a => guessAXInnerBlockElems_length I a) vs (p2 - 1) hp2sub
        have hgetblkn2 : (guessAXInnerBlockElems I a')[p]? = some l := by
          have hstep : (guessAXOuterBlockElems I b vs)[p2]?
              = (vs.flatMap (guessAXInnerBlockElems I))[p2 - 1]? := by
            unfold guessAXOuterBlockElems
            rw [show p2 = (p2 - 1) + 1 from by omega, List.getElem?_cons_succ,
              List.getElem?_append_left (by rw [hFlatLen]; omega)]
            congr 1
          rw [hstep, heqgetj] at hgetblkn
          exact hgetblkn
        have hinnerStart : nestedInnerStart ks (ksPrefix ks (m + 1) + j)
            = nestedInnerStart ks (ksPrefix ks (m + 1)) + 3 * j := by
          rcases Nat.lt_or_ge m N with hmN | hmN
          · obtain ⟨b', vs', km, hb'vs', hksm, hlen'⟩ := houter m hmN
            rw [hvan] at hb'vs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'vs'
            have hvslen : vs.length = km + 1 := by rw [hb'vs'.2]; exact hlen'
            have hjlt : j < vs.length := (List.getElem?_eq_some_iff.mp hvaj).1
            have hm1lt : m + 1 < ks.length := by omega
            have hkeq : ks[m + 1]'hm1lt = km :=
              Option.some.inj ((List.getElem?_eq_getElem hm1lt).symm.trans hksm)
            exact nestedInnerStart_outerRest_add ks m hm1lt j (by rw [hkeq]; omega)
          · have hmN' : m = N := by omega
            obtain ⟨b', vs', hb'vs', hlen'⟩ := houterLast
            rw [hmN'] at hvan
            rw [hvan] at hb'vs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'vs'
            have hvslen : vs.length = 1 := by rw [hb'vs'.2]; exact hlen'
            have hjlt : j < vs.length := (List.getElem?_eq_some_iff.mp hvaj).1
            have hj0 : j = 0 := by omega
            subst hj0
            simp
        have hcrosstier : nestedOuterStart ks N (m + 1) + 1
            = nestedInnerStart ks (ksPrefix ks (m + 1)) :=
          nestedOuterStart_succ_eq_innerStart ks N (m + 1) hks (by omega)
        have hoffidPos2 : idPos e = nestedInnerStart ks (ksPrefix ks (m + 1) + j) + p := by
          rw [hinnerStart]
          omega
        have hcalllen : nestedCallLen (ksPrefix ks (m + 1) + j) = 3 := by
          have hpos : ksPrefix ks (m + 1) ≠ 0 := by rw [Ne, ksPrefix_eq_zero_iff]; omega
          unfold nestedCallLen; rw [if_neg (by omega)]
        have hplt3 : p < nestedCallLen (ksPrefix ks (m + 1) + j) := by rw [hcalllen]; exact hpL'
        have hns1' : ksPrefix ks 1 = K0 + 1 := by
          show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
          rw [show ksPrefix ks 0 = 0 from rfl, hgd0]
          omega
        have hmono1 : ksPrefix ks 1 ≤ ksPrefix ks (m + 1) := ksPrefix_mono ks (by omega)
        have hp012 : p = 0 ∨ p = 1 ∨ p = 2 := by omega
        rcases hp012 with rfl | rfl | rfl
        · -- `p = 0`: `xA`.
          have hgetblk0 := hgetblkn2
          rw [h0_xA a'] at hgetblk0
          simp only [Option.some.injEq] at hgetblk0
          have heloc : e.loc = Loc.xA := by rw [hloce, ← hgetblk0]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetblk0]; rfl
          refine ⟨ksPrefix ks (m + 1) + j, 0, hoffidPos2, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show (0 : ℕ) < 2 from by omega, if_true]
          have hnth : rawNthEvent trace Tid.guessAX Loc.xA OpType.wt
              (ksPrefix ks (m + 1) + j) = some e := by
            let pxA : ThreadLabel (domainOf I) Tid.guessAX → Bool := fun l' =>
              @decide (l'.1.loc = Loc.xA ∧ l'.1.op = OpType.wt)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq l'.1.loc Loc.xA) inferInstance)
            let bvalxA : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX :=
              fun a => ⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩
            have h0xA' : ∀ a, (guessAXInnerBlockElems I a)[(0 : ℕ)]? = some (bvalxA a) := h0_xA
            have hfalsexA' : ∀ (a : Val I × Val I × Val I) (q : ℕ)
                (b0 : ThreadLabel (domainOf I) Tid.guessAX),
                q ≠ 0 → (guessAXInnerBlockElems I a)[q]? = some b0 → pxA b0 = false := hfalse_xA
            have htruexA' : ∀ a, pxA (bvalxA a) = true := fun _ => rfl
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessAXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3E :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => pxA p'.1)
                  = [(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩, 1)] := by rfl
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))
                  = [(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩, 1)] := hHead3E
            have hInner0Count : ((inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
                pxA).length = K0 := by
              rw [guessAXInnerBlockElems_filter I pxA 0 bvalxA h0xA' htruexA' hfalsexA']
              simp [hinner0]
            have hInner0ZipCountE : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => pxA p'.1)).length = K0 := by
              rw [zipIdx_filter_length]; exact hInner0Count
            have hInner0ZipCount : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))).length = K0 :=
              hInner0ZipCountE
            have hOuterPrefixCount : (((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).filter pxA).length = ksPrefix ks (m + 1) - ksPrefix ks 1 :=
              guessAXOuterRest_prefix_matchCount I ks N hks outerRest houter pxA 0 bvalxA
                h0xA' htruexA' hfalsexA'
                (fun b0 hb0 => hpredNonBridgeGen Loc.xA (by decide) b0 OpType.wt hb0)
                m (by omega)
            have hOuterPrefixZipCountE : ((((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => pxA p'.1)).length = ksPrefix ks (m + 1) - ksPrefix ks 1 := by
              rw [zipIdx_filter_length]; exact hOuterPrefixCount
            have hOuterPrefixZipCount : ((((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))).length
                = ksPrefix ks (m + 1) - ksPrefix ks 1 := hOuterPrefixZipCountE
            have hVsMatchE := zipIdx_flatMap_filter_getElem (guessAXInnerBlockElems I) 3 0
              (fun a => guessAXInnerBlockElems_length I a) pxA bvalxA
              h0xA' htruexA' hfalsexA'
              vs ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1) j a' hvaj
            have hVsMatch : (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)))[j]?
                = some (⟨EventLabel.wt Tid.guessAX Loc.xA a'.1, rfl⟩,
                    (3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 0) :=
              hVsMatchE
            have hsplit1 : outerRest.take (m + 1) = outerRest.take m ++ [(b, vs)] := by
              rw [List.take_add_one, hvan]; rfl
            have hsplit2 : outerRest = outerRest.take (m + 1) ++ outerRest.drop (m + 1) :=
              (List.take_append_drop (m + 1) outerRest).symm
            rw [show ksPrefix ks (m + 1) + j = (ksPrefix ks (m + 1) + j - 1) + 1 from by omega]
            rw [hHead3]
            simp only [List.cons_append, List.map_cons, List.getElem?_cons_succ, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            rw [show outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)
                = (outerRest.take m).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2) ++
                  (guessAXOuterBlockElems I b vs ++
                    (outerRest.drop (m + 1)).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2))
                from by
              conv_lhs => rw [hsplit2]
              rw [hsplit1]
              simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc]]
            simp only [List.zipIdx_append, List.filter_append, List.getElem?_map,
              List.append_assoc]
            have hOBSegXA : (((guessAXOuterBlockElems I b vs).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length)).filter
                (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)))
                = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)) := by
              have hzAxyF := hpredNonBridgeGen Loc.xA (by decide)
                (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX) OpType.wt
                (by decide : Loc.zAxy ∈ BridgeLoc)
              have hellAyxF := hpredNonBridgeGen Loc.xA (by decide)
                (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX) OpType.rd
                (by decide : Loc.ellAyx ∈ BridgeLoc)
              have hunfold : guessAXOuterBlockElems I b vs =
                  (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX) ::
                    (vs.flatMap (guessAXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessAX)]) := rfl
              have hzAxyNeg : ¬ @decide ((⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.loc = Loc.xA ∧
                  (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.op = OpType.wt)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX).1.loc Loc.xA) inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.zAxy ≠ Loc.xA)
              have hellAyxNeg : ¬ @decide ((⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.loc = Loc.xA ∧
                  (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.op = OpType.wt)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX).1.loc Loc.xA) inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.ellAyx ≠ Loc.xA)
              have hellAyxNeg' : (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                  ((3 * K0 + 4) + ((outerRest.take m).flatMap
                    (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 +
                    (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))
                = List.filter (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))
                    ([] : List (ThreadLabel (domainOf I) Tid.guessAX × ℕ)) := by
                rw [List.zipIdx_cons, List.zipIdx_nil]
                exact List.filter_cons_of_neg hellAyxNeg
              calc (((guessAXOuterBlockElems I b vs).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)))
                  = (((⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX),
                      (3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length) ::
                      ((vs.flatMap (guessAXInnerBlockElems I) ++
                        [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                            ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                        ((3 * K0 + 4) + ((outerRest.take m).flatMap
                          (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1))).filter
                    (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)) := by
                    rw [hunfold, List.zipIdx_cons]
                _ = ((vs.flatMap (guessAXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)) :=
                  List.filter_cons_of_neg hzAxyNeg
                _ = (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))) ++
                    ((([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 +
                        (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))) := by
                    rw [List.zipIdx_append, List.filter_append]
                _ = (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))) ++
                    (List.filter (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))
                      ([] : List (ThreadLabel (domainOf I) Tid.guessAX × ℕ))) :=
                  congrArg (fun x => ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)) ++ x)
                    hellAyxNeg'
                _ = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)) ++ [] := by
                    rw [List.filter_nil]
                _ = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt)) :=
                  List.append_nil _
            simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.reduceAdd]
            rw [show 3 * K0 + 1 + 1 + 1 + 1 = 3 * K0 + 4 from by omega]
            rw [hOBSegXA]
            have hHeadEllaLen0 : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))
                (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx (3 * K0 + 1 + 1 + 1))) = [] := by
              rfl
            have hHeadEllaLen0' : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.xA ∧ p'.1.1.op = OpType.wt))
                (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx (3 * K0 + 1 + 1 + 1))).length
                = 0 := by rw [hHeadEllaLen0]; rfl
            rw [List.getElem?_append_right
              (by rw [hInner0ZipCount]; omega),
              List.getElem?_append_right
              (by rw [hHeadEllaLen0]; simp),
              List.getElem?_append_right
              (by rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']; omega),
              List.getElem?_append_left
              (by
                have := (List.getElem?_eq_some_iff.mp hVsMatch).1
                rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']
                omega)]
            rw [hInner0ZipCount, hHeadEllaLen0', hOuterPrefixZipCount]
            rw [show ksPrefix ks (m + 1) + j - 1 - K0 - 0 - (ksPrefix ks (m + 1) - ksPrefix ks 1) = j from by
              omega]
            rw [hVsMatch]
            simp only [Option.map_some]
            have hival : 3 * K0 + 4 + ((List.take m outerRest).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 0 = i := by omega
            have hlab : EventLabel.wt Tid.guessAX Loc.xA a'.1 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk0
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · -- `p = 1`: `zAx'x`.
          have hgetblk1 := hgetblkn2
          rw [h0_zAx'x a'] at hgetblk1
          simp only [Option.some.injEq] at hgetblk1
          have heloc : e.loc = Loc.zAx'x := by rw [hloce, ← hgetblk1]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetblk1]; rfl
          refine ⟨ksPrefix ks (m + 1) + j, 1, hoffidPos2, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show (1 : ℕ) < 2 from by omega, if_true]
          have hnth : rawNthEvent trace Tid.guessAX Loc.zAx'x OpType.wt
              (ksPrefix ks (m + 1) + j) = some e := by
            let pzAx'x : ThreadLabel (domainOf I) Tid.guessAX → Bool := fun l' =>
              @decide (l'.1.loc = Loc.zAx'x ∧ l'.1.op = OpType.wt)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq l'.1.loc Loc.zAx'x) inferInstance)
            let bvalzAx'x : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX :=
              fun a => ⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩
            have h0zAx'x' : ∀ a, (guessAXInnerBlockElems I a)[(1 : ℕ)]? = some (bvalzAx'x a) := h0_zAx'x
            have hfalsezAx'x' : ∀ (a : Val I × Val I × Val I) (q : ℕ)
                (b0 : ThreadLabel (domainOf I) Tid.guessAX),
                q ≠ 1 → (guessAXInnerBlockElems I a)[q]? = some b0 → pzAx'x b0 = false := hfalse_zAx'x
            have htruezAx'x' : ∀ a, pzAx'x (bvalzAx'x a) = true := fun _ => rfl
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessAXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3E :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => pzAx'x p'.1)
                  = [(⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩, 2)] := by rfl
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))
                  = [(⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩, 2)] := hHead3E
            have hInner0Count : ((inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
                pzAx'x).length = K0 := by
              rw [guessAXInnerBlockElems_filter I pzAx'x 1 bvalzAx'x h0zAx'x' htruezAx'x' hfalsezAx'x']
              simp [hinner0]
            have hInner0ZipCountE : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => pzAx'x p'.1)).length = K0 := by
              rw [zipIdx_filter_length]; exact hInner0Count
            have hInner0ZipCount : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))).length = K0 :=
              hInner0ZipCountE
            have hOuterPrefixCount : (((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).filter pzAx'x).length = ksPrefix ks (m + 1) - ksPrefix ks 1 :=
              guessAXOuterRest_prefix_matchCount I ks N hks outerRest houter pzAx'x 1 bvalzAx'x
                h0zAx'x' htruezAx'x' hfalsezAx'x'
                (fun b0 hb0 => hpredNonBridgeGen Loc.zAx'x (by decide) b0 OpType.wt hb0)
                m (by omega)
            have hOuterPrefixZipCountE : ((((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => pzAx'x p'.1)).length = ksPrefix ks (m + 1) - ksPrefix ks 1 := by
              rw [zipIdx_filter_length]; exact hOuterPrefixCount
            have hOuterPrefixZipCount : ((((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))).length
                = ksPrefix ks (m + 1) - ksPrefix ks 1 := hOuterPrefixZipCountE
            have hVsMatchE := zipIdx_flatMap_filter_getElem (guessAXInnerBlockElems I) 3 1
              (fun a => guessAXInnerBlockElems_length I a) pzAx'x bvalzAx'x
              h0zAx'x' htruezAx'x' hfalsezAx'x'
              vs ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1) j a' hvaj
            have hVsMatch : (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)))[j]?
                = some (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a'.2.1, rfl⟩,
                    (3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 1) :=
              hVsMatchE
            have hsplit1 : outerRest.take (m + 1) = outerRest.take m ++ [(b, vs)] := by
              rw [List.take_add_one, hvan]; rfl
            have hsplit2 : outerRest = outerRest.take (m + 1) ++ outerRest.drop (m + 1) :=
              (List.take_append_drop (m + 1) outerRest).symm
            rw [show ksPrefix ks (m + 1) + j = (ksPrefix ks (m + 1) + j - 1) + 1 from by omega]
            rw [hHead3]
            simp only [List.cons_append, List.map_cons, List.getElem?_cons_succ, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            rw [show outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)
                = (outerRest.take m).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2) ++
                  (guessAXOuterBlockElems I b vs ++
                    (outerRest.drop (m + 1)).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2))
                from by
              conv_lhs => rw [hsplit2]
              rw [hsplit1]
              simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc]]
            simp only [List.zipIdx_append, List.filter_append, List.getElem?_map,
              List.append_assoc]
            have hOBSegXA : (((guessAXOuterBlockElems I b vs).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)))
                = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)) := by
              have hzAxyF := hpredNonBridgeGen Loc.zAx'x (by decide)
                (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX) OpType.wt
                (by decide : Loc.zAxy ∈ BridgeLoc)
              have hellAyxF := hpredNonBridgeGen Loc.zAx'x (by decide)
                (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX) OpType.rd
                (by decide : Loc.ellAyx ∈ BridgeLoc)
              have hunfold : guessAXOuterBlockElems I b vs =
                  (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX) ::
                    (vs.flatMap (guessAXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessAX)]) := rfl
              have hzAxyNeg : ¬ @decide ((⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.loc = Loc.zAx'x ∧
                  (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.op = OpType.wt)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX).1.loc Loc.zAx'x) inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.zAxy ≠ Loc.zAx'x)
              have hellAyxNeg : ¬ @decide ((⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.loc = Loc.zAx'x ∧
                  (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.op = OpType.wt)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX).1.loc Loc.zAx'x) inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.ellAyx ≠ Loc.zAx'x)
              have hellAyxNeg' : (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                  ((3 * K0 + 4) + ((outerRest.take m).flatMap
                    (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 +
                    (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))
                = List.filter (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))
                    ([] : List (ThreadLabel (domainOf I) Tid.guessAX × ℕ)) := by
                rw [List.zipIdx_cons, List.zipIdx_nil]
                exact List.filter_cons_of_neg hellAyxNeg
              calc (((guessAXOuterBlockElems I b vs).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)))
                  = (((⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX),
                      (3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length) ::
                      ((vs.flatMap (guessAXInnerBlockElems I) ++
                        [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                            ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                        ((3 * K0 + 4) + ((outerRest.take m).flatMap
                          (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1))).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)) := by
                    rw [hunfold, List.zipIdx_cons]
                _ = ((vs.flatMap (guessAXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)) :=
                  List.filter_cons_of_neg hzAxyNeg
                _ = (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))) ++
                    ((([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 +
                        (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))) := by
                    rw [List.zipIdx_append, List.filter_append]
                _ = (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))) ++
                    (List.filter (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))
                      ([] : List (ThreadLabel (domainOf I) Tid.guessAX × ℕ))) :=
                  congrArg (fun x => ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)) ++ x)
                    hellAyxNeg'
                _ = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)) ++ [] := by
                    rw [List.filter_nil]
                _ = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt)) :=
                  List.append_nil _
            simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.reduceAdd]
            rw [show 3 * K0 + 1 + 1 + 1 + 1 = 3 * K0 + 4 from by omega]
            rw [hOBSegXA]
            have hHeadEllaLen0 : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))
                (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx (3 * K0 + 1 + 1 + 1))) = [] := by
              rfl
            have hHeadEllaLen0' : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.zAx'x ∧ p'.1.1.op = OpType.wt))
                (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx (3 * K0 + 1 + 1 + 1))).length
                = 0 := by rw [hHeadEllaLen0]; rfl
            rw [List.getElem?_append_right
              (by rw [hInner0ZipCount]; omega),
              List.getElem?_append_right
              (by rw [hHeadEllaLen0]; simp),
              List.getElem?_append_right
              (by rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']; omega),
              List.getElem?_append_left
              (by
                have := (List.getElem?_eq_some_iff.mp hVsMatch).1
                rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']
                omega)]
            rw [hInner0ZipCount, hHeadEllaLen0', hOuterPrefixZipCount]
            rw [show ksPrefix ks (m + 1) + j - 1 - K0 - 0 - (ksPrefix ks (m + 1) - ksPrefix ks 1) = j from by
              omega]
            rw [hVsMatch]
            simp only [Option.map_some]
            have hival : 3 * K0 + 4 + ((List.take m outerRest).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 1 = i := by omega
            have hlab : EventLabel.wt Tid.guessAX Loc.zAx'x a'.2.1 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk1
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · -- `p = 2`: `zAxx'`.
          have hgetblk2 := hgetblkn2
          rw [h0_zAxx' a'] at hgetblk2
          simp only [Option.some.injEq] at hgetblk2
          have heloc : e.loc = Loc.zAxx' := by rw [hloce, ← hgetblk2]; rfl
          have heop : e.op = OpType.rd := by rw [hope, ← hgetblk2]; rfl
          refine ⟨ksPrefix ks (m + 1) + j, 2, hoffidPos2, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show ¬ (2 : ℕ) < 2 from by omega, if_false]
          have hnth : rawNthEvent trace Tid.guessAX Loc.zAxx' OpType.rd
              (ksPrefix ks (m + 1) + j - 1) = some e := by
            let pzAxx' : ThreadLabel (domainOf I) Tid.guessAX → Bool := fun l' =>
              @decide (l'.1.loc = Loc.zAxx' ∧ l'.1.op = OpType.rd)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq l'.1.loc Loc.zAxx') inferInstance)
            let bvalzAxx' : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX :=
              fun a => ⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩
            have h0zAx'x : ∀ a, (guessAXInnerBlockElems I a)[(2 : ℕ)]? = some (bvalzAxx' a) := h0_zAxx'
            have hfalsezAx'x : ∀ (a : Val I × Val I × Val I) (q : ℕ)
                (b0 : ThreadLabel (domainOf I) Tid.guessAX),
                q ≠ 2 → (guessAXInnerBlockElems I a)[q]? = some b0 → pzAxx' b0 = false := hfalse_zAxx'
            have htruezAx'x : ∀ a, pzAxx' (bvalzAxx' a) = true := fun _ => rfl
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessAXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3E :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => pzAxx' p'.1)
                  = [] := by rfl
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)
                    , ⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))
                  = [] := hHead3E
            have hInner0Count : ((inner0Rest.flatMap (guessAXInnerBlockElems I)).filter
                pzAxx').length = K0 := by
              rw [guessAXInnerBlockElems_filter I pzAxx' 2 bvalzAxx' h0zAx'x htruezAx'x hfalsezAx'x]
              simp [hinner0]
            have hInner0ZipCountE : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => pzAxx' p'.1)).length = K0 := by
              rw [zipIdx_filter_length]; exact hInner0Count
            have hInner0ZipCount : (((inner0Rest.flatMap (guessAXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))).length = K0 :=
              hInner0ZipCountE
            have hOuterPrefixCount : (((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).filter pzAxx').length = ksPrefix ks (m + 1) - ksPrefix ks 1 :=
              guessAXOuterRest_prefix_matchCount I ks N hks outerRest houter pzAxx' 2 bvalzAxx'
                h0zAx'x htruezAx'x hfalsezAx'x
                (fun b0 hb0 => hpredNonBridgeGen Loc.zAxx' (by decide) b0 OpType.rd hb0)
                m (by omega)
            have hOuterPrefixZipCountE : ((((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => pzAxx' p'.1)).length = ksPrefix ks (m + 1) - ksPrefix ks 1 := by
              rw [zipIdx_filter_length]; exact hOuterPrefixCount
            have hOuterPrefixZipCount : ((((outerRest.take m).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))).length
                = ksPrefix ks (m + 1) - ksPrefix ks 1 := hOuterPrefixZipCountE
            have hVsMatchE := zipIdx_flatMap_filter_getElem (guessAXInnerBlockElems I) 3 2
              (fun a => guessAXInnerBlockElems_length I a) pzAxx' bvalzAxx'
              h0zAx'x htruezAx'x hfalsezAx'x
              vs ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1) j a' hvaj
            have hVsMatch : (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)))[j]?
                = some (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a'.2.2, rfl⟩,
                    (3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 2) :=
              hVsMatchE
            have hsplit1 : outerRest.take (m + 1) = outerRest.take m ++ [(b, vs)] := by
              rw [List.take_add_one, hvan]; rfl
            have hsplit2 : outerRest = outerRest.take (m + 1) ++ outerRest.drop (m + 1) :=
              (List.take_append_drop (m + 1) outerRest).symm
            rw [hHead3, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            rw [show outerRest.flatMap (fun p => guessAXOuterBlockElems I p.1 p.2)
                = (outerRest.take m).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2) ++
                  (guessAXOuterBlockElems I b vs ++
                    (outerRest.drop (m + 1)).flatMap (fun p => guessAXOuterBlockElems I p.1 p.2))
                from by
              conv_lhs => rw [hsplit2]
              rw [hsplit1]
              simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc]]
            simp only [List.zipIdx_append, List.filter_append, List.getElem?_map,
              List.append_assoc]
            have hOBSegXA : (((guessAXOuterBlockElems I b vs).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessAXOuterBlockElems I p.1 p.2)).length)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)))
                = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)) := by
              have hzAxyF := hpredNonBridgeGen Loc.zAxx' (by decide)
                (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX) OpType.rd
                (by decide : Loc.zAxy ∈ BridgeLoc)
              have hellAyxF := hpredNonBridgeGen Loc.zAxx' (by decide)
                (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX) OpType.rd
                (by decide : Loc.ellAyx ∈ BridgeLoc)
              have hunfold : guessAXOuterBlockElems I b vs =
                  (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX) ::
                    (vs.flatMap (guessAXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessAX)]) := rfl
              have hzAxyNeg : ¬ @decide ((⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.loc = Loc.zAxx' ∧
                  (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.op = OpType.rd)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX).1.loc Loc.zAxx')
                    inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.zAxy ≠ Loc.zAxx')
              have hellAyxNeg : ¬ @decide ((⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.loc = Loc.zAxx' ∧
                  (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessAX).1.op = OpType.rd)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessAX).1.loc Loc.zAxx')
                    inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.ellAyx ≠ Loc.zAxx')
              have hellAyxNeg' : (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                  ((3 * K0 + 4) + ((outerRest.take m).flatMap
                    (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 +
                    (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))
                = List.filter (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))
                    ([] : List (ThreadLabel (domainOf I) Tid.guessAX × ℕ)) := by
                rw [List.zipIdx_cons, List.zipIdx_nil]
                exact List.filter_cons_of_neg hellAyxNeg
              calc (((guessAXOuterBlockElems I b vs).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessAXOuterBlockElems I p.1 p.2)).length)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)))
                  = (((⟨EventLabel.wt Tid.guessAX Loc.zAxy b.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX),
                      (3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length) ::
                      ((vs.flatMap (guessAXInnerBlockElems I) ++
                        [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                            ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                        ((3 * K0 + 4) + ((outerRest.take m).flatMap
                          (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1))).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)) := by
                    rw [hunfold, List.zipIdx_cons]
                _ = ((vs.flatMap (guessAXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)) :=
                  List.filter_cons_of_neg hzAxyNeg
                _ = (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))) ++
                    ((([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx b.2, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 +
                        (vs.flatMap (guessAXInnerBlockElems I)).length)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))) := by
                    rw [List.zipIdx_append, List.filter_append]
                _ = (((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))) ++
                    (List.filter (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))
                      ([] : List (ThreadLabel (domainOf I) Tid.guessAX × ℕ))) :=
                  congrArg (fun x => ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)) ++ x)
                    hellAyxNeg'
                _ = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)) ++ [] := by
                    rw [List.filter_nil]
                _ = ((vs.flatMap (guessAXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd)) :=
                  List.append_nil _
            simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.reduceAdd]
            rw [show 3 + (3 * K0 + 1) = 3 * K0 + 4 from by omega]
            rw [hOBSegXA]
            have hHeadEllaLen0 : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))
                (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx (3 + 3 * K0))) = [] := by
              rfl
            have hHeadEllaLen0' : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.zAxx' ∧ p'.1.1.op = OpType.rd))
                (([(⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessAX)]).zipIdx (3 + 3 * K0))).length
                = 0 := by rw [hHeadEllaLen0]; rfl
            rw [List.getElem?_append_right
              (by rw [hInner0ZipCount]; omega),
              List.getElem?_append_right
              (by rw [hHeadEllaLen0]; simp),
              List.getElem?_append_right
              (by rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']; omega),
              List.getElem?_append_left
              (by
                have := (List.getElem?_eq_some_iff.mp hVsMatch).1
                rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']
                omega)]
            rw [hInner0ZipCount, hHeadEllaLen0', hOuterPrefixZipCount]
            rw [show ksPrefix ks (m + 1) + j - 1 - K0 - 0 - (ksPrefix ks (m + 1) - ksPrefix ks 1) = j from by
              omega]
            rw [hVsMatch]
            simp only [Option.map_some]
            have hival : 3 * K0 + 4 + ((List.take m outerRest).flatMap
                (fun p => guessAXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 2 = i := by omega
            have hlab :
                EventLabel.rd Tid.guessAX Loc.zAxx' a'.2.2 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk2
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
      · -- `p2 = 3 * vs.length + 1`: `ellAyx`, bridge — contradicts `hnb`.
        exfalso
        have hp2L' : p2 < 3 * vs.length + 2 := hp2L
        have hp2eq : p2 = 3 * vs.length + 1 := by omega
        rw [hp2eq, hOuterBlockLast'] at hgetblkn
        simp only [Option.some.injEq] at hgetblkn
        have hloc : e.loc = Loc.ellAyx := by rw [hloce, ← hgetblkn]; rfl
        have hmem : e.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.ellAyx ∈ BridgeLoc)
        exact hnb hmem


/-- Position and index of the non-bridge events of `GuessBX`'s trace, as
`guessAXInner_idPos_rawIndex`. -/
theorem guessBXInner_idPos_rawIndex (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.guessBX)
    (hnb : ¬ e.IsBridge) :
    ∃ k p, idPos e = nestedInnerStart ks k + p ∧ p < nestedCallLen k ∧
      guessBXInnerBlockShape[p]? = some (e.loc, e.op) ∧
      rawIndex trace e = if p < 2 then k else k - 1 := by
  obtain ⟨K0, hks0, hinner0⟩ := hinner0
  have hgd0 : ks.getD 0 0 = K0 := by
    show (ks[0]?).getD 0 = K0
    rw [hks0]; rfl
  obtain ⟨i, l, hget, hee⟩ := mem_traceEventsOf_iff'.mp he
  have hidPos : idPos e = i := by rw [hee]; unfold idPos traceEventId; simp [Nat.unpair_pair]
  have hloce : e.loc = l.1.loc := by rw [hee]; rfl
  have hope : e.op = l.1.op := by rw [hee]; rfl
  have hgetT : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]? = some l := by
    rw [← htrace]; exact hget
  have hFlatLen : ∀ vals : List (Val I × Val I × Val I),
      (vals.flatMap (guessBXInnerBlockElems I)).length = 3 * vals.length := by
    intro vals
    rw [List.length_flatMap]
    have heq : vals.map (fun a => (guessBXInnerBlockElems I a).length) = vals.map (fun _ => 3) :=
      List.map_congr_left (fun a _ => guessBXInnerBlockElems_length I a)
    rw [heq, List.map_const', List.sum_const_nat, Nat.mul_comm]
  have hBlen : (inner0Rest.flatMap (guessBXInnerBlockElems I)).length = 3 * K0 := by
    rw [hFlatLen, hinner0]
  have hrawop : ∀ (x : Loc) (op : OpType), rawOpEvents trace Tid.guessBX x op =
      (((trace Tid.guessBX).zipIdx).filter
          (fun p' => decide (p'.1.1.loc = x ∧ p'.1.1.op = op))).map
        (fun p' => (⟨traceEventId (D := domainOf I) Tid.guessBX p'.2, p'.1.1⟩ :
            Event (domainOf I))) := by
    intro x op
    unfold rawOpEvents traceEventsOf
    rw [List.filter_map]
    congr 1
  have hpredNonBridgeGen : ∀ (y : Loc), y ∉ BridgeLoc →
      ∀ (b0 : ThreadLabel (domainOf I) Tid.guessBX) (op0 : OpType),
      b0.1.loc ∈ BridgeLoc →
      @decide (b0.1.loc = y ∧ b0.1.op = op0)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b0.1.loc y) inferInstance) = false := by
    intro y hy b0 op0 hmem
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    rw [hloc] at hmem
    exact hy hmem
  -- `guessBXInnerBlockElems`'s three marked positions, for each of the three inner
  -- predicates: the position itself (`h0_X`) and the fact no other position matches (`hfalse_X`).
  -- Shared by the `inner0Rest` branch below and the `outerRest` (TAIL) branch.
  have h0_xB : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a)[(0 : ℕ)]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) :=
    fun _ => rfl
  have hfalse_xB : ∀ (a : Val I × Val I × Val I) (q : ℕ) (b : ThreadLabel (domainOf I) Tid.guessBX),
      q ≠ 0 → (guessBXInnerBlockElems I a)[q]? = some b →
      @decide (b.1.loc = Loc.xB ∧ b.1.op = OpType.wt)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b.1.loc Loc.xB) inferInstance) = false := by
    rintro ⟨a1, a2, a3⟩ q b hq0 hqget
    have hqlt : q < 3 := by
      have := (List.getElem?_eq_some_iff.mp hqget).1
      simpa [guessBXInnerBlockElems_length] using this
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    have hq12 : q = 1 ∨ q = 2 := by omega
    rcases hq12 with rfl | rfl
    · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.zBx'x ≠ Loc.xB)
    · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.zBxx' ≠ Loc.xB)
  have h0_zBx'x : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a)[(1 : ℕ)]? =
      some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) :=
    fun _ => rfl
  have hfalse_zBx'x : ∀ (a : Val I × Val I × Val I) (q : ℕ) (b : ThreadLabel (domainOf I) Tid.guessBX),
      q ≠ 1 → (guessBXInnerBlockElems I a)[q]? = some b →
      @decide (b.1.loc = Loc.zBx'x ∧ b.1.op = OpType.wt)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b.1.loc Loc.zBx'x) inferInstance) = false := by
    rintro ⟨a1, a2, a3⟩ q b hq1 hqget
    have hqlt : q < 3 := by
      have := (List.getElem?_eq_some_iff.mp hqget).1
      simpa [guessBXInnerBlockElems_length] using this
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    have hq02 : q = 0 ∨ q = 2 := by omega
    rcases hq02 with rfl | rfl
    · simp only [guessBXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.xB ≠ Loc.zBx'x)
    · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.zBxx' ≠ Loc.zBx'x)
  have h0_zBxx' : ∀ a : Val I × Val I × Val I, (guessBXInnerBlockElems I a)[(2 : ℕ)]? =
      some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX) :=
    fun _ => rfl
  have hfalse_zBxx' : ∀ (a : Val I × Val I × Val I) (q : ℕ) (b : ThreadLabel (domainOf I) Tid.guessBX),
      q ≠ 2 → (guessBXInnerBlockElems I a)[q]? = some b →
      @decide (b.1.loc = Loc.zBxx' ∧ b.1.op = OpType.rd)
        (@instDecidableAnd _ _ ((domainOf I).locDecEq b.1.loc Loc.zBxx') inferInstance) = false := by
    rintro ⟨a1, a2, a3⟩ q b hq2 hqget
    have hqlt : q < 3 := by
      have := (List.getElem?_eq_some_iff.mp hqget).1
      simpa [guessBXInnerBlockElems_length] using this
    simp only [decide_eq_false_iff_not]
    rintro ⟨hloc, -⟩
    have hq01 : q = 0 ∨ q = 1 := by omega
    rcases hq01 with rfl | rfl
    · simp only [guessBXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.xB ≠ Loc.zBxx')
    · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hqget
      rw [← hqget] at hloc
      exact absurd hloc (by decide : Loc.zBx'x ≠ Loc.zBxx')
  rcases Nat.lt_or_ge i (3 * K0 + 4) with hi | hi
  · -- HEAD case: `e` sits among the head's three literal events or `inner0Rest`.
    have hget1 : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]?
        = (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                ThreadLabel (domainOf I) Tid.guessBX)
            , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
            , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ] ++
            inner0Rest.flatMap (guessBXInnerBlockElems I) ++
            [ ⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ ]))[i]? := by
      unfold guessBXBlockWord
      rw [List.getElem?_append_left
        (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)]
    rw [hget1] at hgetT
    rcases Nat.lt_or_ge i (3 + 3 * K0) with hi2 | hi2
    · rw [List.getElem?_append_left
          (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)] at hgetT
      rcases Nat.lt_or_ge i 3 with hi3 | hi3
      · rw [List.getElem?_append_left (by simpa using hi3)] at hgetT
        have hi012 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi012 with rfl | rfl | rfl
        · -- position 0: `zBxy`, bridge — contradicts `hnb`.
          exfalso
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have hloc : e.loc = Loc.zBxy := by rw [hloce, ← hgetT]; rfl
          have hmem : e.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.zBxy ∈ BridgeLoc)
          exact hnb hmem
        · -- position 1: `xB`, call `0`, `p = 0`.
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have heloc : e.loc = Loc.xB := by rw [hloce, ← hgetT]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetT]; rfl
          refine ⟨0, 0, ?_, by norm_num [nestedCallLen], ?_, ?_⟩
          · rw [hidPos]; simp [nestedInnerStart]
          · rw [heloc, heop]; rfl
          · have hnth : rawNthEvent trace Tid.guessBX Loc.xB OpType.wt 0 = some e := by
              unfold rawNthEvent
              rw [hrawop, htrace]
              unfold guessBXBlockWord
              simp only [List.zipIdx_append, List.filter_append]
              have hHead3 :
                  (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessBX)
                      , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                      , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                    (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))
                    = [(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩, 1)] := by rfl
              rw [hHead3]
              simp only [List.cons_append, List.map_cons, List.getElem?_cons_zero]
              rw [hee, ← hgetT]
            exact rawNthEvent_rawIndex hnth
        · -- position 2: `zBx'x`, call `0`, `p = 1`.
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hgetT
          have heloc : e.loc = Loc.zBx'x := by rw [hloce, ← hgetT]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetT]; rfl
          refine ⟨0, 1, ?_, by norm_num [nestedCallLen], ?_, ?_⟩
          · rw [hidPos]; simp [nestedInnerStart]
          · rw [heloc, heop]; rfl
          · have hnth : rawNthEvent trace Tid.guessBX Loc.zBx'x OpType.wt 0 = some e := by
              unfold rawNthEvent
              rw [hrawop, htrace]
              unfold guessBXBlockWord
              simp only [List.zipIdx_append, List.filter_append]
              have hHead3 :
                  (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessBX)
                      , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                      , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))
                    = [(⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩, 2)] := by rfl
              rw [hHead3]
              simp only [List.cons_append, List.map_cons, List.getElem?_cons_zero]
              rw [hee, ← hgetT]
            exact rawNthEvent_rawIndex hnth
      · -- `3 ≤ i < 3 + 3 * K0`: within `inner0Rest`'s flatMap.
        rw [List.getElem?_append_right (by simpa using hi3)] at hgetT
        simp only [List.length_cons, List.length_nil, show 1 + 1 + 1 = 3 from rfl] at hgetT
        have hilt : i - 3 < inner0Rest.length * 3 := by rw [hinner0]; omega
        obtain ⟨n, p, a, hpL, hoffnp, hvan, heqget⟩ :=
          flatMap_uniform_getElem (guessBXInnerBlockElems I) 3
            (fun a => guessBXInnerBlockElems_length I a) inner0Rest (i - 3) hilt
        rw [heqget] at hgetT
        have hgetblk : (guessBXInnerBlockElems I a)[p]? = some l := hgetT
        have hnlt : n < inner0Rest.length := (List.getElem?_eq_some_iff.mp hvan).1
        have hnK0 : n < K0 := by rw [← hinner0]; exact hnlt
        have h0lt : 0 < ks.length := by omega
        have hk0eq : ks[0]'h0lt = K0 :=
          Option.some.inj ((List.getElem?_eq_getElem h0lt).symm.trans hks0)
        have hstart : nestedInnerStart ks (n + 1) = 3 * (n + 1) :=
          nestedInnerStart_inner0Rest ks h0lt n (by rw [hk0eq]; exact hnK0)
        have hoffidPos : idPos e = nestedInnerStart ks (n + 1) + p := by
          rw [hidPos, hstart]; omega
        have hcalllen : nestedCallLen (n + 1) = 3 := by
          unfold nestedCallLen; rw [if_neg (by omega)]
        have hplt3 : p < nestedCallLen (n + 1) := by rw [hcalllen]; exact hpL
        have hp012 : p = 0 ∨ p = 1 ∨ p = 2 := by omega
        rcases hp012 with rfl | rfl | rfl
        · -- `p = 0`: `xB`, target rawIndex `n + 1`.
          have hgetblk0 := hgetblk
          rw [h0_xB a] at hgetblk0
          simp only [Option.some.injEq] at hgetblk0
          have heloc : e.loc = Loc.xB := by rw [hloce, ← hgetblk0]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetblk0]; rfl
          refine ⟨n + 1, 0, hoffidPos, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show (0 : ℕ) < 2 from by omega, if_true]
          have hnth : rawNthEvent trace Tid.guessBX Loc.xB OpType.wt (n + 1) = some e := by
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessBXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))
                  = [(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩, 1)] := by rfl
            have hInnerMatch := zipIdx_flatMap_filter_getElem (guessBXInnerBlockElems I) 3 0
              (fun a => guessBXInnerBlockElems_length I a)
              (fun p' => @decide (p'.1.loc = Loc.xB ∧ p'.1.op = OpType.wt)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.xB) inferInstance))
              (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX))
              h0_xB (fun _ => rfl) hfalse_xB
              inner0Rest 3 n a hvan
            have hInnerMatch' : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)))[n]?
                = some (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩, 3 + n * 3 + 0) := hInnerMatch
            rw [hHead3]
            simp only [List.cons_append, List.map_cons, List.getElem?_cons_succ, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            have hmapped := congrArg (Option.map (fun p' =>
              (⟨traceEventId (D := domainOf I) Tid.guessBX p'.2, p'.1.1⟩ : Event (domainOf I))))
              hInnerMatch'
            rw [Option.map_some] at hmapped
            rw [List.getElem?_map,
              List.getElem?_append_left (by
                rw [List.length_append]
                have := (List.getElem?_eq_some_iff.mp hInnerMatch').1
                omega),
              List.getElem?_append_left (List.getElem?_eq_some_iff.mp hInnerMatch').1]
            refine hmapped.trans ?_
            have hival : 3 + n * 3 + 0 = i := by omega
            have hlab : EventLabel.wt Tid.guessBX Loc.xB a.1 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk0
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · -- `p = 1`: `zBx'x`, target rawIndex `n + 1`.
          have hgetblk1 := hgetblk
          rw [h0_zBx'x a] at hgetblk1
          simp only [Option.some.injEq] at hgetblk1
          have heloc : e.loc = Loc.zBx'x := by rw [hloce, ← hgetblk1]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetblk1]; rfl
          refine ⟨n + 1, 1, hoffidPos, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show (1 : ℕ) < 2 from by omega, if_true]
          have hnth : rawNthEvent trace Tid.guessBX Loc.zBx'x OpType.wt (n + 1) = some e := by
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessBXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))
                  = [(⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩, 2)] := by rfl
            have hInnerMatch := zipIdx_flatMap_filter_getElem (guessBXInnerBlockElems I) 3 1
              (fun a => guessBXInnerBlockElems_length I a)
              (fun p' => @decide (p'.1.loc = Loc.zBx'x ∧ p'.1.op = OpType.wt)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.zBx'x) inferInstance))
              (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX))
              h0_zBx'x (fun _ => rfl) hfalse_zBx'x
              inner0Rest 3 n a hvan
            have hInnerMatch' : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)))[n]?
                = some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩, 3 + n * 3 + 1) := hInnerMatch
            rw [hHead3]
            simp only [List.cons_append, List.map_cons, List.getElem?_cons_succ, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            have hmapped := congrArg (Option.map (fun p' =>
              (⟨traceEventId (D := domainOf I) Tid.guessBX p'.2, p'.1.1⟩ : Event (domainOf I))))
              hInnerMatch'
            rw [Option.map_some] at hmapped
            rw [List.getElem?_map,
              List.getElem?_append_left (by
                rw [List.length_append]
                have := (List.getElem?_eq_some_iff.mp hInnerMatch').1
                omega),
              List.getElem?_append_left (List.getElem?_eq_some_iff.mp hInnerMatch').1]
            refine hmapped.trans ?_
            have hival : 3 + n * 3 + 1 = i := by omega
            have hlab : EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk1
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · -- `p = 2`: `zBxx'`, target rawIndex `n` (call `0`'s skipped read).
          have hgetblk2 := hgetblk
          rw [h0_zBxx' a] at hgetblk2
          simp only [Option.some.injEq] at hgetblk2
          have heloc : e.loc = Loc.zBxx' := by rw [hloce, ← hgetblk2]; rfl
          have heop : e.op = OpType.rd := by rw [hope, ← hgetblk2]; rfl
          refine ⟨n + 1, 2, hoffidPos, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show ¬ (2 : ℕ) < 2 from by omega, if_false]
          have hnth : rawNthEvent trace Tid.guessBX Loc.zBxx' OpType.rd n = some e := by
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessBXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))
                  = [] := by rfl
            have hInnerMatch := zipIdx_flatMap_filter_getElem (guessBXInnerBlockElems I) 3 2
              (fun a => guessBXInnerBlockElems_length I a)
              (fun p' => @decide (p'.1.loc = Loc.zBxx' ∧ p'.1.op = OpType.rd)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq p'.1.loc Loc.zBxx') inferInstance))
              (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX))
              h0_zBxx' (fun _ => rfl) hfalse_zBxx'
              inner0Rest 3 n a hvan
            have hInnerMatch' : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)))[n]?
                = some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩, 3 + n * 3 + 2) := hInnerMatch
            rw [hHead3, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            have hmapped := congrArg (Option.map (fun p' =>
              (⟨traceEventId (D := domainOf I) Tid.guessBX p'.2, p'.1.1⟩ : Event (domainOf I))))
              hInnerMatch'
            rw [Option.map_some] at hmapped
            rw [List.getElem?_map,
              List.getElem?_append_left (by
                rw [List.length_append]
                have := (List.getElem?_eq_some_iff.mp hInnerMatch').1
                omega),
              List.getElem?_append_left (List.getElem?_eq_some_iff.mp hInnerMatch').1]
            refine hmapped.trans ?_
            have hival : 3 + n * 3 + 2 = i := by omega
            have hlab : EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk2
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
    · -- `i = 3 + 3 * K0`: `ellByx`, bridge — contradicts `hnb`.
      exfalso
      have hieq : i = 3 + 3 * K0 := by omega
      rw [List.getElem?_append_right
          (by simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega)] at hgetT
      simp only [List.length_append, List.length_cons, List.length_nil, hBlen] at hgetT
      have hzero : i - (3 + 3 * K0) = 0 := by omega
      rw [hzero] at hgetT
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hgetT
      have hloc : e.loc = Loc.ellByx := by rw [hloce, ← hgetT]; rfl
      have hmem : e.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.ellByx ∈ BridgeLoc)
      exact hnb hmem
  · -- TAIL case: some `outerRest[m]`, outer iteration `M := m + 1`.
    have hget2 : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)[i]?
        = (outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2))[i - (3 * K0 + 4)]? := by
      unfold guessBXBlockWord
      rw [List.getElem?_append_right]
      · congr 1
        simp [List.length_append, List.length_cons, hBlen]
      · simp only [List.length_append, List.length_cons, List.length_nil, hBlen]; omega
    rw [hget2] at hgetT
    have hqlt : i - (3 * K0 + 4) <
        (outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)).length :=
      (List.getElem?_eq_some_iff.mp hgetT).1
    obtain ⟨m, p2, ⟨b, vs⟩, hp2L, hvan, hoffn, heqgetn⟩ :=
      flatMap_getElem_of_lengths (fun p => guessBXOuterBlockElems I p.1 p.2) outerRest
        (i - (3 * K0 + 4)) hqlt
    rw [guessBXOuterBlockElems_length] at hp2L
    have hgetblkn : (guessBXOuterBlockElems I b vs)[p2]? = some l := by
      rw [← heqgetn]; exact hgetT
    have hoffidPos : idPos e = (3 * K0 + 4) + (((outerRest.take m).flatMap
        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + p2) := by
      rw [hidPos]; omega
    have hmlt : m < outerRest.length := (List.getElem?_eq_some_iff.mp hvan).1
    have hstartrel : nestedOuterStart ks N (m + 1)
        = (3 * K0 + 4) + ((outerRest.take m).flatMap
            (fun p => guessBXOuterBlockElems I p.1 p.2)).length := by
      have hp := guessBXOuterRest_prefix_length I ks N hks outerRest houterLen houter houterLast m
        (by omega)
      have hge1 : nestedOuterStart ks N 1 ≤ nestedOuterStart ks N (m + 1) :=
        nestedOuterStart_mono ks N (by omega)
      have hns1 : nestedOuterStart ks N 1 = 3 * K0 + 4 := by
        show nestedOuterStart ks N 0 + nestedOuterLen ks N 0 = 3 * K0 + 4
        rw [show nestedOuterStart ks N 0 = 0 from rfl]
        unfold nestedOuterLen
        rw [if_neg (show (0 : ℕ) ≠ N + 1 by omega), if_pos rfl, hgd0]
        omega
      omega
    have hp0Z' : (guessBXOuterBlockElems I b vs)[(0 : ℕ)]?
        = some (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX) := rfl
    have hOuterBlockLast' : (guessBXOuterBlockElems I b vs)[3 * vs.length + 1]?
        = some (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX) := by
      unfold guessBXOuterBlockElems
      rw [show 3 * vs.length + 1 = (3 * vs.length) + 1 from rfl, List.getElem?_cons_succ,
        List.getElem?_append_right (by rw [hFlatLen]), hFlatLen]
      simp
    rcases Nat.eq_zero_or_pos p2 with hp2z | hp2pos
    · -- `p2 = 0`: `zBxy`, bridge — contradicts `hnb`.
      exfalso
      subst hp2z
      rw [hp0Z'] at hgetblkn
      simp only [Option.some.injEq] at hgetblkn
      have hloc : e.loc = Loc.zBxy := by rw [hloce, ← hgetblkn]; rfl
      have hmem : e.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.zBxy ∈ BridgeLoc)
      exact hnb hmem
    · by_cases hp2le : p2 ≤ 3 * vs.length
      · -- `1 ≤ p2 ≤ 3 * vs.length`: an inner call within outer iteration `m + 1`.
        have hp2sub : p2 - 1 < vs.length * 3 := by omega
        obtain ⟨j, p, a', hpL', hoffjp, hvaj, heqgetj⟩ :=
          flatMap_uniform_getElem (guessBXInnerBlockElems I) 3
            (fun a => guessBXInnerBlockElems_length I a) vs (p2 - 1) hp2sub
        have hgetblkn2 : (guessBXInnerBlockElems I a')[p]? = some l := by
          have hstep : (guessBXOuterBlockElems I b vs)[p2]?
              = (vs.flatMap (guessBXInnerBlockElems I))[p2 - 1]? := by
            unfold guessBXOuterBlockElems
            rw [show p2 = (p2 - 1) + 1 from by omega, List.getElem?_cons_succ,
              List.getElem?_append_left (by rw [hFlatLen]; omega)]
            congr 1
          rw [hstep, heqgetj] at hgetblkn
          exact hgetblkn
        have hinnerStart : nestedInnerStart ks (ksPrefix ks (m + 1) + j)
            = nestedInnerStart ks (ksPrefix ks (m + 1)) + 3 * j := by
          rcases Nat.lt_or_ge m N with hmN | hmN
          · obtain ⟨b', vs', km, hb'vs', hksm, hlen'⟩ := houter m hmN
            rw [hvan] at hb'vs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'vs'
            have hvslen : vs.length = km + 1 := by rw [hb'vs'.2]; exact hlen'
            have hjlt : j < vs.length := (List.getElem?_eq_some_iff.mp hvaj).1
            have hm1lt : m + 1 < ks.length := by omega
            have hkeq : ks[m + 1]'hm1lt = km :=
              Option.some.inj ((List.getElem?_eq_getElem hm1lt).symm.trans hksm)
            exact nestedInnerStart_outerRest_add ks m hm1lt j (by rw [hkeq]; omega)
          · have hmN' : m = N := by omega
            obtain ⟨b', vs', hb'vs', hlen'⟩ := houterLast
            rw [hmN'] at hvan
            rw [hvan] at hb'vs'
            simp only [Option.some.injEq, Prod.mk.injEq] at hb'vs'
            have hvslen : vs.length = 1 := by rw [hb'vs'.2]; exact hlen'
            have hjlt : j < vs.length := (List.getElem?_eq_some_iff.mp hvaj).1
            have hj0 : j = 0 := by omega
            subst hj0
            simp
        have hcrosstier : nestedOuterStart ks N (m + 1) + 1
            = nestedInnerStart ks (ksPrefix ks (m + 1)) :=
          nestedOuterStart_succ_eq_innerStart ks N (m + 1) hks (by omega)
        have hoffidPos2 : idPos e = nestedInnerStart ks (ksPrefix ks (m + 1) + j) + p := by
          rw [hinnerStart]
          omega
        have hcalllen : nestedCallLen (ksPrefix ks (m + 1) + j) = 3 := by
          have hpos : ksPrefix ks (m + 1) ≠ 0 := by rw [Ne, ksPrefix_eq_zero_iff]; omega
          unfold nestedCallLen; rw [if_neg (by omega)]
        have hplt3 : p < nestedCallLen (ksPrefix ks (m + 1) + j) := by rw [hcalllen]; exact hpL'
        have hns1' : ksPrefix ks 1 = K0 + 1 := by
          show ksPrefix ks 0 + (ks.getD 0 0 + 1) = K0 + 1
          rw [show ksPrefix ks 0 = 0 from rfl, hgd0]
          omega
        have hmono1 : ksPrefix ks 1 ≤ ksPrefix ks (m + 1) := ksPrefix_mono ks (by omega)
        have hp012 : p = 0 ∨ p = 1 ∨ p = 2 := by omega
        rcases hp012 with rfl | rfl | rfl
        · -- `p = 0`: `xB`.
          have hgetblk0 := hgetblkn2
          rw [h0_xB a'] at hgetblk0
          simp only [Option.some.injEq] at hgetblk0
          have heloc : e.loc = Loc.xB := by rw [hloce, ← hgetblk0]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetblk0]; rfl
          refine ⟨ksPrefix ks (m + 1) + j, 0, hoffidPos2, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show (0 : ℕ) < 2 from by omega, if_true]
          have hnth : rawNthEvent trace Tid.guessBX Loc.xB OpType.wt
              (ksPrefix ks (m + 1) + j) = some e := by
            let pxB : ThreadLabel (domainOf I) Tid.guessBX → Bool := fun l' =>
              @decide (l'.1.loc = Loc.xB ∧ l'.1.op = OpType.wt)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq l'.1.loc Loc.xB) inferInstance)
            let bvalxB : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX :=
              fun a => ⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩
            have h0xB' : ∀ a, (guessBXInnerBlockElems I a)[(0 : ℕ)]? = some (bvalxB a) := h0_xB
            have hfalsexB' : ∀ (a : Val I × Val I × Val I) (q : ℕ)
                (b0 : ThreadLabel (domainOf I) Tid.guessBX),
                q ≠ 0 → (guessBXInnerBlockElems I a)[q]? = some b0 → pxB b0 = false := hfalse_xB
            have htruexB' : ∀ a, pxB (bvalxB a) = true := fun _ => rfl
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessBXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3E :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => pxB p'.1)
                  = [(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩, 1)] := by rfl
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))
                  = [(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩, 1)] := hHead3E
            have hInner0Count : ((inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
                pxB).length = K0 := by
              rw [guessBXInnerBlockElems_filter I pxB 0 bvalxB h0xB' htruexB' hfalsexB']
              simp [hinner0]
            have hInner0ZipCountE : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => pxB p'.1)).length = K0 := by
              rw [zipIdx_filter_length]; exact hInner0Count
            have hInner0ZipCount : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))).length = K0 :=
              hInner0ZipCountE
            have hOuterPrefixCount : (((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).filter pxB).length = ksPrefix ks (m + 1) - ksPrefix ks 1 :=
              guessBXOuterRest_prefix_matchCount I ks N hks outerRest houter pxB 0 bvalxB
                h0xB' htruexB' hfalsexB'
                (fun b0 hb0 => hpredNonBridgeGen Loc.xB (by decide) b0 OpType.wt hb0)
                m (by omega)
            have hOuterPrefixZipCountE : ((((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => pxB p'.1)).length = ksPrefix ks (m + 1) - ksPrefix ks 1 := by
              rw [zipIdx_filter_length]; exact hOuterPrefixCount
            have hOuterPrefixZipCount : ((((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))).length
                = ksPrefix ks (m + 1) - ksPrefix ks 1 := hOuterPrefixZipCountE
            have hVsMatchE := zipIdx_flatMap_filter_getElem (guessBXInnerBlockElems I) 3 0
              (fun a => guessBXInnerBlockElems_length I a) pxB bvalxB
              h0xB' htruexB' hfalsexB'
              vs ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1) j a' hvaj
            have hVsMatch : (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)))[j]?
                = some (⟨EventLabel.wt Tid.guessBX Loc.xB a'.1, rfl⟩,
                    (3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 0) :=
              hVsMatchE
            have hsplit1 : outerRest.take (m + 1) = outerRest.take m ++ [(b, vs)] := by
              rw [List.take_add_one, hvan]; rfl
            have hsplit2 : outerRest = outerRest.take (m + 1) ++ outerRest.drop (m + 1) :=
              (List.take_append_drop (m + 1) outerRest).symm
            have hpos : (m + 1) * (K0 + 1) ≥ 1 :=
              Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
            have hposK0 : (m + 1) * (K0 + 1) ≥ K0 + 1 := by
              have h1 := Nat.mul_le_mul_right (K0 + 1) (show 1 ≤ m + 1 by omega)
              simp [h1]
            rw [show ksPrefix ks (m + 1) + j = (ksPrefix ks (m + 1) + j - 1) + 1 from by omega]
            rw [hHead3]
            simp only [List.cons_append, List.map_cons, List.getElem?_cons_succ, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            rw [show outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)
                = (outerRest.take m).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2) ++
                  (guessBXOuterBlockElems I b vs ++
                    (outerRest.drop (m + 1)).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2))
                from by
              conv_lhs => rw [hsplit2]
              rw [hsplit1]
              simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc]]
            simp only [List.zipIdx_append, List.filter_append, List.getElem?_map,
              List.append_assoc]
            have hOBSegXB : (((guessBXOuterBlockElems I b vs).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length)).filter
                (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)))
                = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)) := by
              have hzBxyF := hpredNonBridgeGen Loc.xB (by decide)
                (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX) OpType.wt
                (by decide : Loc.zBxy ∈ BridgeLoc)
              have hellByxF := hpredNonBridgeGen Loc.xB (by decide)
                (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX) OpType.rd
                (by decide : Loc.ellByx ∈ BridgeLoc)
              have hunfold : guessBXOuterBlockElems I b vs =
                  (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX) ::
                    (vs.flatMap (guessBXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessBX)]) := rfl
              have hzBxyNeg : ¬ @decide ((⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.loc = Loc.xB ∧
                  (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.op = OpType.wt)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX).1.loc Loc.xB) inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.zBxy ≠ Loc.xB)
              have hellByxNeg : ¬ @decide ((⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.loc = Loc.xB ∧
                  (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.op = OpType.wt)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX).1.loc Loc.xB) inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.ellByx ≠ Loc.xB)
              have hellByxNeg' : (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                  ((3 * K0 + 4) + ((outerRest.take m).flatMap
                    (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 +
                    (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))
                = List.filter (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))
                    ([] : List (ThreadLabel (domainOf I) Tid.guessBX × ℕ)) := by
                rw [List.zipIdx_cons, List.zipIdx_nil]
                exact List.filter_cons_of_neg hellByxNeg
              calc (((guessBXOuterBlockElems I b vs).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)))
                  = (((⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX),
                      (3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length) ::
                      ((vs.flatMap (guessBXInnerBlockElems I) ++
                        [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                            ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                        ((3 * K0 + 4) + ((outerRest.take m).flatMap
                          (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1))).filter
                    (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)) := by
                    rw [hunfold, List.zipIdx_cons]
                _ = ((vs.flatMap (guessBXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)) :=
                  List.filter_cons_of_neg hzBxyNeg
                _ = (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))) ++
                    ((([(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 +
                        (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))) := by
                    rw [List.zipIdx_append, List.filter_append]
                _ = (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))) ++
                    (List.filter (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))
                      ([] : List (ThreadLabel (domainOf I) Tid.guessBX × ℕ))) :=
                  congrArg (fun x => ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)) ++ x)
                    hellByxNeg'
                _ = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)) ++ [] := by
                    rw [List.filter_nil]
                _ = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt)) :=
                  List.append_nil _
            simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.reduceAdd]
            rw [show 3 * K0 + 1 + 1 + 1 + 1 = 3 * K0 + 4 from by omega]
            rw [hOBSegXB]
            have hHeadEllaLen0 : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))
                (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx (3 * K0 + 1 + 1 + 1))) = [] := by
              rfl
            have hHeadEllaLen0' : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.xB ∧ p'.1.1.op = OpType.wt))
                (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx (3 * K0 + 1 + 1 + 1))).length
                = 0 := by rw [hHeadEllaLen0]; rfl
            rw [List.getElem?_append_right
              (by rw [hInner0ZipCount]; omega),
              List.getElem?_append_right
              (by rw [hHeadEllaLen0]; simp),
              List.getElem?_append_right
              (by rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']; omega),
              List.getElem?_append_left
              (by
                have := (List.getElem?_eq_some_iff.mp hVsMatch).1
                rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']
                omega)]
            rw [hInner0ZipCount, hHeadEllaLen0', hOuterPrefixZipCount]
            rw [show ksPrefix ks (m + 1) + j - 1 - K0 - 0 - (ksPrefix ks (m + 1) - ksPrefix ks 1) = j from by
              omega]
            rw [hVsMatch]
            simp only [Option.map_some]
            have hival : 3 * K0 + 4 + ((List.take m outerRest).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 0 = i := by omega
            have hlab : EventLabel.wt Tid.guessBX Loc.xB a'.1 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk0
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · -- `p = 1`: `zBx'x`.
          have hgetblk1 := hgetblkn2
          rw [h0_zBx'x a'] at hgetblk1
          simp only [Option.some.injEq] at hgetblk1
          have heloc : e.loc = Loc.zBx'x := by rw [hloce, ← hgetblk1]; rfl
          have heop : e.op = OpType.wt := by rw [hope, ← hgetblk1]; rfl
          refine ⟨ksPrefix ks (m + 1) + j, 1, hoffidPos2, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show (1 : ℕ) < 2 from by omega, if_true]
          have hnth : rawNthEvent trace Tid.guessBX Loc.zBx'x OpType.wt
              (ksPrefix ks (m + 1) + j) = some e := by
            let pzBx'x : ThreadLabel (domainOf I) Tid.guessBX → Bool := fun l' =>
              @decide (l'.1.loc = Loc.zBx'x ∧ l'.1.op = OpType.wt)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq l'.1.loc Loc.zBx'x) inferInstance)
            let bvalzBx'x : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX :=
              fun a => ⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩
            have h0zBx'x' : ∀ a, (guessBXInnerBlockElems I a)[(1 : ℕ)]? = some (bvalzBx'x a) := h0_zBx'x
            have hfalsezBx'x' : ∀ (a : Val I × Val I × Val I) (q : ℕ)
                (b0 : ThreadLabel (domainOf I) Tid.guessBX),
                q ≠ 1 → (guessBXInnerBlockElems I a)[q]? = some b0 → pzBx'x b0 = false := hfalse_zBx'x
            have htruezBx'x' : ∀ a, pzBx'x (bvalzBx'x a) = true := fun _ => rfl
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessBXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3E :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => pzBx'x p'.1)
                  = [(⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩, 2)] := by rfl
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))
                  = [(⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩, 2)] := hHead3E
            have hInner0Count : ((inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
                pzBx'x).length = K0 := by
              rw [guessBXInnerBlockElems_filter I pzBx'x 1 bvalzBx'x h0zBx'x' htruezBx'x' hfalsezBx'x']
              simp [hinner0]
            have hInner0ZipCountE : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => pzBx'x p'.1)).length = K0 := by
              rw [zipIdx_filter_length]; exact hInner0Count
            have hInner0ZipCount : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))).length = K0 :=
              hInner0ZipCountE
            have hOuterPrefixCount : (((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).filter pzBx'x).length = ksPrefix ks (m + 1) - ksPrefix ks 1 :=
              guessBXOuterRest_prefix_matchCount I ks N hks outerRest houter pzBx'x 1 bvalzBx'x
                h0zBx'x' htruezBx'x' hfalsezBx'x'
                (fun b0 hb0 => hpredNonBridgeGen Loc.zBx'x (by decide) b0 OpType.wt hb0)
                m (by omega)
            have hOuterPrefixZipCountE : ((((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => pzBx'x p'.1)).length = ksPrefix ks (m + 1) - ksPrefix ks 1 := by
              rw [zipIdx_filter_length]; exact hOuterPrefixCount
            have hOuterPrefixZipCount : ((((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))).length
                = ksPrefix ks (m + 1) - ksPrefix ks 1 := hOuterPrefixZipCountE
            have hVsMatchE := zipIdx_flatMap_filter_getElem (guessBXInnerBlockElems I) 3 1
              (fun a => guessBXInnerBlockElems_length I a) pzBx'x bvalzBx'x
              h0zBx'x' htruezBx'x' hfalsezBx'x'
              vs ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1) j a' hvaj
            have hVsMatch : (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)))[j]?
                = some (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a'.2.1, rfl⟩,
                    (3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 1) :=
              hVsMatchE
            have hsplit1 : outerRest.take (m + 1) = outerRest.take m ++ [(b, vs)] := by
              rw [List.take_add_one, hvan]; rfl
            have hsplit2 : outerRest = outerRest.take (m + 1) ++ outerRest.drop (m + 1) :=
              (List.take_append_drop (m + 1) outerRest).symm
            have hpos : (m + 1) * (K0 + 1) ≥ 1 :=
              Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
            have hposK0 : (m + 1) * (K0 + 1) ≥ K0 + 1 := by
              have h1 := Nat.mul_le_mul_right (K0 + 1) (show 1 ≤ m + 1 by omega)
              simp [h1]
            rw [show ksPrefix ks (m + 1) + j = (ksPrefix ks (m + 1) + j - 1) + 1 from by omega]
            rw [hHead3]
            simp only [List.cons_append, List.map_cons, List.getElem?_cons_succ, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            rw [show outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)
                = (outerRest.take m).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2) ++
                  (guessBXOuterBlockElems I b vs ++
                    (outerRest.drop (m + 1)).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2))
                from by
              conv_lhs => rw [hsplit2]
              rw [hsplit1]
              simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc]]
            simp only [List.zipIdx_append, List.filter_append, List.getElem?_map,
              List.append_assoc]
            have hOBSegXB : (((guessBXOuterBlockElems I b vs).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)))
                = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)) := by
              have hzBxyF := hpredNonBridgeGen Loc.zBx'x (by decide)
                (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX) OpType.wt
                (by decide : Loc.zBxy ∈ BridgeLoc)
              have hellByxF := hpredNonBridgeGen Loc.zBx'x (by decide)
                (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX) OpType.rd
                (by decide : Loc.ellByx ∈ BridgeLoc)
              have hunfold : guessBXOuterBlockElems I b vs =
                  (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX) ::
                    (vs.flatMap (guessBXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessBX)]) := rfl
              have hzBxyNeg : ¬ @decide ((⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.loc = Loc.zBx'x ∧
                  (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.op = OpType.wt)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX).1.loc Loc.zBx'x) inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.zBxy ≠ Loc.zBx'x)
              have hellByxNeg : ¬ @decide ((⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.loc = Loc.zBx'x ∧
                  (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.op = OpType.wt)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX).1.loc Loc.zBx'x) inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.ellByx ≠ Loc.zBx'x)
              have hellByxNeg' : (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                  ((3 * K0 + 4) + ((outerRest.take m).flatMap
                    (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 +
                    (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))
                = List.filter (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))
                    ([] : List (ThreadLabel (domainOf I) Tid.guessBX × ℕ)) := by
                rw [List.zipIdx_cons, List.zipIdx_nil]
                exact List.filter_cons_of_neg hellByxNeg
              calc (((guessBXOuterBlockElems I b vs).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)))
                  = (((⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX),
                      (3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length) ::
                      ((vs.flatMap (guessBXInnerBlockElems I) ++
                        [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                            ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                        ((3 * K0 + 4) + ((outerRest.take m).flatMap
                          (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1))).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)) := by
                    rw [hunfold, List.zipIdx_cons]
                _ = ((vs.flatMap (guessBXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)) :=
                  List.filter_cons_of_neg hzBxyNeg
                _ = (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))) ++
                    ((([(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 +
                        (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))) := by
                    rw [List.zipIdx_append, List.filter_append]
                _ = (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))) ++
                    (List.filter (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))
                      ([] : List (ThreadLabel (domainOf I) Tid.guessBX × ℕ))) :=
                  congrArg (fun x => ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)) ++ x)
                    hellByxNeg'
                _ = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)) ++ [] := by
                    rw [List.filter_nil]
                _ = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt)) :=
                  List.append_nil _
            simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.reduceAdd]
            rw [show 3 * K0 + 1 + 1 + 1 + 1 = 3 * K0 + 4 from by omega]
            rw [hOBSegXB]
            have hHeadEllaLen0 : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))
                (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx (3 * K0 + 1 + 1 + 1))) = [] := by
              rfl
            have hHeadEllaLen0' : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.zBx'x ∧ p'.1.1.op = OpType.wt))
                (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx (3 * K0 + 1 + 1 + 1))).length
                = 0 := by rw [hHeadEllaLen0]; rfl
            rw [List.getElem?_append_right
              (by rw [hInner0ZipCount]; omega),
              List.getElem?_append_right
              (by rw [hHeadEllaLen0]; simp),
              List.getElem?_append_right
              (by rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']; omega),
              List.getElem?_append_left
              (by
                have := (List.getElem?_eq_some_iff.mp hVsMatch).1
                rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']
                omega)]
            rw [hInner0ZipCount, hHeadEllaLen0', hOuterPrefixZipCount]
            rw [show ksPrefix ks (m + 1) + j - 1 - K0 - 0 - (ksPrefix ks (m + 1) - ksPrefix ks 1) = j from by
              omega]
            rw [hVsMatch]
            simp only [Option.map_some]
            have hival : 3 * K0 + 4 + ((List.take m outerRest).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 1 = i := by omega
            have hlab : EventLabel.wt Tid.guessBX Loc.zBx'x a'.2.1 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk1
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
        · -- `p = 2`: `zBxx'`.
          have hgetblk2 := hgetblkn2
          rw [h0_zBxx' a'] at hgetblk2
          simp only [Option.some.injEq] at hgetblk2
          have heloc : e.loc = Loc.zBxx' := by rw [hloce, ← hgetblk2]; rfl
          have heop : e.op = OpType.rd := by rw [hope, ← hgetblk2]; rfl
          refine ⟨ksPrefix ks (m + 1) + j, 2, hoffidPos2, hplt3, by rw [heloc, heop]; rfl, ?_⟩
          simp only [show ¬ (2 : ℕ) < 2 from by omega, if_false]
          have hnth : rawNthEvent trace Tid.guessBX Loc.zBxx' OpType.rd
              (ksPrefix ks (m + 1) + j - 1) = some e := by
            let pzBxx' : ThreadLabel (domainOf I) Tid.guessBX → Bool := fun l' =>
              @decide (l'.1.loc = Loc.zBxx' ∧ l'.1.op = OpType.rd)
                (@instDecidableAnd _ _ ((domainOf I).locDecEq l'.1.loc Loc.zBxx') inferInstance)
            let bvalzBxx' : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX :=
              fun a => ⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩
            have h0zBx'x : ∀ a, (guessBXInnerBlockElems I a)[(2 : ℕ)]? = some (bvalzBxx' a) := h0_zBxx'
            have hfalsezBx'x : ∀ (a : Val I × Val I × Val I) (q : ℕ)
                (b0 : ThreadLabel (domainOf I) Tid.guessBX),
                q ≠ 2 → (guessBXInnerBlockElems I a)[q]? = some b0 → pzBxx' b0 = false := hfalse_zBxx'
            have htruezBx'x : ∀ a, pzBxx' (bvalzBxx' a) = true := fun _ => rfl
            unfold rawNthEvent
            rw [hrawop, htrace]
            unfold guessBXBlockWord
            simp only [List.zipIdx_append, List.filter_append]
            have hHead3E :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => pzBxx' p'.1)
                  = [] := by rfl
            have hHead3 :
                (([ (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)
                    , ⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩
                    , ⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ ]).zipIdx 0).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))
                  = [] := hHead3E
            have hInner0Count : ((inner0Rest.flatMap (guessBXInnerBlockElems I)).filter
                pzBxx').length = K0 := by
              rw [guessBXInnerBlockElems_filter I pzBxx' 2 bvalzBxx' h0zBx'x htruezBx'x hfalsezBx'x]
              simp [hinner0]
            have hInner0ZipCountE : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => pzBxx' p'.1)).length = K0 := by
              rw [zipIdx_filter_length]; exact hInner0Count
            have hInner0ZipCount : (((inner0Rest.flatMap (guessBXInnerBlockElems I)).zipIdx 3).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))).length = K0 :=
              hInner0ZipCountE
            have hOuterPrefixCount : (((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).filter pzBxx').length = ksPrefix ks (m + 1) - ksPrefix ks 1 :=
              guessBXOuterRest_prefix_matchCount I ks N hks outerRest houter pzBxx' 2 bvalzBxx'
                h0zBx'x htruezBx'x hfalsezBx'x
                (fun b0 hb0 => hpredNonBridgeGen Loc.zBxx' (by decide) b0 OpType.rd hb0)
                m (by omega)
            have hOuterPrefixZipCountE : ((((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => pzBxx' p'.1)).length = ksPrefix ks (m + 1) - ksPrefix ks 1 := by
              rw [zipIdx_filter_length]; exact hOuterPrefixCount
            have hOuterPrefixZipCount : ((((outerRest.take m).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).zipIdx (3 * K0 + 4)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))).length
                = ksPrefix ks (m + 1) - ksPrefix ks 1 := hOuterPrefixZipCountE
            have hVsMatchE := zipIdx_flatMap_filter_getElem (guessBXInnerBlockElems I) 3 2
              (fun a => guessBXInnerBlockElems_length I a) pzBxx' bvalzBxx'
              h0zBx'x htruezBx'x hfalsezBx'x
              vs ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1) j a' hvaj
            have hVsMatch : (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)))[j]?
                = some (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a'.2.2, rfl⟩,
                    (3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 2) :=
              hVsMatchE
            have hsplit1 : outerRest.take (m + 1) = outerRest.take m ++ [(b, vs)] := by
              rw [List.take_add_one, hvan]; rfl
            have hsplit2 : outerRest = outerRest.take (m + 1) ++ outerRest.drop (m + 1) :=
              (List.take_append_drop (m + 1) outerRest).symm
            rw [hHead3, List.nil_append]
            simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
            rw [show outerRest.flatMap (fun p => guessBXOuterBlockElems I p.1 p.2)
                = (outerRest.take m).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2) ++
                  (guessBXOuterBlockElems I b vs ++
                    (outerRest.drop (m + 1)).flatMap (fun p => guessBXOuterBlockElems I p.1 p.2))
                from by
              conv_lhs => rw [hsplit2]
              rw [hsplit1]
              simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.append_assoc]]
            simp only [List.zipIdx_append, List.filter_append, List.getElem?_map,
              List.append_assoc]
            have hOBSegXB : (((guessBXOuterBlockElems I b vs).zipIdx
                ((3 * K0 + 4) + ((outerRest.take m).flatMap
                  (fun p => guessBXOuterBlockElems I p.1 p.2)).length)).filter
                (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)))
                = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)) := by
              have hzBxyF := hpredNonBridgeGen Loc.zBxx' (by decide)
                (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX) OpType.rd
                (by decide : Loc.zBxy ∈ BridgeLoc)
              have hellByxF := hpredNonBridgeGen Loc.zBxx' (by decide)
                (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX) OpType.rd
                (by decide : Loc.ellByx ∈ BridgeLoc)
              have hunfold : guessBXOuterBlockElems I b vs =
                  (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX) ::
                    (vs.flatMap (guessBXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessBX)]) := rfl
              have hzBxyNeg : ¬ @decide ((⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.loc = Loc.zBxx' ∧
                  (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.op = OpType.rd)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX).1.loc Loc.zBxx')
                    inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.zBxy ≠ Loc.zBxx')
              have hellByxNeg : ¬ @decide ((⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.loc = Loc.zBxx' ∧
                  (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                  ThreadLabel (domainOf I) Tid.guessBX).1.op = OpType.rd)
                  (@instDecidableAnd _ _ ((domainOf I).locDecEq
                    (⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                      ThreadLabel (domainOf I) Tid.guessBX).1.loc Loc.zBxx')
                    inferInstance) = true := by
                simp only [decide_eq_true_eq]
                rintro ⟨hloc, -⟩
                exact absurd hloc (by decide : Loc.ellByx ≠ Loc.zBxx')
              have hellByxNeg' : (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                  ((3 * K0 + 4) + ((outerRest.take m).flatMap
                    (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 +
                    (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
                  (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))
                = List.filter (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))
                    ([] : List (ThreadLabel (domainOf I) Tid.guessBX × ℕ)) := by
                rw [List.zipIdx_cons, List.zipIdx_nil]
                exact List.filter_cons_of_neg hellByxNeg
              calc (((guessBXOuterBlockElems I b vs).zipIdx
                    ((3 * K0 + 4) + ((outerRest.take m).flatMap
                      (fun p => guessBXOuterBlockElems I p.1 p.2)).length)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)))
                  = (((⟨EventLabel.wt Tid.guessBX Loc.zBxy b.1, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX),
                      (3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length) ::
                      ((vs.flatMap (guessBXInnerBlockElems I) ++
                        [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                            ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                        ((3 * K0 + 4) + ((outerRest.take m).flatMap
                          (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1))).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)) := by
                    rw [hunfold, List.zipIdx_cons]
                _ = ((vs.flatMap (guessBXInnerBlockElems I) ++
                      [(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                          ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                    (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)) :=
                  List.filter_cons_of_neg hzBxyNeg
                _ = (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))) ++
                    ((([(⟨EventLabel.rd Tid.guessBX Loc.ellByx b.2, rfl⟩ :
                        ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 +
                        (vs.flatMap (guessBXInnerBlockElems I)).length)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))) := by
                    rw [List.zipIdx_append, List.filter_append]
                _ = (((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))) ++
                    (List.filter (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))
                      ([] : List (ThreadLabel (domainOf I) Tid.guessBX × ℕ))) :=
                  congrArg (fun x => ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)) ++ x)
                    hellByxNeg'
                _ = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)) ++ [] := by
                    rw [List.filter_nil]
                _ = ((vs.flatMap (guessBXInnerBlockElems I)).zipIdx
                      ((3 * K0 + 4) + ((outerRest.take m).flatMap
                        (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1)).filter
                      (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd)) :=
                  List.append_nil _
            simp only [List.length_append, List.length_cons, List.length_nil, hBlen, Nat.reduceAdd]
            rw [show 3 + (3 * K0 + 1) = 3 * K0 + 4 from by omega]
            rw [hOBSegXB]
            have hHeadEllaLen0 : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))
                (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx (3 + 3 * K0))) = [] := by
              rfl
            have hHeadEllaLen0' : (List.filter
                (fun p' => decide (p'.1.1.loc = Loc.zBxx' ∧ p'.1.1.op = OpType.rd))
                (([(⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
                    ThreadLabel (domainOf I) Tid.guessBX)]).zipIdx (3 + 3 * K0))).length
                = 0 := by rw [hHeadEllaLen0]; rfl
            rw [List.getElem?_append_right
              (by rw [hInner0ZipCount]; omega),
              List.getElem?_append_right
              (by rw [hHeadEllaLen0]; simp),
              List.getElem?_append_right
              (by rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']; omega),
              List.getElem?_append_left
              (by
                have := (List.getElem?_eq_some_iff.mp hVsMatch).1
                rw [hOuterPrefixZipCount, hInner0ZipCount, hHeadEllaLen0']
                omega)]
            rw [hInner0ZipCount, hHeadEllaLen0', hOuterPrefixZipCount]
            rw [show ksPrefix ks (m + 1) + j - 1 - K0 - 0 - (ksPrefix ks (m + 1) - ksPrefix ks 1) = j from by
              omega]
            rw [hVsMatch]
            simp only [Option.map_some]
            have hival : 3 * K0 + 4 + ((List.take m outerRest).flatMap
                (fun p => guessBXOuterBlockElems I p.1 p.2)).length + 1 + j * 3 + 2 = i := by omega
            have hlab :
                EventLabel.rd Tid.guessBX Loc.zBxx' a'.2.2 = (l.1 : EventLabel (domainOf I)) :=
              congrArg Subtype.val hgetblk2
            simp only [hival, hlab]
            exact congrArg some hee.symm
          exact rawNthEvent_rawIndex hnth
      · -- `p2 = 3 * vs.length + 1`: `ellByx`, bridge — contradicts `hnb`.
        exfalso
        have hp2L' : p2 < 3 * vs.length + 2 := hp2L
        have hp2eq : p2 = 3 * vs.length + 1 := by omega
        rw [hp2eq, hOuterBlockLast'] at hgetblkn
        simp only [Option.some.injEq] at hgetblkn
        have hloc : e.loc = Loc.ellByx := by rw [hloce, ← hgetblkn]; rfl
        have hmem : e.loc ∈ BridgeLoc := by rw [hloc]; exact (by decide : Loc.ellByx ∈ BridgeLoc)
        exact hnb hmem
/-- Lemma 3.4 for the nested-loop threads for `GuessAX`: along a `tracePo`-edge into a
non-bridge write, `rawIndex` is non-decreasing, and strictly increasing if the
source is a read. Cases on `e1`:

* `e1` non-bridge: by `guessAXInner_idPos_rawIndex` and
  `blockIndex_po_monotone`, the call numbers satisfy `k1 ≤ k2` (strictly if
  `e1` is a read), and `rawIndex e1` is `k1` or (for the `zAxx'`-read)
  `k1 - 1`;
* `e1` the `zAxy` write of outer iteration `M1`: `rawIndex e1 = M1 ≤ k2`;
* `e1` the `ellAyx` read of outer iteration `M1`: `rawIndex e1 = M1 < k2`. -/
theorem guessAX_po_monotone (I : PCPInstance) (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace Tid.guessAX) (he2 : e2 ∈ traceEventsOf trace Tid.guessAX)
    (hpo : tracePo e1 e2) (hwt2 : e2.op = .wt) (hnb2 : ¬ e2.IsBridge) :
    rawIndex trace e1 ≤ rawIndex trace e2 ∧
      (e1.op = .rd → rawIndex trace e1 < rawIndex trace e2) := by
  have hshapewrites : ∀ p x, guessAXInnerBlockShape[p]? = some (x, OpType.rd) → 2 ≤ p := by
    intro p x hpx
    have h3 := blockShapeLen_lt (N := 3) (shape := guessAXInnerBlockShape) rfl p hpx
    have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all [guessAXInnerBlockShape]
  have hshapewrites2 : ∀ p x, guessAXInnerBlockShape[p]? = some (x, OpType.wt) → p < 2 := by
    intro p x hpx
    have h3 := blockShapeLen_lt (N := 3) (shape := guessAXInnerBlockShape) rfl p hpx
    have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all [guessAXInnerBlockShape]
  obtain ⟨k2, p2, hidPos2, hp2lt, hshape2, hrawidx2⟩ :=
    guessAXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he2 hnb2
  have hp2lt2 : p2 < 2 := hshapewrites2 p2 e2.loc (by rw [← hwt2]; exact hshape2)
  have hrawidx2' : rawIndex trace e2 = k2 := by rw [hrawidx2, if_pos hp2lt2]
  by_cases hb1 : e1.IsBridge
  · -- Case B/C: `e1` is a bridge event of some outer iteration `M1`.
    obtain ⟨M1, hM1le, hrawidx1, hcase⟩ :=
      guessAXOuter_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
        hinner0 houterLen houter houterLast htrace he1 hb1
    have hidlt : idPos e1 < idPos e2 := hpo.2
    rw [hidPos2] at hidlt
    have hbridge := nestedOuterStart_succ_eq_innerStart ks N M1 hks hM1le
    have hMprefix : M1 ≤ ksPrefix ks M1 := ksPrefix_ge ks M1
    rcases hcase with ⟨hloc1, hop1, hidPos1⟩ | ⟨hloc1, hop1, hidPos1⟩
    · -- `zAxy` write: non-strict conjunct only.
      have hle_inner : nestedInnerStart ks (ksPrefix ks M1) ≤ nestedInnerStart ks k2 + p2 := by
        omega
      have hle_k : ksPrefix ks M1 ≤ k2 := by
        by_contra hcon
        push Not at hcon
        have hmono2 : nestedInnerStart ks (k2 + 1) ≤ nestedInnerStart ks (ksPrefix ks M1) :=
          (nestedInnerStart_strictMono ks).monotone (by omega)
        have hsucc := nestedInnerStart_succ ks k2
        have hcl2 : 2 ≤ nestedCallLen k2 := by unfold nestedCallLen; split <;> omega
        omega
      exact ⟨by rw [hrawidx1, hrawidx2']; omega,
        fun hrd => by rw [hop1] at hrd; exact absurd hrd (by decide)⟩
    · -- `ellAyx` read: strict conjunct.
      have hOLge : 4 ≤ nestedOuterLen ks N M1 := by
        unfold nestedOuterLen; split_ifs <;> omega
      have hlt_inner : nestedInnerStart ks (ksPrefix ks M1) + 2 ≤
          nestedInnerStart ks k2 + p2 := by omega
      have hlt_k : ksPrefix ks M1 < k2 := by
        by_contra hcon
        push Not at hcon
        have hmono2 : nestedInnerStart ks k2 ≤ nestedInnerStart ks (ksPrefix ks M1) :=
          (nestedInnerStart_strictMono ks).monotone hcon
        omega
      have hMlt : M1 < k2 := by omega
      exact ⟨by rw [hrawidx1, hrawidx2']; omega, fun _ => by rw [hrawidx1, hrawidx2']; omega⟩
  · -- Case A: `e1` non-bridge.
    obtain ⟨k1, p1, hidPos1, hp1lt, hshape1, hrawidx1⟩ :=
      guessAXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
        hinner0 houterLen houter houterLast htrace he1 hb1
    obtain ⟨hle, hstrict⟩ := blockIndex_po_monotone
      (blockStart := nestedInnerStart ks)
      (blockLen := fun k => nestedCallLen k + nestedGap ks k)
      (writesLen := fun _ => 2) (nestedInnerStart_succ ks)
      (n1 := k1) (p1 := p1) (n2 := k2) (p2 := p2)
      (by omega) (by omega) hidPos1 hidPos2
      (fun hrd1 => hshapewrites p1 e1.loc (by rw [hrd1] at hshape1; exact hshape1))
      (fun _ => hp2lt2) hpo hwt2
    by_cases hrd1 : e1.op = OpType.rd
    · have hp1ge2 : 2 ≤ p1 := hshapewrites p1 e1.loc (by rw [hrd1] at hshape1; exact hshape1)
      have hk1pos : k1 ≠ 0 := by
        rintro rfl
        have hcl0 : nestedCallLen 0 = 2 := by decide
        omega
      have hrawidx1' : rawIndex trace e1 = k1 - 1 := by rw [hrawidx1, if_neg (by omega)]
      have hk1ltk2 := hstrict hrd1
      exact ⟨by omega, fun _ => by omega⟩
    · have hp1lt2 : p1 < 2 := by
        by_contra hcon
        push Not at hcon
        have hcl : nestedCallLen k1 ≤ 3 := by unfold nestedCallLen; split <;> omega
        have hp1eq2 : p1 = 2 := by omega
        rw [hp1eq2] at hshape1
        have hzAxx'Rd : guessAXInnerBlockShape[2]? = some (Loc.zAxx', OpType.rd) := by decide
        rw [hzAxx'Rd] at hshape1
        injection hshape1 with heq
        injection heq with _ hop
        exact hrd1 hop.symm
      have hrawidx1' : rawIndex trace e1 = k1 := by rw [hrawidx1, if_pos hp1lt2]
      exact ⟨by omega, fun hrd => absurd hrd hrd1⟩

/-- `ww_dec_2`'s closing step for `GuessAX`: along a `tracePo`-edge from a
non-bridge read to a non-bridge write, `rawIndex` increases by more than one.
The read is a `zAxx'`-read of call `k1 ≥ 1` with `rawIndex e1 = k1 - 1`, and
the write has `rawIndex e2 = k2 > k1` (the paper's "`r_ℓ` is the last event
of call `ℓ + 1`, so `ℓ + 1 < j`"). -/
theorem guessAX_po_monotone_read_gap (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace Tid.guessAX) (he2 : e2 ∈ traceEventsOf trace Tid.guessAX)
    (hpo : tracePo e1 e2) (hrd1 : e1.op = .rd) (hnb1 : ¬ e1.IsBridge)
    (hwt2 : e2.op = .wt) (hnb2 : ¬ e2.IsBridge) :
    rawIndex trace e1 + 1 < rawIndex trace e2 := by
  have hshapewrites : ∀ p x, guessAXInnerBlockShape[p]? = some (x, OpType.rd) → 2 ≤ p := by
    intro p x hpx
    have h3 := blockShapeLen_lt (N := 3) (shape := guessAXInnerBlockShape) rfl p hpx
    have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all [guessAXInnerBlockShape]
  have hshapewrites2 : ∀ p x, guessAXInnerBlockShape[p]? = some (x, OpType.wt) → p < 2 := by
    intro p x hpx
    have h3 := blockShapeLen_lt (N := 3) (shape := guessAXInnerBlockShape) rfl p hpx
    have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all [guessAXInnerBlockShape]
  obtain ⟨k2, p2, hidPos2, hp2lt, hshape2, hrawidx2⟩ :=
    guessAXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he2 hnb2
  have hp2lt2 : p2 < 2 := hshapewrites2 p2 e2.loc (by rw [← hwt2]; exact hshape2)
  have hrawidx2' : rawIndex trace e2 = k2 := by rw [hrawidx2, if_pos hp2lt2]
  obtain ⟨k1, p1, hidPos1, hp1lt, hshape1, hrawidx1⟩ :=
    guessAXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 hnb1
  obtain ⟨hle, hstrict⟩ := blockIndex_po_monotone
    (blockStart := nestedInnerStart ks)
    (blockLen := fun k => nestedCallLen k + nestedGap ks k)
    (writesLen := fun _ => 2) (nestedInnerStart_succ ks)
    (n1 := k1) (p1 := p1) (n2 := k2) (p2 := p2)
    (by omega) (by omega) hidPos1 hidPos2
    (fun hrd1' => hshapewrites p1 e1.loc (by rw [hrd1'] at hshape1; exact hshape1))
    (fun _ => hp2lt2) hpo hwt2
  have hp1ge2 : 2 ≤ p1 := hshapewrites p1 e1.loc (by rw [hrd1] at hshape1; exact hshape1)
  have hk1pos : k1 ≠ 0 := by
    rintro rfl
    have hcl0 : nestedCallLen 0 = 2 := by decide
    omega
  have hrawidx1' : rawIndex trace e1 = k1 - 1 := by rw [hrawidx1, if_neg (by omega)]
  have hk1ltk2 := hstrict hrd1
  omega

/-- Lemma 3.4 for the nested-loop threads for `GuessBX`, as `guessAX_po_monotone`. -/
theorem guessBX_po_monotone (I : PCPInstance) (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace Tid.guessBX) (he2 : e2 ∈ traceEventsOf trace Tid.guessBX)
    (hpo : tracePo e1 e2) (hwt2 : e2.op = .wt) (hnb2 : ¬ e2.IsBridge) :
    rawIndex trace e1 ≤ rawIndex trace e2 ∧
      (e1.op = .rd → rawIndex trace e1 < rawIndex trace e2) := by
  have hshapewrites : ∀ p x, guessBXInnerBlockShape[p]? = some (x, OpType.rd) → 2 ≤ p := by
    intro p x hpx
    have h3 := blockShapeLen_lt (N := 3) (shape := guessBXInnerBlockShape) rfl p hpx
    have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all [guessBXInnerBlockShape]
  have hshapewrites2 : ∀ p x, guessBXInnerBlockShape[p]? = some (x, OpType.wt) → p < 2 := by
    intro p x hpx
    have h3 := blockShapeLen_lt (N := 3) (shape := guessBXInnerBlockShape) rfl p hpx
    have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all [guessBXInnerBlockShape]
  obtain ⟨k2, p2, hidPos2, hp2lt, hshape2, hrawidx2⟩ :=
    guessBXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he2 hnb2
  have hp2lt2 : p2 < 2 := hshapewrites2 p2 e2.loc (by rw [← hwt2]; exact hshape2)
  have hrawidx2' : rawIndex trace e2 = k2 := by rw [hrawidx2, if_pos hp2lt2]
  by_cases hb1 : e1.IsBridge
  · -- Case B/C: `e1` is a bridge event of some outer iteration `M1`.
    obtain ⟨M1, hM1le, hrawidx1, hcase⟩ :=
      guessBXOuter_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
        hinner0 houterLen houter houterLast htrace he1 hb1
    have hidlt : idPos e1 < idPos e2 := hpo.2
    rw [hidPos2] at hidlt
    have hbridge := nestedOuterStart_succ_eq_innerStart ks N M1 hks hM1le
    have hMprefix : M1 ≤ ksPrefix ks M1 := ksPrefix_ge ks M1
    rcases hcase with ⟨hloc1, hop1, hidPos1⟩ | ⟨hloc1, hop1, hidPos1⟩
    · -- `zAxy` write: non-strict conjunct only.
      have hle_inner : nestedInnerStart ks (ksPrefix ks M1) ≤ nestedInnerStart ks k2 + p2 := by
        omega
      have hle_k : ksPrefix ks M1 ≤ k2 := by
        by_contra hcon
        push Not at hcon
        have hmono2 : nestedInnerStart ks (k2 + 1) ≤ nestedInnerStart ks (ksPrefix ks M1) :=
          (nestedInnerStart_strictMono ks).monotone (by omega)
        have hsucc := nestedInnerStart_succ ks k2
        have hcl2 : 2 ≤ nestedCallLen k2 := by unfold nestedCallLen; split <;> omega
        omega
      exact ⟨by rw [hrawidx1, hrawidx2']; omega,
        fun hrd => by rw [hop1] at hrd; exact absurd hrd (by decide)⟩
    · -- `ellAyx` read: strict conjunct.
      have hOLge : 4 ≤ nestedOuterLen ks N M1 := by
        unfold nestedOuterLen; split_ifs <;> omega
      have hlt_inner : nestedInnerStart ks (ksPrefix ks M1) + 2 ≤
          nestedInnerStart ks k2 + p2 := by omega
      have hlt_k : ksPrefix ks M1 < k2 := by
        by_contra hcon
        push Not at hcon
        have hmono2 : nestedInnerStart ks k2 ≤ nestedInnerStart ks (ksPrefix ks M1) :=
          (nestedInnerStart_strictMono ks).monotone hcon
        omega
      have hMlt : M1 < k2 := by omega
      exact ⟨by rw [hrawidx1, hrawidx2']; omega, fun _ => by rw [hrawidx1, hrawidx2']; omega⟩
  · -- Case A: `e1` non-bridge.
    obtain ⟨k1, p1, hidPos1, hp1lt, hshape1, hrawidx1⟩ :=
      guessBXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
        hinner0 houterLen houter houterLast htrace he1 hb1
    obtain ⟨hle, hstrict⟩ := blockIndex_po_monotone
      (blockStart := nestedInnerStart ks)
      (blockLen := fun k => nestedCallLen k + nestedGap ks k)
      (writesLen := fun _ => 2) (nestedInnerStart_succ ks)
      (n1 := k1) (p1 := p1) (n2 := k2) (p2 := p2)
      (by omega) (by omega) hidPos1 hidPos2
      (fun hrd1 => hshapewrites p1 e1.loc (by rw [hrd1] at hshape1; exact hshape1))
      (fun _ => hp2lt2) hpo hwt2
    by_cases hrd1 : e1.op = OpType.rd
    · have hp1ge2 : 2 ≤ p1 := hshapewrites p1 e1.loc (by rw [hrd1] at hshape1; exact hshape1)
      have hk1pos : k1 ≠ 0 := by
        rintro rfl
        have hcl0 : nestedCallLen 0 = 2 := by decide
        omega
      have hrawidx1' : rawIndex trace e1 = k1 - 1 := by rw [hrawidx1, if_neg (by omega)]
      have hk1ltk2 := hstrict hrd1
      exact ⟨by omega, fun _ => by omega⟩
    · have hp1lt2 : p1 < 2 := by
        by_contra hcon
        push Not at hcon
        have hcl : nestedCallLen k1 ≤ 3 := by unfold nestedCallLen; split <;> omega
        have hp1eq2 : p1 = 2 := by omega
        rw [hp1eq2] at hshape1
        have hzAxx'Rd : guessBXInnerBlockShape[2]? = some (Loc.zBxx', OpType.rd) := by decide
        rw [hzAxx'Rd] at hshape1
        injection hshape1 with heq
        injection heq with _ hop
        exact hrd1 hop.symm
      have hrawidx1' : rawIndex trace e1 = k1 := by rw [hrawidx1, if_pos hp1lt2]
      exact ⟨by omega, fun hrd => absurd hrd hrd1⟩

/-- `ww_dec_2`'s closing step for `GuessBX`, as
`guessAX_po_monotone_read_gap`. -/
theorem guessBX_po_monotone_read_gap (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace Tid.guessBX) (he2 : e2 ∈ traceEventsOf trace Tid.guessBX)
    (hpo : tracePo e1 e2) (hrd1 : e1.op = .rd) (hnb1 : ¬ e1.IsBridge)
    (hwt2 : e2.op = .wt) (hnb2 : ¬ e2.IsBridge) :
    rawIndex trace e1 + 1 < rawIndex trace e2 := by
  have hshapewrites : ∀ p x, guessBXInnerBlockShape[p]? = some (x, OpType.rd) → 2 ≤ p := by
    intro p x hpx
    have h3 := blockShapeLen_lt (N := 3) (shape := guessBXInnerBlockShape) rfl p hpx
    have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all [guessBXInnerBlockShape]
  have hshapewrites2 : ∀ p x, guessBXInnerBlockShape[p]? = some (x, OpType.wt) → p < 2 := by
    intro p x hpx
    have h3 := blockShapeLen_lt (N := 3) (shape := guessBXInnerBlockShape) rfl p hpx
    have : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp_all [guessBXInnerBlockShape]
  obtain ⟨k2, p2, hidPos2, hp2lt, hshape2, hrawidx2⟩ :=
    guessBXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he2 hnb2
  have hp2lt2 : p2 < 2 := hshapewrites2 p2 e2.loc (by rw [← hwt2]; exact hshape2)
  have hrawidx2' : rawIndex trace e2 = k2 := by rw [hrawidx2, if_pos hp2lt2]
  obtain ⟨k1, p1, hidPos1, hp1lt, hshape1, hrawidx1⟩ :=
    guessBXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 hnb1
  obtain ⟨hle, hstrict⟩ := blockIndex_po_monotone
    (blockStart := nestedInnerStart ks)
    (blockLen := fun k => nestedCallLen k + nestedGap ks k)
    (writesLen := fun _ => 2) (nestedInnerStart_succ ks)
    (n1 := k1) (p1 := p1) (n2 := k2) (p2 := p2)
    (by omega) (by omega) hidPos1 hidPos2
    (fun hrd1' => hshapewrites p1 e1.loc (by rw [hrd1'] at hshape1; exact hshape1))
    (fun _ => hp2lt2) hpo hwt2
  have hp1ge2 : 2 ≤ p1 := hshapewrites p1 e1.loc (by rw [hrd1] at hshape1; exact hshape1)
  have hk1pos : k1 ≠ 0 := by
    rintro rfl
    have hcl0 : nestedCallLen 0 = 2 := by decide
    omega
  have hrawidx1' : rawIndex trace e1 = k1 - 1 := by rw [hrawidx1, if_neg (by omega)]
  have hk1ltk2 := hstrict hrd1
  omega

/-- Lemma 3.5 for `GuessAX`: its only non-bridge read location
is `zAxx'`, so `po`-edges between non-bridge reads are increasing
(`rawIndex_lt_of_tracePo_sameLocOp`). -/
theorem guessAX_reads_nondecreasing (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace Tid.guessAX) (he2 : e2 ∈ traceEventsOf trace Tid.guessAX)
    (hpo : tracePo e1 e2) (hrd1 : e1.op = .rd) (hrd2 : e2.op = .rd)
    (hnb1 : ¬ e1.IsBridge) (hnb2 : ¬ e2.IsBridge)
    (hdec : rawIndex trace e2 < rawIndex trace e1) : False := by
  obtain ⟨k1, p1, -, -, hshape1, -⟩ :=
    guessAXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 hnb1
  obtain ⟨k2, p2, -, -, hshape2, -⟩ :=
    guessAXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he2 hnb2
  have hp1len : p1 < 3 := blockShapeLen_lt (N := 3) (shape := guessAXInnerBlockShape) rfl p1 hshape1
  have hp2len : p2 < 3 := blockShapeLen_lt (N := 3) (shape := guessAXInnerBlockShape) rfl p2 hshape2
  have heloc1 : e1.loc = Loc.zAxx' := by
    have hp1cases : p1 = 0 ∨ p1 = 1 ∨ p1 = 2 := by omega
    rcases hp1cases with rfl | rfl | rfl
    · have h := hshape1.symm.trans (show guessAXInnerBlockShape[0]? =
        some (Loc.xA, OpType.wt) by decide)
      injection h with h; injection h with _ b; exact absurd (b.symm.trans hrd1) (by decide)
    · have h := hshape1.symm.trans (show guessAXInnerBlockShape[1]? =
        some (Loc.zAx'x, OpType.wt) by decide)
      injection h with h; injection h with _ b; exact absurd (b.symm.trans hrd1) (by decide)
    · have h := hshape1.symm.trans (show guessAXInnerBlockShape[2]? =
        some (Loc.zAxx', OpType.rd) by decide)
      injection h with h; injection h with a _
  have heloc2 : e2.loc = Loc.zAxx' := by
    have hp2cases : p2 = 0 ∨ p2 = 1 ∨ p2 = 2 := by omega
    rcases hp2cases with rfl | rfl | rfl
    · have h := hshape2.symm.trans (show guessAXInnerBlockShape[0]? =
        some (Loc.xA, OpType.wt) by decide)
      injection h with h; injection h with _ b; exact absurd (b.symm.trans hrd2) (by decide)
    · have h := hshape2.symm.trans (show guessAXInnerBlockShape[1]? =
        some (Loc.zAx'x, OpType.wt) by decide)
      injection h with h; injection h with _ b; exact absurd (b.symm.trans hrd2) (by decide)
    · have h := hshape2.symm.trans (show guessAXInnerBlockShape[2]? =
        some (Loc.zAxx', OpType.rd) by decide)
      injection h with h; injection h with a _
  have heloc : e1.loc = e2.loc := heloc1.trans heloc2.symm
  have heop : e1.op = e2.op := hrd1.trans hrd2.symm
  exact absurd (rawIndex_lt_of_tracePo_sameLocOp he1 he2 hpo heloc heop) (by omega)

/-- Lemma 3.5 for `GuessBX`: its only non-bridge read location
is `zBxx'`. -/
theorem guessBX_reads_nondecreasing (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace Tid.guessBX) (he2 : e2 ∈ traceEventsOf trace Tid.guessBX)
    (hpo : tracePo e1 e2) (hrd1 : e1.op = .rd) (hrd2 : e2.op = .rd)
    (hnb1 : ¬ e1.IsBridge) (hnb2 : ¬ e2.IsBridge)
    (hdec : rawIndex trace e2 < rawIndex trace e1) : False := by
  obtain ⟨k1, p1, -, -, hshape1, -⟩ :=
    guessBXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 hnb1
  obtain ⟨k2, p2, -, -, hshape2, -⟩ :=
    guessBXInner_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he2 hnb2
  have hp1len : p1 < 3 := blockShapeLen_lt (N := 3) (shape := guessBXInnerBlockShape) rfl p1 hshape1
  have hp2len : p2 < 3 := blockShapeLen_lt (N := 3) (shape := guessBXInnerBlockShape) rfl p2 hshape2
  have heloc1 : e1.loc = Loc.zBxx' := by
    have hp1cases : p1 = 0 ∨ p1 = 1 ∨ p1 = 2 := by omega
    rcases hp1cases with rfl | rfl | rfl
    · have h := hshape1.symm.trans (show guessBXInnerBlockShape[0]? =
        some (Loc.xB, OpType.wt) by decide)
      injection h with h; injection h with _ b; exact absurd (b.symm.trans hrd1) (by decide)
    · have h := hshape1.symm.trans (show guessBXInnerBlockShape[1]? =
        some (Loc.zBx'x, OpType.wt) by decide)
      injection h with h; injection h with _ b; exact absurd (b.symm.trans hrd1) (by decide)
    · have h := hshape1.symm.trans (show guessBXInnerBlockShape[2]? =
        some (Loc.zBxx', OpType.rd) by decide)
      injection h with h; injection h with a _
  have heloc2 : e2.loc = Loc.zBxx' := by
    have hp2cases : p2 = 0 ∨ p2 = 1 ∨ p2 = 2 := by omega
    rcases hp2cases with rfl | rfl | rfl
    · have h := hshape2.symm.trans (show guessBXInnerBlockShape[0]? =
        some (Loc.xB, OpType.wt) by decide)
      injection h with h; injection h with _ b; exact absurd (b.symm.trans hrd2) (by decide)
    · have h := hshape2.symm.trans (show guessBXInnerBlockShape[1]? =
        some (Loc.zBx'x, OpType.wt) by decide)
      injection h with h; injection h with _ b; exact absurd (b.symm.trans hrd2) (by decide)
    · have h := hshape2.symm.trans (show guessBXInnerBlockShape[2]? =
        some (Loc.zBxx', OpType.rd) by decide)
      injection h with h; injection h with a _
  have heloc : e1.loc = e2.loc := heloc1.trans heloc2.symm
  have heop : e1.op = e2.op := hrd1.trans hrd2.symm
  exact absurd (rawIndex_lt_of_tracePo_sameLocOp he1 he2 hpo heloc heop) (by omega)

/-- The bridge counterpart of Lemma 3.4 for `GuessAX`, from
the proof of Lemma 3.6 in Section 3.5 ("Pairs `{g_α^x,g_α^y}` and
`{g_β^x,g_β^y}`"): "`g_α^x` alternates writes to `zAxy` and reads from `ellAyx`,
starting with a write to `zAxy`. Therefore, po-edges of the form
`r(g_α^x,ellAyx) → w(g_α^x,zAxy)` are increasing." The read is at the end of
outer iteration `M1` and the write at the start of `M2`, so `M1 < M2`. -/
theorem guessAX_bridge_rw_increasing (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace Tid.guessAX) (he2 : e2 ∈ traceEventsOf trace Tid.guessAX)
    (hpo : tracePo e1 e2) (hrd1 : e1.op = .rd) (hwt2 : e2.op = .wt)
    (hb1 : e1.IsBridge) (hb2 : e2.IsBridge) :
    rawIndex trace e1 < rawIndex trace e2 := by
  obtain ⟨M1, hM1le, hrawidx1, hcase1⟩ :=
    guessAXOuter_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 hb1
  obtain ⟨M2, hM2le, hrawidx2, hcase2⟩ :=
    guessAXOuter_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he2 hb2
  rcases hcase1 with ⟨hloc1, hop1, hidPos1⟩ | ⟨hloc1, hop1, hidPos1⟩
  · exact absurd (hop1.symm.trans hrd1) (by decide)
  · rcases hcase2 with ⟨hloc2, hop2, hidPos2⟩ | ⟨hloc2, hop2, hidPos2⟩
    · have hsucc1 : nestedOuterStart ks N (M1 + 1) = idPos e1 + 1 := by
        rw [nestedOuterStart_succ]; omega
      have hidlt : idPos e1 < idPos e2 := hpo.2
      have hlt : nestedOuterStart ks N (M1 + 1) ≤ nestedOuterStart ks N M2 := by omega
      have hMlt : M1 + 1 ≤ M2 := by
        by_contra hcon
        push Not at hcon
        have hmono : nestedOuterStart ks N M2 ≤ nestedOuterStart ks N M1 :=
          (nestedOuterStart_mono ks N) (by omega)
        have hgap : nestedOuterStart ks N M1 < nestedOuterStart ks N (M1 + 1) := by
          rw [nestedOuterStart_succ]
          have : 1 ≤ nestedOuterLen ks N M1 := by unfold nestedOuterLen; split_ifs <;> omega
          omega
        omega
      omega
    · exact absurd (hop2.symm.trans hwt2) (by decide)

/-- The bridge counterpart of Lemma 3.4 for `GuessBX`: "`g_β^x`
alternates writes to `zBxy` and reads from `ellByx`, starting with a write to
`zBxy`." -/
theorem guessBX_bridge_rw_increasing (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (hks : ks.length = N + 1)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (hinner0 : ∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ m, m < N →
      ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace Tid.guessBX) (he2 : e2 ∈ traceEventsOf trace Tid.guessBX)
    (hpo : tracePo e1 e2) (hrd1 : e1.op = .rd) (hwt2 : e2.op = .wt)
    (hb1 : e1.IsBridge) (hb2 : e2.IsBridge) :
    rawIndex trace e1 < rawIndex trace e2 := by
  obtain ⟨M1, hM1le, hrawidx1, hcase1⟩ :=
    guessBXOuter_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 hb1
  obtain ⟨M2, hM2le, hrawidx2, hcase2⟩ :=
    guessBXOuter_idPos_rawIndex I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he2 hb2
  rcases hcase1 with ⟨hloc1, hop1, hidPos1⟩ | ⟨hloc1, hop1, hidPos1⟩
  · exact absurd (hop1.symm.trans hrd1) (by decide)
  · rcases hcase2 with ⟨hloc2, hop2, hidPos2⟩ | ⟨hloc2, hop2, hidPos2⟩
    · have hsucc1 : nestedOuterStart ks N (M1 + 1) = idPos e1 + 1 := by
        rw [nestedOuterStart_succ]; omega
      have hidlt : idPos e1 < idPos e2 := hpo.2
      have hlt : nestedOuterStart ks N (M1 + 1) ≤ nestedOuterStart ks N M2 := by omega
      have hMlt : M1 + 1 ≤ M2 := by
        by_contra hcon
        push Not at hcon
        have hmono : nestedOuterStart ks N M2 ≤ nestedOuterStart ks N M1 :=
          (nestedOuterStart_mono ks N) (by omega)
        have hgap : nestedOuterStart ks N M1 < nestedOuterStart ks N (M1 + 1) := by
          rw [nestedOuterStart_succ]
          have : 1 ≤ nestedOuterLen ks N M1 := by unfold nestedOuterLen; split_ifs <;> omega
          omega
        omega
      omega
    · exact absurd (hop2.symm.trans hwt2) (by decide)


/-! ## Assembly over all twelve threads -/

/-- The shapes of the twelve threads' traces: for every thread, `trace`
decomposes into that thread's block word (`guessAXBlockWord`,
`primeAXBlockWord`, `checkXBlockWord`, ...) for some witness data. One field
per thread, each the hypothesis taken by that thread's `*_po_monotone`
lemma. -/
structure TraceShapes (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t)) : Prop where
  guessAX : ∃ (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I), ks.length = N + 1 ∧
    ∃ inner0Rest outerRest, (∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0) ∧
    outerRest.length = N + 1 ∧
    (∀ m, m < N → ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧
      vs.length = km + 1) ∧
    (∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) ∧
    trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest
  guessBX : ∃ (ks : List ℕ) (N : ℕ) (v1 v2 : Val I) (vB0 : Val I × Val I), ks.length = N + 1 ∧
    ∃ inner0Rest outerRest, (∃ k0, ks[0]? = some k0 ∧ inner0Rest.length = k0) ∧
    outerRest.length = N + 1 ∧
    (∀ m, m < N → ∃ b vs km, outerRest[m]? = some (b, vs) ∧ ks[m + 1]? = some km ∧
      vs.length = km + 1) ∧
    (∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1) ∧
    trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest
  guessAY : ∃ v0 kws, trace Tid.guessAY = guessAYBlockWord I v0 kws
  guessBY : ∃ v0 kws, trace Tid.guessBY = guessBYBlockWord I v0 kws
  primeAX : ∃ vals, trace Tid.primeAX = primeAXBlockWord I vals
  primeBX : ∃ vals, trace Tid.primeBX = primeBXBlockWord I vals
  primeAY : ∃ vals, trace Tid.primeAY = primeAYBlockWord I vals
  primeBY : ∃ vals, trace Tid.primeBY = primeBYBlockWord I vals
  primeCheckX : ∃ cnts, trace Tid.primeCheckX = primeCheckXBlockWord I cnts
  primeCheckY : ∃ cnts, trace Tid.primeCheckY = primeCheckYBlockWord I cnts
  checkX : ∃ v0 kws, trace Tid.checkX = checkXBlockWord I v0 kws
  checkY : ∃ v0 kws, trace Tid.checkY = checkYBlockWord I v0 kws

/-- Lemma 3.4 for any trace satisfying `TraceShapes`: assembled
from the per-thread lemmas (Lemma 3.4 for the primed threads, Lemma 3.4 for the threads skipping a first read,
Lemma 3.4 for the nested-loop threads) by cases on the common thread of `e1`/`e2`. The
statement for `G` itself is `executionGraphOf_po_monotone`. -/
theorem po_monotone_of_traceShapes (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (hshapes : TraceShapes I trace)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace e1.tid) (he2 : e2 ∈ traceEventsOf trace e2.tid)
    (hpo : tracePo e1 e2) (hwt2 : e2.op = .wt) (hnb2 : ¬ e2.IsBridge) :
    rawIndex trace e1 ≤ rawIndex trace e2 ∧
      (e1.op = .rd → rawIndex trace e1 < rawIndex trace e2) := by
  have htid : e1.tid = e2.tid := hpo.1
  rw [← htid] at he2
  match hx : e1.tid with
  | .guessAX =>
    rw [hx] at he1 he2
    obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
      htrace⟩ := hshapes.guessAX
    exact guessAX_po_monotone I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 he2 hpo hwt2 hnb2
  | .guessBX =>
    rw [hx] at he1 he2
    obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
      htrace⟩ := hshapes.guessBX
    exact guessBX_po_monotone I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 he2 hpo hwt2 hnb2
  | .guessAY =>
    rw [hx] at he1 he2
    obtain ⟨v0, kws, htrace⟩ := hshapes.guessAY
    exact guessAY_po_monotone I trace v0 kws htrace he1 he2 hpo hwt2 hnb2
  | .guessBY =>
    rw [hx] at he1 he2
    obtain ⟨v0, kws, htrace⟩ := hshapes.guessBY
    exact guessBY_po_monotone I trace v0 kws htrace he1 he2 hpo hwt2 hnb2
  | .primeAX =>
    rw [hx] at he1 he2
    obtain ⟨vals, htrace⟩ := hshapes.primeAX
    exact primeAX_po_monotone I trace vals htrace he1 he2 hpo hwt2 hnb2
  | .primeBX =>
    rw [hx] at he1 he2
    obtain ⟨vals, htrace⟩ := hshapes.primeBX
    exact primeBX_po_monotone I trace vals htrace he1 he2 hpo hwt2 hnb2
  | .primeAY =>
    rw [hx] at he1 he2
    obtain ⟨vals, htrace⟩ := hshapes.primeAY
    exact primeAY_po_monotone I trace vals htrace he1 he2 hpo hwt2 hnb2
  | .primeBY =>
    rw [hx] at he1 he2
    obtain ⟨vals, htrace⟩ := hshapes.primeBY
    exact primeBY_po_monotone I trace vals htrace he1 he2 hpo hwt2 hnb2
  | .primeCheckX =>
    rw [hx] at he1 he2
    obtain ⟨cnts, htrace⟩ := hshapes.primeCheckX
    exact primeCheckX_po_monotone I trace cnts htrace he1 he2 hpo hwt2 hnb2
  | .primeCheckY =>
    rw [hx] at he1 he2
    obtain ⟨cnts, htrace⟩ := hshapes.primeCheckY
    exact primeCheckY_po_monotone I trace cnts htrace he1 he2 hpo hwt2 hnb2
  | .checkX =>
    rw [hx] at he1 he2
    obtain ⟨v0, kws, htrace⟩ := hshapes.checkX
    exact checkX_po_monotone I trace v0 kws htrace he1 he2 hpo hwt2 hnb2
  | .checkY =>
    rw [hx] at he1 he2
    obtain ⟨v0, kws, htrace⟩ := hshapes.checkY
    exact checkY_po_monotone I trace v0 kws htrace he1 he2 hpo hwt2 hnb2

/-- Lemma 3.5 for any trace satisfying `TraceShapes`. Ten
threads have no decreasing edge (`*_reads_nondecreasing`); `CheckX`/`CheckY`
contribute the eight pairs of Eq. (19) (`checkX_po_reads_decreasing`/
`checkY_po_reads_decreasing`). The statement for `G` itself is
`executionGraphOf_po_reads_decreasing`. -/
theorem po_reads_decreasing_of_traceShapes (I : PCPInstance)
    (trace : ∀ t, Word (ThreadLabel (domainOf I) t))
    (hshapes : TraceShapes I trace)
    {e1 e2 : Event (domainOf I)}
    (he1 : e1 ∈ traceEventsOf trace e1.tid) (he2 : e2 ∈ traceEventsOf trace e2.tid)
    (hpo : tracePo e1 e2) (hrd1 : e1.op = .rd) (hrd2 : e2.op = .rd)
    (hnb1 : ¬ e1.IsBridge) (hnb2 : ¬ e2.IsBridge)
    (hdec : rawIndex trace e2 < rawIndex trace e1) :
    rawIndex trace e1 = rawIndex trace e2 + 1 ∧
      (((e1.loc = Loc.xA ∧ e2.loc = Loc.xA') ∨ (e1.loc = Loc.xA ∧ e2.loc = Loc.xB') ∨
        (e1.loc = Loc.xB ∧ e2.loc = Loc.xA') ∨ (e1.loc = Loc.xB ∧ e2.loc = Loc.xB')) ∨
       ((e1.loc = Loc.yA ∧ e2.loc = Loc.yA') ∨ (e1.loc = Loc.yA ∧ e2.loc = Loc.yB') ∨
        (e1.loc = Loc.yB ∧ e2.loc = Loc.yA') ∨ (e1.loc = Loc.yB ∧ e2.loc = Loc.yB'))) ∧
      (e1.tid = Tid.checkX ∨ e1.tid = Tid.checkY) := by
  have htid : e1.tid = e2.tid := hpo.1
  rw [← htid] at he2
  match hx : e1.tid with
  | .guessAX =>
    rw [hx] at he1 he2
    obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
      htrace⟩ := hshapes.guessAX
    exact absurd hdec (guessAX_reads_nondecreasing I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 he2 hpo hrd1 hrd2 hnb1 hnb2)
  | .guessBX =>
    rw [hx] at he1 he2
    obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
      htrace⟩ := hshapes.guessBX
    exact absurd hdec (guessBX_reads_nondecreasing I trace ks N v1 v2 vB0 hks inner0Rest outerRest
      hinner0 houterLen houter houterLast htrace he1 he2 hpo hrd1 hrd2 hnb1 hnb2)
  | .guessAY =>
    rw [hx] at he1 he2
    obtain ⟨v0, kws, htrace⟩ := hshapes.guessAY
    exact absurd hdec (guessAY_reads_nondecreasing I trace v0 kws htrace he1 he2 hpo hrd1 hrd2
      hnb1 hnb2)
  | .guessBY =>
    rw [hx] at he1 he2
    obtain ⟨v0, kws, htrace⟩ := hshapes.guessBY
    exact absurd hdec (guessBY_reads_nondecreasing I trace v0 kws htrace he1 he2 hpo hrd1 hrd2
      hnb1 hnb2)
  | .primeAX =>
    rw [hx] at he1 he2
    obtain ⟨vals, htrace⟩ := hshapes.primeAX
    exact absurd hdec (primeAX_reads_nondecreasing I trace vals htrace he1 he2 hpo hrd1 hrd2
      hnb1 hnb2)
  | .primeBX =>
    rw [hx] at he1 he2
    obtain ⟨vals, htrace⟩ := hshapes.primeBX
    exact absurd hdec (primeBX_reads_nondecreasing I trace vals htrace he1 he2 hpo hrd1 hrd2
      hnb1 hnb2)
  | .primeAY =>
    rw [hx] at he1 he2
    obtain ⟨vals, htrace⟩ := hshapes.primeAY
    exact absurd hdec (primeAY_reads_nondecreasing I trace vals htrace he1 he2 hpo hrd1 hrd2
      hnb1 hnb2)
  | .primeBY =>
    rw [hx] at he1 he2
    obtain ⟨vals, htrace⟩ := hshapes.primeBY
    exact absurd hdec (primeBY_reads_nondecreasing I trace vals htrace he1 he2 hpo hrd1 hrd2
      hnb1 hnb2)
  | .primeCheckX =>
    rw [hx] at he1 he2
    obtain ⟨cnts, htrace⟩ := hshapes.primeCheckX
    exact absurd hdec (primeCheckX_reads_nondecreasing I trace cnts htrace he1 he2 hpo hrd1 hrd2
      hnb1 hnb2)
  | .primeCheckY =>
    rw [hx] at he1 he2
    obtain ⟨cnts, htrace⟩ := hshapes.primeCheckY
    exact absurd hdec (primeCheckY_reads_nondecreasing I trace cnts htrace he1 he2 hpo hrd1 hrd2
      hnb1 hnb2)
  | .checkX =>
    rw [hx] at he1 he2
    obtain ⟨v0, kws, htrace⟩ := hshapes.checkX
    have h := checkX_po_reads_decreasing I trace v0 kws htrace he1 he2 hpo hrd1 hrd2 hnb1 hnb2
      hdec
    exact ⟨h.1, Or.inl h.2, Or.inl rfl⟩
  | .checkY =>
    rw [hx] at he1 he2
    obtain ⟨v0, kws, htrace⟩ := hshapes.checkY
    have h := checkY_po_reads_decreasing I trace v0 kws htrace he1 he2 hpo hrd1 hrd2 hnb1 hnb2
      hdec
    exact ⟨h.1, Or.inr h.2, Or.inr rfl⟩

end RAUndecidability
