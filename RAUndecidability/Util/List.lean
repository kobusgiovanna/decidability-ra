import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Order.Monotone.Basic

/-!
# List position-decomposition lemmas

General facts about `List.flatMap`/`List.filter`/`List.getElem?` position
arithmetic, used to relate a thread's closed-form word to the positions and
indices of its events.
-/

namespace RAUndecidability

/-- Filtering a `zipIdx`'d list by a predicate on its value component has the
same length as filtering the original list. -/
theorem zipIdx_filter_length {α : Type} (l : List α) (pred : α → Bool) (i : ℕ) :
    ((l.zipIdx i).filter (fun p => pred p.1)).length = (l.filter pred).length := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
      rw [List.zipIdx_cons]
      by_cases h : pred a = true
      · simp [h, ih]
      · simp [h, ih]

/-- A position in `l.filter pred` transfers to a position in
`l.zipIdx.filter (fun p => pred p.1)`, at some original position. -/
theorem zipIdx_filter_getElem_of_filter_getElem {α : Type} (l : List α) (pred : α → Bool)
    (n : ℕ) (a : α) (h : (l.filter pred)[n]? = some a) :
    ∃ k, (l.zipIdx.filter (fun p => pred p.1))[n]? = some (a, k) := by
  have hmap : ((l.zipIdx).filter (fun p => pred p.1)).map Prod.fst = l.filter pred := by
    have h1 : (l.zipIdx).map Prod.fst = l := List.zipIdx_map_fst 0 l
    have h2 : ((l.zipIdx).map Prod.fst).filter pred =
        ((l.zipIdx).filter (pred ∘ Prod.fst)).map Prod.fst := List.filter_map
    rw [h1] at h2
    exact h2.symm
  have hget : (((l.zipIdx).filter (fun p => pred p.1)).map Prod.fst)[n]? = some a := by
    rw [hmap]; exact h
  rw [List.getElem?_map, Option.map_eq_some_iff] at hget
  obtain ⟨p, hp, hpeq⟩ := hget
  exact ⟨p.2, by rw [hp]; congr 1; exact Prod.ext hpeq rfl⟩

/-- If a list's `p0`-th element is the unique one satisfying `pred`, filtering
by `pred` collapses the list to that singleton. -/
theorem list_filter_singleton_of_unique' {α : Type} (l : List α) (pred : α → Bool) (p0 : ℕ)
    (a0 : α) (h0 : l[p0]? = some a0) (htrue : pred a0 = true)
    (hfalse : ∀ q b, q ≠ p0 → l[q]? = some b → pred b = false) :
    l.filter pred = [a0] := by
  induction l generalizing p0 with
  | nil => simp at h0
  | cons a l ih =>
      cases p0 with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
          subst h0
          rw [List.filter_cons_of_pos htrue]
          congr 1
          rw [List.filter_eq_nil_iff]
          intro b hb
          obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hb
          have := hfalse (q + 1) b (Nat.succ_ne_zero q) (by simpa using hq)
          simp [this]
      | succ p0 =>
          simp only [List.getElem?_cons_succ] at h0
          have hfalse2 : ∀ q b, q ≠ p0 → l[q]? = some b → pred b = false := by
            intro q b hne hq
            exact hfalse (q + 1) b (by omega) (by simpa using hq)
          have hane : pred a = false := hfalse 0 a (by omega) rfl
          rw [List.filter_cons_of_neg (by simp [hane])]
          exact ih p0 h0 hfalse2

/-- Position-decomposition of an index into a `flatMap` whose blocks may have
different lengths: `i` splits as `offset + p`, with `offset` the total length
of the first `n` blocks, `vals[n]? = some a`, `p < (block a).length`, and the
value at `i` is the value at position `p` of `block a`. -/
theorem flatMap_getElem_of_lengths {α β : Type} (block : α → List β) :
    ∀ (vals : List α) (i : ℕ), i < (vals.flatMap block).length →
      ∃ n p a, p < (block a).length ∧ vals[n]? = some a ∧
        i = ((vals.take n).flatMap block).length + p ∧
        (vals.flatMap block)[i]? = (block a)[p]? := by
  intro vals
  induction vals with
  | nil => intro i hi; simp at hi
  | cons a vals ih =>
      intro i hi
      rw [List.flatMap_cons]
      rcases Nat.lt_or_ge i (block a).length with h | h
      · exact ⟨0, i, a, h, by simp, by simp, by rw [List.getElem?_append_left h]⟩
      · have hi2 : i < (block a).length + (vals.flatMap block).length := by
          simpa [List.length_append] using hi
        have hi' : i - (block a).length < (vals.flatMap block).length := by omega
        obtain ⟨n, p, a', hpL, hva, hoff, heq⟩ := ih (i - (block a).length) hi'
        refine ⟨n + 1, p, a', hpL, by simpa using hva, ?_, ?_⟩
        · rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
          omega
        · rw [List.getElem?_append_right h, heq]

/-- The forward direction of `flatMap_uniform_getElem`: for a uniform-block
`flatMap`, the value at position `n * L + p` is the value at position `p` of
the `n`-th block. -/
theorem flatMap_uniform_getElem_fwd {α β : Type} (block : α → List β) (L : ℕ)
    (hL : ∀ a, (block a).length = L) :
    ∀ (vals : List α) (n p : ℕ) (a : α), vals[n]? = some a → p < L →
      (vals.flatMap block)[n * L + p]? = (block a)[p]? := by
  intro vals
  induction vals with
  | nil => intro n p a hva hp; simp at hva
  | cons a0 vals ih =>
      intro n p a hva hp
      rw [List.flatMap_cons]
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hva
          subst hva
          simp only [Nat.zero_mul, Nat.zero_add]
          rw [List.getElem?_append_left (by rw [hL]; exact hp)]
      | succ n =>
          simp only [List.getElem?_cons_succ] at hva
          rw [show (n + 1) * L + p = L + (n * L + p) by rw [Nat.succ_mul]; omega]
          rw [List.getElem?_append_right (by rw [hL]; omega)]
          simp only [hL, Nat.add_sub_cancel_left]
          exact ih n p a hva hp

/-- Position-decomposition of a single index into a uniform-block `flatMap`:
`i < vals.length * L` splits as `i = n * L + p` with `vals[n]? = some a` and
`p < L`, and the value at `i` reads off as the value at position `p` of the
block belonging to `a`. -/
theorem flatMap_uniform_getElem {α β : Type} (block : α → List β) (L : ℕ)
    (hL : ∀ a, (block a).length = L) :
    ∀ (vals : List α) (i : ℕ), i < vals.length * L →
      ∃ n p a, p < L ∧ i = n * L + p ∧ vals[n]? = some a ∧
        (vals.flatMap block)[i]? = (block a)[p]? := by
  intro vals i hi
  have hi' : i < (vals.flatMap block).length := by
    rw [List.length_flatMap]
    have heq1 : (vals.map (fun a => (block a).length)) = vals.map (fun _ => L) := by
      apply List.map_congr_left
      intro a _
      exact hL a
    rw [heq1, List.map_const', List.sum_const_nat]
    omega
  obtain ⟨n, p, a, hpL, hva, hoff, heq⟩ := flatMap_getElem_of_lengths block vals i hi'
  have hnlt : n < vals.length := (List.getElem?_eq_some_iff.mp hva).1
  have htakelen : (vals.take n).length = n := by
    rw [List.length_take]
    omega
  have hlenflat : ((vals.take n).flatMap block).length = n * L := by
    rw [List.length_flatMap]
    have heq2 : ((vals.take n).map (fun a => (block a).length))
        = (vals.take n).map (fun _ => L) := by
      apply List.map_congr_left
      intro a _
      exact hL a
    rw [heq2, List.map_const', List.sum_const_nat, htakelen]
  refine ⟨n, p, a, ?_, ?_, hva, heq⟩
  · rw [← hL a]; exact hpL
  · rw [hoff, hlenflat]

/-- Filtering a uniform-block `flatMap`, when `pred` matches exactly one
position `p0` in every block, reads off directly as the per-block match, with
the original (zipIdx) position carried along. -/
theorem zipIdx_flatMap_filter_getElem {α β : Type} (block : α → List β) (L p0 : ℕ)
    (hL : ∀ a, (block a).length = L)
    (predL : β → Bool) (bval : α → β) (h0 : ∀ a, (block a)[p0]? = some (bval a))
    (htrue : ∀ a, predL (bval a) = true)
    (hfalse : ∀ a q b, q ≠ p0 → (block a)[q]? = some b → predL b = false) :
    ∀ (vals : List α) (k n : ℕ) (a : α), vals[n]? = some a →
      (((vals.flatMap block).zipIdx k).filter (fun p => predL p.1))[n]?
        = some (bval a, k + n * L + p0) := by
  intro vals
  induction vals with
  | nil => intro k n a hva; simp at hva
  | cons a vals ih =>
      intro k n a' hva'
      rw [List.flatMap_cons, List.zipIdx_append, hL, List.filter_append]
      have hsingle : (((block a).zipIdx k).filter (fun p => predL p.1)) = [(bval a, k+p0)] := by
        apply list_filter_singleton_of_unique' ((block a).zipIdx k) (fun p => predL p.1) p0
          (bval a, k+p0)
        · rw [List.getElem?_zipIdx, h0 a]
          rfl
        · exact htrue a
        · intro q b hq hget
          rw [List.getElem?_zipIdx] at hget
          rcases hb : (block a)[q]? with _ | b0
          · rw [hb] at hget; simp at hget
          · rw [hb] at hget
            simp only [Option.map_some, Option.some.injEq] at hget
            rw [← hget]
            exact hfalse a q b0 hq hb
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hva'
          subst hva'
          rw [hsingle]
          simp
      | succ n =>
          simp only [List.getElem?_cons_succ] at hva'
          rw [hsingle, List.getElem?_append_right (by simp)]
          simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_sub_cancel]
          have hih := ih (k + L) n a' hva'
          have hsm : (n + 1) * L = n * L + L := Nat.succ_mul n L
          have heq : k + L + n * L + p0 = k + (n + 1) * L + p0 := by rw [hsm]; omega
          rw [← heq]
          exact hih

/-- `zipIdx_flatMap_filter_getElem` for blocks of varying length, with a
marked position `p0 a` that may depend on the block: the offset is the length
of the first `n` blocks instead of `n * L`. -/
theorem flatMap_filter_getElem_of_lengths {α β : Type} (block : α → List β) (p0 : α → ℕ)
    (predL : β → Bool) (bval : α → β) (h0 : ∀ a, (block a)[p0 a]? = some (bval a))
    (htrue : ∀ a, predL (bval a) = true)
    (hfalse : ∀ a q b, q ≠ p0 a → (block a)[q]? = some b → predL b = false) :
    ∀ (vals : List α) (k n : ℕ) (a : α), vals[n]? = some a →
      (((vals.flatMap block).zipIdx k).filter (fun p => predL p.1))[n]?
        = some (bval a, k + ((vals.take n).flatMap block).length + p0 a) := by
  intro vals
  induction vals with
  | nil => intro k n a hva; simp at hva
  | cons a vals ih =>
      intro k n a' hva'
      rw [List.flatMap_cons, List.zipIdx_append, List.filter_append]
      have hsingle : (((block a).zipIdx k).filter (fun p => predL p.1)) = [(bval a, k + p0 a)] := by
        apply list_filter_singleton_of_unique' ((block a).zipIdx k) (fun p => predL p.1) (p0 a)
          (bval a, k + p0 a)
        · rw [List.getElem?_zipIdx, h0 a]
          rfl
        · exact htrue a
        · intro q b hq hget
          rw [List.getElem?_zipIdx] at hget
          rcases hb : (block a)[q]? with _ | b0
          · rw [hb] at hget; simp at hget
          · rw [hb] at hget
            simp only [Option.map_some, Option.some.injEq] at hget
            rw [← hget]
            exact hfalse a q b0 hq hb
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hva'
          subst hva'
          rw [hsingle]
          simp
      | succ n =>
          simp only [List.getElem?_cons_succ] at hva'
          rw [hsingle, List.getElem?_append_right (by simp)]
          simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.add_sub_cancel]
          have hih := ih (k + (block a).length) n a' hva'
          have hoffset : k + (((a :: vals).take (n + 1)).flatMap block).length + p0 a'
              = (k + (block a).length) + ((vals.take n).flatMap block).length + p0 a' := by
            rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
            omega
          rw [hoffset]
          exact hih

/-- If `l` has one more entry than `ks`, its first `ks.length` entries' second
components have lengths `ks[m] + 1`, and its last entry's second component has
length `1`, then the total of its second-component lengths is
`(ks.map (· + 1)).sum + 1`. Induction on `ks`. -/
theorem sum_snd_length_of_forall_getElem {A B : Type} (l : List (A × List B)) (ks : List ℕ)
    (hlen : l.length = ks.length + 1)
    (hpre : ∀ m, m < ks.length → ∃ a vs km, l[m]? = some (a, vs) ∧ ks[m]? = some km ∧
      vs.length = km + 1)
    (hlast : ∃ a vs, l[ks.length]? = some (a, vs) ∧ vs.length = 1) :
    (l.map (fun p => p.2.length)).sum = (ks.map (· + 1)).sum + 1 := by
  induction ks generalizing l with
  | nil =>
      obtain ⟨a, vs, h0, hvs⟩ := hlast
      simp only [List.length_nil] at hlen h0
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
      subst hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
  | cons k0 ks' ih =>
      have hlencons : (k0 :: ks').length = ks'.length + 1 := by simp
      have hlen1 : l.length = ks'.length + 2 := by rw [hlencons] at hlen; omega
      have hne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
      obtain ⟨l0, l', rfl⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨a0, vs0, km0, hl00, hks00, hvs0⟩ := hpre 0 (by rw [hlencons]; omega)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl00 hks00
      have hlencons2 : (l0 :: l').length = l'.length + 1 := by simp
      have hlen' : l'.length = ks'.length + 1 := by rw [hlencons2] at hlen1; omega
      have hpre' : ∀ m, m < ks'.length → ∃ a vs km, l'[m]? = some (a, vs) ∧ ks'[m]? = some km ∧
          vs.length = km + 1 := by
        intro m hm
        obtain ⟨a, vs, km, hlm, hksm, hvsm⟩ := hpre (m + 1) (by rw [hlencons]; omega)
        refine ⟨a, vs, km, ?_, ?_, hvsm⟩
        · simpa [List.getElem?_cons_succ] using hlm
        · simpa [List.getElem?_cons_succ] using hksm
      have hlast' : ∃ a vs, l'[ks'.length]? = some (a, vs) ∧ vs.length = 1 := by
        obtain ⟨a, vs, hl, hvs⟩ := hlast
        refine ⟨a, vs, ?_, hvs⟩
        rw [hlencons] at hl
        simpa [List.getElem?_cons_succ] using hl
      have hih := ih l' hlen' hpre' hlast'
      have hsum : l0.2.length = km0 + 1 := by rw [hl00]; exact hvs0
      have hkm0eq : k0 = km0 := hks00
      calc ((l0 :: l').map (fun p => p.2.length)).sum
          = l0.2.length + (l'.map (fun p => p.2.length)).sum := by
            rw [List.map_cons, List.sum_cons]
        _ = (km0 + 1) + ((ks'.map (· + 1)).sum + 1) := by rw [hsum, hih]
        _ = ((k0 :: ks').map (· + 1)).sum + 1 := by
            rw [List.map_cons, List.sum_cons, ← hkm0eq]
            omega

/-- The index at which outer iteration `m` begins, as a prefix sum of `ks`
(iteration `i` making `ks[i] + 1` inner calls). Meaningful for
`m ≤ ks.length`. -/
def ksPrefix (ks : List ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => ksPrefix ks m + (ks.getD m 0 + 1)

/-- `ksPrefix ks m = 0` iff `m = 0`. -/
theorem ksPrefix_eq_zero_iff (ks : List ℕ) : ∀ m, ksPrefix ks m = 0 ↔ m = 0
  | 0 => by simp [ksPrefix]
  | m + 1 => by simp only [ksPrefix]; omega

/-- `ksPrefix` across a `List.cons`: peeling `ks`'s head `k0` adds `k0 + 1` to
every later prefix sum. -/
theorem ksPrefix_cons (k0 : ℕ) (ks' : List ℕ) (m : ℕ) :
    ksPrefix (k0 :: ks') (m + 1) = (k0 + 1) + ksPrefix ks' m := by
  induction m with
  | zero => simp [ksPrefix]
  | succ m ih =>
      have hgetD : (k0 :: ks').getD (m + 1) 0 = ks'.getD m 0 := rfl
      show ksPrefix (k0 :: ks') (m + 1) + ((k0 :: ks').getD (m + 1) 0 + 1) =
        (k0 + 1) + ksPrefix ks' (m + 1)
      rw [ih, hgetD]
      show (k0 + 1) + ksPrefix ks' m + (ks'.getD m 0 + 1) = (k0 + 1) + ksPrefix ks' (m + 1)
      have : ksPrefix ks' (m + 1) = ksPrefix ks' m + (ks'.getD m 0 + 1) := rfl
      omega

/-- `ksPrefix ks` is monotone. -/
theorem ksPrefix_mono (ks : List ℕ) : Monotone (ksPrefix ks) := by
  apply monotone_nat_of_le_succ
  intro n
  show ksPrefix ks n ≤ ksPrefix ks n + (ks.getD n 0 + 1)
  omega

/-- `ksPrefix ks m ≥ m`. -/
theorem ksPrefix_ge (ks : List ℕ) : ∀ m, m ≤ ksPrefix ks m
  | 0 => le_refl 0
  | m + 1 => by
      have ih := ksPrefix_ge ks m
      show m + 1 ≤ ksPrefix ks m + (ks.getD m 0 + 1)
      omega

/-- Inverts `ksPrefix`: an index `i < ksPrefix ks ks.length` falls in a unique
outer group `m`, with `ks[m]? = some km`, `n < km + 1` and
`i = ksPrefix ks m + n`. Induction on `ks`. -/
theorem ksPrefix_invert : ∀ (ks : List ℕ) (i : ℕ), i < ksPrefix ks ks.length →
    ∃ m, m < ks.length ∧ ∃ km n, ks[m]? = some km ∧ n < km + 1 ∧ i = ksPrefix ks m + n
  | [], i, hi => by simp [ksPrefix] at hi
  | k0 :: ks', i, hi => by
      have hlen : (k0 :: ks').length = ks'.length + 1 := by simp
      rw [hlen, ksPrefix_cons] at hi
      rcases Nat.lt_or_ge i (k0 + 1) with h | h
      · exact ⟨0, by simp, k0, i, rfl, h, by simp [ksPrefix]⟩
      · obtain ⟨m, hm, km, n, hkm, hn, heq⟩ := ksPrefix_invert ks' (i - (k0 + 1)) (by omega)
        refine ⟨m + 1, by simp only [List.length_cons]; omega, km, n, ?_, hn, ?_⟩
        · simpa using hkm
        · show i = ksPrefix (k0 :: ks') (m + 1) + n
          rw [ksPrefix_cons]
          omega

/-- `ksPrefix ks ks.length` is the sum of `ks[i] + 1` over all entries. -/
theorem ksPrefix_eq_sum : ∀ ks : List ℕ, ksPrefix ks ks.length = (ks.map (· + 1)).sum
  | [] => rfl
  | k0 :: ks' => by
      have hlencons : (k0 :: ks').length = ks'.length + 1 := by simp
      rw [hlencons, ksPrefix_cons, ksPrefix_eq_sum ks']
      simp [List.sum_cons]

/-- `ksPrefix ks m` is the sum of `ks[i] + 1` over the first `m` entries, for
`m ≤ ks.length` (beyond that it keeps growing by `1` per step). -/
theorem ksPrefix_eq_sum_take {ks : List ℕ} : ∀ m, m ≤ ks.length →
    ksPrefix ks m = ((ks.take m).map (· + 1)).sum := by
  intro m
  induction m with
  | zero => intro _; simp [ksPrefix]
  | succ m ih =>
      intro hm
      have hmlt : m < ks.length := by omega
      have ihm := ih (by omega)
      have hstep : ksPrefix ks (m + 1) = ksPrefix ks m + (ks.getD m 0 + 1) := rfl
      rw [hstep, ihm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmlt]
      simp only [Option.getD_some]
      have htake : ks.take (m + 1) = ks.take m ++ [ks[m]] := by
        rw [List.take_add_one]
        simp [List.getElem?_eq_getElem hmlt]
      rw [htake, List.map_append, List.sum_append]
      simp

/-- The length of a `flatten` of a mapped list is the sum of the mapped
blocks' lengths. -/
theorem flatten_map_length {α β : Type} (l : List α) (f : α → List β) :
    (l.map f).flatten.length = (l.map (fun a => (f a).length)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatten_cons, ih]

/-- `(o.map some).getD none = o`. -/
theorem Option_map_some_getD {α : Type} (x : Option α) : (x.map some).getD none = x := by
  cases x <;> rfl

/-- Position-decomposition for a `flatMap` over `l : List (A × List B)` with
per-entry blocks of varying length, phrased in terms of `ksPrefix`: a
filtered position is located by an outer index `m` and an inner index `n`,
at offset `ksPrefix ks m + n`. -/
theorem ksPrefix_flatMap_map_getElem {A B C : Type} (l : List (A × List B)) (ks : List ℕ)
    (f : B → C)
    (hlen : l.length = ks.length + 1)
    (hpre : ∀ m, m < ks.length → ∃ a vs km, l[m]? = some (a, vs) ∧ ks[m]? = some km ∧
      vs.length = km + 1)
    (hlast : ∃ a vs, l[ks.length]? = some (a, vs) ∧ vs.length = 1) :
    ∀ j, j < ksPrefix ks ks.length + 1 →
      ∃ m, m < ks.length + 1 ∧ ∃ a vs n b, l[m]? = some (a, vs) ∧ n < vs.length ∧
        vs[n]? = some b ∧ j = ksPrefix ks m + n ∧
        (l.flatMap (fun p => p.2.map f))[j]? = some (f b) := by
  induction ks generalizing l with
  | nil =>
      intro j hj
      obtain ⟨a, vs, h0, hvs⟩ := hlast
      simp only [List.length_nil] at hlen h0
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
      subst hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
      subst h0
      simp only [List.length_nil, ksPrefix] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hvs
      subst hb
      exact ⟨0, by omega, a, [b], 0, b, rfl, by omega, rfl, by simp [ksPrefix], by simp⟩
  | cons k0 ks' ih =>
      intro j hj
      have hlencons : (k0 :: ks').length = ks'.length + 1 := by simp
      have hlen1 : l.length = ks'.length + 2 := by rw [hlencons] at hlen; omega
      have hne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
      obtain ⟨l0, l', rfl⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨a0, vs0, km0, hl00, hks00, hvs0⟩ := hpre 0 (by rw [hlencons]; omega)
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl00 hks00
      have hkm0eq : k0 = km0 := hks00
      have hsum : vs0.length = k0 + 1 := by rw [hvs0, hkm0eq]
      have hlencons2 : (l0 :: l').length = l'.length + 1 := by simp
      have hlen' : l'.length = ks'.length + 1 := by rw [hlencons2] at hlen1; omega
      have hpre' : ∀ m, m < ks'.length → ∃ a vs km, l'[m]? = some (a, vs) ∧ ks'[m]? = some km ∧
          vs.length = km + 1 := by
        intro m hm
        obtain ⟨a, vs, km, hlm, hksm, hvsm⟩ := hpre (m + 1) (by rw [hlencons]; omega)
        refine ⟨a, vs, km, ?_, ?_, hvsm⟩
        · simpa [List.getElem?_cons_succ] using hlm
        · simpa [List.getElem?_cons_succ] using hksm
      have hlast' : ∃ a vs, l'[ks'.length]? = some (a, vs) ∧ vs.length = 1 := by
        obtain ⟨a, vs, hl, hvs⟩ := hlast
        refine ⟨a, vs, ?_, hvs⟩
        rw [hlencons] at hl
        simpa [List.getElem?_cons_succ] using hl
      have hks0 : ksPrefix (k0 :: ks') 0 = 0 := rfl
      have hflat : (l0 :: l').flatMap (fun p => p.2.map f)
          = l0.2.map f ++ l'.flatMap (fun p => p.2.map f) := List.flatMap_cons ..
      have hl02 : l0.2 = vs0 := by rw [hl00]
      have hl02len : (l0.2.map f).length = k0 + 1 := by rw [hl02, List.length_map, hsum]
      have hl0eta : l0 = (l0.1, vs0) := by rw [← hl02]
      rcases Nat.lt_or_ge j (k0 + 1) with hcase | hcase
      · have hjlt : j < vs0.length := by omega
        obtain ⟨b, hb⟩ : ∃ b, vs0[j]? = some b := ⟨vs0[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
        refine ⟨0, by omega, l0.1, vs0, j, b, ?_, hjlt, hb, by omega, ?_⟩
        · rw [List.getElem?_cons_zero]
          exact congrArg some hl0eta
        · rw [hflat, List.getElem?_append_left (by omega : j < (l0.2.map f).length),
            hl02, List.getElem?_map, hb]
          rfl
      · have hj' : j - (k0 + 1) < ksPrefix ks' ks'.length + 1 := by
          rw [hlencons, ksPrefix_cons] at hj
          omega
        obtain ⟨m', hm', a, vs, n, b, hlm', hnlt, hvsn, hjeq', hgetflat⟩ :=
          ih l' hlen' hpre' hlast' (j - (k0 + 1)) hj'
        refine ⟨m' + 1, by omega, a, vs, n, b, ?_, hnlt, hvsn, ?_, ?_⟩
        · simpa [List.getElem?_cons_succ] using hlm'
        · rw [ksPrefix_cons]
          omega
        · rw [hflat, List.getElem?_append_right (by omega : (l0.2.map f).length ≤ j)]
          rw [show j - (l0.2.map f).length = j - (k0 + 1) by rw [hl02len]]
          exact hgetflat

/-- Filtering a `flatMap` distributes over its blocks. -/
theorem list_filter_flatMap_distrib {α β} (l : List α) (f : α → List β) (p : β → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun x => (f x).filter p) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.filter_append, ih]

/-- The `i`-th element of `l.filter pred` sits at a given original position
`P` if `l[P]` satisfies `pred` and exactly `i` elements before `P` do. No
`Nodup` assumption is needed: the element is identified by its position. -/
theorem List.getElem?_filter_of_take_filter_length {α : Type} (l : List α) (pred : α → Bool)
    (P i : ℕ) (x : α) (hl : l[P]? = some x) (hpred : pred x = true)
    (hcount : ((l.take P).filter pred).length = i) :
    (l.filter pred)[i]? = some x := by
  induction l generalizing P i with
  | nil => simp at hl
  | cons a l ih =>
      cases P with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
          subst hl
          simp only [List.take_zero, List.filter_nil, List.length_nil] at hcount
          subst hcount
          rw [List.filter_cons_of_pos hpred, List.getElem?_cons_zero]
      | succ P =>
          simp only [List.getElem?_cons_succ] at hl
          rw [List.take_succ_cons] at hcount
          by_cases ha : pred a = true
          · rw [List.filter_cons_of_pos ha, List.length_cons] at hcount
            have hi1 : i = (i - 1) + 1 := by omega
            rw [List.filter_cons_of_pos ha, hi1, List.getElem?_cons_succ]
            exact ih P (i - 1) hl (by omega)
          · rw [List.filter_cons_of_neg (by simpa using ha)] at hcount
            rw [List.filter_cons_of_neg (by simpa using ha)]
            exact ih P i hl hcount

/-- Two equal-length lists whose predicates agree position by position have
the same filtered-`take` count for every prefix length `P`. -/
theorem List.filter_take_length_eq_of_forall_getElem {α β : Type} {l1 : List α} {l2 : List β}
    (hlen : l1.length = l2.length) (p1 : α → Bool) (p2 : β → Bool)
    (hrel : ∀ i (h1 : i < l1.length) (h2 : i < l2.length), p1 (l1[i]'h1) = p2 (l2[i]'h2)) :
    ∀ P, ((l1.take P).filter p1).length = ((l2.take P).filter p2).length := by
  intro P
  induction P with
  | zero => simp
  | succ P ih =>
      rw [List.take_add_one, List.take_add_one]
      rcases Nat.lt_or_ge P l1.length with hP1 | hP1
      · have hP2 : P < l2.length := hlen ▸ hP1
        rw [List.getElem?_eq_getElem hP1, List.getElem?_eq_getElem hP2]
        have hrelP := hrel P hP1 hP2
        simp only [Option.toList_some, List.filter_append, List.length_append, ih,
          List.filter_singleton, hrelP]
        rcases p2 l2[P] with _ | _ <;> simp
      · have hP2 : P ≥ l2.length := hlen ▸ hP1
        rw [List.getElem?_eq_none_iff.mpr hP1, List.getElem?_eq_none_iff.mpr hP2]
        simp [ih]

/-- A `flatMap` of singleton lists is a `map`. -/
theorem list_flatMap_singleton_eq_map {α β : Type} (f : α → β) (l : List α) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- Taking `n * L + p` entries of a uniform-block `flatMap`, for an in-block
offset `p ≤ L`: the first `n` blocks in full, plus the first `p` entries of
the `n`-th block. -/
theorem list_take_flatMap_uniform_offset {α β : Type} (block : α → List β) (L : ℕ)
    (hL : ∀ a, (block a).length = L) (vals : List α) :
    ∀ n p a, vals[n]? = some a → p ≤ L →
      (vals.flatMap block).take (n * L + p) = (vals.take n).flatMap block ++ (block a).take p := by
  induction vals with
  | nil => intro n p a hva _; simp at hva
  | cons a0 vals ih =>
      intro n p a hva hp
      rw [List.flatMap_cons]
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hva
          subst hva
          simp only [Nat.zero_mul, Nat.zero_add, List.take_zero, List.flatMap_nil,
            List.nil_append]
          exact List.take_append_of_le_length (hp.trans_eq (hL a0).symm)
      | succ n =>
          simp only [List.getElem?_cons_succ] at hva
          have hmul : (n + 1) * L + p = L + (n * L + p) := by rw [Nat.succ_mul]; omega
          rw [hmul, List.take_append,
            List.take_of_length_le ((le_of_eq (hL a0)).trans (Nat.le_add_right L (n * L + p))),
            hL a0, Nat.add_sub_cancel_left, ih n p a hva hp, List.take_succ_cons,
            List.flatMap_cons, List.append_assoc]

/-- Taking `n * L` entries of a uniform-block `flatMap` is `flatMap`-ing the
first `n` blocks. -/
theorem list_take_flatMap_uniform {α β : Type} (block : α → List β) (L : ℕ)
    (hL : ∀ a, (block a).length = L) (vals : List α) :
    ∀ n, n ≤ vals.length → (vals.flatMap block).take (n * L) = (vals.take n).flatMap block := by
  induction vals with
  | nil => intro n hn; simp_all
  | cons a vals ih =>
      intro n hn
      cases n with
      | zero => simp
      | succ n =>
          rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons]
          have hn' : n ≤ vals.length := by simpa using hn
          have hmul : (n + 1) * L = L + n * L := by rw [Nat.succ_mul, Nat.add_comm]
          rw [hmul, List.take_append,
            List.take_of_length_le ((le_of_eq (hL a)).trans (Nat.le_add_right L (n * L))), hL a,
            Nat.add_sub_cancel_left, ih n hn']

/-- For a uniform-block `flatMap` in which every block has exactly one
`pred`-match, at the same offset `p0 < L`, the number of matches strictly
before position `n * L + p` (with `n ≤ vals.length`, `p ≤ L`) is `n` if
`p ≤ p0` and `n + 1` if `p0 < p`. -/
theorem flatMap_uniform_take_count {α β : Type} (block : α → List β) (L : ℕ)
    (hL : ∀ a, (block a).length = L) (pred : β → Bool) (p0 : ℕ) (_ : p0 < L) (g : α → β)
    (h0 : ∀ a, (block a)[p0]? = some (g a)) (htrue : ∀ a, pred (g a) = true)
    (hfalse : ∀ a q b, q ≠ p0 → (block a)[q]? = some b → pred b = false)
    (vals : List α) (n : ℕ) (a : α) (hva : vals[n]? = some a) (p : ℕ) (hp : p ≤ L) :
    (((vals.flatMap block).take (n * L + p)).filter pred).length
      = n + (if p0 < p then 1 else 0) := by
  rw [list_take_flatMap_uniform_offset block L hL vals n p a hva hp, List.filter_append,
    List.length_append]
  have hn : n < vals.length := (List.getElem?_eq_some_iff.mp hva).1
  have hone : ∀ a', (block a').filter pred = [g a'] := fun a' =>
    list_filter_singleton_of_unique' (block a') pred p0 (g a') (h0 a') (htrue a') (hfalse a')
  have hpiece1 : (((vals.take n).flatMap block).filter pred).length = n := by
    rw [list_filter_flatMap_distrib]
    have heq : (fun x => (block x).filter pred) = (fun x => [g x] : α → List β) := funext hone
    rw [heq, list_flatMap_singleton_eq_map, List.length_map, List.length_take]
    omega
  have hpiece2 : (((block a).take p).filter pred).length = if p0 < p then 1 else 0 := by
    split_ifs with hlt
    · have h0take : (List.take p (block a))[p0]? = some (g a) := by
        rw [List.getElem?_take, if_pos hlt]
        exact h0 a
      have hfalsetake : ∀ q b, q ≠ p0 → (List.take p (block a))[q]? = some b → pred b = false := by
        intro q b hq hqb
        rw [List.getElem?_take] at hqb
        split_ifs at hqb with hqp
        exact hfalse a q b hq hqb
      rw [list_filter_singleton_of_unique' (List.take p (block a)) pred p0 (g a) h0take
        (htrue a) hfalsetake]
      rfl
    · have hnil : ((block a).take p).filter pred = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx hpx
        obtain ⟨q, hqlt, hqget⟩ := List.mem_iff_getElem.mp hx
        have hqlt' : q < p := by
          simp only [List.length_take] at hqlt
          omega
        have hqlen : q < (block a).length := hqlt'.trans_le (hp.trans_eq (hL a).symm)
        have hqfull : (block a)[q]? = some x := by
          rw [List.getElem?_eq_getElem hqlen]
          simpa using hqget
        have hqne : q ≠ p0 := by omega
        have hfx := hfalse a q x hqne hqfull
        rw [hfx] at hpx
        simp at hpx
      rw [hnil]
      rfl
  omega

/-! ## Non-uniform `flatMap`

Generalizations of `list_take_flatMap_uniform_offset` and
`flatMap_uniform_getElem_fwd` to blocks of varying length, as in the outer
blocks of the nested guesser threads: the position `n * L + p` becomes
`((vals.take n).flatMap block).length + p`. -/

/-- `list_take_flatMap_uniform_offset` for blocks of varying length: taking up
to `p` items into block `n` gives the first `n` blocks plus the first `p`
elements of block `n`. -/
theorem list_take_flatMap_offset {α β : Type} (block : α → List β) :
    ∀ (vals : List α) (n p : ℕ) (a : α), vals[n]? = some a → p ≤ (block a).length →
      (vals.flatMap block).take (((vals.take n).flatMap block).length + p) =
        (vals.take n).flatMap block ++ (block a).take p := by
  intro vals
  induction vals with
  | nil => intro n p a hva _; simp at hva
  | cons a0 vals ih =>
      intro n p a hva hp
      rw [List.flatMap_cons]
      cases n with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hva
          subst hva
          simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
            List.nil_append]
          exact List.take_append_of_le_length hp
      | succ n =>
          simp only [List.getElem?_cons_succ] at hva
          rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
          have hmul : (block a0).length + ((vals.take n).flatMap block).length + p
              = (block a0).length + (((vals.take n).flatMap block).length + p) := by omega
          rw [hmul, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
            Nat.add_sub_cancel_left, ih n p a hva hp, List.append_assoc]

/-- The `getElem?` corollary of `list_take_flatMap_offset`: the value at
position `((vals.take n).flatMap block).length + p` is the value at position
`p` of block `n`. -/
theorem list_take_flatMap_offset_getElem {α β : Type} (block : α → List β)
    (vals : List α) (n p : ℕ) (a : α) (hva : vals[n]? = some a) (hp : p < (block a).length) :
    (vals.flatMap block)[((vals.take n).flatMap block).length + p]? = (block a)[p]? := by
  have heq := list_take_flatMap_offset block vals n (p + 1) a hva hp
  set L := ((vals.take n).flatMap block).length with hL
  have hlhs : (vals.flatMap block)[L + p]? =
      ((vals.flatMap block).take (L + (p + 1)))[L + p]? :=
    (List.getElem?_take_of_lt (by omega : L + p < L + (p + 1))).symm
  have hrhs : ((vals.take n).flatMap block ++ (block a).take (p + 1))[L + p]? =
      ((block a).take (p + 1))[p]? := by
    rw [show L + p = ((vals.take n).flatMap block).length + p from by rw [← hL],
      List.getElem?_append_right (Nat.le_add_right _ _)]
    congr 1
    omega
  rw [hlhs, heq, hrhs, List.getElem?_take_of_succ]


end RAUndecidability
