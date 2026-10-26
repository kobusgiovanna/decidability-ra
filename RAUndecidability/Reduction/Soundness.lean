import RAUndecidability.Reduction.Soundness.NoSkipping

/-!
# Soundness (Lemma 3.1, Lemma 3.1)

An execution of `ConcProg I` reaching its final state gives a solution of `I`.
Transcribes the paragraph "Proof of Lemma 3.1" in
Section 3.4. The argument has two halves:

1. **The guesser pair agrees** (`guessAX_guessBX_js_eq`, the proof's first
   three paragraphs): the index sequence `(v0AX, jsAX)` guessed by `g_α^x`
   equals the sequence `(v0BX, jsBX)` guessed by `g_β^x`. This is shown by one
   chain through `c^y`: `c^y` reads the same value from `y_α` and `y_β`
   (step 1); by Eq. (17) these come from `g_α^y`'s and `g_β^y`'s writes
   (step 2); each of these threads writes the same `aux` to `y_α`/`y_β` and to
   its bridge location `ℓ^{y,x}` (step 3); by Eq. (15) `g_α^x`/`g_β^x` read
   these bridge values (step 4), which are their own `aux` draws (step 5).
   The lengths of the sequences are matched by comparing the iterations at
   which each thread reads or writes `⊥`.
2. **The words agree** (`guessAX_guessBX_xA_xB_flatten_eq`, the proof's last
   paragraph): `((v0AX::jsAX).map I.α).flatten = ((v0BX::jsBX).map I.β).flatten`,
   by the analogous chain through `c^x`, which reads the same letter from
   `x_α` and `x_β`.

`guessAX_guessBX_IsSolution` combines the two, and `soundness` unfolds
`(ConcProg I).ReachesFinal`.
-/

namespace RAUndecidability

/-- `g_α^y`'s `ellAyx`-write at filtered index `i + 1`, at the `G.nthWrite`
level: value `Val.cntAux (kw.1 + 1) kw.2` for `kws[i]? = some kw`. -/
theorem guessAY_ellAyx_write_nthWrite_val_succ {I : PCPInstance} (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))} (i : ℕ)
    (hw : G.threadWord Tid.guessAY = (guessAYBlockWord I v0 kws).map some)
    {kw : Fin 4 × Option (Fin I.n)} (hkw : kws[i]? = some kw) :
    ∃ e, G.nthWrite Tid.guessAY Loc.ellAyx (i + 1) = some e ∧
      e.val = Val.cntAux (kw.1 + 1) kw.2 := by
  have hval := guessAYBlockWord_ellAyx_write_val_succ I v0 kws i
  rw [hkw] at hval
  simp only [Option.map_some] at hval
  obtain ⟨e, he, hlab⟩ := ExecutionGraph.nthWrite_lab_eq_of_threadWord hw hval
  refine ⟨e, he, ?_⟩
  rw [Event.val, hlab]
  rfl

/-- `g_α^x`'s `ellAyx`-read at filtered index `0`, at the `G.nthRead` level:
value `vB0.2`. Both `guessAX_ellAyx_read_nthRead_pos0` and
`guessAXBlockWord_ellAyx_read_pos0` concern the entry of
`G.threadEvents Tid.guessAX` at raw position `3 + K0 * 3`. -/
theorem guessAX_ellAyx_read_nthRead_val0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some) :
    ∃ e, G.nthRead Tid.guessAX Loc.ellAyx 0 = some e ∧ e.val = vB0.2 := by
  obtain ⟨hlen, hread⟩ := guessAX_ellAyx_read_nthRead_pos0 I G hinner0len hw1
  have hlabP0 := guessAXBlockWord_ellAyx_read_pos0 I v1 v2 vB0 K0 inner0Rest hinner0len outerRest
  obtain ⟨e, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 (3 + K0 * 3) _ hlabP0
  refine ⟨((G.threadEvents Tid.guessAX)[3 + K0 * 3]'hlen).1, hread, ?_⟩
  rw [show (G.threadEvents Tid.guessAX)[3 + K0 * 3]'hlen
      = (G.threadEvents Tid.guessAX)[3 + K0 * 3]'hlt from rfl, heq]
  rw [Event.val, hlab]
  rfl

/-- `g_α^x`'s `ellAyx`-read at filtered index `m + 1` (`outerRest[m]`), at the
`G.nthRead` level: value `b.2` for `outerRest[m]? = some (b, vs)`. -/
theorem guessAX_ellAyx_read_nthRead_val_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) {b : Val I × Val I} {vs : List (Val I × Val I × Val I)}
    (hmbv : outerRest[m]? = some (b, vs)) :
    ∃ e, G.nthRead Tid.guessAX Loc.ellAyx (m + 1) = some e ∧ e.val = b.2 := by
  obtain ⟨hlen, hread⟩ := guessAX_ellAyx_read_nthRead_pos_outer I G hinner0len hw1 hks hK0
    houterLen houter houterLast m hm hmbv
  have hlabPm := guessAXBlockWord_ellAyx_read_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len ks N hks hK0 houterLen houter houterLast m hm b vs hmbv
  obtain ⟨e, hlt, heq, hlab⟩ :=
    G.threadEvents_getElem_lab_of_threadWord hw1 (nestedOuterStart ks N (m + 2) - 1) _ hlabPm
  refine ⟨((G.threadEvents Tid.guessAX)[nestedOuterStart ks N (m + 2) - 1]'hlen).1, hread, ?_⟩
  rw [show (G.threadEvents Tid.guessAX)[nestedOuterStart ks N (m + 2) - 1]'hlen
      = (G.threadEvents Tid.guessAX)[nestedOuterStart ks N (m + 2) - 1]'hlt from rfl, heq]
  rw [Event.val, hlab]
  rfl

/-- `CheckY`'s `yA`-read value at filtered index `0` (block 0, `First()`
branch): `Val.yTag (Tid.guessAY, true) (some v0)`. -/
theorem checkYBlockWord_yA_read_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((checkYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd))[0]? =
      some (⟨EventLabel.rd Tid.checkY Loc.yA (Val.yTag (Tid.guessAY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkY Loc.yA (Val.yTag (Tid.guessAY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `CheckY`'s `yA`-read value at filtered index `i + 1` (`blockRest`'s
`i`-th entry): `Val.yTag (Tid.guessAY, false) kw.2` for `kws[i]? = some kw`. -/
theorem checkYBlockWord_yA_read_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((checkYBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.rd Tid.checkY Loc.yA
        (Val.yTag (Tid.guessAY, false) kw.2), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkY Loc.yA (Val.yTag (Tid.guessAY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.checkY Loc.yA
        (Val.yTag (Tid.guessAY, false) kw.2), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.yA ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkY Loc.yA (Val.yTag (Tid.guessAY, false) kw.2), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkY)] := by
      intro kw
      unfold checkYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr]
  simp

/-- `CheckY`'s `yB`-read value at filtered index `0`:
`Val.yTag (Tid.guessBY, true) (some v0)`. -/
theorem checkYBlockWord_yB_read_val0 (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) :
    ((checkYBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd))[0]? =
      some (⟨EventLabel.rd Tid.checkY Loc.yB (Val.yTag (Tid.guessBY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkY Loc.yB (Val.yTag (Tid.guessBY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `CheckY`'s `yB`-read value at filtered index `i + 1`:
`Val.yTag (Tid.guessBY, false) kw.2` for `kws[i]? = some kw`. -/
theorem checkYBlockWord_yB_read_val_succ (I : PCPInstance) (v0 : Fin I.n)
    (kws : List (Fin 4 × Option (Fin I.n))) (i : ℕ) :
    ((checkYBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.rd Tid.checkY Loc.yB
        (Val.yTag (Tid.guessBY, false) kw.2), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
  unfold checkYBlockWord
  rw [List.filter_append]
  have hb0 : (checkYBlock0Elems I v0).filter (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkY Loc.yB (Val.yTag (Tid.guessBY, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkY)] := by
    unfold checkYBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkYBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.checkY Loc.yB
        (Val.yTag (Tid.guessBY, false) kw.2), rfl⟩ : ThreadLabel (domainOf I) Tid.checkY)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option (Fin I.n), (checkYBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.yB ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkY Loc.yB (Val.yTag (Tid.guessBY, false) kw.2), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkY)] := by
      intro kw
      unfold checkYBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr]
  simp

/-- Step 1, index `0`: `c^y`'s `0`-th reads of `yA` and `yB` (the `First()`
branch) carry the same `aux` value `some v0`. -/
theorem checkY_yA_read_yB_read_val_eq0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws).map some) :
    ∃ ea eb, G.nthRead Tid.checkY Loc.yA 0 = some ea ∧ G.nthRead Tid.checkY Loc.yB 0 = some eb ∧
      ea.val = Val.yTag (Tid.guessAY, true) (some v0) ∧
      eb.val = Val.yTag (Tid.guessBY, true) (some v0) := by
  obtain ⟨ea, hea, hlaba⟩ :=
    ExecutionGraph.nthRead_lab_eq_of_threadWord hw (checkYBlockWord_yA_read_val0 I v0 kws)
  obtain ⟨eb, heb, hlabb⟩ :=
    ExecutionGraph.nthRead_lab_eq_of_threadWord hw (checkYBlockWord_yB_read_val0 I v0 kws)
  refine ⟨ea, eb, hea, heb, ?_, ?_⟩
  · rw [Event.val, hlaba]; rfl
  · rw [Event.val, hlabb]; rfl

/-- Step 1, index `i + 1`: `c^y`'s `(i + 1)`-th reads of `yA` and `yB` carry
the same `aux` value `kw.2` for `kws[i]? = some kw`. -/
theorem checkY_yA_read_yB_read_val_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))} (i : ℕ)
    (hw : G.threadWord Tid.checkY = (checkYBlockWord I v0 kws).map some)
    {kw : Fin 4 × Option (Fin I.n)} (hkw : kws[i]? = some kw) :
    ∃ ea eb, G.nthRead Tid.checkY Loc.yA (i + 1) = some ea ∧
      G.nthRead Tid.checkY Loc.yB (i + 1) = some eb ∧
      ea.val = Val.yTag (Tid.guessAY, false) kw.2 ∧ eb.val = Val.yTag (Tid.guessBY, false) kw.2 := by
  have hvala := checkYBlockWord_yA_read_val_succ I v0 kws i
  rw [hkw] at hvala
  simp only [Option.map_some] at hvala
  have hvalb := checkYBlockWord_yB_read_val_succ I v0 kws i
  rw [hkw] at hvalb
  simp only [Option.map_some] at hvalb
  obtain ⟨ea, hea, hlaba⟩ := ExecutionGraph.nthRead_lab_eq_of_threadWord hw hvala
  obtain ⟨eb, heb, hlabb⟩ := ExecutionGraph.nthRead_lab_eq_of_threadWord hw hvalb
  refine ⟨ea, eb, hea, heb, ?_, ?_⟩
  · rw [Event.val, hlaba]; rfl
  · rw [Event.val, hlabb]; rfl

/-- Step 2, index `0`: `g_α^y`'s `0`-th `yA`-write and `g_β^y`'s `0`-th
`yB`-write both carry `some v0`. The writer of `c^y`'s read (`rf_total`) is
identified by its `Val.yTag` value (`G_writer_val_tid`; `yA`/`yB` also have
`c^y` as a writer, with `Val.primeTag` values), and its index by Eq. (17)
(`no_skipping_guessAY_checkY_yA`/`no_skipping_guessBY_checkY_yB`). -/
theorem guessAY_guessBY_yA_yB_write_val_eq0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) {v0 : Fin I.n}
    {ea eb : Event (domainOf I)} (hea : G.nthRead Tid.checkY Loc.yA 0 = some ea)
    (heb : G.nthRead Tid.checkY Loc.yB 0 = some eb)
    (hvala : ea.val = Val.yTag (Tid.guessAY, true) (some v0))
    (hvalb : eb.val = Val.yTag (Tid.guessBY, true) (some v0)) :
    ∃ ewa ewb, G.nthWrite Tid.guessAY Loc.yA 0 = some ewa ∧
      G.nthWrite Tid.guessBY Loc.yB 0 = some ewb ∧
      ewa.val = Val.yTag (Tid.guessAY, true) (some v0) ∧
      ewb.val = Val.yTag (Tid.guessBY, true) (some v0) := by
  have hamem : ea ∈ G.opEvents Tid.checkY Loc.yA OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨0, hea⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨heamem, _, _, heaop⟩ := G.mem_opEvents_iff.mp hamem
  obtain ⟨wa, hwa⟩ := G.rf_total (er := ea) heamem heaop
  have hwaval : wa.val = ea.val := G.rf_matches hwa
  rw [hvala] at hwaval
  have hwamem := (G.rf_subset hwa).1
  have hwawt : wa.op = OpType.wt := (G.rf_subset hwa).2.2.1
  have hwatid : wa.tid = Tid.guessAY :=
    G_writer_val_tid I G hG hwamem hwawt (t := Tid.guessAY) (by rw [hwaval]; rfl)
  have hwaloc : wa.loc = Loc.yA := by
    rw [(G.rf_subset hwa).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hamem).2.2.1
  have hwaindex : G.nthWrite Tid.guessAY Loc.yA (G.index wa) = some wa := by
    have hidx := G.index_nthEvent hwamem
    rw [hwatid, hwaloc, hwawt] at hidx
    exact hidx
  have haeq : G.index wa = 0 := no_skipping_guessAY_checkY_yA I G hG (G.index wa) 0 hwaindex hea hwa
  rw [haeq] at hwaindex
  have hbmem : eb ∈ G.opEvents Tid.checkY Loc.yB OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨0, heb⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨hebmem, _, _, hebop⟩ := G.mem_opEvents_iff.mp hbmem
  obtain ⟨wb, hwb⟩ := G.rf_total (er := eb) hebmem hebop
  have hwbval : wb.val = eb.val := G.rf_matches hwb
  rw [hvalb] at hwbval
  have hwbmem := (G.rf_subset hwb).1
  have hwbwt : wb.op = OpType.wt := (G.rf_subset hwb).2.2.1
  have hwbtid : wb.tid = Tid.guessBY :=
    G_writer_val_tid I G hG hwbmem hwbwt (t := Tid.guessBY) (by rw [hwbval]; rfl)
  have hwbloc : wb.loc = Loc.yB := by
    rw [(G.rf_subset hwb).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hbmem).2.2.1
  have hwbindex : G.nthWrite Tid.guessBY Loc.yB (G.index wb) = some wb := by
    have hidx := G.index_nthEvent hwbmem
    rw [hwbtid, hwbloc, hwbwt] at hidx
    exact hidx
  have hbeq : G.index wb = 0 := no_skipping_guessBY_checkY_yB I G hG (G.index wb) 0 hwbindex heb hwb
  rw [hbeq] at hwbindex
  exact ⟨wa, wb, hwaindex, hwbindex, hwaval, hwbval⟩

/-- Step 2, index `i + 1`: `g_α^y`'s `(i+1)`-th `yA`-write and `g_β^y`'s
`(i+1)`-th `yB`-write both carry `kw.2`. -/
theorem guessAY_guessBY_yA_yB_write_val_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ) {kw : Fin 4 × Option (Fin I.n)}
    {ea eb : Event (domainOf I)} (hea : G.nthRead Tid.checkY Loc.yA (i + 1) = some ea)
    (heb : G.nthRead Tid.checkY Loc.yB (i + 1) = some eb)
    (hvala : ea.val = Val.yTag (Tid.guessAY, false) kw.2)
    (hvalb : eb.val = Val.yTag (Tid.guessBY, false) kw.2) :
    ∃ ewa ewb, G.nthWrite Tid.guessAY Loc.yA (i + 1) = some ewa ∧
      G.nthWrite Tid.guessBY Loc.yB (i + 1) = some ewb ∧
      ewa.val = Val.yTag (Tid.guessAY, false) kw.2 ∧
      ewb.val = Val.yTag (Tid.guessBY, false) kw.2 := by
  have hamem : ea ∈ G.opEvents Tid.checkY Loc.yA OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨i + 1, hea⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨heamem, _, _, heaop⟩ := G.mem_opEvents_iff.mp hamem
  obtain ⟨wa, hwa⟩ := G.rf_total (er := ea) heamem heaop
  have hwaval : wa.val = ea.val := G.rf_matches hwa
  rw [hvala] at hwaval
  have hwamem := (G.rf_subset hwa).1
  have hwawt : wa.op = OpType.wt := (G.rf_subset hwa).2.2.1
  have hwatid : wa.tid = Tid.guessAY :=
    G_writer_val_tid I G hG hwamem hwawt (t := Tid.guessAY) (by rw [hwaval]; rfl)
  have hwaloc : wa.loc = Loc.yA := by
    rw [(G.rf_subset hwa).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hamem).2.2.1
  have hwaindex : G.nthWrite Tid.guessAY Loc.yA (G.index wa) = some wa := by
    have hidx := G.index_nthEvent hwamem
    rw [hwatid, hwaloc, hwawt] at hidx
    exact hidx
  have haeq : G.index wa = i + 1 :=
    no_skipping_guessAY_checkY_yA I G hG (G.index wa) (i + 1) hwaindex hea hwa
  rw [haeq] at hwaindex
  have hbmem : eb ∈ G.opEvents Tid.checkY Loc.yB OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨i + 1, heb⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨hebmem, _, _, hebop⟩ := G.mem_opEvents_iff.mp hbmem
  obtain ⟨wb, hwb⟩ := G.rf_total (er := eb) hebmem hebop
  have hwbval : wb.val = eb.val := G.rf_matches hwb
  rw [hvalb] at hwbval
  have hwbmem := (G.rf_subset hwb).1
  have hwbwt : wb.op = OpType.wt := (G.rf_subset hwb).2.2.1
  have hwbtid : wb.tid = Tid.guessBY :=
    G_writer_val_tid I G hG hwbmem hwbwt (t := Tid.guessBY) (by rw [hwbval]; rfl)
  have hwbloc : wb.loc = Loc.yB := by
    rw [(G.rf_subset hwb).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hbmem).2.2.1
  have hwbindex : G.nthWrite Tid.guessBY Loc.yB (G.index wb) = some wb := by
    have hidx := G.index_nthEvent hwbmem
    rw [hwbtid, hwbloc, hwbwt] at hidx
    exact hidx
  have hbeq : G.index wb = i + 1 :=
    no_skipping_guessBY_checkY_yB I G hG (G.index wb) (i + 1) hwbindex heb hwb
  rw [hbeq] at hwbindex
  exact ⟨wa, wb, hwaindex, hwbindex, hwaval, hwbval⟩

/-- Step 3, index `0`: `g_α^y`'s `0`-th `yA`-write and `0`-th `ellAyx`-write
carry the same `aux` value `some v0` (both are written in the same iteration
from the same store). -/
theorem guessAY_yA_write_ellAyx_write_val_eq0 {I : PCPInstance} (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw : G.threadWord Tid.guessAY = (guessAYBlockWord I v0 kws).map some) :
    ∃ ewy ewe, G.nthWrite Tid.guessAY Loc.yA 0 = some ewy ∧
      G.nthWrite Tid.guessAY Loc.ellAyx 0 = some ewe ∧
      ewy.val = Val.yTag (Tid.guessAY, true) (some v0) ∧ ewe.val = Val.cntAux 1 (some v0) := by
  obtain ⟨ewy, hey, hlaby⟩ :=
    ExecutionGraph.nthWrite_lab_eq_of_threadWord hw (guessAYBlockWord_yA_write_val0 I v0 kws)
  obtain ⟨ewe, hee, hlabe⟩ :=
    ExecutionGraph.nthWrite_lab_eq_of_threadWord hw (guessAYBlockWord_ellAyx_write_val0 I v0 kws)
  refine ⟨ewy, ewe, hey, hee, ?_, ?_⟩
  · rw [Event.val, hlaby]; rfl
  · rw [Event.val, hlabe]; rfl

/-- Step 3, index `i + 1`: `g_α^y`'s `(i+1)`-th `yA`-write and `(i+1)`-th
`ellAyx`-write carry the same `aux` value `kw.2` for `kws[i]? = some kw`. -/
theorem guessAY_yA_write_ellAyx_write_val_eq_succ {I : PCPInstance} (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))} (i : ℕ)
    (hw : G.threadWord Tid.guessAY = (guessAYBlockWord I v0 kws).map some)
    {kw : Fin 4 × Option (Fin I.n)} (hkw : kws[i]? = some kw) :
    ∃ ewy ewe, G.nthWrite Tid.guessAY Loc.yA (i + 1) = some ewy ∧
      G.nthWrite Tid.guessAY Loc.ellAyx (i + 1) = some ewe ∧
      ewy.val = Val.yTag (Tid.guessAY, false) kw.2 ∧ ewe.val = Val.cntAux (kw.1 + 1) kw.2 := by
  have hvaly := guessAYBlockWord_yA_write_val_succ I v0 kws i
  rw [hkw] at hvaly
  simp only [Option.map_some] at hvaly
  have hvale := guessAYBlockWord_ellAyx_write_val_succ I v0 kws i
  rw [hkw] at hvale
  simp only [Option.map_some] at hvale
  obtain ⟨ewy, hey, hlaby⟩ := ExecutionGraph.nthWrite_lab_eq_of_threadWord hw hvaly
  obtain ⟨ewe, hee, hlabe⟩ := ExecutionGraph.nthWrite_lab_eq_of_threadWord hw hvale
  refine ⟨ewy, ewe, hey, hee, ?_, ?_⟩
  · rw [Event.val, hlaby]; rfl
  · rw [Event.val, hlabe]; rfl

/-- Step 3, `β` side, index `0`: `g_β^y`'s `0`-th `yB`-write and `0`-th
`ellByx`-write carry the same `aux` value `some v0`. -/
theorem guessBY_yB_write_ellByx_write_val_eq0 {I : PCPInstance} (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))}
    (hw : G.threadWord Tid.guessBY = (guessBYBlockWord I v0 kws).map some) :
    ∃ ewy ewe, G.nthWrite Tid.guessBY Loc.yB 0 = some ewy ∧
      G.nthWrite Tid.guessBY Loc.ellByx 0 = some ewe ∧
      ewy.val = Val.yTag (Tid.guessBY, true) (some v0) ∧ ewe.val = Val.cntAux 1 (some v0) := by
  obtain ⟨ewy, hey, hlaby⟩ :=
    ExecutionGraph.nthWrite_lab_eq_of_threadWord hw (guessBYBlockWord_yB_write_val0 I v0 kws)
  obtain ⟨ewe, hee, hlabe⟩ :=
    ExecutionGraph.nthWrite_lab_eq_of_threadWord hw (guessBYBlockWord_ellByx_write_val0 I v0 kws)
  refine ⟨ewy, ewe, hey, hee, ?_, ?_⟩
  · rw [Event.val, hlaby]; rfl
  · rw [Event.val, hlabe]; rfl

/-- Step 3, `β` side, index `i + 1`: `g_β^y`'s `(i+1)`-th `yB`-write and
`(i+1)`-th `ellByx`-write carry the same `aux` value `kw.2`. -/
theorem guessBY_yB_write_ellByx_write_val_eq_succ {I : PCPInstance} (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))} (i : ℕ)
    (hw : G.threadWord Tid.guessBY = (guessBYBlockWord I v0 kws).map some)
    {kw : Fin 4 × Option (Fin I.n)} (hkw : kws[i]? = some kw) :
    ∃ ewy ewe, G.nthWrite Tid.guessBY Loc.yB (i + 1) = some ewy ∧
      G.nthWrite Tid.guessBY Loc.ellByx (i + 1) = some ewe ∧
      ewy.val = Val.yTag (Tid.guessBY, false) kw.2 ∧ ewe.val = Val.cntAux (kw.1 + 1) kw.2 := by
  have hvaly := guessBYBlockWord_yB_write_val_succ I v0 kws i
  rw [hkw] at hvaly
  simp only [Option.map_some] at hvaly
  have hvale := guessBYBlockWord_ellByx_write_val_succ I v0 kws i
  rw [hkw] at hvale
  simp only [Option.map_some] at hvale
  obtain ⟨ewy, hey, hlaby⟩ := ExecutionGraph.nthWrite_lab_eq_of_threadWord hw hvaly
  obtain ⟨ewe, hee, hlabe⟩ := ExecutionGraph.nthWrite_lab_eq_of_threadWord hw hvale
  refine ⟨ewy, ewe, hey, hee, ?_, ?_⟩
  · rw [Event.val, hlaby]; rfl
  · rw [Event.val, hlabe]; rfl

/-- `g_β^x`'s `ellByx`-read at filtered index `0`, at the `G.nthRead` level:
value `vB0.2`. -/
theorem guessBX_ellByx_read_nthRead_val0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some) :
    ∃ e, G.nthRead Tid.guessBX Loc.ellByx 0 = some e ∧ e.val = vB0.2 := by
  obtain ⟨hlen, hread⟩ := guessBX_ellByx_read_nthRead_pos0 I G hinner0len hw1
  have hlabP0 := guessBXBlockWord_ellByx_read_pos0 I v1 v2 vB0 K0 inner0Rest hinner0len outerRest
  obtain ⟨e, hlt, heq, hlab⟩ := G.threadEvents_getElem_lab_of_threadWord hw1 (3 + K0 * 3) _ hlabP0
  refine ⟨((G.threadEvents Tid.guessBX)[3 + K0 * 3]'hlen).1, hread, ?_⟩
  rw [show (G.threadEvents Tid.guessBX)[3 + K0 * 3]'hlen
      = (G.threadEvents Tid.guessBX)[3 + K0 * 3]'hlt from rfl, heq]
  rw [Event.val, hlab]
  rfl

/-- `g_β^x`'s `ellByx`-read at filtered index `m + 1` (`outerRest[m]`), at the
`G.nthRead` level: value `b.2` for `outerRest[m]? = some (b, vs)`. -/
theorem guessBX_ellByx_read_nthRead_val_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v1 v2 : Val I} {vB0 : Val I × Val I} {K0 : ℕ}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0len : inner0Rest.length = K0)
    (hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some)
    {ks : List ℕ} {N : ℕ} (hks : ks.length = N + 1) (hK0 : ks[0]? = some K0)
    (houterLen : outerRest.length = N + 1)
    (houter : ∀ j, j < N → ∃ b vs km, outerRest[j]? = some (b, vs) ∧
      ks[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLast : ∃ b vs, outerRest[N]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ N) {b : Val I × Val I} {vs : List (Val I × Val I × Val I)}
    (hmbv : outerRest[m]? = some (b, vs)) :
    ∃ e, G.nthRead Tid.guessBX Loc.ellByx (m + 1) = some e ∧ e.val = b.2 := by
  obtain ⟨hlen, hread⟩ := guessBX_ellByx_read_nthRead_pos_outer I G hinner0len hw1 hks hK0
    houterLen houter houterLast m hm hmbv
  have hlabPm := guessBXBlockWord_ellByx_read_outerPos I v1 v2 vB0 K0 inner0Rest outerRest
    hinner0len ks N hks hK0 houterLen houter houterLast m hm b vs hmbv
  obtain ⟨e, hlt, heq, hlab⟩ :=
    G.threadEvents_getElem_lab_of_threadWord hw1 (nestedOuterStart ks N (m + 2) - 1) _ hlabPm
  refine ⟨((G.threadEvents Tid.guessBX)[nestedOuterStart ks N (m + 2) - 1]'hlen).1, hread, ?_⟩
  rw [show (G.threadEvents Tid.guessBX)[nestedOuterStart ks N (m + 2) - 1]'hlen
      = (G.threadEvents Tid.guessBX)[nestedOuterStart ks N (m + 2) - 1]'hlt from rfl, heq]
  rw [Event.val, hlab]
  rfl

/-- Step 4, index `0`: `g_α^x`'s `0`-th `ellAyx`-read has the same value as
`g_α^y`'s `0`-th `ellAyx`-write. The writer of the read is on `g_α^y`
(`writerTid_confined`, `ellAyx` having the single writer `g_α^y`), at index
`0` by Eq. (15) (`no_skipping_guessAX_guessAY_ellAyx`). -/
theorem guessAX_ellAyx_read_val_eq_guessAY_ellAyx_write_val0 (I : PCPInstance)
    (G : ExecutionGraph (domainOf I)) (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {er : Event (domainOf I)} (her : G.nthRead Tid.guessAX Loc.ellAyx 0 = some er) :
    ∃ ew, G.nthWrite Tid.guessAY Loc.ellAyx 0 = some ew ∧ ew.val = er.val := by
  have hermem : er ∈ G.opEvents Tid.guessAX Loc.ellAyx OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨0, her⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨hermem', _, _, herop⟩ := G.mem_opEvents_iff.mp hermem
  obtain ⟨ew, hew⟩ := G.rf_total (er := er) hermem' herop
  have hewval : ew.val = er.val := G.rf_matches hew
  have hewmem := (G.rf_subset hew).1
  have hewwt : ew.op = OpType.wt := (G.rf_subset hew).2.2.1
  have hewtidmem : ew.tid ∈ writerTids ew.loc := writerTid_confined I G hG hewmem hewwt
  have hewloc : ew.loc = Loc.ellAyx := by
    rw [(G.rf_subset hew).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hermem).2.2.1
  rw [hewloc] at hewtidmem
  have hewtid : ew.tid = Tid.guessAY := Finset.mem_singleton.mp hewtidmem
  have hewindex : G.nthWrite Tid.guessAY Loc.ellAyx (G.index ew) = some ew := by
    have hidx := G.index_nthEvent hewmem
    rw [hewtid, hewloc, hewwt] at hidx
    exact hidx
  have heq : G.index ew = 0 := no_skipping_guessAX_guessAY_ellAyx I G hG (G.index ew) 0 hewindex her hew
  rw [heq] at hewindex
  exact ⟨ew, hewindex, hewval⟩

/-- Step 4, index `m + 1`: `g_α^x`'s `(m+1)`-th `ellAyx`-read has the same
value as `g_α^y`'s `(m+1)`-th `ellAyx`-write. -/
theorem guessAX_ellAyx_read_val_eq_guessAY_ellAyx_write_val_succ (I : PCPInstance)
    (G : ExecutionGraph (domainOf I)) (hG : G.Reaches (ConcProg I) (ConcProg I).final) (m : ℕ)
    {er : Event (domainOf I)} (her : G.nthRead Tid.guessAX Loc.ellAyx (m + 1) = some er) :
    ∃ ew, G.nthWrite Tid.guessAY Loc.ellAyx (m + 1) = some ew ∧ ew.val = er.val := by
  have hermem : er ∈ G.opEvents Tid.guessAX Loc.ellAyx OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨m + 1, her⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨hermem', _, _, herop⟩ := G.mem_opEvents_iff.mp hermem
  obtain ⟨ew, hew⟩ := G.rf_total (er := er) hermem' herop
  have hewval : ew.val = er.val := G.rf_matches hew
  have hewmem := (G.rf_subset hew).1
  have hewwt : ew.op = OpType.wt := (G.rf_subset hew).2.2.1
  have hewtidmem : ew.tid ∈ writerTids ew.loc := writerTid_confined I G hG hewmem hewwt
  have hewloc : ew.loc = Loc.ellAyx := by
    rw [(G.rf_subset hew).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hermem).2.2.1
  rw [hewloc] at hewtidmem
  have hewtid : ew.tid = Tid.guessAY := Finset.mem_singleton.mp hewtidmem
  have hewindex : G.nthWrite Tid.guessAY Loc.ellAyx (G.index ew) = some ew := by
    have hidx := G.index_nthEvent hewmem
    rw [hewtid, hewloc, hewwt] at hidx
    exact hidx
  have heq : G.index ew = m + 1 :=
    no_skipping_guessAX_guessAY_ellAyx I G hG (G.index ew) (m + 1) hewindex her hew
  rw [heq] at hewindex
  exact ⟨ew, hewindex, hewval⟩

/-- Step 4, `β` side, index `0`: `g_β^x`'s `0`-th `ellByx`-read has the same
value as `g_β^y`'s `0`-th `ellByx`-write. -/
theorem guessBX_ellByx_read_val_eq_guessBY_ellByx_write_val0 (I : PCPInstance)
    (G : ExecutionGraph (domainOf I)) (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {er : Event (domainOf I)} (her : G.nthRead Tid.guessBX Loc.ellByx 0 = some er) :
    ∃ ew, G.nthWrite Tid.guessBY Loc.ellByx 0 = some ew ∧ ew.val = er.val := by
  have hermem : er ∈ G.opEvents Tid.guessBX Loc.ellByx OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨0, her⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨hermem', _, _, herop⟩ := G.mem_opEvents_iff.mp hermem
  obtain ⟨ew, hew⟩ := G.rf_total (er := er) hermem' herop
  have hewval : ew.val = er.val := G.rf_matches hew
  have hewmem := (G.rf_subset hew).1
  have hewwt : ew.op = OpType.wt := (G.rf_subset hew).2.2.1
  have hewtidmem : ew.tid ∈ writerTids ew.loc := writerTid_confined I G hG hewmem hewwt
  have hewloc : ew.loc = Loc.ellByx := by
    rw [(G.rf_subset hew).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hermem).2.2.1
  rw [hewloc] at hewtidmem
  have hewtid : ew.tid = Tid.guessBY := Finset.mem_singleton.mp hewtidmem
  have hewindex : G.nthWrite Tid.guessBY Loc.ellByx (G.index ew) = some ew := by
    have hidx := G.index_nthEvent hewmem
    rw [hewtid, hewloc, hewwt] at hidx
    exact hidx
  have heq : G.index ew = 0 :=
    no_skipping_guessBX_guessBY_ellByx I G hG (G.index ew) 0 hewindex her hew
  rw [heq] at hewindex
  exact ⟨ew, hewindex, hewval⟩

/-- Step 4, `β` side, index `m + 1`: `g_β^x`'s `(m+1)`-th `ellByx`-read has
the same value as `g_β^y`'s `(m+1)`-th `ellByx`-write. -/
theorem guessBX_ellByx_read_val_eq_guessBY_ellByx_write_val_succ (I : PCPInstance)
    (G : ExecutionGraph (domainOf I)) (hG : G.Reaches (ConcProg I) (ConcProg I).final) (m : ℕ)
    {er : Event (domainOf I)} (her : G.nthRead Tid.guessBX Loc.ellByx (m + 1) = some er) :
    ∃ ew, G.nthWrite Tid.guessBY Loc.ellByx (m + 1) = some ew ∧ ew.val = er.val := by
  have hermem : er ∈ G.opEvents Tid.guessBX Loc.ellByx OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨m + 1, her⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨hermem', _, _, herop⟩ := G.mem_opEvents_iff.mp hermem
  obtain ⟨ew, hew⟩ := G.rf_total (er := er) hermem' herop
  have hewval : ew.val = er.val := G.rf_matches hew
  have hewmem := (G.rf_subset hew).1
  have hewwt : ew.op = OpType.wt := (G.rf_subset hew).2.2.1
  have hewtidmem : ew.tid ∈ writerTids ew.loc := writerTid_confined I G hG hewmem hewwt
  have hewloc : ew.loc = Loc.ellByx := by
    rw [(G.rf_subset hew).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hermem).2.2.1
  rw [hewloc] at hewtidmem
  have hewtid : ew.tid = Tid.guessBY := Finset.mem_singleton.mp hewtidmem
  have hewindex : G.nthWrite Tid.guessBY Loc.ellByx (G.index ew) = some ew := by
    have hidx := G.index_nthEvent hewmem
    rw [hewtid, hewloc, hewwt] at hidx
    exact hidx
  have heq : G.index ew = m + 1 :=
    no_skipping_guessBX_guessBY_ellByx I G hG (G.index ew) (m + 1) hewindex her hew
  rw [heq] at hewindex
  exact ⟨ew, hewindex, hewval⟩

/-- `g_α^x`'s `ellAyx`-read value at filtered index `m + 1`
(`outerRestAX[m].2`) and `g_α^y`'s `ellAyx`-write value at filtered index
`m + 1` (`kw.2`, for `kwsAY[m]? = some kw`) have the same `aux` component. -/
theorem guessAX_guessAY_ellAyx_val_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v1AX v2AX : Val I} {vB0AX : Val I × Val I} {K0AX : ℕ}
    {inner0RestAX : List (Val I × Val I × Val I)}
    {outerRestAX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenAX : inner0RestAX.length = K0AX)
    (hw1AX : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1AX v2AX vB0AX inner0RestAX outerRestAX).map some)
    {ksAX : List ℕ} {NAX : ℕ} (hksAX : ksAX.length = NAX + 1) (hK0AX : ksAX[0]? = some K0AX)
    (houterLenAX : outerRestAX.length = NAX + 1)
    (houterAX : ∀ j, j < NAX → ∃ b vs km, outerRestAX[j]? = some (b, vs) ∧
      ksAX[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLastAX : ∃ b vs, outerRestAX[NAX]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ NAX) {b : Val I × Val I} {vs : List (Val I × Val I × Val I)}
    (hmbv : outerRestAX[m]? = some (b, vs))
    {v0AY : Fin I.n} {kwsAY : List (Fin 4 × Option (Fin I.n))}
    (hwAY : G.threadWord Tid.guessAY = (guessAYBlockWord I v0AY kwsAY).map some)
    {kw : Fin 4 × Option (Fin I.n)} (hkw : kwsAY[m]? = some kw) :
    ∃ r, b.2 = Val.cntAux r kw.2 := by
  obtain ⟨erAX, herAX, hvalAX⟩ := guessAX_ellAyx_read_nthRead_val_succ I G hinner0lenAX hw1AX
    hksAX hK0AX houterLenAX houterAX houterLastAX m hm hmbv
  obtain ⟨ew4, hew4, hval4⟩ := guessAX_ellAyx_read_val_eq_guessAY_ellAyx_write_val_succ I G hG m herAX
  obtain ⟨ewAY, hewAY, hewAYval⟩ := guessAY_ellAyx_write_nthWrite_val_succ G m hwAY hkw
  have heq4 : ew4 = ewAY := Option.some.inj (hew4.symm.trans hewAY)
  rw [heq4, hewAYval] at hval4
  rw [hvalAX] at hval4
  exact ⟨kw.1 + 1, hval4.symm⟩

/-- `g_β^y`'s `ellByx`-write at filtered index `i + 1`, at the `G.nthWrite`
level: value `Val.cntAux (kw.1 + 1) kw.2` for `kws[i]? = some kw`. -/
theorem guessBY_ellByx_write_nthWrite_val_succ {I : PCPInstance} (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {kws : List (Fin 4 × Option (Fin I.n))} (i : ℕ)
    (hw : G.threadWord Tid.guessBY = (guessBYBlockWord I v0 kws).map some)
    {kw : Fin 4 × Option (Fin I.n)} (hkw : kws[i]? = some kw) :
    ∃ e, G.nthWrite Tid.guessBY Loc.ellByx (i + 1) = some e ∧
      e.val = Val.cntAux (kw.1 + 1) kw.2 := by
  have hval := guessBYBlockWord_ellByx_write_val_succ I v0 kws i
  rw [hkw] at hval
  simp only [Option.map_some] at hval
  obtain ⟨e, he, hlab⟩ := ExecutionGraph.nthWrite_lab_eq_of_threadWord hw hval
  refine ⟨e, he, ?_⟩
  rw [Event.val, hlab]
  rfl

/-- `g_β^x`'s `ellByx`-read value at filtered index `m + 1` and `g_β^y`'s
`ellByx`-write value at filtered index `m + 1` have the same `aux`
component. -/
theorem guessBX_guessBY_ellByx_val_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v1BX v2BX : Val I} {vB0BX : Val I × Val I} {K0BX : ℕ}
    {inner0RestBX : List (Val I × Val I × Val I)}
    {outerRestBX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenBX : inner0RestBX.length = K0BX)
    (hw1BX : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1BX v2BX vB0BX inner0RestBX outerRestBX).map some)
    {ksBX : List ℕ} {NBX : ℕ} (hksBX : ksBX.length = NBX + 1) (hK0BX : ksBX[0]? = some K0BX)
    (houterLenBX : outerRestBX.length = NBX + 1)
    (houterBX : ∀ j, j < NBX → ∃ b vs km, outerRestBX[j]? = some (b, vs) ∧
      ksBX[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLastBX : ∃ b vs, outerRestBX[NBX]? = some (b, vs) ∧ vs.length = 1)
    (m : ℕ) (hm : m ≤ NBX) {b : Val I × Val I} {vs : List (Val I × Val I × Val I)}
    (hmbv : outerRestBX[m]? = some (b, vs))
    {v0BY : Fin I.n} {kwsBY : List (Fin 4 × Option (Fin I.n))}
    (hwBY : G.threadWord Tid.guessBY = (guessBYBlockWord I v0BY kwsBY).map some)
    {kw : Fin 4 × Option (Fin I.n)} (hkw : kwsBY[m]? = some kw) :
    ∃ r, b.2 = Val.cntAux r kw.2 := by
  obtain ⟨erBX, herBX, hvalBX⟩ := guessBX_ellByx_read_nthRead_val_succ I G hinner0lenBX hw1BX
    hksBX hK0BX houterLenBX houterBX houterLastBX m hm hmbv
  obtain ⟨ew4, hew4, hval4⟩ := guessBX_ellByx_read_val_eq_guessBY_ellByx_write_val_succ I G hG m herBX
  obtain ⟨ewBY, hewBY, hewBYval⟩ := guessBY_ellByx_write_nthWrite_val_succ G m hwBY hkw
  have heq4 : ew4 = ewBY := Option.some.inj (hew4.symm.trans hewBY)
  rw [heq4, hewBYval] at hval4
  rw [hvalBX] at hval4
  exact ⟨kw.1 + 1, hval4.symm⟩

/-- Steps 1-5 at index `0`: `g_α^x`'s first `aux` draw `v0AX` equals `g_β^x`'s
first `aux` draw `v0BX` (both equal `c^y`'s first `aux` draw `v0`). -/
theorem guessAX_guessBX_v0_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v0 : Fin I.n} {kwsVY : List (Fin 4 × Option (Fin I.n))}
    (hwVY : G.threadWord Tid.checkY = (checkYBlockWord I v0 kwsVY).map some)
    {v0AY : Fin I.n} {kwsAY : List (Fin 4 × Option (Fin I.n))}
    (hwAY : G.threadWord Tid.guessAY = (guessAYBlockWord I v0AY kwsAY).map some)
    {v0BY : Fin I.n} {kwsBY : List (Fin 4 × Option (Fin I.n))}
    (hwBY : G.threadWord Tid.guessBY = (guessBYBlockWord I v0BY kwsBY).map some)
    {v1AX v2AX : Val I} {vB0AX : Val I × Val I} {K0AX : ℕ}
    {inner0RestAX : List (Val I × Val I × Val I)}
    {outerRestAX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenAX : inner0RestAX.length = K0AX)
    (hw1AX : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1AX v2AX vB0AX inner0RestAX outerRestAX).map some)
    {v0AX : Fin I.n} (hvB0AX : vB0AX.2 = Val.cntAux 1 (some v0AX))
    {v1BX v2BX : Val I} {vB0BX : Val I × Val I} {K0BX : ℕ}
    {inner0RestBX : List (Val I × Val I × Val I)}
    {outerRestBX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenBX : inner0RestBX.length = K0BX)
    (hw1BX : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1BX v2BX vB0BX inner0RestBX outerRestBX).map some)
    {v0BX : Fin I.n} (hvB0BX : vB0BX.2 = Val.cntAux 1 (some v0BX)) :
    v0AX = v0BX := by
  -- Step 1: CheckY's reads share `v0`.
  obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkY_yA_read_yB_read_val_eq0 I G hwVY
  -- Step 2: GuessAY's/GuessBY's writes carry `v0` (via the read's writer).
  obtain ⟨ewa, ewb, hewa, hewb, hwaval, hwbval⟩ :=
    guessAY_guessBY_yA_yB_write_val_eq0 I G hG hea heb hvala hvalb
  -- Step 3: GuessAY's/GuessBY's closed forms give the `yA`/`yB`-write
  -- value AND the `ellAyx`/`ellByx`-write value together, both in terms of that
  -- thread's `v0AY`/`v0BY`.
  obtain ⟨ewy, ewe, hewy, hewe, hewyval, heweval⟩ := guessAY_yA_write_ellAyx_write_val_eq0 G hwAY
  obtain ⟨ewy', ewe', hewy', hewe', hewy'val, hewe'val⟩ :=
    guessBY_yB_write_ellByx_write_val_eq0 G hwBY
  -- Identify the step-2 writer with the step-3 closed-form writer (same
  -- `G.nthWrite` position), then read off `v0AY = v0`/`v0BY = v0` by
  -- injectivity of `Val.yTag`.
  have heqa : ewa = ewy := Option.some.inj (hewa.symm.trans hewy)
  rw [heqa, hewyval] at hwaval
  have hv0AY : v0AY = v0 := by injection hwaval with _ h; exact Option.some.inj h
  have heqb : ewb = ewy' := Option.some.inj (hewb.symm.trans hewy')
  rw [heqb, hewy'val] at hwbval
  have hv0BY : v0BY = v0 := by injection hwbval with _ h; exact Option.some.inj h
  rw [hv0AY] at heweval
  rw [hv0BY] at hewe'val
  -- Step 4: GuessAX's/GuessBX's `ellAyx`/`ellByx`-read equals GuessAY's/
  -- GuessBY's `ellAyx`/`ellByx`-write value.
  obtain ⟨erAX, herAX, hvalAX⟩ := guessAX_ellAyx_read_nthRead_val0 I G hinner0lenAX hw1AX
  obtain ⟨ew4, hew4, hval4⟩ := guessAX_ellAyx_read_val_eq_guessAY_ellAyx_write_val0 I G hG herAX
  have heq4 : ew4 = ewe := Option.some.inj (hew4.symm.trans hewe)
  rw [heq4, heweval] at hval4
  obtain ⟨erBX, herBX, hvalBX⟩ := guessBX_ellByx_read_nthRead_val0 I G hinner0lenBX hw1BX
  obtain ⟨ew4', hew4', hval4'⟩ := guessBX_ellByx_read_val_eq_guessBY_ellByx_write_val0 I G hG herBX
  have heq4' : ew4' = ewe' := Option.some.inj (hew4'.symm.trans hewe')
  rw [heq4', hewe'val] at hval4'
  -- Step 5: GuessAX's/GuessBX's read ALSO equals its own closed-form
  -- value directly. Combining with step 4 pins `v0AX = v0` and `v0BX = v0`.
  rw [hvalAX, hvB0AX] at hval4
  rw [hvalBX, hvB0BX] at hval4'
  have hv0AXeq : v0AX = v0 := by injection hval4 with _ h; exact (Option.some.inj h).symm
  have hv0BXeq : v0BX = v0 := by injection hval4' with _ h; exact (Option.some.inj h).symm
  rw [hv0AXeq, hv0BXeq]

/-- Steps 1-5 at index `i + 1`: given `c^y`'s `kws[i]? = some kw`, the
`(i+1)`-th outer iterations of `g_α^x` and `g_β^x` both read a bridge value
with `aux` component `kw.2`. Only the `aux` components agree: the counters
of the two threads need not. -/
theorem guessAX_guessBX_kw_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ)
    {kwVY : Fin 4 × Option (Fin I.n)} {v0VY : Fin I.n} {kwsVY : List (Fin 4 × Option (Fin I.n))}
    (hwVY : G.threadWord Tid.checkY = (checkYBlockWord I v0VY kwsVY).map some)
    (hkwVY : kwsVY[i]? = some kwVY)
    {kwAY : Fin 4 × Option (Fin I.n)} {v0AY : Fin I.n} {kwsAY : List (Fin 4 × Option (Fin I.n))}
    (hwAY : G.threadWord Tid.guessAY = (guessAYBlockWord I v0AY kwsAY).map some)
    (hkwAY : kwsAY[i]? = some kwAY)
    {kwBY : Fin 4 × Option (Fin I.n)} {v0BY : Fin I.n} {kwsBY : List (Fin 4 × Option (Fin I.n))}
    (hwBY : G.threadWord Tid.guessBY = (guessBYBlockWord I v0BY kwsBY).map some)
    (hkwBY : kwsBY[i]? = some kwBY)
    {v1AX v2AX : Val I} {vB0AX : Val I × Val I} {K0AX : ℕ}
    {inner0RestAX : List (Val I × Val I × Val I)}
    {outerRestAX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenAX : inner0RestAX.length = K0AX)
    (hw1AX : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1AX v2AX vB0AX inner0RestAX outerRestAX).map some)
    {ksAX : List ℕ} {NAX : ℕ} (hksAX : ksAX.length = NAX + 1) (hK0AX : ksAX[0]? = some K0AX)
    (houterLenAX : outerRestAX.length = NAX + 1)
    (houterAX : ∀ j, j < NAX → ∃ b vs km, outerRestAX[j]? = some (b, vs) ∧
      ksAX[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLastAX : ∃ b vs, outerRestAX[NAX]? = some (b, vs) ∧ vs.length = 1)
    (hiAX : i ≤ NAX) {bAX : Val I × Val I} {vsAX : List (Val I × Val I × Val I)}
    (hmbvAX : outerRestAX[i]? = some (bAX, vsAX))
    {v1BX v2BX : Val I} {vB0BX : Val I × Val I} {K0BX : ℕ}
    {inner0RestBX : List (Val I × Val I × Val I)}
    {outerRestBX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenBX : inner0RestBX.length = K0BX)
    (hw1BX : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1BX v2BX vB0BX inner0RestBX outerRestBX).map some)
    {ksBX : List ℕ} {NBX : ℕ} (hksBX : ksBX.length = NBX + 1) (hK0BX : ksBX[0]? = some K0BX)
    (houterLenBX : outerRestBX.length = NBX + 1)
    (houterBX : ∀ j, j < NBX → ∃ b vs km, outerRestBX[j]? = some (b, vs) ∧
      ksBX[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLastBX : ∃ b vs, outerRestBX[NBX]? = some (b, vs) ∧ vs.length = 1)
    (hiBX : i ≤ NBX) {bBX : Val I × Val I} {vsBX : List (Val I × Val I × Val I)}
    (hmbvBX : outerRestBX[i]? = some (bBX, vsBX)) :
    ∃ rAX rBX, bAX.2 = Val.cntAux rAX kwVY.2 ∧ bBX.2 = Val.cntAux rBX kwVY.2 := by
  -- Step 1.
  obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkY_yA_read_yB_read_val_eq_succ I G i hwVY hkwVY
  -- Step 2.
  obtain ⟨ewa, ewb, hewa, hewb, hwaval, hwbval⟩ :=
    guessAY_guessBY_yA_yB_write_val_eq_succ I G hG i hea heb hvala hvalb
  -- Step 3.
  obtain ⟨ewy, ewe, hewy, hewe, hewyval, heweval⟩ :=
    guessAY_yA_write_ellAyx_write_val_eq_succ G i hwAY hkwAY
  obtain ⟨ewy', ewe', hewy', hewe', hewy'val, hewe'val⟩ :=
    guessBY_yB_write_ellByx_write_val_eq_succ G i hwBY hkwBY
  have heqa : ewa = ewy := Option.some.inj (hewa.symm.trans hewy)
  rw [heqa, hewyval] at hwaval
  have hkw2AY : kwAY.2 = kwVY.2 := by injection hwaval
  have heqb : ewb = ewy' := Option.some.inj (hewb.symm.trans hewy')
  rw [heqb, hewy'val] at hwbval
  have hkw2BY : kwBY.2 = kwVY.2 := by injection hwbval
  rw [hkw2AY] at heweval
  rw [hkw2BY] at hewe'val
  -- Step 4.
  obtain ⟨erAX, herAX, hvalAX⟩ := guessAX_ellAyx_read_nthRead_val_succ I G hinner0lenAX hw1AX
    hksAX hK0AX houterLenAX houterAX houterLastAX i hiAX hmbvAX
  obtain ⟨ew4, hew4, hval4⟩ :=
    guessAX_ellAyx_read_val_eq_guessAY_ellAyx_write_val_succ I G hG i herAX
  have heq4 : ew4 = ewe := Option.some.inj (hew4.symm.trans hewe)
  rw [heq4, heweval] at hval4
  obtain ⟨erBX, herBX, hvalBX⟩ := guessBX_ellByx_read_nthRead_val_succ I G hinner0lenBX hw1BX
    hksBX hK0BX houterLenBX houterBX houterLastBX i hiBX hmbvBX
  obtain ⟨ew4', hew4', hval4'⟩ :=
    guessBX_ellByx_read_val_eq_guessBY_ellByx_write_val_succ I G hG i herBX
  have heq4' : ew4' = ewe' := Option.some.inj (hew4'.symm.trans hewe')
  rw [heq4', hewe'val] at hval4'
  -- Step 5, and assembly.
  rw [hvalAX] at hval4
  rw [hvalBX] at hval4'
  exact ⟨_, _, hval4.symm, hval4'.symm⟩

/-- `g_α^y`'s `aux` value at index `i + 1` (`kwAY.2`) agrees with `c^y`'s
(`kwVY.2`). -/
theorem guessAY_kwVY_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ)
    {v0VY : Fin I.n} {kwsVY : List (Fin 4 × Option (Fin I.n))}
    (hwVY : G.threadWord Tid.checkY = (checkYBlockWord I v0VY kwsVY).map some)
    {kwVY : Fin 4 × Option (Fin I.n)} (hkwVY : kwsVY[i]? = some kwVY)
    {v0AY : Fin I.n} {kwsAY : List (Fin 4 × Option (Fin I.n))}
    (hwAY : G.threadWord Tid.guessAY = (guessAYBlockWord I v0AY kwsAY).map some)
    {kwAY : Fin 4 × Option (Fin I.n)} (hkwAY : kwsAY[i]? = some kwAY) :
    kwAY.2 = kwVY.2 := by
  obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkY_yA_read_yB_read_val_eq_succ I G i hwVY hkwVY
  obtain ⟨ewa, _, hewa, _, hwaval, _⟩ :=
    guessAY_guessBY_yA_yB_write_val_eq_succ I G hG i hea heb hvala hvalb
  have hvaly := guessAYBlockWord_yA_write_val_succ I v0AY kwsAY i
  rw [hkwAY] at hvaly
  simp only [Option.map_some] at hvaly
  obtain ⟨ewa', hewa', hlaby⟩ := ExecutionGraph.nthWrite_lab_eq_of_threadWord hwAY hvaly
  have heq : ewa = ewa' := Option.some.inj (hewa.symm.trans hewa')
  have hewa'val : ewa'.val = Val.yTag (Tid.guessAY, false) kwAY.2 := by
    rw [Event.val, hlaby]; rfl
  rw [heq, hewa'val] at hwaval
  injection hwaval with _ h2

/-- `g_β^y`'s `aux` value at index `i + 1` (`kwBY.2`) agrees with `c^y`'s
(`kwVY.2`). -/
theorem guessBY_kwVY_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ)
    {v0VY : Fin I.n} {kwsVY : List (Fin 4 × Option (Fin I.n))}
    (hwVY : G.threadWord Tid.checkY = (checkYBlockWord I v0VY kwsVY).map some)
    {kwVY : Fin 4 × Option (Fin I.n)} (hkwVY : kwsVY[i]? = some kwVY)
    {v0BY : Fin I.n} {kwsBY : List (Fin 4 × Option (Fin I.n))}
    (hwBY : G.threadWord Tid.guessBY = (guessBYBlockWord I v0BY kwsBY).map some)
    {kwBY : Fin 4 × Option (Fin I.n)} (hkwBY : kwsBY[i]? = some kwBY) :
    kwBY.2 = kwVY.2 := by
  obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkY_yA_read_yB_read_val_eq_succ I G i hwVY hkwVY
  obtain ⟨_, ewb, _, hewb, _, hwbval⟩ :=
    guessAY_guessBY_yA_yB_write_val_eq_succ I G hG i hea heb hvala hvalb
  have hvaly := guessBYBlockWord_yB_write_val_succ I v0BY kwsBY i
  rw [hkwBY] at hvaly
  simp only [Option.map_some] at hvaly
  obtain ⟨ewb', hewb', hlaby⟩ := ExecutionGraph.nthWrite_lab_eq_of_threadWord hwBY hvaly
  have heq : ewb = ewb' := Option.some.inj (hewb.symm.trans hewb')
  have hewb'val : ewb'.val = Val.yTag (Tid.guessBY, false) kwBY.2 := by
    rw [Event.val, hlaby]; rfl
  rw [heq, hewb'val] at hwbval
  injection hwbval with _ h2

/-- `g_α^y`'s `kws` has the same length as `c^y`'s. If one were shorter, its
terminating entry (tagged `none`) would force the other's entry at that index
to be `none` too (`guessAY_kwVY_eq_succ`), but that entry is tagged
`some _`. -/
theorem guessAY_checkY_kws_length_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v0VY : Fin I.n} {jsVY : List (Fin I.n)} {kwsVY : List (Fin 4 × Option (Fin I.n))}
    (hwVY : G.threadWord Tid.checkY = (checkYBlockWord I v0VY kwsVY).map some)
    (hkwsVYlen : kwsVY.length = jsVY.length + 1)
    (hkwsVYval : ∀ i, i < kwsVY.length → kwsVY[i]?.map Prod.snd = some (jsVY[i]?))
    {v0AY : Fin I.n} {jsAY : List (Fin I.n)} {kwsAY : List (Fin 4 × Option (Fin I.n))}
    (hwAY : G.threadWord Tid.guessAY = (guessAYBlockWord I v0AY kwsAY).map some)
    (hkwsAYlen : kwsAY.length = jsAY.length + 1)
    (hkwsAYval : ∀ i, i < kwsAY.length → kwsAY[i]?.map Prod.snd = some (jsAY[i]?)) :
    kwsAY.length = kwsVY.length := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- `kwsAY.length < kwsVY.length`: `AY`'s terminator lands strictly
    -- inside `VY`'s real range.
    set i := jsAY.length with hidef
    have hiAY : i < kwsAY.length := by omega
    have hiVY : i < kwsVY.length := by omega
    have hjsAYnone : jsAY[i]? = none := List.getElem?_eq_none (by omega)
    have hval1 := hkwsAYval i hiAY
    rw [hjsAYnone] at hval1
    obtain ⟨kwAY, hkwAY⟩ : ∃ kwAY, kwsAY[i]? = some kwAY :=
      ⟨kwsAY[i]'hiAY, List.getElem?_eq_getElem hiAY⟩
    rw [hkwAY] at hval1
    have hkwAY2 : kwAY.2 = none := by injection hval1
    obtain ⟨kwVY, hkwVY⟩ : ∃ kwVY, kwsVY[i]? = some kwVY :=
      ⟨kwsVY[i]'hiVY, List.getElem?_eq_getElem hiVY⟩
    have hival : i < jsVY.length := by omega
    have hjsVYsome : jsVY[i]? = some (jsVY[i]'hival) := List.getElem?_eq_getElem hival
    have hval2 := hkwsVYval i hiVY
    rw [hkwVY, hjsVYsome] at hval2
    have hkwVY2 : kwVY.2 = some (jsVY[i]'hival) := by injection hval2
    have hcontra := guessAY_kwVY_eq_succ I G hG i hwVY hkwVY hwAY hkwAY
    rw [hkwAY2, hkwVY2] at hcontra
    simp at hcontra
  · -- `kwsAY.length > kwsVY.length`: symmetric, `VY`'s terminator lands
    -- strictly inside `AY`'s real range.
    set i := jsVY.length with hidef
    have hiVY : i < kwsVY.length := by omega
    have hiAY : i < kwsAY.length := by omega
    have hjsVYnone : jsVY[i]? = none := List.getElem?_eq_none (by omega)
    have hval1 := hkwsVYval i hiVY
    rw [hjsVYnone] at hval1
    obtain ⟨kwVY, hkwVY⟩ : ∃ kwVY, kwsVY[i]? = some kwVY :=
      ⟨kwsVY[i]'hiVY, List.getElem?_eq_getElem hiVY⟩
    rw [hkwVY] at hval1
    have hkwVY2 : kwVY.2 = none := by injection hval1
    obtain ⟨kwAY, hkwAY⟩ : ∃ kwAY, kwsAY[i]? = some kwAY :=
      ⟨kwsAY[i]'hiAY, List.getElem?_eq_getElem hiAY⟩
    have hival : i < jsAY.length := by omega
    have hjsAYsome : jsAY[i]? = some (jsAY[i]'hival) := List.getElem?_eq_getElem hival
    have hval2 := hkwsAYval i hiAY
    rw [hkwAY, hjsAYsome] at hval2
    have hkwAY2 : kwAY.2 = some (jsAY[i]'hival) := by injection hval2
    have hcontra := guessAY_kwVY_eq_succ I G hG i hwVY hkwVY hwAY hkwAY
    rw [hkwAY2, hkwVY2] at hcontra
    simp at hcontra

/-- `g_β^y`'s `kws` has the same length as `c^y`'s (as
`guessAY_checkY_kws_length_eq`). -/
theorem guessBY_checkY_kws_length_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v0VY : Fin I.n} {jsVY : List (Fin I.n)} {kwsVY : List (Fin 4 × Option (Fin I.n))}
    (hwVY : G.threadWord Tid.checkY = (checkYBlockWord I v0VY kwsVY).map some)
    (hkwsVYlen : kwsVY.length = jsVY.length + 1)
    (hkwsVYval : ∀ i, i < kwsVY.length → kwsVY[i]?.map Prod.snd = some (jsVY[i]?))
    {v0BY : Fin I.n} {jsBY : List (Fin I.n)} {kwsBY : List (Fin 4 × Option (Fin I.n))}
    (hwBY : G.threadWord Tid.guessBY = (guessBYBlockWord I v0BY kwsBY).map some)
    (hkwsBYlen : kwsBY.length = jsBY.length + 1)
    (hkwsBYval : ∀ i, i < kwsBY.length → kwsBY[i]?.map Prod.snd = some (jsBY[i]?)) :
    kwsBY.length = kwsVY.length := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · set i := jsBY.length with hidef
    have hiBY : i < kwsBY.length := by omega
    have hiVY : i < kwsVY.length := by omega
    have hjsBYnone : jsBY[i]? = none := List.getElem?_eq_none (by omega)
    have hval1 := hkwsBYval i hiBY
    rw [hjsBYnone] at hval1
    obtain ⟨kwBY, hkwBY⟩ : ∃ kwBY, kwsBY[i]? = some kwBY :=
      ⟨kwsBY[i]'hiBY, List.getElem?_eq_getElem hiBY⟩
    rw [hkwBY] at hval1
    have hkwBY2 : kwBY.2 = none := by injection hval1
    obtain ⟨kwVY, hkwVY⟩ : ∃ kwVY, kwsVY[i]? = some kwVY :=
      ⟨kwsVY[i]'hiVY, List.getElem?_eq_getElem hiVY⟩
    have hival : i < jsVY.length := by omega
    have hjsVYsome : jsVY[i]? = some (jsVY[i]'hival) := List.getElem?_eq_getElem hival
    have hval2 := hkwsVYval i hiVY
    rw [hkwVY, hjsVYsome] at hval2
    have hkwVY2 : kwVY.2 = some (jsVY[i]'hival) := by injection hval2
    have hcontra := guessBY_kwVY_eq_succ I G hG i hwVY hkwVY hwBY hkwBY
    rw [hkwBY2, hkwVY2] at hcontra
    simp at hcontra
  · set i := jsVY.length with hidef
    have hiVY : i < kwsVY.length := by omega
    have hiBY : i < kwsBY.length := by omega
    have hjsVYnone : jsVY[i]? = none := List.getElem?_eq_none (by omega)
    have hval1 := hkwsVYval i hiVY
    rw [hjsVYnone] at hval1
    obtain ⟨kwVY, hkwVY⟩ : ∃ kwVY, kwsVY[i]? = some kwVY :=
      ⟨kwsVY[i]'hiVY, List.getElem?_eq_getElem hiVY⟩
    rw [hkwVY] at hval1
    have hkwVY2 : kwVY.2 = none := by injection hval1
    obtain ⟨kwBY, hkwBY⟩ : ∃ kwBY, kwsBY[i]? = some kwBY :=
      ⟨kwsBY[i]'hiBY, List.getElem?_eq_getElem hiBY⟩
    have hival : i < jsBY.length := by omega
    have hjsBYsome : jsBY[i]? = some (jsBY[i]'hival) := List.getElem?_eq_getElem hival
    have hval2 := hkwsBYval i hiBY
    rw [hkwBY, hjsBYsome] at hval2
    have hkwBY2 : kwBY.2 = some (jsBY[i]'hival) := by injection hval2
    have hcontra := guessBY_kwVY_eq_succ I G hG i hwVY hkwVY hwBY hkwBY
    rw [hkwBY2, hkwVY2] at hcontra
    simp at hcontra

/-- `g_α^x`'s number of outer iterations (`NAX`, with
`outerRestAX.length = NAX + 1`) equals `g_α^y`'s `jsAY.length`. As in
`guessAY_checkY_kws_length_eq`: if `NAX < jsAY.length`, `g_α^x`'s terminating
read (tagged `none`) meets a non-terminating write of `g_α^y`; if
`NAX > jsAY.length`, a non-terminating read of `g_α^x` meets `g_α^y`'s
terminating write. -/
theorem guessAX_guessAY_length_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v1AX v2AX : Val I} {vB0AX : Val I × Val I} {K0AX : ℕ}
    {inner0RestAX : List (Val I × Val I × Val I)}
    {outerRestAX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenAX : inner0RestAX.length = K0AX)
    (hw1AX : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1AX v2AX vB0AX inner0RestAX outerRestAX).map some)
    {ksAX : List ℕ} {NAX : ℕ} (hksAX : ksAX.length = NAX + 1) (hK0AX : ksAX[0]? = some K0AX)
    (houterLenAX : outerRestAX.length = NAX + 1)
    (houterAX : ∀ j, j < NAX → ∃ b vs km, outerRestAX[j]? = some (b, vs) ∧
      ksAX[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLastAX : ∃ b vs, outerRestAX[NAX]? = some (b, vs) ∧ vs.length = 1)
    (houterValSomeAX : ∀ m, m < NAX → ∃ b vs, outerRestAX[m]? = some (b, vs) ∧
      ∃ r w, b.2 = Val.cntAux r (some w))
    (houterValNoneAX : ∃ b vs, outerRestAX[NAX]? = some (b, vs) ∧ ∃ r, b.2 = Val.cntAux r none)
    {v0AY : Fin I.n} {jsAY : List (Fin I.n)} {kwsAY : List (Fin 4 × Option (Fin I.n))}
    (hwAY : G.threadWord Tid.guessAY = (guessAYBlockWord I v0AY kwsAY).map some)
    (hkwsAYlen : kwsAY.length = jsAY.length + 1)
    (hkwsAYval : ∀ i, i < kwsAY.length → kwsAY[i]?.map Prod.snd = some (jsAY[i]?)) :
    NAX = jsAY.length := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨b, vs, hbv, r, hbnone⟩ := houterValNoneAX
    have hiAY : NAX < kwsAY.length := by omega
    obtain ⟨kw, hkw⟩ : ∃ kw, kwsAY[NAX]? = some kw :=
      ⟨kwsAY[NAX]'hiAY, List.getElem?_eq_getElem hiAY⟩
    obtain ⟨r', hval⟩ := guessAX_guessAY_ellAyx_val_eq_succ I G hG hinner0lenAX hw1AX
      hksAX hK0AX houterLenAX houterAX houterLastAX NAX (le_refl NAX) hbv hwAY hkw
    rw [hbnone] at hval
    have hkwnone : kw.2 = none := by injection hval with _ h; exact h.symm
    have hival : NAX < jsAY.length := by omega
    have hjsAYsome : jsAY[NAX]? = some (jsAY[NAX]'hival) := List.getElem?_eq_getElem hival
    have hvalAY := hkwsAYval NAX hiAY
    rw [hkw, hjsAYsome] at hvalAY
    have hkwsome : kw.2 = some (jsAY[NAX]'hival) := by injection hvalAY
    rw [hkwnone] at hkwsome
    simp at hkwsome
  · obtain ⟨b, vs, hbv, r, w, hbsome⟩ := houterValSomeAX jsAY.length (by omega)
    have hiAY : jsAY.length < kwsAY.length := by omega
    obtain ⟨kw, hkw⟩ : ∃ kw, kwsAY[jsAY.length]? = some kw :=
      ⟨kwsAY[jsAY.length]'hiAY, List.getElem?_eq_getElem hiAY⟩
    obtain ⟨r', hval⟩ := guessAX_guessAY_ellAyx_val_eq_succ I G hG hinner0lenAX hw1AX
      hksAX hK0AX houterLenAX houterAX houterLastAX jsAY.length (by omega) hbv hwAY hkw
    rw [hbsome] at hval
    have hkwsome : kw.2 = some w := by injection hval with _ h; exact h.symm
    have hjsAYnone : jsAY[jsAY.length]? = none := List.getElem?_eq_none (le_refl _)
    have hvalAY := hkwsAYval jsAY.length hiAY
    rw [hkw, hjsAYnone] at hvalAY
    have hkwnone : kw.2 = none := by injection hvalAY
    rw [hkwsome] at hkwnone
    simp at hkwnone

/-- `g_β^x`'s number of outer iterations equals `g_β^y`'s `jsBY.length` (as
`guessAX_guessAY_length_eq`). -/
theorem guessBX_guessBY_length_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v1BX v2BX : Val I} {vB0BX : Val I × Val I} {K0BX : ℕ}
    {inner0RestBX : List (Val I × Val I × Val I)}
    {outerRestBX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenBX : inner0RestBX.length = K0BX)
    (hw1BX : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1BX v2BX vB0BX inner0RestBX outerRestBX).map some)
    {ksBX : List ℕ} {NBX : ℕ} (hksBX : ksBX.length = NBX + 1) (hK0BX : ksBX[0]? = some K0BX)
    (houterLenBX : outerRestBX.length = NBX + 1)
    (houterBX : ∀ j, j < NBX → ∃ b vs km, outerRestBX[j]? = some (b, vs) ∧
      ksBX[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLastBX : ∃ b vs, outerRestBX[NBX]? = some (b, vs) ∧ vs.length = 1)
    (houterValSomeBX : ∀ m, m < NBX → ∃ b vs, outerRestBX[m]? = some (b, vs) ∧
      ∃ r w, b.2 = Val.cntAux r (some w))
    (houterValNoneBX : ∃ b vs, outerRestBX[NBX]? = some (b, vs) ∧ ∃ r, b.2 = Val.cntAux r none)
    {v0BY : Fin I.n} {jsBY : List (Fin I.n)} {kwsBY : List (Fin 4 × Option (Fin I.n))}
    (hwBY : G.threadWord Tid.guessBY = (guessBYBlockWord I v0BY kwsBY).map some)
    (hkwsBYlen : kwsBY.length = jsBY.length + 1)
    (hkwsBYval : ∀ i, i < kwsBY.length → kwsBY[i]?.map Prod.snd = some (jsBY[i]?)) :
    NBX = jsBY.length := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨b, vs, hbv, r, hbnone⟩ := houterValNoneBX
    have hiBY : NBX < kwsBY.length := by omega
    obtain ⟨kw, hkw⟩ : ∃ kw, kwsBY[NBX]? = some kw :=
      ⟨kwsBY[NBX]'hiBY, List.getElem?_eq_getElem hiBY⟩
    obtain ⟨r', hval⟩ := guessBX_guessBY_ellByx_val_eq_succ I G hG hinner0lenBX hw1BX
      hksBX hK0BX houterLenBX houterBX houterLastBX NBX (le_refl NBX) hbv hwBY hkw
    rw [hbnone] at hval
    have hkwnone : kw.2 = none := by injection hval with _ h; exact h.symm
    have hival : NBX < jsBY.length := by omega
    have hjsBYsome : jsBY[NBX]? = some (jsBY[NBX]'hival) := List.getElem?_eq_getElem hival
    have hvalBY := hkwsBYval NBX hiBY
    rw [hkw, hjsBYsome] at hvalBY
    have hkwsome : kw.2 = some (jsBY[NBX]'hival) := by injection hvalBY
    rw [hkwnone] at hkwsome
    simp at hkwsome
  · obtain ⟨b, vs, hbv, r, w, hbsome⟩ := houterValSomeBX jsBY.length (by omega)
    have hiBY : jsBY.length < kwsBY.length := by omega
    obtain ⟨kw, hkw⟩ : ∃ kw, kwsBY[jsBY.length]? = some kw :=
      ⟨kwsBY[jsBY.length]'hiBY, List.getElem?_eq_getElem hiBY⟩
    obtain ⟨r', hval⟩ := guessBX_guessBY_ellByx_val_eq_succ I G hG hinner0lenBX hw1BX
      hksBX hK0BX houterLenBX houterBX houterLastBX jsBY.length (by omega) hbv hwBY hkw
    rw [hbsome] at hval
    have hkwsome : kw.2 = some w := by injection hval with _ h; exact h.symm
    have hjsBYnone : jsBY[jsBY.length]? = none := List.getElem?_eq_none (le_refl _)
    have hvalBY := hkwsBYval jsBY.length hiBY
    rw [hkw, hjsBYnone] at hvalBY
    have hkwnone : kw.2 = none := by injection hvalBY
    rw [hkwsome] at hkwnone
    simp at hkwnone

/-- The guesser pair agrees: `g_α^x`'s guessed sequence (`v0AX`, `jsAX`)
equals `g_β^x`'s (`v0BX`, `jsBX`), from the pointwise agreement
(`guessAX_guessBX_v0_eq`, `guessAX_guessBX_kw_eq_succ`) and the length
equalities (`guessAX_guessAY_length_eq`, `guessBX_guessBY_length_eq`,
`guessAY_checkY_kws_length_eq`, `guessBY_checkY_kws_length_eq`). -/
theorem guessAX_guessBX_js_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v0 : Fin I.n} {jsVY : List (Fin I.n)} {kwsVY : List (Fin 4 × Option (Fin I.n))}
    (hwVY : G.threadWord Tid.checkY = (checkYBlockWord I v0 kwsVY).map some)
    (hkwsVYlen : kwsVY.length = jsVY.length + 1)
    (hkwsVYval : ∀ i, i < kwsVY.length → kwsVY[i]?.map Prod.snd = some (jsVY[i]?))
    {v0AY : Fin I.n} {jsAY : List (Fin I.n)} {kwsAY : List (Fin 4 × Option (Fin I.n))}
    (hwAY : G.threadWord Tid.guessAY = (guessAYBlockWord I v0AY kwsAY).map some)
    (hkwsAYlen : kwsAY.length = jsAY.length + 1)
    (hkwsAYval : ∀ i, i < kwsAY.length → kwsAY[i]?.map Prod.snd = some (jsAY[i]?))
    {v0BY : Fin I.n} {jsBY : List (Fin I.n)} {kwsBY : List (Fin 4 × Option (Fin I.n))}
    (hwBY : G.threadWord Tid.guessBY = (guessBYBlockWord I v0BY kwsBY).map some)
    (hkwsBYlen : kwsBY.length = jsBY.length + 1)
    (hkwsBYval : ∀ i, i < kwsBY.length → kwsBY[i]?.map Prod.snd = some (jsBY[i]?))
    {v1AX v2AX : Val I} {vB0AX : Val I × Val I} {K0AX : ℕ}
    {inner0RestAX : List (Val I × Val I × Val I)}
    {outerRestAX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenAX : inner0RestAX.length = K0AX)
    (hw1AX : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1AX v2AX vB0AX inner0RestAX outerRestAX).map some)
    {v0AX : Fin I.n} (hvB0AX : vB0AX.2 = Val.cntAux 1 (some v0AX))
    {ksAX : List ℕ} {NAX : ℕ} (hksAX : ksAX.length = NAX + 1) (hK0AX : ksAX[0]? = some K0AX)
    (houterLenAX : outerRestAX.length = NAX + 1)
    (houterAX : ∀ j, j < NAX → ∃ b vs km, outerRestAX[j]? = some (b, vs) ∧
      ksAX[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLastAX : ∃ b vs, outerRestAX[NAX]? = some (b, vs) ∧ vs.length = 1)
    {jsAX : List (Fin I.n)} (hlenAX : jsAX.length = NAX)
    (hjsAX : ∀ m, m ≤ NAX → ∃ b vs, outerRestAX[m]? = some (b, vs) ∧
      ∃ r, b.2 = Val.cntAux r (jsAX[m]?))
    (houterValSomeAX : ∀ m, m < NAX → ∃ b vs, outerRestAX[m]? = some (b, vs) ∧
      ∃ r w, b.2 = Val.cntAux r (some w))
    (houterValNoneAX : ∃ b vs, outerRestAX[NAX]? = some (b, vs) ∧ ∃ r, b.2 = Val.cntAux r none)
    {v1BX v2BX : Val I} {vB0BX : Val I × Val I} {K0BX : ℕ}
    {inner0RestBX : List (Val I × Val I × Val I)}
    {outerRestBX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hinner0lenBX : inner0RestBX.length = K0BX)
    (hw1BX : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1BX v2BX vB0BX inner0RestBX outerRestBX).map some)
    {v0BX : Fin I.n} (hvB0BX : vB0BX.2 = Val.cntAux 1 (some v0BX))
    {ksBX : List ℕ} {NBX : ℕ} (hksBX : ksBX.length = NBX + 1) (hK0BX : ksBX[0]? = some K0BX)
    (houterLenBX : outerRestBX.length = NBX + 1)
    (houterBX : ∀ j, j < NBX → ∃ b vs km, outerRestBX[j]? = some (b, vs) ∧
      ksBX[j + 1]? = some km ∧ vs.length = km + 1)
    (houterLastBX : ∃ b vs, outerRestBX[NBX]? = some (b, vs) ∧ vs.length = 1)
    {jsBX : List (Fin I.n)} (hlenBX : jsBX.length = NBX)
    (hjsBX : ∀ m, m ≤ NBX → ∃ b vs, outerRestBX[m]? = some (b, vs) ∧
      ∃ r, b.2 = Val.cntAux r (jsBX[m]?))
    (houterValSomeBX : ∀ m, m < NBX → ∃ b vs, outerRestBX[m]? = some (b, vs) ∧
      ∃ r w, b.2 = Val.cntAux r (some w))
    (houterValNoneBX : ∃ b vs, outerRestBX[NBX]? = some (b, vs) ∧ ∃ r, b.2 = Val.cntAux r none) :
    v0AX = v0BX ∧ jsAX = jsBX := by
  refine ⟨guessAX_guessBX_v0_eq I G hG hwVY hwAY hwBY hinner0lenAX hw1AX hvB0AX
    hinner0lenBX hw1BX hvB0BX, ?_⟩
  have hNAXeq : NAX = jsAY.length := guessAX_guessAY_length_eq I G hG hinner0lenAX hw1AX
    hksAX hK0AX houterLenAX houterAX houterLastAX houterValSomeAX houterValNoneAX hwAY
    hkwsAYlen hkwsAYval
  have hNBXeq : NBX = jsBY.length := guessBX_guessBY_length_eq I G hG hinner0lenBX hw1BX
    hksBX hK0BX houterLenBX houterBX houterLastBX houterValSomeBX houterValNoneBX hwBY
    hkwsBYlen hkwsBYval
  have hAYVYeq : kwsAY.length = kwsVY.length := guessAY_checkY_kws_length_eq I G hG hwVY
    hkwsVYlen hkwsVYval hwAY hkwsAYlen hkwsAYval
  have hBYVYeq : kwsBY.length = kwsVY.length := guessBY_checkY_kws_length_eq I G hG hwVY
    hkwsVYlen hkwsVYval hwBY hkwsBYlen hkwsBYval
  have hNeq : NAX = NBX := by omega
  apply List.ext_getElem?
  intro i
  by_cases hi : i ≤ NAX
  · have hiBX : i ≤ NBX := by omega
    have hiVY : i < kwsVY.length := by omega
    have hiAY : i < kwsAY.length := by omega
    have hiBY : i < kwsBY.length := by omega
    obtain ⟨kwVY, hkwVY⟩ : ∃ kwVY, kwsVY[i]? = some kwVY :=
      ⟨kwsVY[i]'hiVY, List.getElem?_eq_getElem hiVY⟩
    obtain ⟨kwAY, hkwAY⟩ : ∃ kwAY, kwsAY[i]? = some kwAY :=
      ⟨kwsAY[i]'hiAY, List.getElem?_eq_getElem hiAY⟩
    obtain ⟨kwBY, hkwBY⟩ : ∃ kwBY, kwsBY[i]? = some kwBY :=
      ⟨kwsBY[i]'hiBY, List.getElem?_eq_getElem hiBY⟩
    obtain ⟨bAX, vsAX, hmbvAX, rAX0, hAXval⟩ := hjsAX i hi
    obtain ⟨bBX, vsBX, hmbvBX, rBX0, hBXval⟩ := hjsBX i hiBX
    obtain ⟨rAX, rBX, hchainAX, hchainBX⟩ := guessAX_guessBX_kw_eq_succ I G hG i
      hwVY hkwVY hwAY hkwAY hwBY hkwBY hinner0lenAX hw1AX hksAX hK0AX houterLenAX houterAX
      houterLastAX hi hmbvAX hinner0lenBX hw1BX hksBX hK0BX houterLenBX houterBX houterLastBX
      hiBX hmbvBX
    rw [hAXval] at hchainAX
    rw [hBXval] at hchainBX
    have hjsAXi : jsAX[i]? = kwVY.2 := by
      have := hchainAX
      simp only [Val.cntAux.injEq] at this
      exact this.2
    have hjsBXi : jsBX[i]? = kwVY.2 := by
      have := hchainBX
      simp only [Val.cntAux.injEq] at this
      exact this.2
    rw [hjsAXi, hjsBXi]
  · simp only [not_le] at hi
    have hiAXnone : jsAX[i]? = none := List.getElem?_eq_none (by omega)
    have hiBXnone : jsBX[i]? = none := List.getElem?_eq_none (by omega)
    rw [hiAXnone, hiBXnone]

/-! ## The words agree (the proof's last paragraph)

Step 1: `c^x`'s `i`-th reads of `xA` and `xB` carry the same letter. -/

/-- `CheckX`'s `xA`-read value at filtered index `0` (block 0,
`First()` branch): `Val.xTag (Tid.guessAX, true) (some v0)`. -/
theorem checkXBlockWord_xA_read_val0 (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) :
    ((checkXBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd))[0]? =
      some (⟨EventLabel.rd Tid.checkX Loc.xA (Val.xTag (Tid.guessAX, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkX Loc.xA (Val.xTag (Tid.guessAX, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `CheckX`'s `xA`-read value at filtered index `i + 1` (`blockRest`'s
`i`-th entry): `Val.xTag (Tid.guessAX, false) kw.2` for `kws[i]? = some kw`. -/
theorem checkXBlockWord_xA_read_val_succ (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) (i : ℕ) :
    ((checkXBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.rd Tid.checkX Loc.xA
        (Val.xTag (Tid.guessAX, false) kw.2), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkX Loc.xA (Val.xTag (Tid.guessAX, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkXBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.checkX Loc.xA
        (Val.xTag (Tid.guessAX, false) kw.2), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.xA ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkX Loc.xA (Val.xTag (Tid.guessAX, false) kw.2), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkX)] := by
      intro kw
      unfold checkXBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr]
  simp

/-- `CheckX`'s `xB`-read value at filtered index `0`:
`Val.xTag (Tid.guessBX, true) (some v0)`. -/
theorem checkXBlockWord_xB_read_val0 (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) :
    ((checkXBlockWord I v0 kws).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd))[0]? =
      some (⟨EventLabel.rd Tid.checkX Loc.xB (Val.xTag (Tid.guessBX, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkX Loc.xB (Val.xTag (Tid.guessBX, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  rw [hb0, List.getElem?_append_left (by simp)]
  rfl

/-- `CheckX`'s `xB`-read value at filtered index `i + 1`:
`Val.xTag (Tid.guessBX, false) kw.2` for `kws[i]? = some kw`. -/
theorem checkXBlockWord_xB_read_val_succ (I : PCPInstance) (v0 : I.Γ)
    (kws : List (Fin 4 × Option I.Γ)) (i : ℕ) :
    ((checkXBlockWord I v0 kws).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd))[i + 1]? =
      (kws[i]?).map (fun kw => (⟨EventLabel.rd Tid.checkX Loc.xB
        (Val.xTag (Tid.guessBX, false) kw.2), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
  unfold checkXBlockWord
  rw [List.filter_append]
  have hb0 : (checkXBlock0Elems I v0).filter (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) =
      [(⟨EventLabel.rd Tid.checkX Loc.xB (Val.xTag (Tid.guessBX, true) (some v0)), rfl⟩ :
        ThreadLabel (domainOf I) Tid.checkX)] := by
    unfold checkXBlock0Elems
    rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
      List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
  have hbr : (kws.flatMap (checkXBlockRestElems I)).filter
      (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) =
      kws.map (fun kw => (⟨EventLabel.rd Tid.checkX Loc.xB
        (Val.xTag (Tid.guessBX, false) kw.2), rfl⟩ : ThreadLabel (domainOf I) Tid.checkX)) := by
    rw [list_filter_flatMap_distrib]
    have hone : ∀ kw : Fin 4 × Option I.Γ, (checkXBlockRestElems I kw).filter
        (fun l => l.1.loc = Loc.xB ∧ l.1.op = OpType.rd) =
        [(⟨EventLabel.rd Tid.checkX Loc.xB (Val.xTag (Tid.guessBX, false) kw.2), rfl⟩ :
          ThreadLabel (domainOf I) Tid.checkX)] := by
      intro kw
      unfold checkXBlockRestElems
      rw [List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_pos (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp),
        List.filter_cons_of_neg (by unfold EventLabel.loc EventLabel.op; simp), List.filter_nil]
    simp only [hone]
    exact list_flatMap_singleton_eq_map _ kws
  rw [hb0, hbr]
  simp

/-- Step 1, index `0`: `c^x`'s `0`-th reads of `xA` and `xB` (the `First()`
branch) carry the same letter `some v0`. -/
theorem checkX_xA_read_xB_read_val_eq0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : I.Γ} {kws : List (Fin 4 × Option I.Γ)}
    (hw : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some) :
    ∃ ea eb, G.nthRead Tid.checkX Loc.xA 0 = some ea ∧ G.nthRead Tid.checkX Loc.xB 0 = some eb ∧
      ea.val = Val.xTag (Tid.guessAX, true) (some v0) ∧
      eb.val = Val.xTag (Tid.guessBX, true) (some v0) := by
  obtain ⟨ea, hea, hlaba⟩ :=
    ExecutionGraph.nthRead_lab_eq_of_threadWord hw (checkXBlockWord_xA_read_val0 I v0 kws)
  obtain ⟨eb, heb, hlabb⟩ :=
    ExecutionGraph.nthRead_lab_eq_of_threadWord hw (checkXBlockWord_xB_read_val0 I v0 kws)
  refine ⟨ea, eb, hea, heb, ?_, ?_⟩
  · rw [Event.val, hlaba]; rfl
  · rw [Event.val, hlabb]; rfl

/-- Step 1, index `i + 1`: `c^x`'s `(i + 1)`-th reads of `xA` and `xB` carry
the same letter `kw.2` for `kws[i]? = some kw`. -/
theorem checkX_xA_read_xB_read_val_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : I.Γ} {kws : List (Fin 4 × Option I.Γ)} (i : ℕ)
    (hw : G.threadWord Tid.checkX = (checkXBlockWord I v0 kws).map some)
    {kw : Fin 4 × Option I.Γ} (hkw : kws[i]? = some kw) :
    ∃ ea eb, G.nthRead Tid.checkX Loc.xA (i + 1) = some ea ∧
      G.nthRead Tid.checkX Loc.xB (i + 1) = some eb ∧
      ea.val = Val.xTag (Tid.guessAX, false) kw.2 ∧ eb.val = Val.xTag (Tid.guessBX, false) kw.2 := by
  have hvala := checkXBlockWord_xA_read_val_succ I v0 kws i
  rw [hkw] at hvala
  simp only [Option.map_some] at hvala
  have hvalb := checkXBlockWord_xB_read_val_succ I v0 kws i
  rw [hkw] at hvalb
  simp only [Option.map_some] at hvalb
  obtain ⟨ea, hea, hlaba⟩ := ExecutionGraph.nthRead_lab_eq_of_threadWord hw hvala
  obtain ⟨eb, heb, hlabb⟩ := ExecutionGraph.nthRead_lab_eq_of_threadWord hw hvalb
  refine ⟨ea, eb, hea, heb, ?_, ?_⟩
  · rw [Event.val, hlaba]; rfl
  · rw [Event.val, hlabb]; rfl

/-- Step 2, index `0`: `g_α^x`'s `0`-th `xA`-write and `g_β^x`'s `0`-th
`xB`-write both carry `some v0`. The writer of `c^x`'s read is identified by
its `Val.xTag` value (`G_writer_val_tid`), and its index by Eq. (17)
(`no_skipping_guessAX_checkX_xA`/`no_skipping_guessBX_checkX_xB`). -/
theorem guessAX_guessBX_xA_xB_write_val_eq0 (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) {v0 : I.Γ}
    {ea eb : Event (domainOf I)} (hea : G.nthRead Tid.checkX Loc.xA 0 = some ea)
    (heb : G.nthRead Tid.checkX Loc.xB 0 = some eb)
    (hvala : ea.val = Val.xTag (Tid.guessAX, true) (some v0))
    (hvalb : eb.val = Val.xTag (Tid.guessBX, true) (some v0)) :
    ∃ ewa ewb, G.nthWrite Tid.guessAX Loc.xA 0 = some ewa ∧
      G.nthWrite Tid.guessBX Loc.xB 0 = some ewb ∧
      ewa.val = Val.xTag (Tid.guessAX, true) (some v0) ∧
      ewb.val = Val.xTag (Tid.guessBX, true) (some v0) := by
  have hamem : ea ∈ G.opEvents Tid.checkX Loc.xA OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨0, hea⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨heamem, _, _, heaop⟩ := G.mem_opEvents_iff.mp hamem
  obtain ⟨wa, hwa⟩ := G.rf_total (er := ea) heamem heaop
  have hwaval : wa.val = ea.val := G.rf_matches hwa
  rw [hvala] at hwaval
  have hwamem := (G.rf_subset hwa).1
  have hwawt : wa.op = OpType.wt := (G.rf_subset hwa).2.2.1
  have hwatid : wa.tid = Tid.guessAX :=
    G_writer_val_tid I G hG hwamem hwawt (t := Tid.guessAX) (by rw [hwaval]; rfl)
  have hwaloc : wa.loc = Loc.xA := by
    rw [(G.rf_subset hwa).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hamem).2.2.1
  have hwaindex : G.nthWrite Tid.guessAX Loc.xA (G.index wa) = some wa := by
    have hidx := G.index_nthEvent hwamem
    rw [hwatid, hwaloc, hwawt] at hidx
    exact hidx
  have haeq : G.index wa = 0 := no_skipping_guessAX_checkX_xA I G hG (G.index wa) 0 hwaindex hea hwa
  rw [haeq] at hwaindex
  have hbmem : eb ∈ G.opEvents Tid.checkX Loc.xB OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨0, heb⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨hebmem, _, _, hebop⟩ := G.mem_opEvents_iff.mp hbmem
  obtain ⟨wb, hwb⟩ := G.rf_total (er := eb) hebmem hebop
  have hwbval : wb.val = eb.val := G.rf_matches hwb
  rw [hvalb] at hwbval
  have hwbmem := (G.rf_subset hwb).1
  have hwbwt : wb.op = OpType.wt := (G.rf_subset hwb).2.2.1
  have hwbtid : wb.tid = Tid.guessBX :=
    G_writer_val_tid I G hG hwbmem hwbwt (t := Tid.guessBX) (by rw [hwbval]; rfl)
  have hwbloc : wb.loc = Loc.xB := by
    rw [(G.rf_subset hwb).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hbmem).2.2.1
  have hwbindex : G.nthWrite Tid.guessBX Loc.xB (G.index wb) = some wb := by
    have hidx := G.index_nthEvent hwbmem
    rw [hwbtid, hwbloc, hwbwt] at hidx
    exact hidx
  have hbeq : G.index wb = 0 := no_skipping_guessBX_checkX_xB I G hG (G.index wb) 0 hwbindex heb hwb
  rw [hbeq] at hwbindex
  exact ⟨wa, wb, hwaindex, hwbindex, hwaval, hwbval⟩

/-- Step 2, index `i + 1`: `g_α^x`'s `(i+1)`-th `xA`-write and `g_β^x`'s
`(i+1)`-th `xB`-write both carry `kw.2`. -/
theorem guessAX_guessBX_xA_xB_write_val_eq_succ (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) (i : ℕ) {kw : Fin 4 × Option I.Γ}
    {ea eb : Event (domainOf I)} (hea : G.nthRead Tid.checkX Loc.xA (i + 1) = some ea)
    (heb : G.nthRead Tid.checkX Loc.xB (i + 1) = some eb)
    (hvala : ea.val = Val.xTag (Tid.guessAX, false) kw.2)
    (hvalb : eb.val = Val.xTag (Tid.guessBX, false) kw.2) :
    ∃ ewa ewb, G.nthWrite Tid.guessAX Loc.xA (i + 1) = some ewa ∧
      G.nthWrite Tid.guessBX Loc.xB (i + 1) = some ewb ∧
      ewa.val = Val.xTag (Tid.guessAX, false) kw.2 ∧
      ewb.val = Val.xTag (Tid.guessBX, false) kw.2 := by
  have hamem : ea ∈ G.opEvents Tid.checkX Loc.xA OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨i + 1, hea⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨heamem, _, _, heaop⟩ := G.mem_opEvents_iff.mp hamem
  obtain ⟨wa, hwa⟩ := G.rf_total (er := ea) heamem heaop
  have hwaval : wa.val = ea.val := G.rf_matches hwa
  rw [hvala] at hwaval
  have hwamem := (G.rf_subset hwa).1
  have hwawt : wa.op = OpType.wt := (G.rf_subset hwa).2.2.1
  have hwatid : wa.tid = Tid.guessAX :=
    G_writer_val_tid I G hG hwamem hwawt (t := Tid.guessAX) (by rw [hwaval]; rfl)
  have hwaloc : wa.loc = Loc.xA := by
    rw [(G.rf_subset hwa).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hamem).2.2.1
  have hwaindex : G.nthWrite Tid.guessAX Loc.xA (G.index wa) = some wa := by
    have hidx := G.index_nthEvent hwamem
    rw [hwatid, hwaloc, hwawt] at hidx
    exact hidx
  have haeq : G.index wa = i + 1 :=
    no_skipping_guessAX_checkX_xA I G hG (G.index wa) (i + 1) hwaindex hea hwa
  rw [haeq] at hwaindex
  have hbmem : eb ∈ G.opEvents Tid.checkX Loc.xB OpType.rd := by
    have := List.mem_iff_getElem?.mpr ⟨i + 1, heb⟩
    simpa [ExecutionGraph.nthEvent, ExecutionGraph.nthRead] using this
  obtain ⟨hebmem, _, _, hebop⟩ := G.mem_opEvents_iff.mp hbmem
  obtain ⟨wb, hwb⟩ := G.rf_total (er := eb) hebmem hebop
  have hwbval : wb.val = eb.val := G.rf_matches hwb
  rw [hvalb] at hwbval
  have hwbmem := (G.rf_subset hwb).1
  have hwbwt : wb.op = OpType.wt := (G.rf_subset hwb).2.2.1
  have hwbtid : wb.tid = Tid.guessBX :=
    G_writer_val_tid I G hG hwbmem hwbwt (t := Tid.guessBX) (by rw [hwbval]; rfl)
  have hwbloc : wb.loc = Loc.xB := by
    rw [(G.rf_subset hwb).2.2.2.2]
    exact (G.mem_opEvents_iff.mp hbmem).2.2.1
  have hwbindex : G.nthWrite Tid.guessBX Loc.xB (G.index wb) = some wb := by
    have hidx := G.index_nthEvent hwbmem
    rw [hwbtid, hwbloc, hwbwt] at hidx
    exact hidx
  have hbeq : G.index wb = i + 1 :=
    no_skipping_guessBX_checkX_xB I G hG (G.index wb) (i + 1) hwbindex heb hwb
  rw [hbeq] at hwbindex
  exact ⟨wa, wb, hwaindex, hwbindex, hwaval, hwbval⟩

/-! ## Step 3: letters written by the guessers

`g_α^x`'s `xA`-write at filtered index `idx` carries the letter
`((v0::js).map I.α).flatten[idx]?` (resp. `g_β^x` and `I.β`). The relation
between indices and tile letters is `guessAX_checkX_rf_matches`/
`guessBX_checkX_rf_matches` (`Completeness/Construction.lean`); what is added
here is locating `idx` in the head triple, `inner0Rest` or `outerRest`. -/

/-- `g_α^x`'s `xA`-write at filtered index `idx` carries the letter
`((v0::js).map I.α).flatten[idx]?`, for a decomposition of `g_α^x`'s word
given explicitly (so that several indices can be treated with one and the same
decomposition). -/
theorem guessAX_xA_write_letter_eq_of_shape (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {K0 : ℕ} {js : List (Fin I.n)} {v1 v2 : Val I} {vB0 : Val I × Val I}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hα : (I.α v0).length = K0 + 1)
    (hinner0len : inner0Rest.length = K0)
    (houterlen : outerRest.length = js.length + 1)
    (hpreOuter : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (hv1xA : ∃ j : Fin (GuessAX.maxLen I + 2), j.val = 1 ∧
      v1 = Val.xTag (Tid.guessAX, true) (GuessAX.jthLetter I (some v0) j))
    (hinner0valxA : ∀ n, n < inner0Rest.length → ∃ e j, inner0Rest[n]? = some e ∧ j.val = n + 2 ∧
      e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some v0) j))
    (houtervalxA : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      (m < js.length → ∃ w, js[m]? = some w ∧
        ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some w) j)) ∧
      (m = js.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I none j)))
    (hσ1 : G.threadLabels Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (idx : ℕ) {ew : Event (domainOf I)} (hew : G.nthWrite Tid.guessAX Loc.xA idx = some ew) :
    ∃ tag : Bool, ew.val = Val.xTag (Tid.guessAX, tag) (((v0 :: js).map I.α).flatten[idx]?) := by
  have hne : I.α v0 ≠ [] := I.hα v0
  have hlen0 : 0 < (I.α v0).length := List.length_pos_of_ne_nil hne
  have hflatne : ((v0 :: js).map I.α).flatten ≠ [] := by
    have hlensum : ((v0 :: js).map I.α).flatten.length
        = (I.α v0).length + (js.map I.α).flatten.length := by simp [List.flatten_cons]
    exact List.ne_nil_of_length_pos (by omega)
  obtain ⟨c0, cs, hflat⟩ := List.exists_cons_of_ne_nil hflatne
  obtain ⟨-, hv1eq, hinnereq, houtereq, -⟩ := guessAX_checkX_rf_matches I v0 js c0 cs hflat
    K0 hα v1 inner0Rest outerRest hinner0len hpreOuter hv1xA hinner0valxA houtervalxA c0 rfl
    [] (fun i hi => by simp at hi)
  have hw1 : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAX, hσ1]
  have hew_eq := G.nthEvent_lab_of_threadWord hw1 Loc.xA OpType.wt idx
  rw [show G.nthEvent Tid.guessAX Loc.xA OpType.wt idx = G.nthWrite Tid.guessAX Loc.xA idx
    from rfl, hew] at hew_eq
  have hfilteq := guessAX_xA_write_filter_eq
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
  have hew_eq := hfilteq ▸ hew_eq
  have hew_eq := (guessAXBlockWord_xA_filter_eq I v1 v2 vB0 inner0Rest outerRest) ▸ hew_eq
  rw [List.append_assoc] at hew_eq
  set ev : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX :=
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)) with hevdef
  rcases idx with _ | j
  · -- idx = 0: the head triple's first entry `v1`.
    simp only [List.getElem?_append_left
      (by simp : (0 : ℕ) < ([(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessAX)]).length),
      List.getElem?_cons_zero, Option.map_some] at hew_eq
    have hewval : ew.val = v1 := by
      have hewlab : ew.lab = EventLabel.wt Tid.guessAX Loc.xA v1 := Option.some.inj hew_eq
      rw [Event.val, hewlab]; rfl
    exact ⟨true, by rw [hewval, hv1eq, hflat, List.getElem?_cons_zero]⟩
  · -- idx = j + 1.
    rw [List.getElem?_append_right (by simp : ([(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)]).length ≤ j + 1)] at hew_eq
    simp only [List.length_singleton] at hew_eq
    rw [show j + 1 - 1 = j from by omega] at hew_eq
    rcases Nat.lt_or_ge j inner0Rest.length with hjlt | hjge
    · -- inside `inner0Rest`.
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_map] at hew_eq
      obtain ⟨e, he, c, hcs, heval⟩ := hinnereq j hjlt
      rw [he] at hew_eq
      simp only [Option.map_some, Option.some.injEq] at hew_eq
      have hewval : ew.val = e.1 := by rw [Event.val, hew_eq]; rfl
      exact ⟨false, by rw [hewval, heval, hflat, List.getElem?_cons_succ, hcs]⟩
    · -- inside `outerRest`, via `ksPrefix`.
      rw [List.getElem?_append_right (by simpa using hjge)] at hew_eq
      simp only [List.length_map, hinner0len] at hew_eq
      rw [hinner0len] at hjge
      have hks_len : (guessAXJsToKs I js).length = js.length := by simp [guessAXJsToKs]
      have houterLen' : outerRest.length = (guessAXJsToKs I js).length + 1 := by
        rw [hks_len]; exact houterlen
      have houter' : ∀ m, m < (guessAXJsToKs I js).length → ∃ a vs km,
          outerRest[m]? = some (a, vs) ∧ (guessAXJsToKs I js)[m]? = some km ∧
          vs.length = km + 1 := by rw [hks_len]; exact hpreOuter
      have houterLast' : ∃ a vs, outerRest[(guessAXJsToKs I js).length]? = some (a, vs) ∧
          vs.length = 1 := by rw [hks_len]; exact hlastOuter
      have hsum : (outerRest.map (fun p => p.2.length)).sum
          = ((guessAXJsToKs I js).map (· + 1)).sum + 1 :=
        sum_snd_length_of_forall_getElem outerRest (guessAXJsToKs I js) houterLen'
          houter' houterLast'
      have hlen_outer_flat : (outerRest.flatMap (fun p => p.2.map ev)).length
          = ksPrefix (guessAXJsToKs I js) js.length + 1 := by
        have hlenflat : (outerRest.flatMap (fun p => p.2.map ev)).length
            = (outerRest.map (fun p => p.2.length)).sum := by
          rw [List.length_flatMap]
          congr 1
          apply List.map_congr_left
          intro p _
          exact List.length_map ..
        rw [hlenflat, hsum, guessAXJsToKs_succ_sum_eq_flatten_length,
          ksPrefix_guessAXJsToKs_eq_flatten_length I js js.length (le_refl _), List.take_length]
      set j' := j - K0 with hj'def
      have hj'lt0 : j' < ksPrefix (guessAXJsToKs I js) js.length + 1 := by
        by_contra hcon
        push Not at hcon
        have hnone : (outerRest.flatMap (fun p => p.2.map ev))[j']? = none :=
          List.getElem?_eq_none (by omega)
        rw [hnone] at hew_eq
        simp at hew_eq
      have hj'lt : j' < ksPrefix (guessAXJsToKs I js) (guessAXJsToKs I js).length + 1 := by
        rw [hks_len]; exact hj'lt0
      obtain ⟨m, hmlt, a, vs, n, e, hbvs, hnlt, hvsn, hjeq, hgetflat⟩ :=
        ksPrefix_flatMap_map_getElem outerRest (guessAXJsToKs I js) ev
          houterLen' houter' houterLast' j' hj'lt
      rw [hgetflat] at hew_eq
      simp only [Option.map_some, Option.some.injEq] at hew_eq
      have hewval : ew.val = e.1 := by rw [Event.val, hew_eq]; rfl
      have hmlt' : m < js.length + 1 := by rw [hks_len] at hmlt; omega
      have heval := houtereq m hmlt' a vs hbvs n e hnlt hvsn
      refine ⟨false, ?_⟩
      rw [hewval, heval, hflat]
      have hidxeq : (c0 :: cs)[j + 1]? = cs[K0 + ksPrefix (guessAXJsToKs I js) m + n]? := by
        have hK0 : (I.α v0).length = K0 + 1 := hα
        have hidx' : j + 1 = (K0 + ksPrefix (guessAXJsToKs I js) m + n) + 1 := by omega
        rw [hidx', List.getElem?_cons_succ]
      rw [hidxeq]

/-- `g_β^x`'s `xB`-write at filtered index `idx` carries the letter
`((v0::js).map I.β).flatten[idx]?` (as
`guessAX_xA_write_letter_eq_of_shape`). -/
theorem guessBX_xB_write_letter_eq_of_shape (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    {v0 : Fin I.n} {K0 : ℕ} {js : List (Fin I.n)} {v1 v2 : Val I} {vB0 : Val I × Val I}
    {inner0Rest : List (Val I × Val I × Val I)}
    {outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hβ : (I.β v0).length = K0 + 1)
    (hinner0len : inner0Rest.length = K0)
    (houterlen : outerRest.length = js.length + 1)
    (hpreOuter : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (hv1xB : ∃ j : Fin (GuessBX.maxLen I + 2), j.val = 1 ∧
      v1 = Val.xTag (Tid.guessBX, true) (GuessBX.jthLetter I (some v0) j))
    (hinner0valxB : ∀ n, n < inner0Rest.length → ∃ e j, inner0Rest[n]? = some e ∧ j.val = n + 2 ∧
      e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some v0) j))
    (houtervalxB : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      (m < js.length → ∃ w, js[m]? = some w ∧
        ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some w) j)) ∧
      (m = js.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I none j)))
    (hσ1 : G.threadLabels Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (idx : ℕ) {ew : Event (domainOf I)} (hew : G.nthWrite Tid.guessBX Loc.xB idx = some ew) :
    ∃ tag : Bool, ew.val = Val.xTag (Tid.guessBX, tag) (((v0 :: js).map I.β).flatten[idx]?) := by
  have hne : I.β v0 ≠ [] := I.hβ v0
  have hlen0 : 0 < (I.β v0).length := List.length_pos_of_ne_nil hne
  have hflatne : ((v0 :: js).map I.β).flatten ≠ [] := by
    have hlensum : ((v0 :: js).map I.β).flatten.length
        = (I.β v0).length + (js.map I.β).flatten.length := by simp [List.flatten_cons]
    exact List.ne_nil_of_length_pos (by omega)
  obtain ⟨c0, cs, hflat⟩ := List.exists_cons_of_ne_nil hflatne
  obtain ⟨-, hv1eq, hinnereq, houtereq, -⟩ := guessBX_checkX_rf_matches I v0 js c0 cs hflat
    K0 hβ v1 inner0Rest outerRest hinner0len hpreOuter hv1xB hinner0valxB houtervalxB c0 rfl
    [] (fun i hi => by simp at hi)
  have hw1 : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBX, hσ1]
  have hew_eq := G.nthEvent_lab_of_threadWord hw1 Loc.xB OpType.wt idx
  rw [show G.nthEvent Tid.guessBX Loc.xB OpType.wt idx = G.nthWrite Tid.guessBX Loc.xB idx
    from rfl, hew] at hew_eq
  have hfilteq := guessBX_xB_write_filter_eq
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
  have hew_eq := hfilteq ▸ hew_eq
  have hew_eq := (guessBXBlockWord_xB_filter_eq I v1 v2 vB0 inner0Rest outerRest) ▸ hew_eq
  rw [List.append_assoc] at hew_eq
  set ev : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX :=
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)) with hevdef
  rcases idx with _ | j
  · -- idx = 0: the head triple's first entry `v1`.
    simp only [List.getElem?_append_left
      (by simp : (0 : ℕ) < ([(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ :
        ThreadLabel (domainOf I) Tid.guessBX)]).length),
      List.getElem?_cons_zero, Option.map_some] at hew_eq
    have hewval : ew.val = v1 := by
      have hewlab : ew.lab = EventLabel.wt Tid.guessBX Loc.xB v1 := Option.some.inj hew_eq
      rw [Event.val, hewlab]; rfl
    exact ⟨true, by rw [hewval, hv1eq, hflat, List.getElem?_cons_zero]⟩
  · -- idx = j + 1.
    rw [List.getElem?_append_right (by simp : ([(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)]).length ≤ j + 1)] at hew_eq
    simp only [List.length_singleton] at hew_eq
    rw [show j + 1 - 1 = j from by omega] at hew_eq
    rcases Nat.lt_or_ge j inner0Rest.length with hjlt | hjge
    · -- inside `inner0Rest`.
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_map] at hew_eq
      obtain ⟨e, he, c, hcs, heval⟩ := hinnereq j hjlt
      rw [he] at hew_eq
      simp only [Option.map_some, Option.some.injEq] at hew_eq
      have hewval : ew.val = e.1 := by rw [Event.val, hew_eq]; rfl
      exact ⟨false, by rw [hewval, heval, hflat, List.getElem?_cons_succ, hcs]⟩
    · -- inside `outerRest`, via `ksPrefix`.
      rw [List.getElem?_append_right (by simpa using hjge)] at hew_eq
      simp only [List.length_map, hinner0len] at hew_eq
      rw [hinner0len] at hjge
      have hks_len : (guessBXJsToKs I js).length = js.length := by simp [guessBXJsToKs]
      have houterLen' : outerRest.length = (guessBXJsToKs I js).length + 1 := by
        rw [hks_len]; exact houterlen
      have houter' : ∀ m, m < (guessBXJsToKs I js).length → ∃ a vs km,
          outerRest[m]? = some (a, vs) ∧ (guessBXJsToKs I js)[m]? = some km ∧
          vs.length = km + 1 := by rw [hks_len]; exact hpreOuter
      have houterLast' : ∃ a vs, outerRest[(guessBXJsToKs I js).length]? = some (a, vs) ∧
          vs.length = 1 := by rw [hks_len]; exact hlastOuter
      have hsum : (outerRest.map (fun p => p.2.length)).sum
          = ((guessBXJsToKs I js).map (· + 1)).sum + 1 :=
        sum_snd_length_of_forall_getElem outerRest (guessBXJsToKs I js) houterLen'
          houter' houterLast'
      have hlen_outer_flat : (outerRest.flatMap (fun p => p.2.map ev)).length
          = ksPrefix (guessBXJsToKs I js) js.length + 1 := by
        have hlenflat : (outerRest.flatMap (fun p => p.2.map ev)).length
            = (outerRest.map (fun p => p.2.length)).sum := by
          rw [List.length_flatMap]
          congr 1
          apply List.map_congr_left
          intro p _
          exact List.length_map ..
        rw [hlenflat, hsum, guessBXJsToKs_succ_sum_eq_flatten_length,
          ksPrefix_guessBXJsToKs_eq_flatten_length I js js.length (le_refl _), List.take_length]
      set j' := j - K0 with hj'def
      have hj'lt0 : j' < ksPrefix (guessBXJsToKs I js) js.length + 1 := by
        by_contra hcon
        push Not at hcon
        have hnone : (outerRest.flatMap (fun p => p.2.map ev))[j']? = none :=
          List.getElem?_eq_none (by omega)
        rw [hnone] at hew_eq
        simp at hew_eq
      have hj'lt : j' < ksPrefix (guessBXJsToKs I js) (guessBXJsToKs I js).length + 1 := by
        rw [hks_len]; exact hj'lt0
      obtain ⟨m, hmlt, a, vs, n, e, hbvs, hnlt, hvsn, hjeq, hgetflat⟩ :=
        ksPrefix_flatMap_map_getElem outerRest (guessBXJsToKs I js) ev
          houterLen' houter' houterLast' j' hj'lt
      rw [hgetflat] at hew_eq
      simp only [Option.map_some, Option.some.injEq] at hew_eq
      have hewval : ew.val = e.1 := by rw [Event.val, hew_eq]; rfl
      have hmlt' : m < js.length + 1 := by rw [hks_len] at hmlt; omega
      have heval := houtereq m hmlt' a vs hbvs n e hnlt hvsn
      refine ⟨false, ?_⟩
      rw [hewval, heval, hflat]
      have hidxeq : (c0 :: cs)[j + 1]? = cs[K0 + ksPrefix (guessBXJsToKs I js) m + n]? := by
        have hK0 : (I.β v0).length = K0 + 1 := hβ
        have hidx' : j + 1 = (K0 + ksPrefix (guessBXJsToKs I js) m + n) + 1 := by omega
        rw [hidx', List.getElem?_cons_succ]
      rw [hidxeq]


/-! ## Step 4: length matching

`c^x` makes `kwsVX.length + 1` reads of `xA`: index `0` reads `v0VX` (never
`⊥`), index `i + 1` reads `kwsVX[i].2`, which is `none` exactly at the last
index. On `g_α^x`'s side, the letter at `idx` is
`((v0AX::jsAX).map I.α).flatten[idx]?`, which is `none` exactly from
`idx = flatten.length` on. Matching the two `none` positions gives
`flatten.length = kwsVX.length`. -/

/-- The length of `g_α^x`'s word `((v0AX::jsAX).map I.α).flatten` equals
`c^x`'s `kwsVX.length`. -/
theorem guessAX_checkX_xA_length_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v0VX : I.Γ} {jsVX : List I.Γ} {kwsVX : List (Fin 4 × Option I.Γ)}
    (hwVX : G.threadWord Tid.checkX = (checkXBlockWord I v0VX kwsVX).map some)
    (hkwsVXlen : kwsVX.length = jsVX.length + 1)
    (hkwsVXval : ∀ i, i < kwsVX.length → kwsVX[i]?.map Prod.snd = some (jsVX[i]?))
    {v0AX : Fin I.n} {K0AX : ℕ} {jsAX : List (Fin I.n)} {v1AX v2AX : Val I}
    {vB0AX : Val I × Val I} {inner0RestAX : List (Val I × Val I × Val I)}
    {outerRestAX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hαAX : (I.α v0AX).length = K0AX + 1)
    (hinner0lenAX : inner0RestAX.length = K0AX)
    (houterlenAX : outerRestAX.length = jsAX.length + 1)
    (hpreOuterAX : ∀ m, m < jsAX.length → ∃ b vs km, outerRestAX[m]? = some (b, vs) ∧
      (guessAXJsToKs I jsAX)[m]? = some km ∧ vs.length = km + 1)
    (hlastOuterAX : ∃ b vs, outerRestAX[jsAX.length]? = some (b, vs) ∧ vs.length = 1)
    (hv1xAAX : ∃ j : Fin (GuessAX.maxLen I + 2), j.val = 1 ∧
      v1AX = Val.xTag (Tid.guessAX, true) (GuessAX.jthLetter I (some v0AX) j))
    (hinner0valxAAX : ∀ n, n < inner0RestAX.length → ∃ e j, inner0RestAX[n]? = some e ∧
      j.val = n + 2 ∧ e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some v0AX) j))
    (houtervalxAAX : ∀ m, m < jsAX.length + 1 → ∃ b vs, outerRestAX[m]? = some (b, vs) ∧
      (m < jsAX.length → ∃ w, jsAX[m]? = some w ∧
        ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some w) j)) ∧
      (m = jsAX.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I none j)))
    (hσ1AX : G.threadLabels Tid.guessAX =
      guessAXBlockWord I v1AX v2AX vB0AX inner0RestAX outerRestAX) :
    ((v0AX :: jsAX).map I.α).flatten.length = kwsVX.length := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- `flatten.length < kwsVX.length`: contradiction at read/write index `flatten.length`.
    have hne0 : I.α v0AX ≠ [] := I.hα v0AX
    have hp1 : 1 ≤ ((v0AX :: jsAX).map I.α).flatten.length := by
      have hsub : (I.α v0AX).length ≤ ((v0AX :: jsAX).map I.α).flatten.length := by
        simp [List.flatten_cons]
      have := List.length_pos_of_ne_nil hne0
      omega
    set p := ((v0AX :: jsAX).map I.α).flatten.length with hpdef
    set i := p - 1 with hidef
    have hpeq : p = i + 1 := by omega
    have hilt : i < jsVX.length := by omega
    have hiltkws : i < kwsVX.length := by omega
    obtain ⟨kw, hkw⟩ : ∃ kw, kwsVX[i]? = some kw :=
      ⟨kwsVX[i]'hiltkws, List.getElem?_eq_getElem hiltkws⟩
    have hjssome : jsVX[i]? = some (jsVX[i]'hilt) := List.getElem?_eq_getElem hilt
    have hvalkw := hkwsVXval i hiltkws
    rw [hkw, hjssome] at hvalkw
    have hkw2 : kw.2 = some (jsVX[i]'hilt) := by injection hvalkw
    obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkX_xA_read_xB_read_val_eq_succ I G i hwVX hkw
    obtain ⟨ewa, ewb, hwaindex, hwbindex, hwaval, hwbval⟩ :=
      guessAX_guessBX_xA_xB_write_val_eq_succ I G hG i hea heb hvala hvalb
    rw [← hpeq] at hwaindex
    obtain ⟨tag, htag⟩ := guessAX_xA_write_letter_eq_of_shape I G hαAX hinner0lenAX houterlenAX
      hpreOuterAX hlastOuterAX hv1xAAX hinner0valxAAX houtervalxAAX hσ1AX p hwaindex
    have hflatnone : ((v0AX :: jsAX).map I.α).flatten[p]? = none :=
      List.getElem?_eq_none (le_refl _)
    rw [htag, hflatnone, hkw2] at hwaval
    injection hwaval with _ hcontra
    exact absurd hcontra (by simp)
  · -- `flatten.length > kwsVX.length`: contradiction at read/write index `kwsVX.length`.
    have hq1 : 1 ≤ kwsVX.length := by omega
    set q := kwsVX.length with hqdef
    set i := q - 1 with hidef
    have hqeq : q = i + 1 := by omega
    have hieqjs : i = jsVX.length := by omega
    have hiltkws : i < kwsVX.length := by omega
    obtain ⟨kw, hkw⟩ : ∃ kw, kwsVX[i]? = some kw :=
      ⟨kwsVX[i]'hiltkws, List.getElem?_eq_getElem hiltkws⟩
    have hjsnone : jsVX[i]? = none := by rw [hieqjs]; exact List.getElem?_eq_none (le_refl _)
    have hvalkw := hkwsVXval i hiltkws
    rw [hkw, hjsnone] at hvalkw
    have hkw2 : kw.2 = none := by injection hvalkw
    obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkX_xA_read_xB_read_val_eq_succ I G i hwVX hkw
    obtain ⟨ewa, ewb, hwaindex, hwbindex, hwaval, hwbval⟩ :=
      guessAX_guessBX_xA_xB_write_val_eq_succ I G hG i hea heb hvala hvalb
    rw [← hqeq] at hwaindex
    obtain ⟨tag, htag⟩ := guessAX_xA_write_letter_eq_of_shape I G hαAX hinner0lenAX houterlenAX
      hpreOuterAX hlastOuterAX hv1xAAX hinner0valxAAX houtervalxAAX hσ1AX q hwaindex
    have hqlt : q < ((v0AX :: jsAX).map I.α).flatten.length := by omega
    have hflatsome : ((v0AX :: jsAX).map I.α).flatten[q]? =
        some (((v0AX :: jsAX).map I.α).flatten[q]'hqlt) := List.getElem?_eq_getElem hqlt
    rw [htag, hflatsome, hkw2] at hwaval
    injection hwaval with _ hcontra
    exact absurd hcontra (by simp)

/-- The length of `g_β^x`'s word `((v0BX::jsBX).map I.β).flatten` equals
`c^x`'s `kwsVX.length`. -/
theorem guessBX_checkX_xB_length_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v0VX : I.Γ} {jsVX : List I.Γ} {kwsVX : List (Fin 4 × Option I.Γ)}
    (hwVX : G.threadWord Tid.checkX = (checkXBlockWord I v0VX kwsVX).map some)
    (hkwsVXlen : kwsVX.length = jsVX.length + 1)
    (hkwsVXval : ∀ i, i < kwsVX.length → kwsVX[i]?.map Prod.snd = some (jsVX[i]?))
    {v0BX : Fin I.n} {K0BX : ℕ} {jsBX : List (Fin I.n)} {v1BX v2BX : Val I}
    {vB0BX : Val I × Val I} {inner0RestBX : List (Val I × Val I × Val I)}
    {outerRestBX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hβBX : (I.β v0BX).length = K0BX + 1)
    (hinner0lenBX : inner0RestBX.length = K0BX)
    (houterlenBX : outerRestBX.length = jsBX.length + 1)
    (hpreOuterBX : ∀ m, m < jsBX.length → ∃ b vs km, outerRestBX[m]? = some (b, vs) ∧
      (guessBXJsToKs I jsBX)[m]? = some km ∧ vs.length = km + 1)
    (hlastOuterBX : ∃ b vs, outerRestBX[jsBX.length]? = some (b, vs) ∧ vs.length = 1)
    (hv1xBBX : ∃ j : Fin (GuessBX.maxLen I + 2), j.val = 1 ∧
      v1BX = Val.xTag (Tid.guessBX, true) (GuessBX.jthLetter I (some v0BX) j))
    (hinner0valxBBX : ∀ n, n < inner0RestBX.length → ∃ e j, inner0RestBX[n]? = some e ∧
      j.val = n + 2 ∧ e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some v0BX) j))
    (houtervalxBBX : ∀ m, m < jsBX.length + 1 → ∃ b vs, outerRestBX[m]? = some (b, vs) ∧
      (m < jsBX.length → ∃ w, jsBX[m]? = some w ∧
        ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some w) j)) ∧
      (m = jsBX.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I none j)))
    (hσ1BX : G.threadLabels Tid.guessBX =
      guessBXBlockWord I v1BX v2BX vB0BX inner0RestBX outerRestBX) :
    ((v0BX :: jsBX).map I.β).flatten.length = kwsVX.length := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- `flatten.length < kwsVX.length`: contradiction at read/write index `flatten.length`.
    have hne0 : I.β v0BX ≠ [] := I.hβ v0BX
    have hp1 : 1 ≤ ((v0BX :: jsBX).map I.β).flatten.length := by
      have hsub : (I.β v0BX).length ≤ ((v0BX :: jsBX).map I.β).flatten.length := by
        simp [List.flatten_cons]
      have := List.length_pos_of_ne_nil hne0
      omega
    set p := ((v0BX :: jsBX).map I.β).flatten.length with hpdef
    set i := p - 1 with hidef
    have hpeq : p = i + 1 := by omega
    have hilt : i < jsVX.length := by omega
    have hiltkws : i < kwsVX.length := by omega
    obtain ⟨kw, hkw⟩ : ∃ kw, kwsVX[i]? = some kw :=
      ⟨kwsVX[i]'hiltkws, List.getElem?_eq_getElem hiltkws⟩
    have hjssome : jsVX[i]? = some (jsVX[i]'hilt) := List.getElem?_eq_getElem hilt
    have hvalkw := hkwsVXval i hiltkws
    rw [hkw, hjssome] at hvalkw
    have hkw2 : kw.2 = some (jsVX[i]'hilt) := by injection hvalkw
    obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkX_xA_read_xB_read_val_eq_succ I G i hwVX hkw
    obtain ⟨ewa, ewb, hwaindex, hwbindex, hwaval, hwbval⟩ :=
      guessAX_guessBX_xA_xB_write_val_eq_succ I G hG i hea heb hvala hvalb
    rw [← hpeq] at hwbindex
    obtain ⟨tag, htag⟩ := guessBX_xB_write_letter_eq_of_shape I G hβBX hinner0lenBX houterlenBX
      hpreOuterBX hlastOuterBX hv1xBBX hinner0valxBBX houtervalxBBX hσ1BX p hwbindex
    have hflatnone : ((v0BX :: jsBX).map I.β).flatten[p]? = none :=
      List.getElem?_eq_none (le_refl _)
    rw [htag, hflatnone, hkw2] at hwbval
    injection hwbval with _ hcontra
    exact absurd hcontra (by simp)
  · -- `flatten.length > kwsVX.length`: contradiction at read/write index `kwsVX.length`.
    have hq1 : 1 ≤ kwsVX.length := by omega
    set q := kwsVX.length with hqdef
    set i := q - 1 with hidef
    have hqeq : q = i + 1 := by omega
    have hieqjs : i = jsVX.length := by omega
    have hiltkws : i < kwsVX.length := by omega
    obtain ⟨kw, hkw⟩ : ∃ kw, kwsVX[i]? = some kw :=
      ⟨kwsVX[i]'hiltkws, List.getElem?_eq_getElem hiltkws⟩
    have hjsnone : jsVX[i]? = none := by rw [hieqjs]; exact List.getElem?_eq_none (le_refl _)
    have hvalkw := hkwsVXval i hiltkws
    rw [hkw, hjsnone] at hvalkw
    have hkw2 : kw.2 = none := by injection hvalkw
    obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkX_xA_read_xB_read_val_eq_succ I G i hwVX hkw
    obtain ⟨ewa, ewb, hwaindex, hwbindex, hwaval, hwbval⟩ :=
      guessAX_guessBX_xA_xB_write_val_eq_succ I G hG i hea heb hvala hvalb
    rw [← hqeq] at hwbindex
    obtain ⟨tag, htag⟩ := guessBX_xB_write_letter_eq_of_shape I G hβBX hinner0lenBX houterlenBX
      hpreOuterBX hlastOuterBX hv1xBBX hinner0valxBBX houtervalxBBX hσ1BX q hwbindex
    have hqlt : q < ((v0BX :: jsBX).map I.β).flatten.length := by omega
    have hflatsome : ((v0BX :: jsBX).map I.β).flatten[q]? =
        some (((v0BX :: jsBX).map I.β).flatten[q]'hqlt) := List.getElem?_eq_getElem hqlt
    rw [htag, hflatsome, hkw2] at hwbval
    injection hwbval with _ hcontra
    exact absurd hcontra (by simp)

/-! ## Step 5: the words agree -/

/-- `((v0AX::jsAX).map I.α).flatten = ((v0BX::jsBX).map I.β).flatten`, by
`List.ext_getElem?`: at `k = 0` and at `k = j + 1` with `j < kwsVX.length` by
steps 1-3; beyond, both sides are `none` by step 4. -/
theorem guessAX_guessBX_xA_xB_flatten_eq (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final)
    {v0VX : I.Γ} {jsVX : List I.Γ} {kwsVX : List (Fin 4 × Option I.Γ)}
    (hwVX : G.threadWord Tid.checkX = (checkXBlockWord I v0VX kwsVX).map some)
    (hkwsVXlen : kwsVX.length = jsVX.length + 1)
    (hkwsVXval : ∀ i, i < kwsVX.length → kwsVX[i]?.map Prod.snd = some (jsVX[i]?))
    {v0AX : Fin I.n} {K0AX : ℕ} {jsAX : List (Fin I.n)} {v1AX v2AX : Val I}
    {vB0AX : Val I × Val I} {inner0RestAX : List (Val I × Val I × Val I)}
    {outerRestAX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hαAX : (I.α v0AX).length = K0AX + 1)
    (hinner0lenAX : inner0RestAX.length = K0AX)
    (houterlenAX : outerRestAX.length = jsAX.length + 1)
    (hpreOuterAX : ∀ m, m < jsAX.length → ∃ b vs km, outerRestAX[m]? = some (b, vs) ∧
      (guessAXJsToKs I jsAX)[m]? = some km ∧ vs.length = km + 1)
    (hlastOuterAX : ∃ b vs, outerRestAX[jsAX.length]? = some (b, vs) ∧ vs.length = 1)
    (hv1xAAX : ∃ j : Fin (GuessAX.maxLen I + 2), j.val = 1 ∧
      v1AX = Val.xTag (Tid.guessAX, true) (GuessAX.jthLetter I (some v0AX) j))
    (hinner0valxAAX : ∀ n, n < inner0RestAX.length → ∃ e j, inner0RestAX[n]? = some e ∧
      j.val = n + 2 ∧ e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some v0AX) j))
    (houtervalxAAX : ∀ m, m < jsAX.length + 1 → ∃ b vs, outerRestAX[m]? = some (b, vs) ∧
      (m < jsAX.length → ∃ w, jsAX[m]? = some w ∧
        ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some w) j)) ∧
      (m = jsAX.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I none j)))
    (hσ1AX : G.threadLabels Tid.guessAX =
      guessAXBlockWord I v1AX v2AX vB0AX inner0RestAX outerRestAX)
    {v0BX : Fin I.n} {K0BX : ℕ} {jsBX : List (Fin I.n)} {v1BX v2BX : Val I}
    {vB0BX : Val I × Val I} {inner0RestBX : List (Val I × Val I × Val I)}
    {outerRestBX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (hβBX : (I.β v0BX).length = K0BX + 1)
    (hinner0lenBX : inner0RestBX.length = K0BX)
    (houterlenBX : outerRestBX.length = jsBX.length + 1)
    (hpreOuterBX : ∀ m, m < jsBX.length → ∃ b vs km, outerRestBX[m]? = some (b, vs) ∧
      (guessBXJsToKs I jsBX)[m]? = some km ∧ vs.length = km + 1)
    (hlastOuterBX : ∃ b vs, outerRestBX[jsBX.length]? = some (b, vs) ∧ vs.length = 1)
    (hv1xBBX : ∃ j : Fin (GuessBX.maxLen I + 2), j.val = 1 ∧
      v1BX = Val.xTag (Tid.guessBX, true) (GuessBX.jthLetter I (some v0BX) j))
    (hinner0valxBBX : ∀ n, n < inner0RestBX.length → ∃ e j, inner0RestBX[n]? = some e ∧
      j.val = n + 2 ∧ e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some v0BX) j))
    (houtervalxBBX : ∀ m, m < jsBX.length + 1 → ∃ b vs, outerRestBX[m]? = some (b, vs) ∧
      (m < jsBX.length → ∃ w, jsBX[m]? = some w ∧
        ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some w) j)) ∧
      (m = jsBX.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I none j)))
    (hσ1BX : G.threadLabels Tid.guessBX =
      guessBXBlockWord I v1BX v2BX vB0BX inner0RestBX outerRestBX) :
    ((v0AX :: jsAX).map I.α).flatten = ((v0BX :: jsBX).map I.β).flatten := by
  have hlenAX := guessAX_checkX_xA_length_eq I G hG hwVX hkwsVXlen hkwsVXval hαAX hinner0lenAX
    houterlenAX hpreOuterAX hlastOuterAX hv1xAAX hinner0valxAAX houtervalxAAX hσ1AX
  have hlenBX := guessBX_checkX_xB_length_eq I G hG hwVX hkwsVXlen hkwsVXval hβBX hinner0lenBX
    houterlenBX hpreOuterBX hlastOuterBX hv1xBBX hinner0valxBBX houtervalxBBX hσ1BX
  apply List.ext_getElem?
  intro k
  rcases k with _ | j
  · -- k = 0.
    obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ := checkX_xA_read_xB_read_val_eq0 I G hwVX
    obtain ⟨ewa, ewb, hwaindex, hwbindex, hwaval, hwbval⟩ :=
      guessAX_guessBX_xA_xB_write_val_eq0 I G hG hea heb hvala hvalb
    obtain ⟨tagA, htagA⟩ := guessAX_xA_write_letter_eq_of_shape I G hαAX hinner0lenAX
      houterlenAX hpreOuterAX hlastOuterAX hv1xAAX hinner0valxAAX houtervalxAAX hσ1AX 0 hwaindex
    obtain ⟨tagB, htagB⟩ := guessBX_xB_write_letter_eq_of_shape I G hβBX hinner0lenBX
      houterlenBX hpreOuterBX hlastOuterBX hv1xBBX hinner0valxBBX houtervalxBBX hσ1BX 0 hwbindex
    rw [htagA] at hwaval
    rw [htagB] at hwbval
    injection hwaval with _ hAeq
    injection hwbval with _ hBeq
    exact hAeq.trans hBeq.symm
  · -- k = j + 1.
    rcases Nat.lt_or_ge j kwsVX.length with hjlt | hjge
    · obtain ⟨kw, hkw⟩ : ∃ kw, kwsVX[j]? = some kw :=
        ⟨kwsVX[j]'hjlt, List.getElem?_eq_getElem hjlt⟩
      obtain ⟨ea, eb, hea, heb, hvala, hvalb⟩ :=
        checkX_xA_read_xB_read_val_eq_succ I G j hwVX hkw
      obtain ⟨ewa, ewb, hwaindex, hwbindex, hwaval, hwbval⟩ :=
        guessAX_guessBX_xA_xB_write_val_eq_succ I G hG j hea heb hvala hvalb
      obtain ⟨tagA, htagA⟩ := guessAX_xA_write_letter_eq_of_shape I G hαAX hinner0lenAX
        houterlenAX hpreOuterAX hlastOuterAX hv1xAAX hinner0valxAAX houtervalxAAX hσ1AX
        (j + 1) hwaindex
      obtain ⟨tagB, htagB⟩ := guessBX_xB_write_letter_eq_of_shape I G hβBX hinner0lenBX
        houterlenBX hpreOuterBX hlastOuterBX hv1xBBX hinner0valxBBX houtervalxBBX hσ1BX
        (j + 1) hwbindex
      rw [htagA] at hwaval
      rw [htagB] at hwbval
      injection hwaval with _ hAeq
      injection hwbval with _ hBeq
      exact hAeq.trans hBeq.symm
    · have hjAX : ((v0AX :: jsAX).map I.α).flatten.length ≤ j + 1 := by omega
      have hjBX : ((v0BX :: jsBX).map I.β).flatten.length ≤ j + 1 := by omega
      rw [List.getElem?_eq_none hjAX, List.getElem?_eq_none hjBX]

/-! ## The solution -/

/-- Rephrases a `guessAX_shape_inv` decomposition into the hypotheses of
`guessAX_guessBX_js_eq` (with `ksAX := K0AX :: guessAXJsToKs I jsAX`). -/
theorem guessAX_js_eq_hyps_of_shape_inv (I : PCPInstance) {K0AX : ℕ}
    {jsAX : List (Fin I.n)} {outerRestAX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (houterlenAX : outerRestAX.length = jsAX.length + 1)
    (hpreOuterAX : ∀ m, m < jsAX.length → ∃ b vs km, outerRestAX[m]? = some (b, vs) ∧
      (guessAXJsToKs I jsAX)[m]? = some km ∧ vs.length = km + 1)
    (hlastOuterAX : ∃ b vs, outerRestAX[jsAX.length]? = some (b, vs) ∧ vs.length = 1)
    (hbridgevalAX : ∀ m, m < jsAX.length + 1 → ∃ b vs, outerRestAX[m]? = some (b, vs) ∧
      b.1 = Val.cnt (⟨(2 + m) % 4, by omega⟩ : Fin 4) ∧
      (m < jsAX.length → ∃ w, jsAX[m]? = some w ∧
        b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) (some w)) ∧
      (m = jsAX.length → b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) none)) :
    ∃ (ksAX : List ℕ) (NAX : ℕ), ksAX.length = NAX + 1 ∧ ksAX[0]? = some K0AX ∧
      outerRestAX.length = NAX + 1 ∧
      (∀ j, j < NAX → ∃ b vs km, outerRestAX[j]? = some (b, vs) ∧
        ksAX[j + 1]? = some km ∧ vs.length = km + 1) ∧
      (∃ b vs, outerRestAX[NAX]? = some (b, vs) ∧ vs.length = 1) ∧
      jsAX.length = NAX ∧
      (∀ m, m ≤ NAX → ∃ b vs, outerRestAX[m]? = some (b, vs) ∧
        ∃ r, b.2 = Val.cntAux r (jsAX[m]?)) ∧
      (∀ m, m < NAX → ∃ b vs, outerRestAX[m]? = some (b, vs) ∧
        ∃ r w, b.2 = Val.cntAux r (some w)) ∧
      (∃ b vs, outerRestAX[NAX]? = some (b, vs) ∧ ∃ r, b.2 = Val.cntAux r none) := by
  refine ⟨K0AX :: guessAXJsToKs I jsAX, jsAX.length, ?_, ?_, houterlenAX, ?_, hlastOuterAX, rfl,
    ?_, ?_, ?_⟩
  · simp [guessAXJsToKs]
  · simp
  · intro j hj
    obtain ⟨b, vs, km, hbvs, hkm, hvslen⟩ := hpreOuterAX j hj
    exact ⟨b, vs, km, hbvs, by rw [List.getElem?_cons_succ]; exact hkm, hvslen⟩
  · intro m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · obtain ⟨b, vs, hbvs, -, hsome, -⟩ := hbridgevalAX m (by omega)
      obtain ⟨w, hw, hb2⟩ := hsome hlt
      exact ⟨b, vs, hbvs, _, by rw [hw]; exact hb2⟩
    · obtain ⟨b, vs, hbvs, -, -, hnone⟩ := hbridgevalAX m (by omega)
      have hjsNone : jsAX[m]? = none := by rw [heq]; exact List.getElem?_eq_none (le_refl _)
      exact ⟨b, vs, hbvs, _, by rw [hjsNone]; exact hnone heq⟩
  · intro m hm
    obtain ⟨b, vs, hbvs, -, hsome, -⟩ := hbridgevalAX m (by omega)
    obtain ⟨w, hw, hb2⟩ := hsome hm
    exact ⟨b, vs, hbvs, _, w, hb2⟩
  · obtain ⟨b, vs, hbvs, -, -, hnone⟩ := hbridgevalAX jsAX.length (by omega)
    exact ⟨b, vs, hbvs, _, hnone rfl⟩

/-- The `β`/`g_β^x` counterpart of `guessAX_js_eq_hyps_of_shape_inv`. -/
theorem guessBX_js_eq_hyps_of_shape_inv (I : PCPInstance) {K0BX : ℕ}
    {jsBX : List (Fin I.n)} {outerRestBX : List ((Val I × Val I) × List (Val I × Val I × Val I))}
    (houterlenBX : outerRestBX.length = jsBX.length + 1)
    (hpreOuterBX : ∀ m, m < jsBX.length → ∃ b vs km, outerRestBX[m]? = some (b, vs) ∧
      (guessBXJsToKs I jsBX)[m]? = some km ∧ vs.length = km + 1)
    (hlastOuterBX : ∃ b vs, outerRestBX[jsBX.length]? = some (b, vs) ∧ vs.length = 1)
    (hbridgevalBX : ∀ m, m < jsBX.length + 1 → ∃ b vs, outerRestBX[m]? = some (b, vs) ∧
      b.1 = Val.cnt (⟨(2 + m) % 4, by omega⟩ : Fin 4) ∧
      (m < jsBX.length → ∃ w, jsBX[m]? = some w ∧
        b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) (some w)) ∧
      (m = jsBX.length → b.2 = Val.cntAux (⟨(2 + m) % 4, by omega⟩ : Fin 4) none)) :
    ∃ (ksBX : List ℕ) (NBX : ℕ), ksBX.length = NBX + 1 ∧ ksBX[0]? = some K0BX ∧
      outerRestBX.length = NBX + 1 ∧
      (∀ j, j < NBX → ∃ b vs km, outerRestBX[j]? = some (b, vs) ∧
        ksBX[j + 1]? = some km ∧ vs.length = km + 1) ∧
      (∃ b vs, outerRestBX[NBX]? = some (b, vs) ∧ vs.length = 1) ∧
      jsBX.length = NBX ∧
      (∀ m, m ≤ NBX → ∃ b vs, outerRestBX[m]? = some (b, vs) ∧
        ∃ r, b.2 = Val.cntAux r (jsBX[m]?)) ∧
      (∀ m, m < NBX → ∃ b vs, outerRestBX[m]? = some (b, vs) ∧
        ∃ r w, b.2 = Val.cntAux r (some w)) ∧
      (∃ b vs, outerRestBX[NBX]? = some (b, vs) ∧ ∃ r, b.2 = Val.cntAux r none) := by
  refine ⟨K0BX :: guessBXJsToKs I jsBX, jsBX.length, ?_, ?_, houterlenBX, ?_, hlastOuterBX, rfl,
    ?_, ?_, ?_⟩
  · simp [guessBXJsToKs]
  · simp
  · intro j hj
    obtain ⟨b, vs, km, hbvs, hkm, hvslen⟩ := hpreOuterBX j hj
    exact ⟨b, vs, km, hbvs, by rw [List.getElem?_cons_succ]; exact hkm, hvslen⟩
  · intro m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · obtain ⟨b, vs, hbvs, -, hsome, -⟩ := hbridgevalBX m (by omega)
      obtain ⟨w, hw, hb2⟩ := hsome hlt
      exact ⟨b, vs, hbvs, _, by rw [hw]; exact hb2⟩
    · obtain ⟨b, vs, hbvs, -, -, hnone⟩ := hbridgevalBX m (by omega)
      have hjsNone : jsBX[m]? = none := by rw [heq]; exact List.getElem?_eq_none (le_refl _)
      exact ⟨b, vs, hbvs, _, by rw [hjsNone]; exact hnone heq⟩
  · intro m hm
    obtain ⟨b, vs, hbvs, -, hsome, -⟩ := hbridgevalBX m (by omega)
    obtain ⟨w, hw, hb2⟩ := hsome hm
    exact ⟨b, vs, hbvs, _, w, hb2⟩
  · obtain ⟨b, vs, hbvs, -, -, hnone⟩ := hbridgevalBX jsBX.length (by omega)
    exact ⟨b, vs, hbvs, _, hnone rfl⟩

/-- An execution `G` reaching `ConcProg I`'s final state gives a PCP solution:
the closed forms of `c^x`, `c^y`, `g_α^x`, `g_α^y`, `g_β^x`, `g_β^y` are
extracted once, and the guesser pair's agreement (`guessAX_guessBX_js_eq`)
together with the word equality (`guessAX_guessBX_xA_xB_flatten_eq`)
witnesses `I.IsSolution (v0AX::jsAX)`. -/
theorem guessAX_guessBX_IsSolution (I : PCPInstance) (G : ExecutionGraph (domainOf I))
    (hG : G.Reaches (ConcProg I) (ConcProg I).final) : I.HasSolution := by
  obtain ⟨s1VX, cLast1VX, φ1VX, hrun1VX⟩ := checkX_run_of_reaches I G hG
  obtain ⟨v0VX, jsVX, kwsVX, hsVX, hkwsVXlen, hkwsVXmod, hkwsVXval, hσVX⟩ :=
    checkX_shape_inv_vals I hrun1VX
  have hwVX : G.threadWord Tid.checkX = (checkXBlockWord I v0VX kwsVX).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkX, hσVX]
  obtain ⟨s1VY, cLast1VY, φ1VY, hrun1VY⟩ := checkY_run_of_reaches I G hG
  obtain ⟨v0VY, jsVY, kwsVY, hsVY, hkwsVYlen, hkwsVYmod, hkwsVYval, hσVY⟩ :=
    checkY_shape_inv_vals I hrun1VY
  have hwVY : G.threadWord Tid.checkY = (checkYBlockWord I v0VY kwsVY).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.checkY, hσVY]
  obtain ⟨s1AY, cLast1AY, φ1AY, hrun1AY⟩ := guessAY_run_of_reaches I G hG
  obtain ⟨v0AY, jsAY, kwsAY, hsAY, hkwsAYlen, hkwsAYmod, hkwsAYval, hσAY⟩ :=
    guessAY_shape_inv_vals I hrun1AY
  have hwAY : G.threadWord Tid.guessAY = (guessAYBlockWord I v0AY kwsAY).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAY, hσAY]
  obtain ⟨s1BY, cLast1BY, φ1BY, hrun1BY⟩ := guessBY_run_of_reaches I G hG
  obtain ⟨v0BY, jsBY, kwsBY, hsBY, hkwsBYlen, hkwsBYmod, hkwsBYval, hσBY⟩ :=
    guessBY_shape_inv_vals I hrun1BY
  have hwBY : G.threadWord Tid.guessBY = (guessBYBlockWord I v0BY kwsBY).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBY, hσBY]
  obtain ⟨s1AX, cLast1AX, φ1AX, hrun1AX⟩ := guessAX_run_of_reaches I G hG
  obtain ⟨v0AX, K0AX, jsAX, v1AX, v2AX, vB0AX, inner0RestAX, outerRestAX,
    hαAX, hsAX, hinner0lenAX, houterlenAX, hpreOuterAX, hlastOuterAX, hv2AX, hinner0valAX,
    houtervalAX, hvB01AX, hvB02AX, hbridgevalAX, hv1xAAX, hinner0valxAAX, houtervalxAAX,
    hσ1AX⟩ := guessAX_shape_inv I hrun1AX
  obtain ⟨s1BX, cLast1BX, φ1BX, hrun1BX⟩ := guessBX_run_of_reaches I G hG
  obtain ⟨v0BX, K0BX, jsBX, v1BX, v2BX, vB0BX, inner0RestBX, outerRestBX,
    hβBX, hsBX, hinner0lenBX, houterlenBX, hpreOuterBX, hlastOuterBX, hv2BX, hinner0valBX,
    houtervalBX, hvB01BX, hvB02BX, hbridgevalBX, hv1xBBX, hinner0valxBBX, houtervalxBBX,
    hσ1BX⟩ := guessBX_shape_inv I hrun1BX
  obtain ⟨ksAX, NAX, hksAX, hK0AX, houterLenAX, houterAX, houterLastAX, hlenAX, hjsAX,
    houterValSomeAX, houterValNoneAX⟩ :=
    guessAX_js_eq_hyps_of_shape_inv I houterlenAX hpreOuterAX hlastOuterAX hbridgevalAX
  obtain ⟨ksBX, NBX, hksBX, hK0BX, houterLenBX, houterBX, houterLastBX, hlenBX, hjsBX,
    houterValSomeBX, houterValNoneBX⟩ :=
    guessBX_js_eq_hyps_of_shape_inv I houterlenBX hpreOuterBX hlastOuterBX hbridgevalBX
  have hw1AX : G.threadWord Tid.guessAX =
      (guessAXBlockWord I v1AX v2AX vB0AX inner0RestAX outerRestAX).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessAX, hσ1AX]
  have hw1BX : G.threadWord Tid.guessBX =
      (guessBXBlockWord I v1BX v2BX vB0BX inner0RestBX outerRestBX).map some := by
    rw [G.threadWord_eq_map_threadLabels Tid.guessBX, hσ1BX]
  obtain ⟨hv0eq, hjseq⟩ := guessAX_guessBX_js_eq I G hG hwVY hkwsVYlen hkwsVYval
    hwAY hkwsAYlen hkwsAYval hwBY hkwsBYlen hkwsBYval
    hinner0lenAX hw1AX hvB02AX hksAX hK0AX houterLenAX houterAX houterLastAX hlenAX hjsAX
    houterValSomeAX houterValNoneAX
    hinner0lenBX hw1BX hvB02BX hksBX hK0BX houterLenBX houterBX houterLastBX hlenBX hjsBX
    houterValSomeBX houterValNoneBX
  have hflateq := guessAX_guessBX_xA_xB_flatten_eq I G hG hwVX hkwsVXlen hkwsVXval
    hαAX hinner0lenAX houterlenAX hpreOuterAX hlastOuterAX hv1xAAX hinner0valxAAX
    houtervalxAAX hσ1AX
    hβBX hinner0lenBX houterlenBX hpreOuterBX hlastOuterBX hv1xBBX hinner0valxBBX
    houtervalxBBX hσ1BX
  refine ⟨v0AX :: jsAX, List.cons_ne_nil _ _, ?_⟩
  rw [hflateq, ← hv0eq, ← hjseq]

/-- **Paper:** Lemma 3.1.

Lemma 3.1: an execution of `ConcProg I` reaching its final state
gives a solution of `I`. Transcribes the paragraph "Proof of
Lemma 3.1" in Section 3.4. -/
theorem soundness (I : PCPInstance) (h : (ConcProg I).ReachesFinal) : I.HasSolution := by
  obtain ⟨G, hG⟩ := h
  exact guessAX_guessBX_IsSolution I G hG

end RAUndecidability
