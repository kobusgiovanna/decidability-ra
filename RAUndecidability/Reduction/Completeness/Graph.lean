import RAUndecidability.Reduction.Completeness.Monotonicity

/-!
# The execution graph `G`

The execution graph `G` of §3.5 ("The execution graph G"), for a solved
instance: the facts its fields need beyond `Completeness/Construction.lean`
(every read falls in one of `traceRf`'s branches, writes are confined to
their locations' writers, `rf_unique`, `rf_matches`), the graph itself
(`executionGraphOf`), and the properties of `G` used for its RA-consistency
(`Completeness/Consistency.lean`): Lemmas 3.4 and 3.5 restated for `G`, and
the thread-level `rf` topology and `hb` separation (Fig. 4).
-/

namespace RAUndecidability

/-! ## Exhaustiveness of `traceRf`'s branches

`traceRf` (`Completeness/Construction.lean`) transcribes Eq. (15)-(17)
("Specifying `G.rf`") as a 28-branch case split on a read event's
`(tid, loc)`; for `rf_total`, every read event must fall in one of these
branches. The lemmas below show this one thread at a time, from its
`*BlockShape`/`*BlockElems` facts, and `traceRf_reads_confined` combines
them. -/

/-- `primeAX`'s only read location is `zAx'x`. -/
theorem traceRf_reads_primeAX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.primeAX) (herop : er.op = .rd) :
    er.loc = Loc.zAx'x := by
  obtain ⟨vals, htrace⟩ := hshapes.primeAX
  have hshape : ∀ x ∈ primeAXBlockWord I vals, (x.1.loc, x.1.op) ∈ primeAXBlockShape := by
    intro x hx
    unfold primeAXBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeAXBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ primeAXBlockShape := by rw [← hloc]; exact hmem
  unfold primeAXBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact congrArg Prod.fst h

/-- primeBX's only real read location: `zBx'x`. See `traceRf_reads_primeAX`. -/
theorem traceRf_reads_primeBX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.primeBX) (herop : er.op = .rd) :
    er.loc = Loc.zBx'x := by
  obtain ⟨vals, htrace⟩ := hshapes.primeBX
  have hshape : ∀ x ∈ primeBXBlockWord I vals, (x.1.loc, x.1.op) ∈ primeBXBlockShape := by
    intro x hx
    unfold primeBXBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeBXBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ primeBXBlockShape := by rw [← hloc]; exact hmem
  unfold primeBXBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact congrArg Prod.fst h

/-- primeAY's only real read location: `zAy'y`. See `traceRf_reads_primeAX`. -/
theorem traceRf_reads_primeAY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.primeAY) (herop : er.op = .rd) :
    er.loc = Loc.zAy'y := by
  obtain ⟨vals, htrace⟩ := hshapes.primeAY
  have hshape : ∀ x ∈ primeAYBlockWord I vals, (x.1.loc, x.1.op) ∈ primeAYBlockShape := by
    intro x hx
    unfold primeAYBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeAYBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ primeAYBlockShape := by rw [← hloc]; exact hmem
  unfold primeAYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact congrArg Prod.fst h

/-- primeBY's only real read location: `zBy'y`. See `traceRf_reads_primeAX`. -/
theorem traceRf_reads_primeBY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.primeBY) (herop : er.op = .rd) :
    er.loc = Loc.zBy'y := by
  obtain ⟨vals, htrace⟩ := hshapes.primeBY
  have hshape : ∀ x ∈ primeBYBlockWord I vals, (x.1.loc, x.1.op) ∈ primeBYBlockShape := by
    intro x hx
    unfold primeBYBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeBYBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ primeBYBlockShape := by rw [← hloc]; exact hmem
  unfold primeBYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact congrArg Prod.fst h

/-- primeCheckX's real read locations: `xA'`, `xB'`, `xA`, `xB`
(Eq. (16)'s symmetric primed reads). See `traceRf_reads_primeAX`. -/
theorem traceRf_reads_primeCheckX (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.primeCheckX)
    (herop : er.op = .rd) :
    er.loc = Loc.xA' ∨ er.loc = Loc.xB' ∨ er.loc = Loc.xA ∨ er.loc = Loc.xB := by
  obtain ⟨cnts, htrace⟩ := hshapes.primeCheckX
  have hshape : ∀ x ∈ primeCheckXBlockWord I cnts, (x.1.loc, x.1.op) ∈ primeCheckXBlockShape := by
    intro x hx
    unfold primeCheckXBlockWord at hx
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeCheckXBlockElems_shape I c
    rw [← hshapeeq]
    exact List.mem_map_of_mem hc
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ primeCheckXBlockShape := by rw [← hloc]; exact hmem
  unfold primeCheckXBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Prod.fst h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Prod.fst h)))

/-- primeCheckY's real read locations: `yA'`, `yB'`, `yA`, `yB`.
See `traceRf_reads_primeCheckX`. -/
theorem traceRf_reads_primeCheckY (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.primeCheckY)
    (herop : er.op = .rd) :
    er.loc = Loc.yA' ∨ er.loc = Loc.yB' ∨ er.loc = Loc.yA ∨ er.loc = Loc.yB := by
  obtain ⟨cnts, htrace⟩ := hshapes.primeCheckY
  have hshape : ∀ x ∈ primeCheckYBlockWord I cnts, (x.1.loc, x.1.op) ∈ primeCheckYBlockShape := by
    intro x hx
    unfold primeCheckYBlockWord at hx
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeCheckYBlockElems_shape I c
    rw [← hshapeeq]
    exact List.mem_map_of_mem hc
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ primeCheckYBlockShape := by rw [← hloc]; exact hmem
  unfold primeCheckYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Prod.fst h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Prod.fst h)))

/-- checkX's real read locations: `xA`, `xB`, `xA'`, `xB'` (Eq. (16)).
See `traceRf_reads_primeAX`. -/
theorem traceRf_reads_checkX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.checkX)
    (herop : er.op = .rd) :
    er.loc = Loc.xA ∨ er.loc = Loc.xB ∨ er.loc = Loc.xA' ∨ er.loc = Loc.xB' := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.checkX
  have hshape : ∀ x ∈ checkXBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ checkXBlockShape := by
    intro x hx
    unfold checkXBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := checkXBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ checkXBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [checkXBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := checkXBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ checkXBlockShape := by rw [← hloc]; exact hmem
  unfold checkXBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Prod.fst h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Prod.fst h)))

/-- checkY's real read locations: `yA`, `yB`, `yA'`, `yB'`. See `traceRf_reads_checkX`. -/
theorem traceRf_reads_checkY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.checkY)
    (herop : er.op = .rd) :
    er.loc = Loc.yA ∨ er.loc = Loc.yB ∨ er.loc = Loc.yA' ∨ er.loc = Loc.yB' := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.checkY
  have hshape : ∀ x ∈ checkYBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ checkYBlockShape := by
    intro x hx
    unfold checkYBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := checkYBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ checkYBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [checkYBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := checkYBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ checkYBlockShape := by rw [← hloc]; exact hmem
  unfold checkYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Prod.fst h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Prod.fst h)))

/-! ## Non-bridge threads (Lemma 3.8)

A bridge event can only occur on `GuessAX`/`GuessAY`/`GuessBX`/`GuessBY`: the
other eight threads never access a bridge location. -/

/-- No event of `PrimeAX`'s trace is a bridge event. See `traceRf_reads_primeAX`. -/
theorem traceEventsOf_primeAX_not_bridge (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.primeAX) : ¬ e.IsBridge := by
  obtain ⟨vals, htrace⟩ := hshapes.primeAX
  have hshape : ∀ x ∈ primeAXBlockWord I vals, (x.1.loc, x.1.op) ∈ primeAXBlockShape := by
    intro x hx
    unfold primeAXBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeAXBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  exact primeAXBlockShape_no_bridge _ (traceEventsOf_locOp_mem_of_forall htrace hshape he)

/-- No event of `PrimeAY`'s trace is a bridge event. See `traceRf_reads_primeAX`. -/
theorem traceEventsOf_primeAY_not_bridge (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.primeAY) : ¬ e.IsBridge := by
  obtain ⟨vals, htrace⟩ := hshapes.primeAY
  have hshape : ∀ x ∈ primeAYBlockWord I vals, (x.1.loc, x.1.op) ∈ primeAYBlockShape := by
    intro x hx
    unfold primeAYBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeAYBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  exact primeAYBlockShape_no_bridge _ (traceEventsOf_locOp_mem_of_forall htrace hshape he)

/-- No event of `PrimeBX`'s trace is a bridge event. See `traceRf_reads_primeAX`. -/
theorem traceEventsOf_primeBX_not_bridge (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.primeBX) : ¬ e.IsBridge := by
  obtain ⟨vals, htrace⟩ := hshapes.primeBX
  have hshape : ∀ x ∈ primeBXBlockWord I vals, (x.1.loc, x.1.op) ∈ primeBXBlockShape := by
    intro x hx
    unfold primeBXBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeBXBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  exact primeBXBlockShape_no_bridge _ (traceEventsOf_locOp_mem_of_forall htrace hshape he)

/-- No event of `PrimeBY`'s trace is a bridge event. See `traceRf_reads_primeAX`. -/
theorem traceEventsOf_primeBY_not_bridge (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.primeBY) : ¬ e.IsBridge := by
  obtain ⟨vals, htrace⟩ := hshapes.primeBY
  have hshape : ∀ x ∈ primeBYBlockWord I vals, (x.1.loc, x.1.op) ∈ primeBYBlockShape := by
    intro x hx
    unfold primeBYBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeBYBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  exact primeBYBlockShape_no_bridge _ (traceEventsOf_locOp_mem_of_forall htrace hshape he)

/-- No event of `PrimeCheckX`'s trace is a bridge event. See `traceRf_reads_primeAX`. -/
theorem traceEventsOf_primeCheckX_not_bridge (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.primeCheckX) : ¬ e.IsBridge := by
  obtain ⟨cnts, htrace⟩ := hshapes.primeCheckX
  have hshape : ∀ x ∈ primeCheckXBlockWord I cnts, (x.1.loc, x.1.op) ∈ primeCheckXBlockShape := by
    intro x hx
    unfold primeCheckXBlockWord at hx
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeCheckXBlockElems_shape I c
    rw [← hshapeeq]
    exact List.mem_map_of_mem hc
  exact primeCheckXBlockShape_no_bridge _ (traceEventsOf_locOp_mem_of_forall htrace hshape he)

/-- No event of `PrimeCheckY`'s trace is a bridge event. See `traceRf_reads_primeAX`. -/
theorem traceEventsOf_primeCheckY_not_bridge (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.primeCheckY) : ¬ e.IsBridge := by
  obtain ⟨cnts, htrace⟩ := hshapes.primeCheckY
  have hshape : ∀ x ∈ primeCheckYBlockWord I cnts, (x.1.loc, x.1.op) ∈ primeCheckYBlockShape := by
    intro x hx
    unfold primeCheckYBlockWord at hx
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeCheckYBlockElems_shape I c
    rw [← hshapeeq]
    exact List.mem_map_of_mem hc
  exact primeCheckYBlockShape_no_bridge _ (traceEventsOf_locOp_mem_of_forall htrace hshape he)

/-- No event of `CheckX`'s trace is a bridge event. See `traceRf_reads_checkX`. -/
theorem traceEventsOf_checkX_not_bridge (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.checkX) : ¬ e.IsBridge := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.checkX
  have hshape : ∀ x ∈ checkXBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ checkXBlockShape := by
    intro x hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := checkXBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ checkXBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [checkXBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := checkXBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  exact checkXBlockShape_no_bridge _ (traceEventsOf_locOp_mem_of_forall htrace hshape he)

/-- No event of `CheckY`'s trace is a bridge event. See `traceRf_reads_checkX`. -/
theorem traceEventsOf_checkY_not_bridge (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace)
    {e : Event (domainOf I)} (he : e ∈ traceEventsOf trace Tid.checkY) : ¬ e.IsBridge := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.checkY
  have hshape : ∀ x ∈ checkYBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ checkYBlockShape := by
    intro x hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := checkYBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ checkYBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [checkYBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := checkYBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  exact checkYBlockShape_no_bridge _ (traceEventsOf_locOp_mem_of_forall htrace hshape he)

/-- guessAY's real read locations: `zAxy`, `zAyy'` (Eq. (15)).
See `traceRf_reads_primeAX`. -/
theorem traceRf_reads_guessAY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.guessAY)
    (herop : er.op = .rd) :
    er.loc = Loc.zAxy ∨ er.loc = Loc.zAyy' := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.guessAY
  have hshape : ∀ x ∈ guessAYBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ guessAYBlockShape := by
    intro x hx
    unfold guessAYBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := guessAYBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ guessAYBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [guessAYBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := guessAYBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ guessAYBlockShape := by rw [← hloc]; exact hmem
  unfold guessAYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)

/-- guessBY's real read locations: `zBxy`, `zByy'`. See `traceRf_reads_guessAY`. -/
theorem traceRf_reads_guessBY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.guessBY)
    (herop : er.op = .rd) :
    er.loc = Loc.zBxy ∨ er.loc = Loc.zByy' := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.guessBY
  have hshape : ∀ x ∈ guessBYBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ guessBYBlockShape := by
    intro x hx
    unfold guessBYBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := guessBYBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ guessBYBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [guessBYBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := guessBYBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈ guessBYBlockShape := by rw [← hloc]; exact hmem
  unfold guessBYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)

/-- `guessAX`'s read locations: `zAxx'`, `ellAyx`. -/
theorem traceRf_reads_guessAX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.guessAX)
    (herop : er.op = .rd) :
    er.loc = Loc.zAxx' ∨ er.loc = Loc.ellAyx := by
  obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
    htrace⟩ := hshapes.guessAX
  have hshape : ∀ x ∈ guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest,
      (x.1.loc, x.1.op) ∈
        ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
          (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)) := by
    have hinnerMem : ∀ v : Val I × Val I × Val I, ∀ x ∈ guessAXInnerBlockElems I v,
        (x.1.loc, x.1.op) ∈
          ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
            (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)) := by
      intro v x hx
      have hshapeeq := guessAXInnerBlockElems_shape I v
      obtain ⟨y, hy⟩ : ∃ y : Loc × OpType, (x.1.loc, x.1.op) = y := ⟨_, rfl⟩
      have hx' : y ∈ guessAXInnerBlockShape := by
        rw [← hy, ← hshapeeq]; exact List.mem_map_of_mem hx
      unfold guessAXInnerBlockShape at hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      have hgoal : y ∈
          ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
            (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)) := by
        rcases hx' with h | h | h <;> subst h <;> decide
      exact hy ▸ hgoal
    intro x hx
    unfold guessAXBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxouter
    · rcases List.mem_append.mp hx0 with hx0' | hxellAyx
      · rcases List.mem_append.mp hx0' with hxlead | hxinner
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxlead
          rcases hxlead with h | h | h <;> subst h <;>
            simp only [EventLabel.loc, EventLabel.op]
          · exact (by decide : (Loc.zAxy, OpType.wt) ∈
              ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
                (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
          · exact (by decide : (Loc.xA, OpType.wt) ∈
              ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
                (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
          · exact (by decide : (Loc.zAx'x, OpType.wt) ∈
              ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
                (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
        · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hxinner
          exact hinnerMem v x hv
      · simp only [List.mem_singleton] at hxellAyx
        subst hxellAyx
        simp only [EventLabel.loc, EventLabel.op]
        exact (by decide : (Loc.ellAyx, OpType.rd) ∈
          ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
            (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
    · obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp hxouter
      unfold guessAXOuterBlockElems at hp
      rcases List.mem_cons.mp hp with hp1 | hp2
      · subst hp1
        simp only [EventLabel.loc, EventLabel.op]
        exact (by decide : (Loc.zAxy, OpType.wt) ∈
          ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
            (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
      · rcases List.mem_append.mp hp2 with hp2' | hp3
        · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hp2'
          exact hinnerMem v x hv
        · simp only [List.mem_singleton] at hp3
          subst hp3
          simp only [EventLabel.loc, EventLabel.op]
          exact (by decide : (Loc.ellAyx, OpType.rd) ∈
            ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
              (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈
      ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
        (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)) := by
    rw [← hloc]; exact hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inl (congrArg Prod.fst h)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inr (congrArg Prod.fst h)

/-- guessBX's real read locations: `zBxx'`, `ellByx`. See `traceRf_reads_guessAX`. -/
theorem traceRf_reads_guessBX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEventsOf trace Tid.guessBX)
    (herop : er.op = .rd) :
    er.loc = Loc.zBxx' ∨ er.loc = Loc.ellByx := by
  obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
    htrace⟩ := hshapes.guessBX
  have hshape : ∀ x ∈ guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest,
      (x.1.loc, x.1.op) ∈
        ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
          (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)) := by
    have hinnerMem : ∀ v : Val I × Val I × Val I, ∀ x ∈ guessBXInnerBlockElems I v,
        (x.1.loc, x.1.op) ∈
          ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
            (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)) := by
      intro v x hx
      have hshapeeq := guessBXInnerBlockElems_shape I v
      obtain ⟨y, hy⟩ : ∃ y : Loc × OpType, (x.1.loc, x.1.op) = y := ⟨_, rfl⟩
      have hx' : y ∈ guessBXInnerBlockShape := by
        rw [← hy, ← hshapeeq]; exact List.mem_map_of_mem hx
      unfold guessBXInnerBlockShape at hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      have hgoal : y ∈
          ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
            (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)) := by
        rcases hx' with h | h | h <;> subst h <;> decide
      exact hy ▸ hgoal
    intro x hx
    unfold guessBXBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxouter
    · rcases List.mem_append.mp hx0 with hx0' | hxellAyx
      · rcases List.mem_append.mp hx0' with hxlead | hxinner
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxlead
          rcases hxlead with h | h | h <;> subst h <;>
            simp only [EventLabel.loc, EventLabel.op]
          · exact (by decide : (Loc.zBxy, OpType.wt) ∈
              ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
                (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
          · exact (by decide : (Loc.xB, OpType.wt) ∈
              ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
                (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
          · exact (by decide : (Loc.zBx'x, OpType.wt) ∈
              ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
                (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
        · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hxinner
          exact hinnerMem v x hv
      · simp only [List.mem_singleton] at hxellAyx
        subst hxellAyx
        simp only [EventLabel.loc, EventLabel.op]
        exact (by decide : (Loc.ellByx, OpType.rd) ∈
          ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
            (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
    · obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp hxouter
      unfold guessBXOuterBlockElems at hp
      rcases List.mem_cons.mp hp with hp1 | hp2
      · subst hp1
        simp only [EventLabel.loc, EventLabel.op]
        exact (by decide : (Loc.zBxy, OpType.wt) ∈
          ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
            (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
      · rcases List.mem_append.mp hp2 with hp2' | hp3
        · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hp2'
          exact hinnerMem v x hv
        · simp only [List.mem_singleton] at hp3
          subst hp3
          simp only [EventLabel.loc, EventLabel.op]
          exact (by decide : (Loc.ellByx, OpType.rd) ∈
            ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
              (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape her
  rw [herop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, er.loc = x := ⟨er.loc, rfl⟩
  have hmem2 : (x, OpType.rd) ∈
      ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
        (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)) := by
    rw [← hloc]; exact hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inl (congrArg Prod.fst h)
  · have h2 : OpType.rd = OpType.wt := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inr (congrArg Prod.fst h)

/-- Every read event of `trace` has its `(tid, loc)` in one of `traceRf`'s 28
branches. -/
theorem traceRf_reads_confined (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {er : Event (domainOf I)} (her : er ∈ traceEvents trace) (herop : er.op = .rd) :
    (er.tid = Tid.guessAX ∧ (er.loc = Loc.zAxx' ∨ er.loc = Loc.ellAyx)) ∨
    (er.tid = Tid.primeAX ∧ er.loc = Loc.zAx'x) ∨
    (er.tid = Tid.guessAY ∧ (er.loc = Loc.zAxy ∨ er.loc = Loc.zAyy')) ∨
    (er.tid = Tid.primeAY ∧ er.loc = Loc.zAy'y) ∨
    (er.tid = Tid.guessBX ∧ (er.loc = Loc.zBxx' ∨ er.loc = Loc.ellByx)) ∨
    (er.tid = Tid.primeBX ∧ er.loc = Loc.zBx'x) ∨
    (er.tid = Tid.guessBY ∧ (er.loc = Loc.zBxy ∨ er.loc = Loc.zByy')) ∨
    (er.tid = Tid.primeBY ∧ er.loc = Loc.zBy'y) ∨
    (er.tid = Tid.checkX ∧
      (er.loc = Loc.xA ∨ er.loc = Loc.xB ∨ er.loc = Loc.xA' ∨ er.loc = Loc.xB')) ∨
    (er.tid = Tid.primeCheckX ∧
      (er.loc = Loc.xA' ∨ er.loc = Loc.xB' ∨ er.loc = Loc.xA ∨ er.loc = Loc.xB)) ∨
    (er.tid = Tid.checkY ∧
      (er.loc = Loc.yA ∨ er.loc = Loc.yB ∨ er.loc = Loc.yA' ∨ er.loc = Loc.yB')) ∨
    (er.tid = Tid.primeCheckY ∧
      (er.loc = Loc.yA' ∨ er.loc = Loc.yB' ∨ er.loc = Loc.yA ∨ er.loc = Loc.yB)) := by
  match het : er.tid with
  | Tid.guessAX =>
      exact Or.inl ⟨rfl,
        traceRf_reads_guessAX I hshapes (mem_traceEvents_of_tid her het) herop⟩
  | Tid.primeAX =>
      exact Or.inr (Or.inl ⟨rfl,
        traceRf_reads_primeAX I hshapes (mem_traceEvents_of_tid her het) herop⟩)
  | Tid.guessAY =>
      exact Or.inr (Or.inr (Or.inl ⟨rfl,
        traceRf_reads_guessAY I hshapes (mem_traceEvents_of_tid her het) herop⟩))
  | Tid.primeAY =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        traceRf_reads_primeAY I hshapes (mem_traceEvents_of_tid her het) herop⟩)))
  | Tid.guessBX =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        traceRf_reads_guessBX I hshapes (mem_traceEvents_of_tid her het) herop⟩))))
  | Tid.primeBX =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        traceRf_reads_primeBX I hshapes (mem_traceEvents_of_tid her het) herop⟩)))))
  | Tid.guessBY =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        traceRf_reads_guessBY I hshapes (mem_traceEvents_of_tid her het) herop⟩))))))
  | Tid.primeBY =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        traceRf_reads_primeBY I hshapes (mem_traceEvents_of_tid her het) herop⟩)))))))
  | Tid.checkX =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        traceRf_reads_checkX I hshapes (mem_traceEvents_of_tid her het) herop⟩))))))))
  | Tid.primeCheckX =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,
        traceRf_reads_primeCheckX I hshapes (mem_traceEvents_of_tid her het) herop⟩)))))))))
  | Tid.checkY =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨rfl,
          traceRf_reads_checkY I hshapes (mem_traceEvents_of_tid her het) herop⟩))))))))))
  | Tid.primeCheckY =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (⟨rfl,
          traceRf_reads_primeCheckY I hshapes (mem_traceEvents_of_tid her het) herop⟩)))))))))))

/-! ## Confinement of writes (`G`'s `mo_total`)

Every write event's thread is among its location's `writerTids`, the
hypothesis `hwriters` of `traceEventsMo_total`. Shown one thread at a time
and combined in `traceMo_writers_confined`. -/

/-- `primeAX`'s only write locations: `xA'`, `zAxx'`. -/
theorem traceMo_writes_primeAX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.primeAX) (hewop : ew.op = .wt) :
    ew.loc = Loc.xA' ∨ ew.loc = Loc.zAxx' := by
  obtain ⟨vals, htrace⟩ := hshapes.primeAX
  have hshape : ∀ x ∈ primeAXBlockWord I vals, (x.1.loc, x.1.op) ∈ primeAXBlockShape := by
    intro x hx
    unfold primeAXBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeAXBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ primeAXBlockShape := by rw [← hloc]; exact hmem
  unfold primeAXBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- primeBX's only write locations: `xB'`, `zBxx'`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_primeBX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.primeBX) (hewop : ew.op = .wt) :
    ew.loc = Loc.xB' ∨ ew.loc = Loc.zBxx' := by
  obtain ⟨vals, htrace⟩ := hshapes.primeBX
  have hshape : ∀ x ∈ primeBXBlockWord I vals, (x.1.loc, x.1.op) ∈ primeBXBlockShape := by
    intro x hx
    unfold primeBXBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeBXBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ primeBXBlockShape := by rw [← hloc]; exact hmem
  unfold primeBXBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- primeAY's only write locations: `yA'`, `zAyy'`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_primeAY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.primeAY) (hewop : ew.op = .wt) :
    ew.loc = Loc.yA' ∨ ew.loc = Loc.zAyy' := by
  obtain ⟨vals, htrace⟩ := hshapes.primeAY
  have hshape : ∀ x ∈ primeAYBlockWord I vals, (x.1.loc, x.1.op) ∈ primeAYBlockShape := by
    intro x hx
    unfold primeAYBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeAYBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ primeAYBlockShape := by rw [← hloc]; exact hmem
  unfold primeAYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- primeBY's only write locations: `yB'`, `zByy'`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_primeBY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.primeBY) (hewop : ew.op = .wt) :
    ew.loc = Loc.yB' ∨ ew.loc = Loc.zByy' := by
  obtain ⟨vals, htrace⟩ := hshapes.primeBY
  have hshape : ∀ x ∈ primeBYBlockWord I vals, (x.1.loc, x.1.op) ∈ primeBYBlockShape := by
    intro x hx
    unfold primeBYBlockWord at hx
    obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeBYBlockElems_shape I l
    rw [← hshapeeq]
    exact List.mem_map_of_mem hl
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ primeBYBlockShape := by rw [← hloc]; exact hmem
  unfold primeBYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- primeCheckX's only write locations: `xA'`, `xB'`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_primeCheckX (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.primeCheckX)
    (hewop : ew.op = .wt) :
    ew.loc = Loc.xA' ∨ ew.loc = Loc.xB' := by
  obtain ⟨cnts, htrace⟩ := hshapes.primeCheckX
  have hshape : ∀ x ∈ primeCheckXBlockWord I cnts,
      (x.1.loc, x.1.op) ∈ primeCheckXBlockShape := by
    intro x hx
    unfold primeCheckXBlockWord at hx
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeCheckXBlockElems_shape I c
    rw [← hshapeeq]
    exact List.mem_map_of_mem hc
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ primeCheckXBlockShape := by rw [← hloc]; exact hmem
  unfold primeCheckXBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- primeCheckY's only write locations: `yA'`, `yB'`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_primeCheckY (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.primeCheckY)
    (hewop : ew.op = .wt) :
    ew.loc = Loc.yA' ∨ ew.loc = Loc.yB' := by
  obtain ⟨cnts, htrace⟩ := hshapes.primeCheckY
  have hshape : ∀ x ∈ primeCheckYBlockWord I cnts,
      (x.1.loc, x.1.op) ∈ primeCheckYBlockShape := by
    intro x hx
    unfold primeCheckYBlockWord at hx
    obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp hx
    have hshapeeq := primeCheckYBlockElems_shape I c
    rw [← hshapeeq]
    exact List.mem_map_of_mem hc
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ primeCheckYBlockShape := by rw [← hloc]; exact hmem
  unfold primeCheckYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- checkX's only write locations: `xA`, `xB`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_checkX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.checkX) (hewop : ew.op = .wt) :
    ew.loc = Loc.xA ∨ ew.loc = Loc.xB := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.checkX
  have hshape : ∀ x ∈ checkXBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ checkXBlockShape := by
    intro x hx
    unfold checkXBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := checkXBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ checkXBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [checkXBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := checkXBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ checkXBlockShape := by rw [← hloc]; exact hmem
  unfold checkXBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- checkY's only write locations: `yA`, `yB`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_checkY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.checkY) (hewop : ew.op = .wt) :
    ew.loc = Loc.yA ∨ ew.loc = Loc.yB := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.checkY
  have hshape : ∀ x ∈ checkYBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ checkYBlockShape := by
    intro x hx
    unfold checkYBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := checkYBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ checkYBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [checkYBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := checkYBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ checkYBlockShape := by rw [← hloc]; exact hmem
  unfold checkYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- guessAY's write locations: `yA`, `ellAyx`, `zAy'y`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_guessAY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.guessAY) (hewop : ew.op = .wt) :
    ew.loc = Loc.yA ∨ ew.loc = Loc.ellAyx ∨ ew.loc = Loc.zAy'y := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.guessAY
  have hshape : ∀ x ∈ guessAYBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ guessAYBlockShape := by
    intro x hx
    unfold guessAYBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := guessAYBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ guessAYBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [guessAYBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := guessAYBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ guessAYBlockShape := by rw [← hloc]; exact hmem
  unfold guessAYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · exact Or.inr (Or.inr (congrArg Prod.fst h))
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- guessBY's write locations: `yB`, `ellByx`, `zBy'y`. See `traceMo_writes_primeAX`. -/
theorem traceMo_writes_guessBY (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.guessBY) (hewop : ew.op = .wt) :
    ew.loc = Loc.yB ∨ ew.loc = Loc.ellByx ∨ ew.loc = Loc.zBy'y := by
  obtain ⟨v0, kws, htrace⟩ := hshapes.guessBY
  have hshape : ∀ x ∈ guessBYBlockWord I v0 kws, (x.1.loc, x.1.op) ∈ guessBYBlockShape := by
    intro x hx
    unfold guessBYBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxrest
    · have hshapeeq := guessBYBlock0Elems_shape I v0
      have hmem0 : (x.1.loc, x.1.op) ∈ guessBYBlock0Shape := by
        rw [← hshapeeq]; exact List.mem_map_of_mem hx0
      rw [guessBYBlockShape_prefix] at hmem0
      exact List.mem_of_mem_take hmem0
    · obtain ⟨kw, -, hkw⟩ := List.mem_flatMap.mp hxrest
      have hshapeeq := guessBYBlockRestElems_shape I kw
      rw [← hshapeeq]
      exact List.mem_map_of_mem hkw
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈ guessBYBlockShape := by rw [← hloc]; exact hmem
  unfold guessBYBlockShape at hmem2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · exact Or.inr (Or.inr (congrArg Prod.fst h))
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- `guessAX`'s write locations: `xA`, `zAx'x`, `zAxy`. -/
theorem traceMo_writes_guessAX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.guessAX) (hewop : ew.op = .wt) :
    ew.loc = Loc.xA ∨ ew.loc = Loc.zAx'x ∨ ew.loc = Loc.zAxy := by
  obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
    htrace⟩ := hshapes.guessAX
  have hshape : ∀ x ∈ guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest,
      (x.1.loc, x.1.op) ∈
        ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
          (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)) := by
    have hinnerMem : ∀ v : Val I × Val I × Val I, ∀ x ∈ guessAXInnerBlockElems I v,
        (x.1.loc, x.1.op) ∈
          ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
            (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)) := by
      intro v x hx
      have hshapeeq := guessAXInnerBlockElems_shape I v
      obtain ⟨y, hy⟩ : ∃ y : Loc × OpType, (x.1.loc, x.1.op) = y := ⟨_, rfl⟩
      have hx' : y ∈ guessAXInnerBlockShape := by
        rw [← hy, ← hshapeeq]; exact List.mem_map_of_mem hx
      unfold guessAXInnerBlockShape at hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      have hgoal : y ∈
          ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
            (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)) := by
        rcases hx' with h | h | h <;> subst h <;> decide
      exact hy ▸ hgoal
    intro x hx
    unfold guessAXBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxouter
    · rcases List.mem_append.mp hx0 with hx0' | hxellAyx
      · rcases List.mem_append.mp hx0' with hxlead | hxinner
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxlead
          rcases hxlead with h | h | h <;> subst h <;>
            simp only [EventLabel.loc, EventLabel.op]
          · exact (by decide : (Loc.zAxy, OpType.wt) ∈
              ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
                (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
          · exact (by decide : (Loc.xA, OpType.wt) ∈
              ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
                (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
          · exact (by decide : (Loc.zAx'x, OpType.wt) ∈
              ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
                (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
        · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hxinner
          exact hinnerMem v x hv
      · simp only [List.mem_singleton] at hxellAyx
        subst hxellAyx
        simp only [EventLabel.loc, EventLabel.op]
        exact (by decide : (Loc.ellAyx, OpType.rd) ∈
          ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
            (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
    · obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp hxouter
      unfold guessAXOuterBlockElems at hp
      rcases List.mem_cons.mp hp with hp1 | hp2
      · subst hp1
        simp only [EventLabel.loc, EventLabel.op]
        exact (by decide : (Loc.zAxy, OpType.wt) ∈
          ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
            (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
      · rcases List.mem_append.mp hp2 with hp2' | hp3
        · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hp2'
          exact hinnerMem v x hv
        · simp only [List.mem_singleton] at hp3
          subst hp3
          simp only [EventLabel.loc, EventLabel.op]
          exact (by decide : (Loc.ellAyx, OpType.rd) ∈
            ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
              (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)))
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈
      ([(Loc.xA, OpType.wt), (Loc.zAx'x, OpType.wt), (Loc.zAxx', OpType.rd),
        (Loc.zAxy, OpType.wt), (Loc.ellAyx, OpType.rd)] : List (Loc × OpType)) := by
    rw [← hloc]; exact hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inr (Or.inr (congrArg Prod.fst h))
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- guessBX's write locations: `xB`, `zBx'x`, `zBxy`. See `traceMo_writes_guessAX`. -/
theorem traceMo_writes_guessBX (I : PCPInstance) {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (hshapes : TraceShapes I trace)
    {ew : Event (domainOf I)} (hew : ew ∈ traceEventsOf trace Tid.guessBX) (hewop : ew.op = .wt) :
    ew.loc = Loc.xB ∨ ew.loc = Loc.zBx'x ∨ ew.loc = Loc.zBxy := by
  obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
    htrace⟩ := hshapes.guessBX
  have hshape : ∀ x ∈ guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest,
      (x.1.loc, x.1.op) ∈
        ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
          (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)) := by
    have hinnerMem : ∀ v : Val I × Val I × Val I, ∀ x ∈ guessBXInnerBlockElems I v,
        (x.1.loc, x.1.op) ∈
          ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
            (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)) := by
      intro v x hx
      have hshapeeq := guessBXInnerBlockElems_shape I v
      obtain ⟨y, hy⟩ : ∃ y : Loc × OpType, (x.1.loc, x.1.op) = y := ⟨_, rfl⟩
      have hx' : y ∈ guessBXInnerBlockShape := by
        rw [← hy, ← hshapeeq]; exact List.mem_map_of_mem hx
      unfold guessBXInnerBlockShape at hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      have hgoal : y ∈
          ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
            (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)) := by
        rcases hx' with h | h | h <;> subst h <;> decide
      exact hy ▸ hgoal
    intro x hx
    unfold guessBXBlockWord at hx
    rcases List.mem_append.mp hx with hx0 | hxouter
    · rcases List.mem_append.mp hx0 with hx0' | hxellAyx
      · rcases List.mem_append.mp hx0' with hxlead | hxinner
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxlead
          rcases hxlead with h | h | h <;> subst h <;>
            simp only [EventLabel.loc, EventLabel.op]
          · exact (by decide : (Loc.zBxy, OpType.wt) ∈
              ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
                (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
          · exact (by decide : (Loc.xB, OpType.wt) ∈
              ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
                (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
          · exact (by decide : (Loc.zBx'x, OpType.wt) ∈
              ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
                (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
        · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hxinner
          exact hinnerMem v x hv
      · simp only [List.mem_singleton] at hxellAyx
        subst hxellAyx
        simp only [EventLabel.loc, EventLabel.op]
        exact (by decide : (Loc.ellByx, OpType.rd) ∈
          ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
            (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
    · obtain ⟨p, -, hp⟩ := List.mem_flatMap.mp hxouter
      unfold guessBXOuterBlockElems at hp
      rcases List.mem_cons.mp hp with hp1 | hp2
      · subst hp1
        simp only [EventLabel.loc, EventLabel.op]
        exact (by decide : (Loc.zBxy, OpType.wt) ∈
          ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
            (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
      · rcases List.mem_append.mp hp2 with hp2' | hp3
        · obtain ⟨v, -, hv⟩ := List.mem_flatMap.mp hp2'
          exact hinnerMem v x hv
        · simp only [List.mem_singleton] at hp3
          subst hp3
          simp only [EventLabel.loc, EventLabel.op]
          exact (by decide : (Loc.ellByx, OpType.rd) ∈
            ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
              (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)))
  have hmem := traceEventsOf_locOp_mem_of_forall htrace hshape hew
  rw [hewop] at hmem
  obtain ⟨x, hloc⟩ : ∃ x : Loc, ew.loc = x := ⟨ew.loc, rfl⟩
  have hmem2 : (x, OpType.wt) ∈
      ([(Loc.xB, OpType.wt), (Loc.zBx'x, OpType.wt), (Loc.zBxx', OpType.rd),
        (Loc.zBxy, OpType.wt), (Loc.ellByx, OpType.rd)] : List (Loc × OpType)) := by
    rw [← hloc]; exact hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem2
  rw [hloc]
  rcases hmem2 with h | h | h | h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (Or.inl (congrArg Prod.fst h))
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)
  · exact Or.inr (Or.inr (congrArg Prod.fst h))
  · have h2 : OpType.wt = OpType.rd := congrArg Prod.snd h
    exact absurd h2 (by decide)

/-- The `writerTids` memberships used by `traceMo_writers_confined`. (Stated
without parameters so that `decide` applies.) -/
theorem writerTids_confined_facts :
    Tid.primeAX ∈ writerTids Loc.xA' ∧ Tid.primeAX ∈ writerTids Loc.zAxx' ∧
    Tid.primeBX ∈ writerTids Loc.xB' ∧ Tid.primeBX ∈ writerTids Loc.zBxx' ∧
    Tid.primeAY ∈ writerTids Loc.yA' ∧ Tid.primeAY ∈ writerTids Loc.zAyy' ∧
    Tid.primeBY ∈ writerTids Loc.yB' ∧ Tid.primeBY ∈ writerTids Loc.zByy' ∧
    Tid.primeCheckX ∈ writerTids Loc.xA' ∧ Tid.primeCheckX ∈ writerTids Loc.xB' ∧
    Tid.primeCheckY ∈ writerTids Loc.yA' ∧ Tid.primeCheckY ∈ writerTids Loc.yB' ∧
    Tid.checkX ∈ writerTids Loc.xA ∧ Tid.checkX ∈ writerTids Loc.xB ∧
    Tid.checkY ∈ writerTids Loc.yA ∧ Tid.checkY ∈ writerTids Loc.yB ∧
    Tid.guessAY ∈ writerTids Loc.yA ∧ Tid.guessAY ∈ writerTids Loc.ellAyx ∧
      Tid.guessAY ∈ writerTids Loc.zAy'y ∧
    Tid.guessBY ∈ writerTids Loc.yB ∧ Tid.guessBY ∈ writerTids Loc.ellByx ∧
      Tid.guessBY ∈ writerTids Loc.zBy'y ∧
    Tid.guessAX ∈ writerTids Loc.xA ∧ Tid.guessAX ∈ writerTids Loc.zAx'x ∧
      Tid.guessAX ∈ writerTids Loc.zAxy ∧
    Tid.guessBX ∈ writerTids Loc.xB ∧ Tid.guessBX ∈ writerTids Loc.zBx'x ∧
      Tid.guessBX ∈ writerTids Loc.zBxy := by
  decide

/-- Every write event of `trace` has its thread among its location's
`writerTids`. -/
theorem traceMo_writers_confined (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (hshapes : TraceShapes I trace) :
    ∀ e ∈ traceEvents trace, e.IsWriting → e.tid ∈ writerTids e.loc := by
  obtain ⟨hpAXa, hpAXz, hpBXa, hpBXz, hpAYa, hpAYz, hpBYa, hpBYz,
    hpVXa, hpVXb, hpVYa, hpVYb, hVXa, hVXb, hVYa, hVYb,
    hGAYa, hGAYe, hGAYz, hGBYa, hGBYe, hGBYz,
    hGAXa, hGAXz1, hGAXz2, hGBXa, hGBXz1, hGBXz2⟩ := writerTids_confined_facts
  intro e he hwriting
  match het : e.tid with
  | Tid.primeAX =>
      rcases traceMo_writes_primeAX I hshapes (mem_traceEvents_of_tid he het) hwriting with h | h
      · rw [h]; exact hpAXa
      · rw [h]; exact hpAXz
  | Tid.primeBX =>
      rcases traceMo_writes_primeBX I hshapes (mem_traceEvents_of_tid he het) hwriting with h | h
      · rw [h]; exact hpBXa
      · rw [h]; exact hpBXz
  | Tid.primeAY =>
      rcases traceMo_writes_primeAY I hshapes (mem_traceEvents_of_tid he het) hwriting with h | h
      · rw [h]; exact hpAYa
      · rw [h]; exact hpAYz
  | Tid.primeBY =>
      rcases traceMo_writes_primeBY I hshapes (mem_traceEvents_of_tid he het) hwriting with h | h
      · rw [h]; exact hpBYa
      · rw [h]; exact hpBYz
  | Tid.primeCheckX =>
      rcases traceMo_writes_primeCheckX I hshapes (mem_traceEvents_of_tid he het) hwriting
        with h | h
      · rw [h]; exact hpVXa
      · rw [h]; exact hpVXb
  | Tid.primeCheckY =>
      rcases traceMo_writes_primeCheckY I hshapes (mem_traceEvents_of_tid he het) hwriting
        with h | h
      · rw [h]; exact hpVYa
      · rw [h]; exact hpVYb
  | Tid.checkX =>
      rcases traceMo_writes_checkX I hshapes (mem_traceEvents_of_tid he het) hwriting with h | h
      · rw [h]; exact hVXa
      · rw [h]; exact hVXb
  | Tid.checkY =>
      rcases traceMo_writes_checkY I hshapes (mem_traceEvents_of_tid he het) hwriting with h | h
      · rw [h]; exact hVYa
      · rw [h]; exact hVYb
  | Tid.guessAY =>
      rcases traceMo_writes_guessAY I hshapes (mem_traceEvents_of_tid he het) hwriting
        with h | h | h
      · rw [h]; exact hGAYa
      · rw [h]; exact hGAYe
      · rw [h]; exact hGAYz
  | Tid.guessBY =>
      rcases traceMo_writes_guessBY I hshapes (mem_traceEvents_of_tid he het) hwriting
        with h | h | h
      · rw [h]; exact hGBYa
      · rw [h]; exact hGBYe
      · rw [h]; exact hGBYz
  | Tid.guessAX =>
      rcases traceMo_writes_guessAX I hshapes (mem_traceEvents_of_tid he het) hwriting
        with h | h | h
      · rw [h]; exact hGAXa
      · rw [h]; exact hGAXz1
      · rw [h]; exact hGAXz2
  | Tid.guessBX =>
      rcases traceMo_writes_guessBX I hshapes (mem_traceEvents_of_tid he het) hwriting
        with h | h | h
      · rw [h]; exact hGBXa
      · rw [h]; exact hGBXz1
      · rw [h]; exact hGBXz2

/-! ## `G`'s `rf_unique` -/

/-- `G`'s `rf_unique` for `traceRf`: a read has at most one incoming
`rf`-edge. `traceRf`'s match depends only on `er.tid`/`er.loc`, so two edges
into `er` fall in the same branch, where both writers are the same-index
write (`rawNthWrite_unique_of_rawNthRead`). -/
theorem traceRf_unique {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    {ew1 ew2 er : Event (domainOf I)}
    (h1 : traceRf I trace ew1 er) (h2 : traceRf I trace ew2 er) : ew1 = ew2 := by
  unfold traceRf at h1 h2
  match her : er.tid with
  | Tid.guessAX =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.guessAY =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.guessBX =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.guessBY =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.primeAX =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.primeAY =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.primeBX =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.primeBY =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
  | Tid.checkX =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.xB =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.xB' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.checkY =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.yB =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.yB' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.primeCheckX =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.xB =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.yA =>
          rw [hel] at h1
          simp at h1
      | Loc.yB =>
          rw [hel] at h1
          simp at h1
      | Loc.xA' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.xB' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.yA' =>
          rw [hel] at h1
          simp at h1
      | Loc.yB' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1
  | Tid.primeCheckY =>
      rw [her] at h1 h2
      match hel : er.loc with
      | Loc.xA =>
          rw [hel] at h1
          simp at h1
      | Loc.xB =>
          rw [hel] at h1
          simp at h1
      | Loc.yA =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.yB =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.xA' =>
          rw [hel] at h1
          simp at h1
      | Loc.xB' =>
          rw [hel] at h1
          simp at h1
      | Loc.yA' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.yB' =>
          rw [hel] at h1 h2
          exact rawNthWrite_unique_of_rawNthRead h1 h2
      | Loc.zAxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAyy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxx' =>
          rw [hel] at h1
          simp at h1
      | Loc.zByy' =>
          rw [hel] at h1
          simp at h1
      | Loc.zAxy =>
          rw [hel] at h1
          simp at h1
      | Loc.zBxy =>
          rw [hel] at h1
          simp at h1
      | Loc.ellAyx =>
          rw [hel] at h1
          simp at h1
      | Loc.ellByx =>
          rw [hel] at h1
          simp at h1
      | Loc.zAx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zAy'y =>
          rw [hel] at h1
          simp at h1
      | Loc.zBx'x =>
          rw [hel] at h1
          simp at h1
      | Loc.zBy'y =>
          rw [hel] at h1
          simp at h1

/-! ## `rf_matches`: `guessAX`/`zAxx'` (Eq. (15))

The `guessAX` side of the branch whose `primeAX` side is
`rawNthWrite_primeAX_zAxx'_eq` (`Completeness/Construction.lean`). -/

/-- The `zAxx'`-read match, as a predicate on `Loc`/`OpType` alone. -/
def zAxx'ReadPredCore (loc : Loc) (op : OpType) : Bool :=
  match loc, op with | Loc.zAxx', OpType.rd => true | _, _ => false

/-- `zAxx'ReadPredCore`, lifted to `guessAX`'s `ThreadLabel`. (One named
predicate, so that all facts below are stated against the same term.) -/
def guessAXZAxReadPred (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessAX) : Bool :=
  zAxx'ReadPredCore lab.1.loc lab.1.op

/-- No bridge location matches `zAxx'ReadPredCore`. -/
theorem zAxx'ReadPredCore_bridge : ∀ y : Loc, ∀ z : OpType, y ∈ BridgeLoc →
    zAxx'ReadPredCore y z = false := by
  intro y z hb0
  cases y <;> cases z <;> revert hb0 <;> decide

/-- `zAxx'ReadPredCore_bridge`, lifted to `guessAXZAxReadPred`. -/
theorem bridgeloc_check (I : PCPInstance) :
    ∀ (lab : ThreadLabel (domainOf I) Tid.guessAX), lab.1.loc ∈ BridgeLoc →
    guessAXZAxReadPred I lab = false := by
  intro lab hloc
  unfold guessAXZAxReadPred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  rw [hy] at hloc
  exact zAxx'ReadPredCore_bridge y z hloc

/-- `guessAXBlockWord`'s `zAxx'`-reads: those of `inner0Rest` (position `2`
of each inner call) followed by those of `outerRest` (none of the head's
`zAxy`, `xA`, `zAx'x`, nor the `ellAyx` reads, matches). -/
theorem guessAXBlockWord_zAxx'_filter_eq (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (guessAXZAxReadPred I)
      = inner0Rest.map (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX)) ++
        outerRest.flatMap (fun p => p.2.map (fun a =>
          (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX))) := by
  have hinner := guessAXInnerBlockElems_filter I
    (guessAXZAxReadPred I) 2
    (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.xA, OpType.wt with
          | Loc.zAxx', OpType.rd => true | _, _ => false) = false)
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zAx'x, OpType.wt with
          | Loc.zAxx', OpType.rd => true | _, _ => false) = false))
  have houter := fun (b : Val I × Val I) (vs : List (Val I × Val I × Val I)) =>
    guessAXOuterBlockElems_filter I b vs
    (guessAXZAxReadPred I) 2
    (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b0 hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.xA, OpType.wt with
          | Loc.zAxx', OpType.rd => true | _, _ => false) = false)
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zAx'x, OpType.wt with
          | Loc.zAxx', OpType.rd => true | _, _ => false) = false))
    (by
      intro b0 hb0
      exact bridgeloc_check I b0 hb0)
  unfold guessAXBlockWord
  simp only [List.filter_append, hinner]
  have hcore : ∀ y : Loc, ∀ z : OpType, ¬ (y = Loc.zAxx' ∧ z = OpType.rd) →
      zAxx'ReadPredCore y z = false := by
    intro y z hne
    cases y <;> cases z <;> first | rfl | (exfalso; exact hne ⟨rfl, rfl⟩)
  have hz1 : guessAXZAxReadPred I (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    hcore Loc.zAxy OpType.wt (by decide)
  have hz2 : guessAXZAxReadPred I (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    hcore Loc.xA OpType.wt (by decide)
  have hz3 : guessAXZAxReadPred I (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    hcore Loc.zAx'x OpType.wt (by decide)
  have hz4 : guessAXZAxReadPred I (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    hcore Loc.ellAyx OpType.rd (by decide)
  simp only [List.filter_cons, List.filter_nil, hz1, hz2, hz3, hz4, List.nil_append,
    List.append_nil, if_false, Bool.false_eq_true]
  rw [list_filter_flatMap_distrib]
  congr 1
  apply List.flatMap_congr
  intro p _
  exact houter p.1 p.2

theorem zAxx'ReadPredCore_iff (y : Loc) (z : OpType) :
    zAxx'ReadPredCore y z = true ↔ (y = Loc.zAxx' ∧ z = OpType.rd) := by
  cases y <;> cases z <;> decide

theorem guessAXZAxReadPred_iff (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessAX) :
    guessAXZAxReadPred I lab = true ↔ (lab.1.loc = Loc.zAxx' ∧ lab.1.op = OpType.rd) := by
  unfold guessAXZAxReadPred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  exact zAxx'ReadPredCore_iff y z

theorem rawNthRead_guessAX_zAxx'_eq (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (ks : List ℕ) (hlenOuter : outerRest.length = ks.length + 1)
    (hpreOuter : ∀ m, m < ks.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      ks[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[ks.length]? = some (b, vs) ∧ vs.length = 1)
    {i : ℕ} {er : Event (domainOf I)}
    (h : rawNthRead trace Tid.guessAX Loc.zAxx' i = some er) :
    (i < inner0Rest.length ∧ ∃ e, inner0Rest[i]? = some e ∧ er.val = e.2.2) ∨
    (∃ m, m < ks.length + 1 ∧ ∃ b vs n e, outerRest[m]? = some (b, vs) ∧ n < vs.length ∧
      vs[n]? = some e ∧ i = inner0Rest.length + ksPrefix ks m + n ∧ er.val = e.2.2) := by
  set ev : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX :=
    (fun a => (⟨EventLabel.rd Tid.guessAX Loc.zAxx' a.2.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)) with hev
  have hpredL := guessAXZAxReadPred_iff I
  have hlen_eq := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessAX)
    (x := Loc.zAxx') (op := OpType.rd) (predL := guessAXZAxReadPred I) htrace hpredL
  have hfilt : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter (guessAXZAxReadPred I)
      = inner0Rest.map ev ++ outerRest.flatMap (fun p => p.2.map ev) := by
    rw [hev]; exact guessAXBlockWord_zAxx'_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt0 : i < (rawOpEvents trace Tid.guessAX Loc.zAxx' OpType.rd).length :=
    (List.getElem?_eq_some_iff.mp h).1
  rw [hlen_eq, hfilt, List.length_append, List.length_map] at hilt0
  rcases Nat.lt_or_ge i inner0Rest.length with hcase | hcase
  · left
    refine ⟨hcase, ?_⟩
    obtain ⟨e, he⟩ : ∃ e, inner0Rest[i]? = some e :=
      ⟨inner0Rest[i]'hcase, List.getElem?_eq_getElem hcase⟩
    have hgetf :
        ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
          (guessAXZAxReadPred I))[i]? = some (ev e) := by
      rw [hfilt, List.getElem?_append_left (by simpa using hcase), List.getElem?_map, he]
      rfl
    obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessAXZAxReadPred I) i
      (ev e) hgetf
    have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessAX)
      (l := guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
    have hraw : rawNthEvent trace Tid.guessAX Loc.zAxx' OpType.rd i = some er := h
    rw [hraw] at hconn
    refine ⟨e, he, ?_⟩
    injection hconn with hconn
    rw [hconn]
    rfl
  · right
    have hlen_outer_flat :
        (outerRest.flatMap (fun p => p.2.map ev)).length
          = ksPrefix ks ks.length + 1 := by
      have h1 : (outerRest.flatMap (fun p => p.2.map ev)).length
          = (outerRest.map (fun p => (p.2.map (ev)).length)).sum := by
        rw [List.length_flatMap]
      have h2 : (outerRest.map (fun p => (p.2.map (ev)).length)).sum
          = (outerRest.map (fun p => p.2.length)).sum := by
        congr 1
        apply List.map_congr_left
        intro p _
        exact List.length_map ..
      have h3 : (outerRest.map (fun p => p.2.length)).sum = (ks.map (· + 1)).sum + 1 :=
        sum_snd_length_of_forall_getElem outerRest ks hlenOuter hpreOuter hlastOuter
      rw [h1, h2, h3, ksPrefix_eq_sum]
    have hj' : i - inner0Rest.length < ksPrefix ks ks.length + 1 := by
      rw [← hlen_outer_flat]; omega
    obtain ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, hjeq, hgetflat⟩ :=
      ksPrefix_flatMap_map_getElem outerRest ks (ev)
        hlenOuter hpreOuter hlastOuter (i - inner0Rest.length) hj'
    have hgetf :
        ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
          (guessAXZAxReadPred I))[i]? = some (ev b) := by
      rw [hfilt, List.getElem?_append_right (by rw [List.length_map]; omega), List.length_map]
      exact hgetflat
    obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessAXZAxReadPred I) i (ev b) hgetf
    have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessAX)
      (l := guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
    have hraw : rawNthEvent trace Tid.guessAX Loc.zAxx' OpType.rd i = some er := h
    rw [hraw] at hconn
    refine ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, by omega, ?_⟩
    injection hconn with hconn
    rw [hconn]
    rfl

theorem traceRf_matches_guessAX_zAxx' (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (vals : List (Val I)) (htracePAX : trace Tid.primeAX = primeAXBlockWord I vals)
    (cnt0P : Fin 4) (hcnt0P : cnt0P = 0)
    (hvalsVal : ∀ i, i < vals.length →
      vals[i]? = some (Val.cnt (⟨(cnt0P.val + i + 1) % 4, by omega⟩ : Fin 4)))
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (K0 : ℕ) (hlen1 : inner0Rest.length = K0)
    (js : List (Fin I.n)) (hlen2 : outerRest.length = js.length + 1)
    (houterC : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastC : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (cnt0G : Fin 4) (hcnt0G : cnt0G = 0)
    (hval1 : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨((cnt0G + 1).val + n) % 4, by omega⟩ : Fin 4))
    (hval2 : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨((cnt0G + 1).val + K0 + ksPrefix (guessAXJsToKs I js) m + n) % 4,
          by omega⟩ : Fin 4))
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.primeAX Loc.zAxx' i = some ew ∧
      rawNthRead trace Tid.guessAX Loc.zAxx' i = some er) :
    ew.val = er.val := by
  subst hcnt0P
  subst hcnt0G
  obtain ⟨i, hew, her⟩ := h
  obtain ⟨v, hv, hewval⟩ := rawNthWrite_primeAX_zAxx'_eq I vals htracePAX hew
  have hvlen : i < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hvform := hvalsVal i hvlen
  rw [hvform] at hv
  injection hv with hv
  have hkslen : (guessAXJsToKs I js).length = js.length := by unfold guessAXJsToKs; simp
  have hlen2' : outerRest.length = (guessAXJsToKs I js).length + 1 := by rw [hkslen]; exact hlen2
  have houterC' : ∀ m, m < (guessAXJsToKs I js).length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1 := by
    rw [hkslen]; exact houterC
  have houterLastC' :
      ∃ b vs, outerRest[(guessAXJsToKs I js).length]? = some (b, vs) ∧ vs.length = 1 := by
    rw [hkslen]; exact houterLastC
  rcases rawNthRead_guessAX_zAxx'_eq I v1 v2 vB0 inner0Rest outerRest htraceGAX
      (guessAXJsToKs I js) hlen2' houterC' houterLastC' her with
    ⟨hilt, e, he, herval⟩ | ⟨m, hm, b, vs, n, e, hbv, hnlt, hvsn, hieq, herval⟩
  · obtain ⟨e', he', he22'⟩ := hval1 i (by rw [hlen1] at hilt ⊢; omega)
    rw [he] at he'
    injection he' with he'
    subst he'
    rw [hewval, herval, he22', ← hv]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    omega
  · have hm' : m < js.length + 1 := by rw [hkslen] at hm; omega
    obtain ⟨b', vs', hbv', hval'⟩ := hval2 m hm'
    rw [hbv] at hbv'
    simp only [Option.some.injEq, Prod.mk.injEq] at hbv'
    obtain ⟨hbeq, hvseq⟩ := hbv'
    subst hbeq
    subst hvseq
    obtain ⟨e', he', he22'⟩ := hval' n hnlt
    rw [hvsn] at he'
    injection he' with he'
    subst he'
    rw [hewval, herval, he22', ← hv]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    rw [hlen1] at hieq
    omega

/-- `traceRf_matches_guessAX_zAxx'` for the general construction:
`hvalsVal`/`hval1`/`hval2` come from `primeAX_general_run`/
`guessAX_general_run`. -/
theorem traceRf_matches_guessAX_zAxx'_general (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (cs : List I.Γ)
    (vals : List (Val I)) (htracePAX : trace Tid.primeAX = primeAXBlockWord I vals)
    (_ : vals.length = cs.length + 1)
    (hvalsVal : ∀ i, i < vals.length → vals[i]? = some (Val.cnt (⟨(i + 1) % 4, by omega⟩ : Fin 4)))
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (K0 : ℕ) (hlen1 : inner0Rest.length = K0)
    (js : List (Fin I.n)) (hlen2 : outerRest.length = js.length + 1)
    (houterC : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastC : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (hval1raw : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4) ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4))
    (hval2raw : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix (guessAXJsToKs I js) m + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix (guessAXJsToKs I js) m + n + 1) % 4, by omega⟩ : Fin 4))
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.primeAX Loc.zAxx' i = some ew ∧
      rawNthRead trace Tid.guessAX Loc.zAxx' i = some er) :
    ew.val = er.val := by
  have hvalsVal' : ∀ i, i < vals.length →
      vals[i]? = some (Val.cnt (⟨((0 : Fin 4).val + i + 1) % 4, by omega⟩ : Fin 4)) := by
    intro i hi
    rw [hvalsVal i hi]; congr 2; apply Fin.ext; simp
  have hval1 : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨((0 + 1 : Fin 4).val + n) % 4, by omega⟩ : Fin 4) := by
    intro n hn
    obtain ⟨e, he, he22, _⟩ := hval1raw n hn
    refine ⟨e, he, ?_⟩
    rw [he22]; congr 2
  have hval2 : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨((0 + 1 : Fin 4).val + K0 + ksPrefix (guessAXJsToKs I js) m + n) % 4,
          by omega⟩ : Fin 4) := by
    intro m hm
    obtain ⟨b, vs, hbv, hval2raw'⟩ := hval2raw m hm
    refine ⟨b, vs, hbv, ?_⟩
    intro n hn
    obtain ⟨e, he, he22, _⟩ := hval2raw' n hn
    refine ⟨e, he, ?_⟩
    rw [he22]; congr 2
  exact traceRf_matches_guessAX_zAxx' I vals htracePAX 0 rfl hvalsVal'
    v1 v2 vB0 inner0Rest outerRest htraceGAX K0 hlen1 js hlen2 houterC houterLastC 0 rfl
    hval1 hval2 h

/-- `rf_total` for the `guessAX`/`zAxx'` branch (Eq. (15)):
every read `er` at `(guessAX, zAxx')` has a matching `primeAX` write. The
count of `guessAX`'s `zAxx'`-reads (`guessAXBlockWord_zAxx'_filter_eq`) is
bounded by the count of `primeAX`'s `zAxx'`-writes
(`primeAXBlockWord_zAxx'_length`). -/
theorem traceRf_total_guessAX_zAxx' (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)} (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceG : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (vals : List (Val I)) (htraceP : trace Tid.primeAX = primeAXBlockWord I vals)
    (hcount : inner0Rest.length + (outerRest.map (fun p => p.2.length)).sum ≤ vals.length)
    {er : Event (domainOf I)} (her_tid : er.tid = Tid.guessAX) (her_loc : er.loc = Loc.zAxx')
    (her : er ∈ traceEvents trace) (herop : er.op = .rd) :
    ∃ ew, traceRf I trace ew er := by
  have hmemT : er ∈ traceEventsOf trace Tid.guessAX := mem_traceEvents_of_tid her her_tid
  have hmemOp : er ∈ rawOpEvents trace Tid.guessAX Loc.zAxx' OpType.rd := by
    unfold rawOpEvents
    exact List.mem_filter.mpr ⟨hmemT, by rw [her_loc, herop]; rfl⟩
  set i := (rawOpEvents trace Tid.guessAX Loc.zAxx' OpType.rd).idxOf er with hidef
  have hread : rawNthRead trace Tid.guessAX Loc.zAxx' i = some er := rawNthEvent_of_mem hmemOp
  have hilt_reader : i < (rawOpEvents trace Tid.guessAX Loc.zAxx' OpType.rd).length :=
    List.idxOf_lt_length_iff.mpr hmemOp
  have hpredL := guessAXZAxReadPred_iff I
  have hlen_eq := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessAX)
    (x := Loc.zAxx') (op := OpType.rd) (predL := guessAXZAxReadPred I) htraceG hpredL
  have hfilt := guessAXBlockWord_zAxx'_filter_eq I v1 v2 vB0 inner0Rest outerRest
  rw [hlen_eq, hfilt, List.length_append, List.length_flatMap] at hilt_reader
  simp only [List.length_map] at hilt_reader
  have hpredW : ∀ lab : ThreadLabel (domainOf I) Tid.primeAX,
      (match lab.1.loc, lab.1.op with | Loc.zAxx', OpType.wt => true | _, _ => false) = true ↔
        (lab.1.loc = Loc.zAxx' ∧ lab.1.op = OpType.wt) := by
    intro lab
    obtain ⟨x, hx⟩ : ∃ x : Loc, lab.1.loc = x := ⟨lab.1.loc, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : OpType, lab.1.op = y := ⟨lab.1.op, rfl⟩
    rw [hx, hy]
    cases x <;> cases y <;> simp; rfl
  have hlenW := rawOpEvents_length_eq (D := domainOf I) (t := Tid.primeAX)
    (x := Loc.zAxx') (op := OpType.wt) htraceP hpredW
  have hlenW' : (rawOpEvents trace Tid.primeAX Loc.zAxx' OpType.wt).length = vals.length :=
    hlenW.trans (primeAXBlockWord_zAxx'_length I vals)
  have hilt_writer : i < (rawOpEvents trace Tid.primeAX Loc.zAxx' OpType.wt).length := by
    rw [hlenW']
    omega
  obtain ⟨ew, hew⟩ := rawNthEvent_exists_of_lt_length hilt_writer
  refine ⟨ew, ?_⟩
  unfold traceRf
  rw [her_tid, her_loc]
  exact ⟨i, hew, hread⟩

/-! ## `rf_matches`: `guessAX`/`primeAX` `zAx'x` (Eq. (15)) -/

def zAx'xWritePredCore (loc : Loc) (op : OpType) : Bool :=
  match loc, op with | Loc.zAx'x, OpType.wt => true | _, _ => false

theorem zAx'xWritePredCore_iff (y : Loc) (z : OpType) :
    zAx'xWritePredCore y z = true ↔ (y = Loc.zAx'x ∧ z = OpType.wt) := by
  cases y <;> cases z <;> decide

theorem zAx'xWritePredCore_bridge : ∀ y : Loc, ∀ z : OpType, y ∈ BridgeLoc →
    zAx'xWritePredCore y z = false := by
  intro y z hb0
  cases y <;> cases z <;> revert hb0 <;> decide

/-- `zAx'xWritePredCore`, lifted to `guessAX`'s `ThreadLabel`. -/
def guessAXZAxprimeWritePred (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessAX) :
    Bool :=
  zAx'xWritePredCore lab.1.loc lab.1.op

theorem guessAXZAxprimeWritePred_iff (I : PCPInstance)
    (lab : ThreadLabel (domainOf I) Tid.guessAX) :
    guessAXZAxprimeWritePred I lab = true ↔ (lab.1.loc = Loc.zAx'x ∧ lab.1.op = OpType.wt) := by
  unfold guessAXZAxprimeWritePred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  exact zAx'xWritePredCore_iff y z

theorem guessAXZAxprimeWritePred_bridge (I : PCPInstance) :
    ∀ (lab : ThreadLabel (domainOf I) Tid.guessAX), lab.1.loc ∈ BridgeLoc →
    guessAXZAxprimeWritePred I lab = false := by
  intro lab hloc
  unfold guessAXZAxprimeWritePred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  rw [hy] at hloc
  exact zAx'xWritePredCore_bridge y z hloc

/-- `guessAXBlockWord`'s `zAx'x`-writes: the head's `v2` (written by the
thread's first call), then those of `inner0Rest` (position `1`), then those of
`outerRest`. -/
theorem guessAXBlockWord_zAx'x_filter_eq (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter (guessAXZAxprimeWritePred I)
      = [(⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] ++
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX)) ++
        outerRest.flatMap (fun p => p.2.map (fun a =>
          (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX))) := by
  have hinner := guessAXInnerBlockElems_filter I
    (guessAXZAxprimeWritePred I) 1
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq02 : q = 0 ∨ q = 2 := by omega
      rcases hq02 with rfl | rfl
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.xA, OpType.wt with
          | Loc.zAx'x, OpType.wt => true | _, _ => false) = false)
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zAxx', OpType.rd with
          | Loc.zAx'x, OpType.wt => true | _, _ => false) = false))
  have houter := fun (b : Val I × Val I) (vs : List (Val I × Val I × Val I)) =>
    guessAXOuterBlockElems_filter I b vs
    (guessAXZAxprimeWritePred I) 1
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b0 hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq02 : q = 0 ∨ q = 2 := by omega
      rcases hq02 with rfl | rfl
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.xA, OpType.wt with
          | Loc.zAx'x, OpType.wt => true | _, _ => false) = false)
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zAxx', OpType.rd with
          | Loc.zAx'x, OpType.wt => true | _, _ => false) = false))
    (by
      intro b0 hb0
      exact guessAXZAxprimeWritePred_bridge I b0 hb0)
  unfold guessAXBlockWord
  simp only [List.filter_append, hinner]
  have hz1 : guessAXZAxprimeWritePred I (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    guessAXZAxprimeWritePred_bridge I _ (by decide : Loc.zAxy ∈ BridgeLoc)
  have hz2 : guessAXZAxprimeWritePred I (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false := by
    unfold guessAXZAxprimeWritePred
    exact (by decide : (match Loc.xA, OpType.wt with
      | Loc.zAx'x, OpType.wt => true | _, _ => false) = false)
  have hz3 : guessAXZAxprimeWritePred I (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = true := by
    unfold guessAXZAxprimeWritePred
    exact (by decide : (match Loc.zAx'x, OpType.wt with
      | Loc.zAx'x, OpType.wt => true | _, _ => false) = true)
  have hz4 : guessAXZAxprimeWritePred I (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    guessAXZAxprimeWritePred_bridge I _ (by decide : Loc.ellAyx ∈ BridgeLoc)
  simp only [List.filter_cons, List.filter_nil, hz1, hz2, hz3, hz4,
    List.append_nil, if_true, if_false, Bool.false_eq_true]
  rw [list_filter_flatMap_distrib]
  congr 1
  apply List.flatMap_congr
  intro p _
  exact houter p.1 p.2

theorem rawNthWrite_guessAX_zAx'x_eq (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (ks : List ℕ) (hlenOuter : outerRest.length = ks.length + 1)
    (hpreOuter : ∀ m, m < ks.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      ks[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[ks.length]? = some (b, vs) ∧ vs.length = 1)
    {i : ℕ} {ew : Event (domainOf I)}
    (h : rawNthWrite trace Tid.guessAX Loc.zAx'x i = some ew) :
    (i = 0 ∧ ew.val = v2) ∨
    (1 ≤ i ∧ i - 1 < inner0Rest.length ∧ ∃ e, inner0Rest[i - 1]? = some e ∧ ew.val = e.2.1) ∨
    (∃ m, m < ks.length + 1 ∧ ∃ b vs n e, outerRest[m]? = some (b, vs) ∧ n < vs.length ∧
      vs[n]? = some e ∧ i = 1 + inner0Rest.length + ksPrefix ks m + n ∧ ew.val = e.2.1) := by
  set ev : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX :=
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.zAx'x a.2.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)) with hev
  have hpredL := guessAXZAxprimeWritePred_iff I
  have hlen_eq := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessAX)
    (x := Loc.zAx'x) (op := OpType.wt) (predL := guessAXZAxprimeWritePred I) htrace hpredL
  have hfilt : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (guessAXZAxprimeWritePred I)
      = [(⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] ++
        inner0Rest.map ev ++ outerRest.flatMap (fun p => p.2.map ev) := by
    rw [hev]; exact guessAXBlockWord_zAx'x_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt0 : i < (rawOpEvents trace Tid.guessAX Loc.zAx'x OpType.wt).length :=
    (List.getElem?_eq_some_iff.mp h).1
  rw [hlen_eq, hfilt, List.length_append, List.length_append, List.length_singleton,
    List.length_map] at hilt0
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    left
    refine ⟨rfl, ?_⟩
    obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessAXZAxprimeWritePred I) 0
      (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
      (by rw [hfilt]; rfl)
    have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessAX)
      (l := guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
    have hraw : rawNthEvent trace Tid.guessAX Loc.zAx'x OpType.wt 0 = some ew := h
    rw [hraw] at hconn
    injection hconn with hconn
    rw [hconn]
    rfl
  · rcases Nat.lt_or_ge (i - 1) inner0Rest.length with hcase | hcase
    · right; left
      refine ⟨by omega, hcase, ?_⟩
      obtain ⟨e, he⟩ : ∃ e, inner0Rest[i - 1]? = some e :=
        ⟨inner0Rest[i-1]'hcase, List.getElem?_eq_getElem hcase⟩
      have hgetf :
          ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
            (guessAXZAxprimeWritePred I))[i]? = some (ev e) := by
        rw [hfilt, List.getElem?_append_left (by simp; omega),
          List.getElem?_append_right (by simp; omega), List.length_singleton,
          List.getElem?_map, he]
        rfl
      obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
        (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessAXZAxprimeWritePred I) i
        (ev e) hgetf
      have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessAX)
        (l := guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
      have hraw : rawNthEvent trace Tid.guessAX Loc.zAx'x OpType.wt i = some ew := h
      rw [hraw] at hconn
      refine ⟨e, he, ?_⟩
      injection hconn with hconn
      rw [hconn]
      rfl
    · right; right
      have hlen_outer_flat :
          (outerRest.flatMap (fun p => p.2.map ev)).length = ksPrefix ks ks.length + 1 := by
        have h1 : (outerRest.flatMap (fun p => p.2.map ev)).length
            = (outerRest.map (fun p => (p.2.map ev).length)).sum := by
          rw [List.length_flatMap]
        have h2 : (outerRest.map (fun p => (p.2.map ev).length)).sum
            = (outerRest.map (fun p => p.2.length)).sum := by
          congr 1
          apply List.map_congr_left
          intro p _
          exact List.length_map ..
        have h3 : (outerRest.map (fun p => p.2.length)).sum = (ks.map (· + 1)).sum + 1 :=
          sum_snd_length_of_forall_getElem outerRest ks hlenOuter hpreOuter hlastOuter
        rw [h1, h2, h3, ksPrefix_eq_sum]
      have hj' : i - 1 - inner0Rest.length < ksPrefix ks ks.length + 1 := by
        rw [← hlen_outer_flat]; omega
      obtain ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, hjeq, hgetflat⟩ :=
        ksPrefix_flatMap_map_getElem outerRest ks ev
          hlenOuter hpreOuter hlastOuter (i - 1 - inner0Rest.length) hj'
      have hgetf :
          ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
            (guessAXZAxprimeWritePred I))[i]? = some (ev b) := by
        rw [hfilt, List.getElem?_append_right (by simp; omega)]
        have hlen12 : ([(⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX)] ++ inner0Rest.map ev).length
            = 1 + inner0Rest.length := by simp; omega
        rw [hlen12]
        have hidxeq : i - (1 + inner0Rest.length) = i - 1 - inner0Rest.length := by omega
        rw [hidxeq]
        exact hgetflat
      obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
        (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessAXZAxprimeWritePred I) i
        (ev b) hgetf
      have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessAX)
        (l := guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
      have hraw : rawNthEvent trace Tid.guessAX Loc.zAx'x OpType.wt i = some ew := h
      rw [hraw] at hconn
      refine ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, by omega, ?_⟩
      injection hconn with hconn
      rw [hconn]
      rfl

/-- `rf_total` for the `primeAX`/`zAx'x` branch (Eq. (15)): the count of
`primeAX`'s `zAx'x`-reads (`primeAXBlockWord_zAx'x_length`) is bounded by the
count of `guessAX`'s `zAx'x`-writes (`guessAXBlockWord_zAx'x_filter_eq`). -/
theorem traceRf_total_primeAX_zAx'x (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (vals : List (Val I)) (htraceP : trace Tid.primeAX = primeAXBlockWord I vals)
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceG : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (hcount : vals.length ≤ 1 + inner0Rest.length + (outerRest.map (fun p => p.2.length)).sum)
    {er : Event (domainOf I)} (her_tid : er.tid = Tid.primeAX) (her_loc : er.loc = Loc.zAx'x)
    (her : er ∈ traceEvents trace) (herop : er.op = .rd) :
    ∃ ew, traceRf I trace ew er := by
  have hmemT : er ∈ traceEventsOf trace Tid.primeAX := mem_traceEvents_of_tid her her_tid
  have hmemOp : er ∈ rawOpEvents trace Tid.primeAX Loc.zAx'x OpType.rd := by
    unfold rawOpEvents
    exact List.mem_filter.mpr ⟨hmemT, by rw [her_loc, herop]; rfl⟩
  set i := (rawOpEvents trace Tid.primeAX Loc.zAx'x OpType.rd).idxOf er with hidef
  have hread : rawNthRead trace Tid.primeAX Loc.zAx'x i = some er := rawNthEvent_of_mem hmemOp
  have hilt_reader : i < (rawOpEvents trace Tid.primeAX Loc.zAx'x OpType.rd).length :=
    List.idxOf_lt_length_iff.mpr hmemOp
  have hpredL : ∀ lab : ThreadLabel (domainOf I) Tid.primeAX,
      (match lab.1.loc, lab.1.op with | Loc.zAx'x, OpType.rd => true | _, _ => false) = true ↔
        (lab.1.loc = Loc.zAx'x ∧ lab.1.op = OpType.rd) := by
    intro lab
    obtain ⟨x, hx⟩ : ∃ x : Loc, lab.1.loc = x := ⟨lab.1.loc, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : OpType, lab.1.op = y := ⟨lab.1.op, rfl⟩
    rw [hx, hy]
    cases x <;> cases y <;> simp; rfl
  have hlen := rawOpEvents_length_eq (D := domainOf I) (t := Tid.primeAX)
    (x := Loc.zAx'x) (op := OpType.rd) htraceP hpredL
  rw [hlen.trans (primeAXBlockWord_zAx'x_length I vals)] at hilt_reader
  have hpredW := guessAXZAxprimeWritePred_iff I
  have hlenW := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessAX)
    (x := Loc.zAx'x) (op := OpType.wt) (predL := guessAXZAxprimeWritePred I) htraceG hpredW
  have hfiltW := guessAXBlockWord_zAx'x_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt_writer : i < (rawOpEvents trace Tid.guessAX Loc.zAx'x OpType.wt).length := by
    rw [hlenW, hfiltW, List.length_append, List.length_append, List.length_singleton,
      List.length_map, List.length_flatMap]
    simp only [List.length_map]
    omega
  obtain ⟨ew, hew⟩ := rawNthEvent_exists_of_lt_length hilt_writer
  refine ⟨ew, ?_⟩
  unfold traceRf
  rw [her_tid, her_loc]
  exact ⟨i, hew, hread⟩

theorem traceRf_matches_guessAX_primeAX_zAx'x (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (K0 : ℕ) (hlen1 : inner0Rest.length = K0)
    (js : List (Fin I.n)) (hlen2 : outerRest.length = js.length + 1)
    (houterC : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastC : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (cnt0G : Fin 4) (hcnt0G : cnt0G = 0)
    (hv2 : v2 = Val.cnt (cnt0G + 1))
    (hval1 : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨((cnt0G + 1).val + n + 1) % 4, by omega⟩ : Fin 4))
    (hval2 : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨((cnt0G + 1).val + K0 + ksPrefix (guessAXJsToKs I js) m + n + 1) % 4,
          by omega⟩ : Fin 4))
    (vals : List (Val I)) (htracePAX : trace Tid.primeAX = primeAXBlockWord I vals)
    (cnt0P : Fin 4) (hcnt0P : cnt0P = 0)
    (hvalsVal : ∀ i, i < vals.length →
      vals[i]? = some (Val.cnt (⟨(cnt0P.val + i + 1) % 4, by omega⟩ : Fin 4)))
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.guessAX Loc.zAx'x i = some ew ∧
      rawNthRead trace Tid.primeAX Loc.zAx'x i = some er) :
    ew.val = er.val := by
  subst hcnt0G
  subst hcnt0P
  obtain ⟨i, hew, her⟩ := h
  obtain ⟨v, hv, herval⟩ := rawNthRead_primeAX_zAx'x_eq I vals htracePAX her
  have hvlen : i < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hvform := hvalsVal i hvlen
  rw [hvform] at hv
  injection hv with hv
  have hkslen : (guessAXJsToKs I js).length = js.length := by unfold guessAXJsToKs; simp
  have hlen2' : outerRest.length = (guessAXJsToKs I js).length + 1 := by rw [hkslen]; exact hlen2
  have houterC' : ∀ m, m < (guessAXJsToKs I js).length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1 := by
    rw [hkslen]; exact houterC
  have houterLastC' :
      ∃ b vs, outerRest[(guessAXJsToKs I js).length]? = some (b, vs) ∧ vs.length = 1 := by
    rw [hkslen]; exact houterLastC
  rcases rawNthWrite_guessAX_zAx'x_eq I v1 v2 vB0 inner0Rest outerRest htraceGAX
      (guessAXJsToKs I js) hlen2' houterC' houterLastC' hew with
    ⟨hi0, hewval⟩ | ⟨hipos, hcase, e, he, hewval⟩ |
      ⟨m, hm, b, vs, n, e, hbv, hnlt, hvsn, hieq, hewval⟩
  · subst hi0
    rw [hewval, herval, hv2, ← hv]
    congr 1
  · obtain ⟨e', he', he21'⟩ := hval1 (i - 1) (by rw [hlen1] at hcase ⊢; omega)
    rw [he] at he'
    injection he' with he'
    subst he'
    rw [hewval, herval, he21', ← hv]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    omega
  · have hm' : m < js.length + 1 := by rw [hkslen] at hm; omega
    obtain ⟨b', vs', hbv', hval'⟩ := hval2 m hm'
    rw [hbv] at hbv'
    simp only [Option.some.injEq, Prod.mk.injEq] at hbv'
    obtain ⟨hbeq, hvseq⟩ := hbv'
    subst hbeq
    subst hvseq
    obtain ⟨e', he', he21'⟩ := hval' n hnlt
    rw [hvsn] at he'
    injection he' with he'
    subst he'
    rw [hewval, herval, he21', ← hv]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    rw [hlen1] at hieq
    omega

/-- `traceRf_matches_guessAX_primeAX_zAx'x` for the general construction. -/
theorem traceRf_matches_guessAX_primeAX_zAx'x_general (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (K0 : ℕ) (hlen1 : inner0Rest.length = K0)
    (js : List (Fin I.n)) (hlen2 : outerRest.length = js.length + 1)
    (houterC : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastC : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (hv2raw : v2 = Val.cnt (1 : Fin 4))
    (hval1raw : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4) ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4))
    (hval2raw : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix (guessAXJsToKs I js) m + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix (guessAXJsToKs I js) m + n + 1) % 4, by omega⟩ : Fin 4))
    (vals : List (Val I)) (htracePAX : trace Tid.primeAX = primeAXBlockWord I vals)
    (hvalsVal : ∀ i, i < vals.length → vals[i]? = some (Val.cnt (⟨(i + 1) % 4, by omega⟩ : Fin 4)))
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.guessAX Loc.zAx'x i = some ew ∧
      rawNthRead trace Tid.primeAX Loc.zAx'x i = some er) :
    ew.val = er.val := by
  have hv2 : v2 = Val.cnt ((0 : Fin 4) + 1) := by rw [hv2raw]; congr 1
  have hval1 : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨((0 + 1 : Fin 4).val + n + 1) % 4, by omega⟩ : Fin 4) := by
    intro n hn
    obtain ⟨e, he, _, he21⟩ := hval1raw n hn
    exact ⟨e, he, by rw [he21]; congr 2⟩
  have hval2 : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨((0 + 1 : Fin 4).val + K0 + ksPrefix (guessAXJsToKs I js) m + n + 1) % 4,
          by omega⟩ : Fin 4) := by
    intro m hm
    obtain ⟨b, vs, hbv, hval2raw'⟩ := hval2raw m hm
    refine ⟨b, vs, hbv, fun n hn => ?_⟩
    obtain ⟨e, he, _, he21⟩ := hval2raw' n hn
    exact ⟨e, he, by rw [he21]; congr 2⟩
  have hvalsVal' : ∀ i, i < vals.length →
      vals[i]? = some (Val.cnt (⟨((0 : Fin 4).val + i + 1) % 4, by omega⟩ : Fin 4)) := by
    intro i hi; rw [hvalsVal i hi]; congr 2; apply Fin.ext; simp
  exact traceRf_matches_guessAX_primeAX_zAx'x I v1 v2 vB0 inner0Rest outerRest htraceGAX K0
    hlen1 js hlen2 houterC houterLastC 0 rfl hv2 hval1 hval2 vals htracePAX 0 rfl hvalsVal' h

/-! ## `rf_matches`: `guessAX`/`checkX` `xA` (Eq. (17))

`w_i(g_α^x,x_α) ⟶rf r_i(c^x,x_α)`. In `guessAXBlockWord`, `xA` is
written like `zAx'x`, but at offset `0` of each inner call. The read half is
`rawNthRead_checkX_xA_eq` (`Construction.lean`). -/

/-- `guessAX`'s `xA`-write match, lifted from `xAWritePredCore`. -/
def guessAXXAWritePred (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessAX) : Bool :=
  xAWritePredCore lab.1.loc lab.1.op

theorem guessAXXAWritePred_iff (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessAX) :
    guessAXXAWritePred I lab = true ↔ (lab.1.loc = Loc.xA ∧ lab.1.op = OpType.wt) := by
  unfold guessAXXAWritePred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  exact xAWritePredCore_iff y z

theorem guessAXXAWritePred_bridge (I : PCPInstance) :
    ∀ (lab : ThreadLabel (domainOf I) Tid.guessAX), lab.1.loc ∈ BridgeLoc →
    guessAXXAWritePred I lab = false := by
  intro lab hloc
  unfold guessAXXAWritePred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  rw [hy] at hloc
  exact xAWritePredCore_bridge y z hloc

/-- `guessAXBlockWord`'s `xA`-writes: the head's `v1`, then offset `0` of
every inner call (as `guessAXBlockWord_zAx'x_filter_eq`). -/
theorem guessAXBlockWord_xA_filter_eq (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter (guessAXXAWritePred I)
      = [(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] ++
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessAX)) ++
        outerRest.flatMap (fun p => p.2.map (fun a =>
          (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX))) := by
  have hinner := guessAXInnerBlockElems_filter I
    (guessAXXAWritePred I) 0
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq12 : q = 1 ∨ q = 2 := by omega
      rcases hq12 with rfl | rfl
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zAx'x, OpType.wt with
          | Loc.xA, OpType.wt => true | _, _ => false) = false)
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zAxx', OpType.rd with
          | Loc.xA, OpType.wt => true | _, _ => false) = false))
  have houter := fun (b : Val I × Val I) (vs : List (Val I × Val I × Val I)) =>
    guessAXOuterBlockElems_filter I b vs
    (guessAXXAWritePred I) 0
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b0 hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq12 : q = 1 ∨ q = 2 := by omega
      rcases hq12 with rfl | rfl
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zAx'x, OpType.wt with
          | Loc.xA, OpType.wt => true | _, _ => false) = false)
      · simp only [guessAXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zAxx', OpType.rd with
          | Loc.xA, OpType.wt => true | _, _ => false) = false))
    (by
      intro b0 hb0
      exact guessAXXAWritePred_bridge I b0 hb0)
  unfold guessAXBlockWord
  simp only [List.filter_append, hinner]
  have hz1 : guessAXXAWritePred I (⟨EventLabel.wt Tid.guessAX Loc.zAxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    guessAXXAWritePred_bridge I _ (by decide : Loc.zAxy ∈ BridgeLoc)
  have hz2 : guessAXXAWritePred I (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = true := by
    unfold guessAXXAWritePred
    exact (by decide : (match Loc.xA, OpType.wt with
      | Loc.xA, OpType.wt => true | _, _ => false) = true)
  have hz3 : guessAXXAWritePred I (⟨EventLabel.wt Tid.guessAX Loc.zAx'x v2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false := by
    unfold guessAXXAWritePred
    exact (by decide : (match Loc.zAx'x, OpType.wt with
      | Loc.xA, OpType.wt => true | _, _ => false) = false)
  have hz4 : guessAXXAWritePred I (⟨EventLabel.rd Tid.guessAX Loc.ellAyx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX) = false :=
    guessAXXAWritePred_bridge I _ (by decide : Loc.ellAyx ∈ BridgeLoc)
  simp only [List.filter_cons, List.filter_nil, hz1, hz2, hz3, hz4,
    List.append_nil, if_true, if_false, Bool.false_eq_true]
  rw [list_filter_flatMap_distrib]
  congr 1
  apply List.flatMap_congr
  intro p _
  exact houter p.1 p.2

/-- `guessAX`'s `i`-th `xA`-write is the head's `v1` (`i = 0`), an
`inner0Rest` entry's `.1`, or an `outerRest` entry's `.1` located through
`ksPrefix`. -/
theorem rawNthWrite_guessAX_xA_eq (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htrace : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (ks : List ℕ) (hlenOuter : outerRest.length = ks.length + 1)
    (hpreOuter : ∀ m, m < ks.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      ks[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[ks.length]? = some (b, vs) ∧ vs.length = 1)
    {i : ℕ} {ew : Event (domainOf I)}
    (h : rawNthWrite trace Tid.guessAX Loc.xA i = some ew) :
    (i = 0 ∧ ew.val = v1) ∨
    (1 ≤ i ∧ i - 1 < inner0Rest.length ∧ ∃ e, inner0Rest[i - 1]? = some e ∧ ew.val = e.1) ∨
    (∃ m, m < ks.length + 1 ∧ ∃ b vs n e, outerRest[m]? = some (b, vs) ∧ n < vs.length ∧
      vs[n]? = some e ∧ i = 1 + inner0Rest.length + ksPrefix ks m + n ∧ ew.val = e.1) := by
  set ev : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessAX :=
    (fun a => (⟨EventLabel.wt Tid.guessAX Loc.xA a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessAX)) with hev
  have hpredL := guessAXXAWritePred_iff I
  have hlen_eq := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessAX)
    (x := Loc.xA) (op := OpType.wt) (predL := guessAXXAWritePred I) htrace hpredL
  have hfilt : (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (guessAXXAWritePred I)
      = [(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)] ++
        inner0Rest.map ev ++ outerRest.flatMap (fun p => p.2.map ev) := by
    rw [hev]; exact guessAXBlockWord_xA_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt0 : i < (rawOpEvents trace Tid.guessAX Loc.xA OpType.wt).length :=
    (List.getElem?_eq_some_iff.mp h).1
  rw [hlen_eq, hfilt, List.length_append, List.length_append, List.length_singleton,
    List.length_map] at hilt0
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    left
    refine ⟨rfl, ?_⟩
    obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
      (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessAXXAWritePred I) 0
      (⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessAX)
      (by rw [hfilt]; rfl)
    have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessAX)
      (l := guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
    have hraw : rawNthEvent trace Tid.guessAX Loc.xA OpType.wt 0 = some ew := h
    rw [hraw] at hconn
    injection hconn with hconn
    rw [hconn]
    rfl
  · rcases Nat.lt_or_ge (i - 1) inner0Rest.length with hcase | hcase
    · right; left
      refine ⟨by omega, hcase, ?_⟩
      obtain ⟨e, he⟩ : ∃ e, inner0Rest[i - 1]? = some e :=
        ⟨inner0Rest[i-1]'hcase, List.getElem?_eq_getElem hcase⟩
      have hgetf :
          ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
            (guessAXXAWritePred I))[i]? = some (ev e) := by
        rw [hfilt, List.getElem?_append_left (by simp; omega),
          List.getElem?_append_right (by simp; omega), List.length_singleton,
          List.getElem?_map, he]
        rfl
      obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
        (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessAXXAWritePred I) i
        (ev e) hgetf
      have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessAX)
        (l := guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
      have hraw : rawNthEvent trace Tid.guessAX Loc.xA OpType.wt i = some ew := h
      rw [hraw] at hconn
      refine ⟨e, he, ?_⟩
      injection hconn with hconn
      rw [hconn]
      rfl
    · right; right
      have hlen_outer_flat :
          (outerRest.flatMap (fun p => p.2.map ev)).length = ksPrefix ks ks.length + 1 := by
        have h1 : (outerRest.flatMap (fun p => p.2.map ev)).length
            = (outerRest.map (fun p => (p.2.map ev).length)).sum := by
          rw [List.length_flatMap]
        have h2 : (outerRest.map (fun p => (p.2.map ev).length)).sum
            = (outerRest.map (fun p => p.2.length)).sum := by
          congr 1
          apply List.map_congr_left
          intro p _
          exact List.length_map ..
        have h3 : (outerRest.map (fun p => p.2.length)).sum = (ks.map (· + 1)).sum + 1 :=
          sum_snd_length_of_forall_getElem outerRest ks hlenOuter hpreOuter hlastOuter
        rw [h1, h2, h3, ksPrefix_eq_sum]
      have hj' : i - 1 - inner0Rest.length < ksPrefix ks ks.length + 1 := by
        rw [← hlen_outer_flat]; omega
      obtain ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, hjeq, hgetflat⟩ :=
        ksPrefix_flatMap_map_getElem outerRest ks ev
          hlenOuter hpreOuter hlastOuter (i - 1 - inner0Rest.length) hj'
      have hgetf :
          ((guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
            (guessAXXAWritePred I))[i]? = some (ev b) := by
        rw [hfilt, List.getElem?_append_right (by simp; omega)]
        have hlen12 : ([(⟨EventLabel.wt Tid.guessAX Loc.xA v1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessAX)] ++ inner0Rest.map ev).length
            = 1 + inner0Rest.length := by simp; omega
        rw [hlen12]
        have hidxeq : i - (1 + inner0Rest.length) = i - 1 - inner0Rest.length := by omega
        rw [hidxeq]
        exact hgetflat
      obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
        (guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessAXXAWritePred I) i
        (ev b) hgetf
      have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessAX)
        (l := guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
      have hraw : rawNthEvent trace Tid.guessAX Loc.xA OpType.wt i = some ew := h
      rw [hraw] at hconn
      refine ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, by omega, ?_⟩
      injection hconn with hconn
      rw [hconn]
      rfl

/-- `rf_total` for the `checkX`/`xA` branch (Eq. (17)): `checkX` makes
`1 + kws.length` `xA`-reads and `guessAX` makes
`1 + inner0Rest.length + (outerRest.map …).sum` `xA`-writes, equal by
`hsum`. -/
theorem traceRf_total_checkX_xA (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v0 : I.Γ) (kws : List (Fin 4 × Option I.Γ))
    (htraceV : trace Tid.checkX = checkXBlockWord I v0 kws)
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceG : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (hsum : 1 + inner0Rest.length + (outerRest.map (fun p => p.2.length)).sum = 1 + kws.length)
    {er : Event (domainOf I)} (her_tid : er.tid = Tid.checkX) (her_loc : er.loc = Loc.xA)
    (her : er ∈ traceEvents trace) (herop : er.op = .rd) :
    ∃ ew, traceRf I trace ew er := by
  have hmemT : er ∈ traceEventsOf trace Tid.checkX := mem_traceEvents_of_tid her her_tid
  have hmemOp : er ∈ rawOpEvents trace Tid.checkX Loc.xA OpType.rd := by
    unfold rawOpEvents
    exact List.mem_filter.mpr ⟨hmemT, by rw [her_loc, herop]; rfl⟩
  set i := (rawOpEvents trace Tid.checkX Loc.xA OpType.rd).idxOf er with hidef
  have hread : rawNthRead trace Tid.checkX Loc.xA i = some er := rawNthEvent_of_mem hmemOp
  have hilt_reader : i < (rawOpEvents trace Tid.checkX Loc.xA OpType.rd).length :=
    List.idxOf_lt_length_iff.mpr hmemOp
  have hlen := rawOpEvents_length_eq (D := domainOf I) (t := Tid.checkX)
    (x := Loc.xA) (op := OpType.rd) (predL := checkXXAReadPred I) htraceV
    (checkXXAReadPred_iff I)
  have hlen2 : ((checkXBlockWord I v0 kws).filter (checkXXAReadPred I)).length
      = 1 + kws.length := by
    unfold checkXBlockWord
    rw [List.filter_append, List.length_append, checkXBlock0Elems_xA_read_filter,
      checkXBlockRestElems_xA_read_filter, List.length_singleton]
  rw [hlen.trans hlen2] at hilt_reader
  have hlenW := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessAX)
    (x := Loc.xA) (op := OpType.wt) (predL := guessAXXAWritePred I) htraceG
    (guessAXXAWritePred_iff I)
  have hfiltW := guessAXBlockWord_xA_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt_writer : i < (rawOpEvents trace Tid.guessAX Loc.xA OpType.wt).length := by
    rw [hlenW, hfiltW, List.length_append, List.length_append, List.length_singleton,
      List.length_map, List.length_flatMap]
    simp only [List.length_map]
    omega
  obtain ⟨ew, hew⟩ := rawNthEvent_exists_of_lt_length hilt_writer
  refine ⟨ew, ?_⟩
  unfold traceRf
  rw [her_tid, her_loc]
  exact ⟨i, hew, hread⟩

/-- `traceRf` for the `guessAX`/`checkX` `xA` pair (Eq. (17)): at a shared
index `i`, the value `guessAX` writes to `x_α` equals the value `checkX` reads
from it. The agreement of the letters at each index is taken as hypotheses
(`hv0eq`/`hv1eq`/`hinnerAgree`/`houterAgree`/`hkwsAgree`, against a common
flattened `α`-word `c0 :: cs`); it is derived from a solution in
`traceRf_matches_checkX_guessAX_xA_general`.

`houterAgree` is an `Option` equation, so that it covers the terminating
write: at `m = ks.length` the letter written is `none` (`extAlpha I none =
[none]`), at index `cs.length`, where `cs[cs.length]? = none` too. -/
theorem traceRf_matches_checkX_guessAX_xA (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (ks : List ℕ) (hlenOuter : outerRest.length = ks.length + 1)
    (hpreOuter : ∀ m, m < ks.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      ks[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[ks.length]? = some (b, vs) ∧ vs.length = 1)
    (v0 : I.Γ) (kws : List (Fin 4 × Option I.Γ))
    (htraceVX : trace Tid.checkX = checkXBlockWord I v0 kws)
    (c0 : I.Γ) (cs : List I.Γ)
    (hv0eq : v0 = c0)
    (hv1eq : v1 = Val.xTag (Tid.guessAX, true) (some c0))
    (hinnerAgree : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      ∃ c, cs[n]? = some c ∧ e.1 = Val.xTag (Tid.guessAX, false) (some c))
    (houterAgree : ∀ m, m < ks.length + 1 → ∀ b vs, outerRest[m]? = some (b, vs) →
      ∀ n e, n < vs.length → vs[n]? = some e →
      e.1 = Val.xTag (Tid.guessAX, false) (cs[inner0Rest.length + ksPrefix ks m + n]?))
    (hkwsAgree : ∀ i, i < kws.length → ∃ kw, kws[i]? = some kw ∧ kw.2 = cs[i]?)
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.guessAX Loc.xA i = some ew ∧
      rawNthRead trace Tid.checkX Loc.xA i = some er) :
    ew.val = er.val := by
  obtain ⟨i, hew, her⟩ := h
  rcases rawNthWrite_guessAX_xA_eq I v1 v2 vB0 inner0Rest outerRest htraceGAX ks hlenOuter
    hpreOuter hlastOuter hew with
    ⟨hi0, hewval⟩ | ⟨hipos, hilt, e, he, hewval⟩ |
    ⟨m, hm, b, vs, n, e, hbv, hnlt, hvsn, hieq, hewval⟩
  · subst hi0
    rcases rawNthRead_checkX_xA_eq I v0 kws htraceVX her with
      ⟨-, herval⟩ | ⟨kw, hkw, hipos, herval⟩
    · rw [hewval, herval, hv1eq, hv0eq]
    · omega
  · rcases rawNthRead_checkX_xA_eq I v0 kws htraceVX her with
      ⟨hi0, herval⟩ | ⟨kw, hkw, hipos', herval⟩
    · omega
    · obtain ⟨e1, he1, c, hcs, hev⟩ := hinnerAgree (i - 1) hilt
      rw [he] at he1
      injection he1 with he1
      subst he1
      have hklt : i - 1 < kws.length := (List.getElem?_eq_some_iff.mp hkw).1
      obtain ⟨kw1, hkw1, hkweq⟩ := hkwsAgree (i - 1) hklt
      rw [hkw] at hkw1
      injection hkw1 with hkw1
      subst hkw1
      rw [hewval, herval, hev, hkweq, hcs]
  · rcases rawNthRead_checkX_xA_eq I v0 kws htraceVX her with
      ⟨hi0, herval⟩ | ⟨kw, hkw, hipos', herval⟩
    · omega
    · have hev := houterAgree m hm b vs hbv n e hnlt hvsn
      have hii : i - 1 = inner0Rest.length + ksPrefix ks m + n := by omega
      have hklt : i - 1 < kws.length := (List.getElem?_eq_some_iff.mp hkw).1
      obtain ⟨kw1, hkw1, hkweq⟩ := hkwsAgree (i - 1) hklt
      rw [hkw] at hkw1
      injection hkw1 with hkw1
      subst hkw1
      rw [hii] at hkweq
      rw [hewval, herval, hev, hkweq]

/-- `traceRf_matches_checkX_guessAX_xA` for the general construction: for a
solution `j0 :: js` (with flattened `α`-word `c0 :: cs`), the agreement
hypotheses follow from `guessAX_general_run` and `checkX_general_run_val`
(`guessAX_checkX_rf_matches`). -/
theorem traceRf_matches_checkX_guessAX_xA_general (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (j0 : Fin I.n) (js : List (Fin I.n)) (K0 : ℕ) (hlen0 : (I.α j0).length = K0 + 1)
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessAX = guessAXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (hlen1A : inner0Rest.length = K0)
    (hlen2A : outerRest.length = js.length + 1)
    (houterCA : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessAXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastCA : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (hv1rawA : ∃ j : Fin (GuessAX.maxLen I + 2), j.val = 1 ∧
      v1 = Val.xTag (Tid.guessAX, true) (GuessAX.jthLetter I (some j0) j))
    (hinnerrawA : ∀ n, n < inner0Rest.length → ∃ e j, inner0Rest[n]? = some e ∧ j.val = n + 2 ∧
      e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some j0) j))
    (houterrawA : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      (m < js.length → ∃ w, js[m]? = some w ∧
        ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I (some w) j)) ∧
      (m = js.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessAX, false) (GuessAX.jthLetter I none j)))
    (v0 : I.Γ) (kws : List (Fin 4 × Option I.Γ))
    (htraceVX : trace Tid.checkX = checkXBlockWord I v0 kws)
    (c0 : I.Γ) (cs : List I.Γ) (hflat : ((j0 :: js).map I.α).flatten = c0 :: cs) (hv0 : v0 = c0)
    (hvalVX : ∀ i, i < kws.length →
      ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w) ∧ w = cs[i]?)
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.guessAX Loc.xA i = some ew ∧
      rawNthRead trace Tid.checkX Loc.xA i = some er) :
    ew.val = er.val := by
  obtain ⟨hv0eq, hv1eq, hinnerAgree, houterAgree, hkwsAgree⟩ :=
    guessAX_checkX_rf_matches I j0 js c0 cs hflat K0 hlen0 v1 inner0Rest outerRest
      hlen1A houterCA hv1rawA hinnerrawA houterrawA v0 hv0 kws hvalVX
  have hkslen : (guessAXJsToKs I js).length = js.length := by unfold guessAXJsToKs; simp
  refine traceRf_matches_checkX_guessAX_xA I v1 v2 vB0 inner0Rest outerRest htraceGAX
    (guessAXJsToKs I js) (by rw [hkslen]; exact hlen2A)
    (by rw [hkslen]; exact houterCA) (by rw [hkslen]; exact houterLastCA)
    v0 kws htraceVX c0 cs hv0eq hv1eq hinnerAgree ?_ hkwsAgree h
  intro m hm b vs hbv n e hnlt hvsn
  rw [hkslen] at hm
  rw [hlen1A]
  exact houterAgree m hm b vs hbv n e hnlt hvsn


/-! ## `rf_matches`: `guessBX`/`zBxx'` (Eq. (15))

The mirror of the `guessAX`/`zAxx'` branch. -/

/-- The `zBxx'`-read match, as a predicate on `Loc`/`OpType` alone. -/
def zBxx'ReadPredCore (loc : Loc) (op : OpType) : Bool :=
  match loc, op with | Loc.zBxx', OpType.rd => true | _, _ => false

/-- `zBxx'ReadPredCore`, lifted to `guessBX`'s `ThreadLabel`. -/
def guessBXZBxReadPred (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessBX) : Bool :=
  zBxx'ReadPredCore lab.1.loc lab.1.op

/-- No bridge location matches `zBxx'ReadPredCore`. -/
theorem zBxx'ReadPredCore_bridge : ∀ y : Loc, ∀ z : OpType, y ∈ BridgeLoc →
    zBxx'ReadPredCore y z = false := by
  intro y z hb0
  cases y <;> cases z <;> revert hb0 <;> decide

/-- `zBxx'ReadPredCore_bridge`, lifted to `guessBXZBxReadPred`. -/
theorem guessBXZBxReadPred_bridge (I : PCPInstance) :
    ∀ (lab : ThreadLabel (domainOf I) Tid.guessBX), lab.1.loc ∈ BridgeLoc →
    guessBXZBxReadPred I lab = false := by
  intro lab hloc
  unfold guessBXZBxReadPred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  rw [hy] at hloc
  exact zBxx'ReadPredCore_bridge y z hloc

/-- `guessBXBlockWord`'s `zBxx'`-reads: those of `inner0Rest` (position `2`
of each inner call) followed by those of `outerRest`. -/
theorem guessBXBlockWord_zBxx'_filter_eq (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (guessBXZBxReadPred I)
      = inner0Rest.map (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX)) ++
        outerRest.flatMap (fun p => p.2.map (fun a =>
          (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX))) := by
  have hinner := guessBXInnerBlockElems_filter I
    (guessBXZBxReadPred I) 2
    (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.xB, OpType.wt with
          | Loc.zBxx', OpType.rd => true | _, _ => false) = false)
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zBx'x, OpType.wt with
          | Loc.zBxx', OpType.rd => true | _, _ => false) = false))
  have houter := fun (b : Val I × Val I) (vs : List (Val I × Val I × Val I)) =>
    guessBXOuterBlockElems_filter I b vs
    (guessBXZBxReadPred I) 2
    (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b0 hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq01 : q = 0 ∨ q = 1 := by omega
      rcases hq01 with rfl | rfl
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.xB, OpType.wt with
          | Loc.zBxx', OpType.rd => true | _, _ => false) = false)
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zBx'x, OpType.wt with
          | Loc.zBxx', OpType.rd => true | _, _ => false) = false))
    (by
      intro b0 hb0
      exact guessBXZBxReadPred_bridge I b0 hb0)
  unfold guessBXBlockWord
  simp only [List.filter_append, hinner]
  have hcore : ∀ y : Loc, ∀ z : OpType, ¬ (y = Loc.zBxx' ∧ z = OpType.rd) →
      zBxx'ReadPredCore y z = false := by
    intro y z hne
    cases y <;> cases z <;> first | rfl | (exfalso; exact hne ⟨rfl, rfl⟩)
  have hz1 : guessBXZBxReadPred I (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    hcore Loc.zBxy OpType.wt (by decide)
  have hz2 : guessBXZBxReadPred I (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    hcore Loc.xB OpType.wt (by decide)
  have hz3 : guessBXZBxReadPred I (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    hcore Loc.zBx'x OpType.wt (by decide)
  have hz4 : guessBXZBxReadPred I (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    hcore Loc.ellByx OpType.rd (by decide)
  simp only [List.filter_cons, List.filter_nil, hz1, hz2, hz3, hz4, List.nil_append,
    List.append_nil, if_false, Bool.false_eq_true]
  rw [list_filter_flatMap_distrib]
  congr 1
  apply List.flatMap_congr
  intro p _
  exact houter p.1 p.2

theorem zBxx'ReadPredCore_iff (y : Loc) (z : OpType) :
    zBxx'ReadPredCore y z = true ↔ (y = Loc.zBxx' ∧ z = OpType.rd) := by
  cases y <;> cases z <;> decide

theorem guessBXZBxReadPred_iff (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessBX) :
    guessBXZBxReadPred I lab = true ↔ (lab.1.loc = Loc.zBxx' ∧ lab.1.op = OpType.rd) := by
  unfold guessBXZBxReadPred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  exact zBxx'ReadPredCore_iff y z

theorem rawNthRead_guessBX_zBxx'_eq (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (ks : List ℕ) (hlenOuter : outerRest.length = ks.length + 1)
    (hpreOuter : ∀ m, m < ks.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      ks[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[ks.length]? = some (b, vs) ∧ vs.length = 1)
    {i : ℕ} {er : Event (domainOf I)}
    (h : rawNthRead trace Tid.guessBX Loc.zBxx' i = some er) :
    (i < inner0Rest.length ∧ ∃ e, inner0Rest[i]? = some e ∧ er.val = e.2.2) ∨
    (∃ m, m < ks.length + 1 ∧ ∃ b vs n e, outerRest[m]? = some (b, vs) ∧ n < vs.length ∧
      vs[n]? = some e ∧ i = inner0Rest.length + ksPrefix ks m + n ∧ er.val = e.2.2) := by
  set ev : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX :=
    (fun a => (⟨EventLabel.rd Tid.guessBX Loc.zBxx' a.2.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)) with hev
  have hpredL := guessBXZBxReadPred_iff I
  have hlen_eq := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessBX)
    (x := Loc.zBxx') (op := OpType.rd) (predL := guessBXZBxReadPred I) htrace hpredL
  have hfilt : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter (guessBXZBxReadPred I)
      = inner0Rest.map ev ++ outerRest.flatMap (fun p => p.2.map ev) := by
    rw [hev]; exact guessBXBlockWord_zBxx'_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt0 : i < (rawOpEvents trace Tid.guessBX Loc.zBxx' OpType.rd).length :=
    (List.getElem?_eq_some_iff.mp h).1
  rw [hlen_eq, hfilt, List.length_append, List.length_map] at hilt0
  rcases Nat.lt_or_ge i inner0Rest.length with hcase | hcase
  · left
    refine ⟨hcase, ?_⟩
    obtain ⟨e, he⟩ : ∃ e, inner0Rest[i]? = some e :=
      ⟨inner0Rest[i]'hcase, List.getElem?_eq_getElem hcase⟩
    have hgetf :
        ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
          (guessBXZBxReadPred I))[i]? = some (ev e) := by
      rw [hfilt, List.getElem?_append_left (by simpa using hcase), List.getElem?_map, he]
      rfl
    obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessBXZBxReadPred I) i
      (ev e) hgetf
    have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessBX)
      (l := guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
    have hraw : rawNthEvent trace Tid.guessBX Loc.zBxx' OpType.rd i = some er := h
    rw [hraw] at hconn
    refine ⟨e, he, ?_⟩
    injection hconn with hconn
    rw [hconn]
    rfl
  · right
    have hlen_outer_flat :
        (outerRest.flatMap (fun p => p.2.map ev)).length
          = ksPrefix ks ks.length + 1 := by
      have h1 : (outerRest.flatMap (fun p => p.2.map ev)).length
          = (outerRest.map (fun p => (p.2.map (ev)).length)).sum := by
        rw [List.length_flatMap]
      have h2 : (outerRest.map (fun p => (p.2.map (ev)).length)).sum
          = (outerRest.map (fun p => p.2.length)).sum := by
        congr 1
        apply List.map_congr_left
        intro p _
        exact List.length_map ..
      have h3 : (outerRest.map (fun p => p.2.length)).sum = (ks.map (· + 1)).sum + 1 :=
        sum_snd_length_of_forall_getElem outerRest ks hlenOuter hpreOuter hlastOuter
      rw [h1, h2, h3, ksPrefix_eq_sum]
    have hj' : i - inner0Rest.length < ksPrefix ks ks.length + 1 := by
      rw [← hlen_outer_flat]; omega
    obtain ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, hjeq, hgetflat⟩ :=
      ksPrefix_flatMap_map_getElem outerRest ks (ev)
        hlenOuter hpreOuter hlastOuter (i - inner0Rest.length) hj'
    have hgetf :
        ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
          (guessBXZBxReadPred I))[i]? = some (ev b) := by
      rw [hfilt, List.getElem?_append_right (by rw [List.length_map]; omega), List.length_map]
      exact hgetflat
    obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessBXZBxReadPred I) i (ev b) hgetf
    have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessBX)
      (l := guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
    have hraw : rawNthEvent trace Tid.guessBX Loc.zBxx' OpType.rd i = some er := h
    rw [hraw] at hconn
    refine ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, by omega, ?_⟩
    injection hconn with hconn
    rw [hconn]
    rfl

/-- `rf_total` for the `guessBX`/`zBxx'` branch (Eq. (15)), as
`traceRf_total_guessAX_zAxx'`. -/
theorem traceRf_total_guessBX_zBxx' (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceG : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (vals : List (Val I)) (htraceP : trace Tid.primeBX = primeBXBlockWord I vals)
    (hcount : inner0Rest.length + (outerRest.map (fun p => p.2.length)).sum ≤ vals.length)
    {er : Event (domainOf I)} (her_tid : er.tid = Tid.guessBX) (her_loc : er.loc = Loc.zBxx')
    (her : er ∈ traceEvents trace) (herop : er.op = .rd) :
    ∃ ew, traceRf I trace ew er := by
  have hmemT : er ∈ traceEventsOf trace Tid.guessBX := mem_traceEvents_of_tid her her_tid
  have hmemOp : er ∈ rawOpEvents trace Tid.guessBX Loc.zBxx' OpType.rd := by
    unfold rawOpEvents
    exact List.mem_filter.mpr ⟨hmemT, by rw [her_loc, herop]; rfl⟩
  set i := (rawOpEvents trace Tid.guessBX Loc.zBxx' OpType.rd).idxOf er with hidef
  have hread : rawNthRead trace Tid.guessBX Loc.zBxx' i = some er := rawNthEvent_of_mem hmemOp
  have hilt_reader : i < (rawOpEvents trace Tid.guessBX Loc.zBxx' OpType.rd).length :=
    List.idxOf_lt_length_iff.mpr hmemOp
  have hpredL := guessBXZBxReadPred_iff I
  have hlen_eq := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessBX)
    (x := Loc.zBxx') (op := OpType.rd) (predL := guessBXZBxReadPred I) htraceG hpredL
  have hfilt := guessBXBlockWord_zBxx'_filter_eq I v1 v2 vB0 inner0Rest outerRest
  rw [hlen_eq, hfilt, List.length_append, List.length_flatMap] at hilt_reader
  simp only [List.length_map] at hilt_reader
  have hpredW : ∀ lab : ThreadLabel (domainOf I) Tid.primeBX,
      (match lab.1.loc, lab.1.op with | Loc.zBxx', OpType.wt => true | _, _ => false) = true ↔
        (lab.1.loc = Loc.zBxx' ∧ lab.1.op = OpType.wt) := by
    intro lab
    obtain ⟨x, hx⟩ : ∃ x : Loc, lab.1.loc = x := ⟨lab.1.loc, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : OpType, lab.1.op = y := ⟨lab.1.op, rfl⟩
    rw [hx, hy]
    cases x <;> cases y <;> simp; rfl
  have hlenW := rawOpEvents_length_eq (D := domainOf I) (t := Tid.primeBX)
    (x := Loc.zBxx') (op := OpType.wt) htraceP hpredW
  have hilt_writer : i < (rawOpEvents trace Tid.primeBX Loc.zBxx' OpType.wt).length := by
    rw [hlenW.trans (primeBXBlockWord_zBxx'_length I vals)]
    omega
  obtain ⟨ew, hew⟩ := rawNthEvent_exists_of_lt_length hilt_writer
  refine ⟨ew, ?_⟩
  unfold traceRf
  rw [her_tid, her_loc]
  exact ⟨i, hew, hread⟩

theorem traceRf_matches_guessBX_zBxx' (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (vals : List (Val I)) (htracePAX : trace Tid.primeBX = primeBXBlockWord I vals)
    (cnt0P : Fin 4) (hcnt0P : cnt0P = 0)
    (hvalsVal : ∀ i, i < vals.length →
      vals[i]? = some (Val.cnt (⟨(cnt0P.val + i + 1) % 4, by omega⟩ : Fin 4)))
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (K0 : ℕ) (hlen1 : inner0Rest.length = K0)
    (js : List (Fin I.n)) (hlen2 : outerRest.length = js.length + 1)
    (houterC : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastC : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (cnt0G : Fin 4) (hcnt0G : cnt0G = 0)
    (hval1 : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨((cnt0G + 1).val + n) % 4, by omega⟩ : Fin 4))
    (hval2 : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨((cnt0G + 1).val + K0 + ksPrefix (guessBXJsToKs I js) m + n) % 4,
          by omega⟩ : Fin 4))
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.primeBX Loc.zBxx' i = some ew ∧
      rawNthRead trace Tid.guessBX Loc.zBxx' i = some er) :
    ew.val = er.val := by
  subst hcnt0P
  subst hcnt0G
  obtain ⟨i, hew, her⟩ := h
  obtain ⟨v, hv, hewval⟩ := rawNthWrite_primeBX_zBxx'_eq I vals htracePAX hew
  have hvlen : i < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hvform := hvalsVal i hvlen
  rw [hvform] at hv
  injection hv with hv
  have hkslen : (guessBXJsToKs I js).length = js.length := by unfold guessBXJsToKs; simp
  have hlen2' : outerRest.length = (guessBXJsToKs I js).length + 1 := by rw [hkslen]; exact hlen2
  have houterC' : ∀ m, m < (guessBXJsToKs I js).length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1 := by
    rw [hkslen]; exact houterC
  have houterLastC' :
      ∃ b vs, outerRest[(guessBXJsToKs I js).length]? = some (b, vs) ∧ vs.length = 1 := by
    rw [hkslen]; exact houterLastC
  rcases rawNthRead_guessBX_zBxx'_eq I v1 v2 vB0 inner0Rest outerRest htraceGAX
      (guessBXJsToKs I js) hlen2' houterC' houterLastC' her with
    ⟨hilt, e, he, herval⟩ | ⟨m, hm, b, vs, n, e, hbv, hnlt, hvsn, hieq, herval⟩
  · obtain ⟨e', he', he22'⟩ := hval1 i (by rw [hlen1] at hilt ⊢; omega)
    rw [he] at he'
    injection he' with he'
    subst he'
    rw [hewval, herval, he22', ← hv]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    omega
  · have hm' : m < js.length + 1 := by rw [hkslen] at hm; omega
    obtain ⟨b', vs', hbv', hval'⟩ := hval2 m hm'
    rw [hbv] at hbv'
    simp only [Option.some.injEq, Prod.mk.injEq] at hbv'
    obtain ⟨hbeq, hvseq⟩ := hbv'
    subst hbeq
    subst hvseq
    obtain ⟨e', he', he22'⟩ := hval' n hnlt
    rw [hvsn] at he'
    injection he' with he'
    subst he'
    rw [hewval, herval, he22', ← hv]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    rw [hlen1] at hieq
    omega

/-- `traceRf_matches_guessBX_zBxx'` for the general construction. -/
theorem traceRf_matches_guessBX_zBxx'_general (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (cs : List I.Γ)
    (vals : List (Val I)) (htracePBX : trace Tid.primeBX = primeBXBlockWord I vals)
    (_ : vals.length = cs.length + 1)
    (hvalsVal : ∀ i, i < vals.length → vals[i]? = some (Val.cnt (⟨(i + 1) % 4, by omega⟩ : Fin 4)))
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGBX : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (K0 : ℕ) (hlen1 : inner0Rest.length = K0)
    (js : List (Fin I.n)) (hlen2 : outerRest.length = js.length + 1)
    (houterC : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastC : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (hval1raw : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4) ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4))
    (hval2raw : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix (guessBXJsToKs I js) m + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix (guessBXJsToKs I js) m + n + 1) % 4, by omega⟩ : Fin 4))
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.primeBX Loc.zBxx' i = some ew ∧
      rawNthRead trace Tid.guessBX Loc.zBxx' i = some er) :
    ew.val = er.val := by
  have hvalsVal' : ∀ i, i < vals.length →
      vals[i]? = some (Val.cnt (⟨((0 : Fin 4).val + i + 1) % 4, by omega⟩ : Fin 4)) := by
    intro i hi
    rw [hvalsVal i hi]; congr 2; apply Fin.ext; simp
  have hval1 : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨((0 + 1 : Fin 4).val + n) % 4, by omega⟩ : Fin 4) := by
    intro n hn
    obtain ⟨e, he, he22, _⟩ := hval1raw n hn
    refine ⟨e, he, ?_⟩
    rw [he22]; congr 2
  have hval2 : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨((0 + 1 : Fin 4).val + K0 + ksPrefix (guessBXJsToKs I js) m + n) % 4,
          by omega⟩ : Fin 4) := by
    intro m hm
    obtain ⟨b, vs, hbv, hval2raw'⟩ := hval2raw m hm
    refine ⟨b, vs, hbv, ?_⟩
    intro n hn
    obtain ⟨e, he, he22, _⟩ := hval2raw' n hn
    refine ⟨e, he, ?_⟩
    rw [he22]; congr 2
  exact traceRf_matches_guessBX_zBxx' I vals htracePBX 0 rfl hvalsVal'
    v1 v2 vB0 inner0Rest outerRest htraceGBX K0 hlen1 js hlen2 houterC houterLastC 0 rfl
    hval1 hval2 h

/-! ## `rf_matches`: `guessBX`/`primeBX` `zBx'x` (Eq. (15)) -/

def zBx'xWritePredCore (loc : Loc) (op : OpType) : Bool :=
  match loc, op with | Loc.zBx'x, OpType.wt => true | _, _ => false

theorem zBx'xWritePredCore_iff (y : Loc) (z : OpType) :
    zBx'xWritePredCore y z = true ↔ (y = Loc.zBx'x ∧ z = OpType.wt) := by
  cases y <;> cases z <;> decide

theorem zBx'xWritePredCore_bridge : ∀ y : Loc, ∀ z : OpType, y ∈ BridgeLoc →
    zBx'xWritePredCore y z = false := by
  intro y z hb0
  cases y <;> cases z <;> revert hb0 <;> decide

/-- `zBx'xWritePredCore`, lifted to `guessBX`'s `ThreadLabel`. -/
def guessBXZBxprimeWritePred (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessBX) :
    Bool :=
  zBx'xWritePredCore lab.1.loc lab.1.op

theorem guessBXZBxprimeWritePred_iff (I : PCPInstance)
    (lab : ThreadLabel (domainOf I) Tid.guessBX) :
    guessBXZBxprimeWritePred I lab = true ↔ (lab.1.loc = Loc.zBx'x ∧ lab.1.op = OpType.wt) := by
  unfold guessBXZBxprimeWritePred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  exact zBx'xWritePredCore_iff y z

theorem guessBXZBxprimeWritePred_bridge (I : PCPInstance) :
    ∀ (lab : ThreadLabel (domainOf I) Tid.guessBX), lab.1.loc ∈ BridgeLoc →
    guessBXZBxprimeWritePred I lab = false := by
  intro lab hloc
  unfold guessBXZBxprimeWritePred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  rw [hy] at hloc
  exact zBx'xWritePredCore_bridge y z hloc

/-- `guessBXBlockWord`'s `zBx'x`-writes: the head's `v2`, then those of
`inner0Rest` (position `1`), then those of `outerRest`. -/
theorem guessBXBlockWord_zBx'x_filter_eq (I : PCPInstance) (v1 v2 : Val I)
    (vB0 : Val I × Val I) (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter (guessBXZBxprimeWritePred I)
      = [(⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] ++
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX)) ++
        outerRest.flatMap (fun p => p.2.map (fun a =>
          (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX))) := by
  have hinner := guessBXInnerBlockElems_filter I
    (guessBXZBxprimeWritePred I) 1
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq02 : q = 0 ∨ q = 2 := by omega
      rcases hq02 with rfl | rfl
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.xB, OpType.wt with
          | Loc.zBx'x, OpType.wt => true | _, _ => false) = false)
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zBxx', OpType.rd with
          | Loc.zBx'x, OpType.wt => true | _, _ => false) = false))
  have houter := fun (b : Val I × Val I) (vs : List (Val I × Val I × Val I)) =>
    guessBXOuterBlockElems_filter I b vs
    (guessBXZBxprimeWritePred I) 1
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b0 hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq02 : q = 0 ∨ q = 2 := by omega
      rcases hq02 with rfl | rfl
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_zero, Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.xB, OpType.wt with
          | Loc.zBx'x, OpType.wt => true | _, _ => false) = false)
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zBxx', OpType.rd with
          | Loc.zBx'x, OpType.wt => true | _, _ => false) = false))
    (by
      intro b0 hb0
      exact guessBXZBxprimeWritePred_bridge I b0 hb0)
  unfold guessBXBlockWord
  simp only [List.filter_append, hinner]
  have hz1 : guessBXZBxprimeWritePred I (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    guessBXZBxprimeWritePred_bridge I _ (by decide : Loc.zBxy ∈ BridgeLoc)
  have hz2 : guessBXZBxprimeWritePred I (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false := by
    unfold guessBXZBxprimeWritePred
    exact (by decide : (match Loc.xB, OpType.wt with
      | Loc.zBx'x, OpType.wt => true | _, _ => false) = false)
  have hz3 : guessBXZBxprimeWritePred I (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = true := by
    unfold guessBXZBxprimeWritePred
    exact (by decide : (match Loc.zBx'x, OpType.wt with
      | Loc.zBx'x, OpType.wt => true | _, _ => false) = true)
  have hz4 : guessBXZBxprimeWritePred I (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    guessBXZBxprimeWritePred_bridge I _ (by decide : Loc.ellByx ∈ BridgeLoc)
  simp only [List.filter_cons, List.filter_nil, hz1, hz2, hz3, hz4,
    List.append_nil, if_true, if_false, Bool.false_eq_true]
  rw [list_filter_flatMap_distrib]
  congr 1
  apply List.flatMap_congr
  intro p _
  exact houter p.1 p.2

theorem rawNthWrite_guessBX_zBx'x_eq (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (ks : List ℕ) (hlenOuter : outerRest.length = ks.length + 1)
    (hpreOuter : ∀ m, m < ks.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      ks[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[ks.length]? = some (b, vs) ∧ vs.length = 1)
    {i : ℕ} {ew : Event (domainOf I)}
    (h : rawNthWrite trace Tid.guessBX Loc.zBx'x i = some ew) :
    (i = 0 ∧ ew.val = v2) ∨
    (1 ≤ i ∧ i - 1 < inner0Rest.length ∧ ∃ e, inner0Rest[i - 1]? = some e ∧ ew.val = e.2.1) ∨
    (∃ m, m < ks.length + 1 ∧ ∃ b vs n e, outerRest[m]? = some (b, vs) ∧ n < vs.length ∧
      vs[n]? = some e ∧ i = 1 + inner0Rest.length + ksPrefix ks m + n ∧ ew.val = e.2.1) := by
  set ev : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX :=
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.zBx'x a.2.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)) with hev
  have hpredL := guessBXZBxprimeWritePred_iff I
  have hlen_eq := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessBX)
    (x := Loc.zBx'x) (op := OpType.wt) (predL := guessBXZBxprimeWritePred I) htrace hpredL
  have hfilt : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (guessBXZBxprimeWritePred I)
      = [(⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] ++
        inner0Rest.map ev ++ outerRest.flatMap (fun p => p.2.map ev) := by
    rw [hev]; exact guessBXBlockWord_zBx'x_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt0 : i < (rawOpEvents trace Tid.guessBX Loc.zBx'x OpType.wt).length :=
    (List.getElem?_eq_some_iff.mp h).1
  rw [hlen_eq, hfilt, List.length_append, List.length_append, List.length_singleton,
    List.length_map] at hilt0
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    left
    refine ⟨rfl, ?_⟩
    obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessBXZBxprimeWritePred I) 0
      (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
      (by rw [hfilt]; rfl)
    have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessBX)
      (l := guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
    have hraw : rawNthEvent trace Tid.guessBX Loc.zBx'x OpType.wt 0 = some ew := h
    rw [hraw] at hconn
    injection hconn with hconn
    rw [hconn]
    rfl
  · rcases Nat.lt_or_ge (i - 1) inner0Rest.length with hcase | hcase
    · right; left
      refine ⟨by omega, hcase, ?_⟩
      obtain ⟨e, he⟩ : ∃ e, inner0Rest[i - 1]? = some e :=
        ⟨inner0Rest[i-1]'hcase, List.getElem?_eq_getElem hcase⟩
      have hgetf :
          ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
            (guessBXZBxprimeWritePred I))[i]? = some (ev e) := by
        rw [hfilt, List.getElem?_append_left (by simp; omega),
          List.getElem?_append_right (by simp; omega), List.length_singleton,
          List.getElem?_map, he]
        rfl
      obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
        (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessBXZBxprimeWritePred I) i
        (ev e) hgetf
      have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessBX)
        (l := guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
      have hraw : rawNthEvent trace Tid.guessBX Loc.zBx'x OpType.wt i = some ew := h
      rw [hraw] at hconn
      refine ⟨e, he, ?_⟩
      injection hconn with hconn
      rw [hconn]
      rfl
    · right; right
      have hlen_outer_flat :
          (outerRest.flatMap (fun p => p.2.map ev)).length = ksPrefix ks ks.length + 1 := by
        have h1 : (outerRest.flatMap (fun p => p.2.map ev)).length
            = (outerRest.map (fun p => (p.2.map ev).length)).sum := by
          rw [List.length_flatMap]
        have h2 : (outerRest.map (fun p => (p.2.map ev).length)).sum
            = (outerRest.map (fun p => p.2.length)).sum := by
          congr 1
          apply List.map_congr_left
          intro p _
          exact List.length_map ..
        have h3 : (outerRest.map (fun p => p.2.length)).sum = (ks.map (· + 1)).sum + 1 :=
          sum_snd_length_of_forall_getElem outerRest ks hlenOuter hpreOuter hlastOuter
        rw [h1, h2, h3, ksPrefix_eq_sum]
      have hj' : i - 1 - inner0Rest.length < ksPrefix ks ks.length + 1 := by
        rw [← hlen_outer_flat]; omega
      obtain ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, hjeq, hgetflat⟩ :=
        ksPrefix_flatMap_map_getElem outerRest ks ev
          hlenOuter hpreOuter hlastOuter (i - 1 - inner0Rest.length) hj'
      have hgetf :
          ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
            (guessBXZBxprimeWritePred I))[i]? = some (ev b) := by
        rw [hfilt, List.getElem?_append_right (by simp; omega)]
        have hlen12 : ([(⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX)] ++ inner0Rest.map ev).length
            = 1 + inner0Rest.length := by simp; omega
        rw [hlen12]
        have hidxeq : i - (1 + inner0Rest.length) = i - 1 - inner0Rest.length := by omega
        rw [hidxeq]
        exact hgetflat
      obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
        (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessBXZBxprimeWritePred I) i
        (ev b) hgetf
      have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessBX)
        (l := guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
      have hraw : rawNthEvent trace Tid.guessBX Loc.zBx'x OpType.wt i = some ew := h
      rw [hraw] at hconn
      refine ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, by omega, ?_⟩
      injection hconn with hconn
      rw [hconn]
      rfl

/-- `rf_total` for the `primeBX`/`zBx'x` branch (Eq. (15)), as
`traceRf_total_primeAX_zAx'x`. -/
theorem traceRf_total_primeBX_zBx'x (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (vals : List (Val I)) (htraceP : trace Tid.primeBX = primeBXBlockWord I vals)
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceG : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (hcount : vals.length ≤ 1 + inner0Rest.length + (outerRest.map (fun p => p.2.length)).sum)
    {er : Event (domainOf I)} (her_tid : er.tid = Tid.primeBX) (her_loc : er.loc = Loc.zBx'x)
    (her : er ∈ traceEvents trace) (herop : er.op = .rd) :
    ∃ ew, traceRf I trace ew er := by
  have hmemT : er ∈ traceEventsOf trace Tid.primeBX := mem_traceEvents_of_tid her her_tid
  have hmemOp : er ∈ rawOpEvents trace Tid.primeBX Loc.zBx'x OpType.rd := by
    unfold rawOpEvents
    exact List.mem_filter.mpr ⟨hmemT, by rw [her_loc, herop]; rfl⟩
  set i := (rawOpEvents trace Tid.primeBX Loc.zBx'x OpType.rd).idxOf er with hidef
  have hread : rawNthRead trace Tid.primeBX Loc.zBx'x i = some er := rawNthEvent_of_mem hmemOp
  have hilt_reader : i < (rawOpEvents trace Tid.primeBX Loc.zBx'x OpType.rd).length :=
    List.idxOf_lt_length_iff.mpr hmemOp
  have hpredL : ∀ lab : ThreadLabel (domainOf I) Tid.primeBX,
      (match lab.1.loc, lab.1.op with | Loc.zBx'x, OpType.rd => true | _, _ => false) = true ↔
        (lab.1.loc = Loc.zBx'x ∧ lab.1.op = OpType.rd) := by
    intro lab
    obtain ⟨x, hx⟩ : ∃ x : Loc, lab.1.loc = x := ⟨lab.1.loc, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : OpType, lab.1.op = y := ⟨lab.1.op, rfl⟩
    rw [hx, hy]
    cases x <;> cases y <;> simp; rfl
  have hlen := rawOpEvents_length_eq (D := domainOf I) (t := Tid.primeBX)
    (x := Loc.zBx'x) (op := OpType.rd) htraceP hpredL
  rw [hlen.trans (primeBXBlockWord_zBx'x_length I vals)] at hilt_reader
  have hpredW := guessBXZBxprimeWritePred_iff I
  have hlenW := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessBX)
    (x := Loc.zBx'x) (op := OpType.wt) (predL := guessBXZBxprimeWritePred I) htraceG hpredW
  have hfiltW := guessBXBlockWord_zBx'x_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt_writer : i < (rawOpEvents trace Tid.guessBX Loc.zBx'x OpType.wt).length := by
    rw [hlenW, hfiltW, List.length_append, List.length_append, List.length_singleton,
      List.length_map, List.length_flatMap]
    simp only [List.length_map]
    omega
  obtain ⟨ew, hew⟩ := rawNthEvent_exists_of_lt_length hilt_writer
  refine ⟨ew, ?_⟩
  unfold traceRf
  rw [her_tid, her_loc]
  exact ⟨i, hew, hread⟩

theorem traceRf_matches_guessBX_primeBX_zBx'x (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (K0 : ℕ) (hlen1 : inner0Rest.length = K0)
    (js : List (Fin I.n)) (hlen2 : outerRest.length = js.length + 1)
    (houterC : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastC : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (cnt0G : Fin 4) (hcnt0G : cnt0G = 0)
    (hv2 : v2 = Val.cnt (cnt0G + 1))
    (hval1 : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨((cnt0G + 1).val + n + 1) % 4, by omega⟩ : Fin 4))
    (hval2 : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨((cnt0G + 1).val + K0 + ksPrefix (guessBXJsToKs I js) m + n + 1) % 4,
          by omega⟩ : Fin 4))
    (vals : List (Val I)) (htracePAX : trace Tid.primeBX = primeBXBlockWord I vals)
    (cnt0P : Fin 4) (hcnt0P : cnt0P = 0)
    (hvalsVal : ∀ i, i < vals.length →
      vals[i]? = some (Val.cnt (⟨(cnt0P.val + i + 1) % 4, by omega⟩ : Fin 4)))
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.guessBX Loc.zBx'x i = some ew ∧
      rawNthRead trace Tid.primeBX Loc.zBx'x i = some er) :
    ew.val = er.val := by
  subst hcnt0G
  subst hcnt0P
  obtain ⟨i, hew, her⟩ := h
  obtain ⟨v, hv, herval⟩ := rawNthRead_primeBX_zBx'x_eq I vals htracePAX her
  have hvlen : i < vals.length := (List.getElem?_eq_some_iff.mp hv).1
  have hvform := hvalsVal i hvlen
  rw [hvform] at hv
  injection hv with hv
  have hkslen : (guessBXJsToKs I js).length = js.length := by unfold guessBXJsToKs; simp
  have hlen2' : outerRest.length = (guessBXJsToKs I js).length + 1 := by rw [hkslen]; exact hlen2
  have houterC' : ∀ m, m < (guessBXJsToKs I js).length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1 := by
    rw [hkslen]; exact houterC
  have houterLastC' :
      ∃ b vs, outerRest[(guessBXJsToKs I js).length]? = some (b, vs) ∧ vs.length = 1 := by
    rw [hkslen]; exact houterLastC
  rcases rawNthWrite_guessBX_zBx'x_eq I v1 v2 vB0 inner0Rest outerRest htraceGAX
      (guessBXJsToKs I js) hlen2' houterC' houterLastC' hew with
    ⟨hi0, hewval⟩ | ⟨hipos, hcase, e, he, hewval⟩ |
      ⟨m, hm, b, vs, n, e, hbv, hnlt, hvsn, hieq, hewval⟩
  · subst hi0
    rw [hewval, herval, hv2, ← hv]
    congr 1
  · obtain ⟨e', he', he21'⟩ := hval1 (i - 1) (by rw [hlen1] at hcase ⊢; omega)
    rw [he] at he'
    injection he' with he'
    subst he'
    rw [hewval, herval, he21', ← hv]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    omega
  · have hm' : m < js.length + 1 := by rw [hkslen] at hm; omega
    obtain ⟨b', vs', hbv', hval'⟩ := hval2 m hm'
    rw [hbv] at hbv'
    simp only [Option.some.injEq, Prod.mk.injEq] at hbv'
    obtain ⟨hbeq, hvseq⟩ := hbv'
    subst hbeq
    subst hvseq
    obtain ⟨e', he', he21'⟩ := hval' n hnlt
    rw [hvsn] at he'
    injection he' with he'
    subst he'
    rw [hewval, herval, he21', ← hv]
    congr 1
    apply Fin.ext
    simp [Fin.add_def]
    rw [hlen1] at hieq
    omega

/-- `traceRf_matches_guessBX_primeBX_zBx'x` for the general construction. -/
theorem traceRf_matches_guessBX_primeBX_zBx'x_general (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGBX : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (K0 : ℕ) (hlen1 : inner0Rest.length = K0)
    (js : List (Fin I.n)) (hlen2 : outerRest.length = js.length + 1)
    (houterC : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastC : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (hv2raw : v2 = Val.cnt (1 : Fin 4))
    (hval1raw : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.2 = Val.cnt (⟨(1 + n) % 4, by omega⟩ : Fin 4) ∧
      e.2.1 = Val.cnt (⟨(1 + n + 1) % 4, by omega⟩ : Fin 4))
    (hval2raw : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.2 = Val.cnt (⟨(1 + K0 + ksPrefix (guessBXJsToKs I js) m + n) % 4, by omega⟩ : Fin 4) ∧
        e.2.1 = Val.cnt (⟨(1 + K0 + ksPrefix (guessBXJsToKs I js) m + n + 1) % 4, by omega⟩ : Fin 4))
    (vals : List (Val I)) (htracePBX : trace Tid.primeBX = primeBXBlockWord I vals)
    (hvalsVal : ∀ i, i < vals.length → vals[i]? = some (Val.cnt (⟨(i + 1) % 4, by omega⟩ : Fin 4)))
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.guessBX Loc.zBx'x i = some ew ∧
      rawNthRead trace Tid.primeBX Loc.zBx'x i = some er) :
    ew.val = er.val := by
  have hv2 : v2 = Val.cnt ((0 : Fin 4) + 1) := by rw [hv2raw]; congr 1
  have hval1 : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      e.2.1 = Val.cnt (⟨((0 + 1 : Fin 4).val + n + 1) % 4, by omega⟩ : Fin 4) := by
    intro n hn
    obtain ⟨e, he, _, he21⟩ := hval1raw n hn
    exact ⟨e, he, by rw [he21]; congr 2⟩
  have hval2 : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      ∀ n, n < vs.length → ∃ e, vs[n]? = some e ∧
        e.2.1 = Val.cnt (⟨((0 + 1 : Fin 4).val + K0 + ksPrefix (guessBXJsToKs I js) m + n + 1) % 4,
          by omega⟩ : Fin 4) := by
    intro m hm
    obtain ⟨b, vs, hbv, hval2raw'⟩ := hval2raw m hm
    refine ⟨b, vs, hbv, fun n hn => ?_⟩
    obtain ⟨e, he, _, he21⟩ := hval2raw' n hn
    exact ⟨e, he, by rw [he21]; congr 2⟩
  have hvalsVal' : ∀ i, i < vals.length →
      vals[i]? = some (Val.cnt (⟨((0 : Fin 4).val + i + 1) % 4, by omega⟩ : Fin 4)) := by
    intro i hi; rw [hvalsVal i hi]; congr 2; apply Fin.ext; simp
  exact traceRf_matches_guessBX_primeBX_zBx'x I v1 v2 vB0 inner0Rest outerRest htraceGBX K0
    hlen1 js hlen2 houterC houterLastC 0 rfl hv2 hval1 hval2 vals htracePBX 0 rfl hvalsVal' h

/-! ## `rf_matches`: `guessBX`/`checkX` `xB` (Eq. (17))

The mirror of the `guessAX`/`checkX` `xA` branch. -/

/-- `guessBX`'s `xB`-write match, lifted from `xBWritePredCore`. -/
def guessBXXBWritePred (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessBX) : Bool :=
  xBWritePredCore lab.1.loc lab.1.op

theorem guessBXXBWritePred_iff (I : PCPInstance) (lab : ThreadLabel (domainOf I) Tid.guessBX) :
    guessBXXBWritePred I lab = true ↔ (lab.1.loc = Loc.xB ∧ lab.1.op = OpType.wt) := by
  unfold guessBXXBWritePred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  exact xBWritePredCore_iff y z

theorem guessBXXBWritePred_bridge (I : PCPInstance) :
    ∀ (lab : ThreadLabel (domainOf I) Tid.guessBX), lab.1.loc ∈ BridgeLoc →
    guessBXXBWritePred I lab = false := by
  intro lab hloc
  unfold guessBXXBWritePred
  obtain ⟨y, hy⟩ : ∃ y : Loc, lab.1.loc = y := ⟨lab.1.loc, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : OpType, lab.1.op = z := ⟨lab.1.op, rfl⟩
  rw [hy, hz]
  rw [hy] at hloc
  exact xBWritePredCore_bridge y z hloc

/-- `guessBXBlockWord`'s `xB`-writes: the head's `v1`, then offset `0` of
every inner call. -/
theorem guessBXBlockWord_xB_filter_eq (I : PCPInstance) (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I))) :
    (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter (guessBXXBWritePred I)
      = [(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] ++
        inner0Rest.map (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
          ThreadLabel (domainOf I) Tid.guessBX)) ++
        outerRest.flatMap (fun p => p.2.map (fun a =>
          (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX))) := by
  have hinner := guessBXInnerBlockElems_filter I
    (guessBXXBWritePred I) 0
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq12 : q = 1 ∨ q = 2 := by omega
      rcases hq12 with rfl | rfl
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zBx'x, OpType.wt with
          | Loc.xB, OpType.wt => true | _, _ => false) = false)
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zBxx', OpType.rd with
          | Loc.xB, OpType.wt => true | _, _ => false) = false))
  have houter := fun (b : Val I × Val I) (vs : List (Val I × Val I × Val I)) =>
    guessBXOuterBlockElems_filter I b vs
    (guessBXXBWritePred I) 0
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX))
    (fun a => rfl)
    (fun a => rfl)
    (by
      intro a q b0 hq hget
      have hqlt : q < 3 := (List.getElem?_eq_some_iff.mp hget).1
      have hq12 : q = 1 ∨ q = 2 := by omega
      rcases hq12 with rfl | rfl
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zBx'x, OpType.wt with
          | Loc.xB, OpType.wt => true | _, _ => false) = false)
      · simp only [guessBXInnerBlockElems, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at hget
        rw [← hget]
        exact (by decide : (match Loc.zBxx', OpType.rd with
          | Loc.xB, OpType.wt => true | _, _ => false) = false))
    (by
      intro b0 hb0
      exact guessBXXBWritePred_bridge I b0 hb0)
  unfold guessBXBlockWord
  simp only [List.filter_append, hinner]
  have hz1 : guessBXXBWritePred I (⟨EventLabel.wt Tid.guessBX Loc.zBxy vB0.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    guessBXXBWritePred_bridge I _ (by decide : Loc.zBxy ∈ BridgeLoc)
  have hz2 : guessBXXBWritePred I (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = true := by
    unfold guessBXXBWritePred
    exact (by decide : (match Loc.xB, OpType.wt with
      | Loc.xB, OpType.wt => true | _, _ => false) = true)
  have hz3 : guessBXXBWritePred I (⟨EventLabel.wt Tid.guessBX Loc.zBx'x v2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false := by
    unfold guessBXXBWritePred
    exact (by decide : (match Loc.zBx'x, OpType.wt with
      | Loc.xB, OpType.wt => true | _, _ => false) = false)
  have hz4 : guessBXXBWritePred I (⟨EventLabel.rd Tid.guessBX Loc.ellByx vB0.2, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX) = false :=
    guessBXXBWritePred_bridge I _ (by decide : Loc.ellByx ∈ BridgeLoc)
  simp only [List.filter_cons, List.filter_nil, hz1, hz2, hz3, hz4,
    List.append_nil, if_true, if_false, Bool.false_eq_true]
  rw [list_filter_flatMap_distrib]
  congr 1
  apply List.flatMap_congr
  intro p _
  exact houter p.1 p.2

/-- `guessBX`'s `i`-th `xB`-write is the head's `v1` (`i = 0`), an
`inner0Rest` entry's `.1`, or an `outerRest` entry's `.1` located through
`ksPrefix`. -/
theorem rawNthWrite_guessBX_xB_eq (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htrace : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (ks : List ℕ) (hlenOuter : outerRest.length = ks.length + 1)
    (hpreOuter : ∀ m, m < ks.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      ks[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[ks.length]? = some (b, vs) ∧ vs.length = 1)
    {i : ℕ} {ew : Event (domainOf I)}
    (h : rawNthWrite trace Tid.guessBX Loc.xB i = some ew) :
    (i = 0 ∧ ew.val = v1) ∨
    (1 ≤ i ∧ i - 1 < inner0Rest.length ∧ ∃ e, inner0Rest[i - 1]? = some e ∧ ew.val = e.1) ∨
    (∃ m, m < ks.length + 1 ∧ ∃ b vs n e, outerRest[m]? = some (b, vs) ∧ n < vs.length ∧
      vs[n]? = some e ∧ i = 1 + inner0Rest.length + ksPrefix ks m + n ∧ ew.val = e.1) := by
  set ev : Val I × Val I × Val I → ThreadLabel (domainOf I) Tid.guessBX :=
    (fun a => (⟨EventLabel.wt Tid.guessBX Loc.xB a.1, rfl⟩ :
      ThreadLabel (domainOf I) Tid.guessBX)) with hev
  have hpredL := guessBXXBWritePred_iff I
  have hlen_eq := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessBX)
    (x := Loc.xB) (op := OpType.wt) (predL := guessBXXBWritePred I) htrace hpredL
  have hfilt : (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
      (guessBXXBWritePred I)
      = [(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)] ++
        inner0Rest.map ev ++ outerRest.flatMap (fun p => p.2.map ev) := by
    rw [hev]; exact guessBXBlockWord_xB_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt0 : i < (rawOpEvents trace Tid.guessBX Loc.xB OpType.wt).length :=
    (List.getElem?_eq_some_iff.mp h).1
  rw [hlen_eq, hfilt, List.length_append, List.length_append, List.length_singleton,
    List.length_map] at hilt0
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    left
    refine ⟨rfl, ?_⟩
    obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
      (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessBXXBWritePred I) 0
      (⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ : ThreadLabel (domainOf I) Tid.guessBX)
      (by rw [hfilt]; rfl)
    have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessBX)
      (l := guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
    have hraw : rawNthEvent trace Tid.guessBX Loc.xB OpType.wt 0 = some ew := h
    rw [hraw] at hconn
    injection hconn with hconn
    rw [hconn]
    rfl
  · rcases Nat.lt_or_ge (i - 1) inner0Rest.length with hcase | hcase
    · right; left
      refine ⟨by omega, hcase, ?_⟩
      obtain ⟨e, he⟩ : ∃ e, inner0Rest[i - 1]? = some e :=
        ⟨inner0Rest[i-1]'hcase, List.getElem?_eq_getElem hcase⟩
      have hgetf :
          ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
            (guessBXXBWritePred I))[i]? = some (ev e) := by
        rw [hfilt, List.getElem?_append_left (by simp; omega),
          List.getElem?_append_right (by simp; omega), List.length_singleton,
          List.getElem?_map, he]
        rfl
      obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
        (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessBXXBWritePred I) i
        (ev e) hgetf
      have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessBX)
        (l := guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
      have hraw : rawNthEvent trace Tid.guessBX Loc.xB OpType.wt i = some ew := h
      rw [hraw] at hconn
      refine ⟨e, he, ?_⟩
      injection hconn with hconn
      rw [hconn]
      rfl
    · right; right
      have hlen_outer_flat :
          (outerRest.flatMap (fun p => p.2.map ev)).length = ksPrefix ks ks.length + 1 := by
        have h1 : (outerRest.flatMap (fun p => p.2.map ev)).length
            = (outerRest.map (fun p => (p.2.map ev).length)).sum := by
          rw [List.length_flatMap]
        have h2 : (outerRest.map (fun p => (p.2.map ev).length)).sum
            = (outerRest.map (fun p => p.2.length)).sum := by
          congr 1
          apply List.map_congr_left
          intro p _
          exact List.length_map ..
        have h3 : (outerRest.map (fun p => p.2.length)).sum = (ks.map (· + 1)).sum + 1 :=
          sum_snd_length_of_forall_getElem outerRest ks hlenOuter hpreOuter hlastOuter
        rw [h1, h2, h3, ksPrefix_eq_sum]
      have hj' : i - 1 - inner0Rest.length < ksPrefix ks ks.length + 1 := by
        rw [← hlen_outer_flat]; omega
      obtain ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, hjeq, hgetflat⟩ :=
        ksPrefix_flatMap_map_getElem outerRest ks ev
          hlenOuter hpreOuter hlastOuter (i - 1 - inner0Rest.length) hj'
      have hgetf :
          ((guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest).filter
            (guessBXXBWritePred I))[i]? = some (ev b) := by
        rw [hfilt, List.getElem?_append_right (by simp; omega)]
        have hlen12 : ([(⟨EventLabel.wt Tid.guessBX Loc.xB v1, rfl⟩ :
            ThreadLabel (domainOf I) Tid.guessBX)] ++ inner0Rest.map ev).length
            = 1 + inner0Rest.length := by simp; omega
        rw [hlen12]
        have hidxeq : i - (1 + inner0Rest.length) = i - 1 - inner0Rest.length := by omega
        rw [hidxeq]
        exact hgetflat
      obtain ⟨k, hzip⟩ := zipIdx_filter_getElem_of_filter_getElem
        (guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) (guessBXXBWritePred I) i
        (ev b) hgetf
      have hconn := rawNthEvent_of_zipIdx_filter (trace := trace) (t := Tid.guessBX)
        (l := guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest) htrace hpredL hzip
      have hraw : rawNthEvent trace Tid.guessBX Loc.xB OpType.wt i = some ew := h
      rw [hraw] at hconn
      refine ⟨m, hm, a, vs, n, b, hlm, hnlt, hvsn, by omega, ?_⟩
      injection hconn with hconn
      rw [hconn]
      rfl

/-- `rf_total` for the `checkX`/`xB` branch (Eq. (17)), as
`traceRf_total_checkX_xA`. -/
theorem traceRf_total_checkX_xB (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v0 : I.Γ) (kws : List (Fin 4 × Option I.Γ))
    (htraceV : trace Tid.checkX = checkXBlockWord I v0 kws)
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceG : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (hsum : 1 + inner0Rest.length + (outerRest.map (fun p => p.2.length)).sum = 1 + kws.length)
    {er : Event (domainOf I)} (her_tid : er.tid = Tid.checkX) (her_loc : er.loc = Loc.xB)
    (her : er ∈ traceEvents trace) (herop : er.op = .rd) :
    ∃ ew, traceRf I trace ew er := by
  have hmemT : er ∈ traceEventsOf trace Tid.checkX := mem_traceEvents_of_tid her her_tid
  have hmemOp : er ∈ rawOpEvents trace Tid.checkX Loc.xB OpType.rd := by
    unfold rawOpEvents
    exact List.mem_filter.mpr ⟨hmemT, by rw [her_loc, herop]; rfl⟩
  set i := (rawOpEvents trace Tid.checkX Loc.xB OpType.rd).idxOf er with hidef
  have hread : rawNthRead trace Tid.checkX Loc.xB i = some er := rawNthEvent_of_mem hmemOp
  have hilt_reader : i < (rawOpEvents trace Tid.checkX Loc.xB OpType.rd).length :=
    List.idxOf_lt_length_iff.mpr hmemOp
  have hlen := rawOpEvents_length_eq (D := domainOf I) (t := Tid.checkX)
    (x := Loc.xB) (op := OpType.rd) (predL := checkXXBReadPred I) htraceV
    (checkXXBReadPred_iff I)
  have hlen2 : ((checkXBlockWord I v0 kws).filter (checkXXBReadPred I)).length
      = 1 + kws.length := by
    unfold checkXBlockWord
    rw [List.filter_append, List.length_append, checkXBlock0Elems_xB_read_filter,
      checkXBlockRestElems_xB_read_filter, List.length_singleton]
  rw [hlen.trans hlen2] at hilt_reader
  have hlenW := rawOpEvents_length_eq (D := domainOf I) (t := Tid.guessBX)
    (x := Loc.xB) (op := OpType.wt) (predL := guessBXXBWritePred I) htraceG
    (guessBXXBWritePred_iff I)
  have hfiltW := guessBXBlockWord_xB_filter_eq I v1 v2 vB0 inner0Rest outerRest
  have hilt_writer : i < (rawOpEvents trace Tid.guessBX Loc.xB OpType.wt).length := by
    rw [hlenW, hfiltW, List.length_append, List.length_append, List.length_singleton,
      List.length_map, List.length_flatMap]
    simp only [List.length_map]
    omega
  obtain ⟨ew, hew⟩ := rawNthEvent_exists_of_lt_length hilt_writer
  refine ⟨ew, ?_⟩
  unfold traceRf
  rw [her_tid, her_loc]
  exact ⟨i, hew, hread⟩

/-- `traceRf` for the `guessBX`/`checkX` `xB` pair (Eq. (17)), as
`traceRf_matches_checkX_guessAX_xA`, with the flattened `β`-word. -/
theorem traceRf_matches_checkX_guessBX_xB (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (ks : List ℕ) (hlenOuter : outerRest.length = ks.length + 1)
    (hpreOuter : ∀ m, m < ks.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      ks[m]? = some km ∧ vs.length = km + 1)
    (hlastOuter : ∃ b vs, outerRest[ks.length]? = some (b, vs) ∧ vs.length = 1)
    (v0 : I.Γ) (kws : List (Fin 4 × Option I.Γ))
    (htraceVX : trace Tid.checkX = checkXBlockWord I v0 kws)
    (c0 : I.Γ) (cs : List I.Γ)
    (hv0eq : v0 = c0)
    (hv1eq : v1 = Val.xTag (Tid.guessBX, true) (some c0))
    (hinnerAgree : ∀ n, n < inner0Rest.length → ∃ e, inner0Rest[n]? = some e ∧
      ∃ c, cs[n]? = some c ∧ e.1 = Val.xTag (Tid.guessBX, false) (some c))
    (houterAgree : ∀ m, m < ks.length + 1 → ∀ b vs, outerRest[m]? = some (b, vs) →
      ∀ n e, n < vs.length → vs[n]? = some e →
      e.1 = Val.xTag (Tid.guessBX, false) (cs[inner0Rest.length + ksPrefix ks m + n]?))
    (hkwsAgree : ∀ i, i < kws.length → ∃ kw, kws[i]? = some kw ∧ kw.2 = cs[i]?)
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.guessBX Loc.xB i = some ew ∧
      rawNthRead trace Tid.checkX Loc.xB i = some er) :
    ew.val = er.val := by
  obtain ⟨i, hew, her⟩ := h
  rcases rawNthWrite_guessBX_xB_eq I v1 v2 vB0 inner0Rest outerRest htraceGAX ks hlenOuter
    hpreOuter hlastOuter hew with
    ⟨hi0, hewval⟩ | ⟨hipos, hilt, e, he, hewval⟩ |
    ⟨m, hm, b, vs, n, e, hbv, hnlt, hvsn, hieq, hewval⟩
  · subst hi0
    rcases rawNthRead_checkX_xB_eq I v0 kws htraceVX her with
      ⟨-, herval⟩ | ⟨kw, hkw, hipos, herval⟩
    · rw [hewval, herval, hv1eq, hv0eq]
    · omega
  · rcases rawNthRead_checkX_xB_eq I v0 kws htraceVX her with
      ⟨hi0, herval⟩ | ⟨kw, hkw, hipos', herval⟩
    · omega
    · obtain ⟨e1, he1, c, hcs, hev⟩ := hinnerAgree (i - 1) hilt
      rw [he] at he1
      injection he1 with he1
      subst he1
      have hklt : i - 1 < kws.length := (List.getElem?_eq_some_iff.mp hkw).1
      obtain ⟨kw1, hkw1, hkweq⟩ := hkwsAgree (i - 1) hklt
      rw [hkw] at hkw1
      injection hkw1 with hkw1
      subst hkw1
      rw [hewval, herval, hev, hkweq, hcs]
  · rcases rawNthRead_checkX_xB_eq I v0 kws htraceVX her with
      ⟨hi0, herval⟩ | ⟨kw, hkw, hipos', herval⟩
    · omega
    · have hev := houterAgree m hm b vs hbv n e hnlt hvsn
      have hii : i - 1 = inner0Rest.length + ksPrefix ks m + n := by omega
      have hklt : i - 1 < kws.length := (List.getElem?_eq_some_iff.mp hkw).1
      obtain ⟨kw1, hkw1, hkweq⟩ := hkwsAgree (i - 1) hklt
      rw [hkw] at hkw1
      injection hkw1 with hkw1
      subst hkw1
      rw [hii] at hkweq
      rw [hewval, herval, hev, hkweq]

/-- `traceRf_matches_checkX_guessBX_xB` for the general construction. -/
theorem traceRf_matches_checkX_guessBX_xB_general (I : PCPInstance)
    {trace : ∀ t, Word (ThreadLabel (domainOf I) t)}
    (j0 : Fin I.n) (js : List (Fin I.n)) (K0 : ℕ) (hlen0 : (I.β j0).length = K0 + 1)
    (v1 v2 : Val I) (vB0 : Val I × Val I)
    (inner0Rest : List (Val I × Val I × Val I))
    (outerRest : List ((Val I × Val I) × List (Val I × Val I × Val I)))
    (htraceGAX : trace Tid.guessBX = guessBXBlockWord I v1 v2 vB0 inner0Rest outerRest)
    (hlen1A : inner0Rest.length = K0)
    (hlen2A : outerRest.length = js.length + 1)
    (houterCA : ∀ m, m < js.length → ∃ b vs km, outerRest[m]? = some (b, vs) ∧
      (guessBXJsToKs I js)[m]? = some km ∧ vs.length = km + 1)
    (houterLastCA : ∃ b vs, outerRest[js.length]? = some (b, vs) ∧ vs.length = 1)
    (hv1rawA : ∃ j : Fin (GuessBX.maxLen I + 2), j.val = 1 ∧
      v1 = Val.xTag (Tid.guessBX, true) (GuessBX.jthLetter I (some j0) j))
    (hinnerrawA : ∀ n, n < inner0Rest.length → ∃ e j, inner0Rest[n]? = some e ∧ j.val = n + 2 ∧
      e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some j0) j))
    (houterrawA : ∀ m, m < js.length + 1 → ∃ b vs, outerRest[m]? = some (b, vs) ∧
      (m < js.length → ∃ w, js[m]? = some w ∧
        ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
          e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I (some w) j)) ∧
      (m = js.length → ∀ n, n < vs.length → ∃ e j, vs[n]? = some e ∧ j.val = n + 1 ∧
        e.1 = Val.xTag (Tid.guessBX, false) (GuessBX.jthLetter I none j)))
    (v0 : I.Γ) (kws : List (Fin 4 × Option I.Γ))
    (htraceVX : trace Tid.checkX = checkXBlockWord I v0 kws)
    (c0 : I.Γ) (cs : List I.Γ) (hflat : ((j0 :: js).map I.β).flatten = c0 :: cs) (hv0 : v0 = c0)
    (hvalVX : ∀ i, i < kws.length →
      ∃ w, kws[i]? = some (⟨(1 + i) % 4, by omega⟩, w) ∧ w = cs[i]?)
    {ew er : Event (domainOf I)}
    (h : ∃ i, rawNthWrite trace Tid.guessBX Loc.xB i = some ew ∧
      rawNthRead trace Tid.checkX Loc.xB i = some er) :
    ew.val = er.val := by
  obtain ⟨hv0eq, hv1eq, hinnerAgree, houterAgree, hkwsAgree⟩ :=
    guessBX_checkX_rf_matches I j0 js c0 cs hflat K0 hlen0 v1 inner0Rest outerRest
      hlen1A houterCA hv1rawA hinnerrawA houterrawA v0 hv0 kws hvalVX
  have hkslen : (guessBXJsToKs I js).length = js.length := by unfold guessBXJsToKs; simp
  refine traceRf_matches_checkX_guessBX_xB I v1 v2 vB0 inner0Rest outerRest htraceGAX
    (guessBXJsToKs I js) (by rw [hkslen]; exact hlen2A)
    (by rw [hkslen]; exact houterCA) (by rw [hkslen]; exact houterLastCA)
    v0 kws htraceVX c0 cs hv0eq hv1eq hinnerAgree ?_ hkwsAgree h
  intro m hm b vs hbv n e hnlt hvsn
  rw [hkslen] at hm
  rw [hlen1A]
  exact houterAgree m hm b vs hbv n e hnlt hvsn

/-- For a solved `I`, one trace satisfying `TraceShapes` for which `traceRf`
satisfies `rf_total` and `rf_matches`, and every thread's word is a word of
its program (`IsWord`) and, with `term` appended, reaches its final state. -/
theorem traceRf_valid_general (I : PCPInstance) (hsol : I.HasSolution) :
    ∃ (trace : ∀ t, Word (ThreadLabel (domainOf I) t)),
      TraceShapes I trace ∧
      (∀ {er : Event (domainOf I)}, er ∈ traceEvents trace → er.op = .rd →
        ∃ ew, traceRf I trace ew er) ∧
      (∀ {ew er : Event (domainOf I)}, traceRf I trace ew er → ew.val = er.val) ∧
      (∀ t, (ConcProgOf I t).IsWord ((trace t).map some)) ∧
      (∀ t, (ConcProgOf I t).Reaches ((trace t).map some ++ [none]) (ConcProgOf I t).final) := by
  obtain ⟨j0, js, c0, cs, hjs0, hflat⟩ := I.solution_streams hsol
  have hflatβ : ((j0 :: js).map I.β).flatten = c0 :: cs := by rw [← hjs0.2]; exact hflat
  have hposA : 0 < (I.α j0).length := List.length_pos_of_ne_nil (I.hα j0)
  have hposB : 0 < (I.β j0).length := List.length_pos_of_ne_nil (I.hβ j0)
  have hlenA : (I.α j0).length = (I.α j0).length - 1 + 1 := by omega
  have hlenB : (I.β j0).length = (I.β j0).length - 1 + 1 := by omega
  obtain ⟨v1A, v2A, vB0A, inner0RestA, outerRestA, φ'A, cLastA, hlen1A, hlen2A, houterCA,
    houterLastCA, hv2A, hinnerCntA, houterCntA, hvB01A, hvB02A, houterBA, hv1rawA, hinnerrawA,
    houterrawA, hrunA⟩ :=
    guessAX_general_run I j0 js ((I.α j0).length - 1) hlenA
  obtain ⟨v1B, v2B, vB0B, inner0RestB, outerRestB, φ'B, cLastB, hlen1B, hlen2B, houterCB,
    houterLastCB, hv2B, hinnerCntB, houterCntB, hvB01B, hvB02B, houterBB, hv1rawB, hinnerrawB,
    houterrawB, hrunB⟩ :=
    guessBX_general_run I j0 js ((I.β j0).length - 1) hlenB
  obtain ⟨kwsAY, φ'AY, cLastAY, hlenAY, hvalAY, hrunAY⟩ := guessAY_general_run_val I j0 js
  obtain ⟨kwsBY, φ'BY, cLastBY, hlenBY, hvalBY, hrunBY⟩ := guessBY_general_run_val I j0 js
  obtain ⟨kwsVX, φ'VX, cLastVX, hlenVX, hvalVX, hrunVX⟩ := checkX_general_run_val I c0 cs
  obtain ⟨kwsVY, φ'VY, cLastVY, hlenVY, hvalVY, hrunVY⟩ := checkY_general_run_val I j0 js
  obtain ⟨valsPAX, φ'PAX, cLastPAX, hlenPAX, hvalsPAX, hbPAX, hrunPAX⟩ :=
    primeAX_general_run I cs.length
  obtain ⟨valsPBX, φ'PBX, cLastPBX, hlenPBX, hvalsPBX, hbPBX, hrunPBX⟩ :=
    primeBX_general_run_val I cs.length
  obtain ⟨valsPAY, φ'PAY, cLastPAY, hlenPAY, hvalsPAY, hbPAY, hrunPAY⟩ :=
    primeAY_general_run I js.length
  obtain ⟨valsPBY, φ'PBY, cLastPBY, hlenPBY, hvalsPBY, hbPBY, hrunPBY⟩ :=
    primeBY_general_run I js.length
  obtain ⟨cntsPVX, φ'PVX, cLastPVX, hlenPVX, hvalsPVX, hbPVX, hrunPVX⟩ :=
    primeCheckX_general_run I cs.length
  obtain ⟨cntsPVY, φ'PVY, cLastPVY, hlenPVY, hvalsPVY, hbPVY, hrunPVY⟩ :=
    primeCheckY_general_run I js.length
  have hshapes : TraceShapes I (fun t => match t with
      | .guessAX => guessAXBlockWord I v1A v2A vB0A inner0RestA outerRestA
      | .guessBX => guessBXBlockWord I v1B v2B vB0B inner0RestB outerRestB
      | .guessAY => guessAYBlockWord I j0 kwsAY
      | .guessBY => guessBYBlockWord I j0 kwsBY
      | .checkX => checkXBlockWord I c0 kwsVX
      | .checkY => checkYBlockWord I j0 kwsVY
      | .primeAX => primeAXBlockWord I valsPAX
      | .primeBX => primeBXBlockWord I valsPBX
      | .primeAY => primeAYBlockWord I valsPAY
      | .primeBY => primeBYBlockWord I valsPBY
      | .primeCheckX => primeCheckXBlockWord I cntsPVX
      | .primeCheckY => primeCheckYBlockWord I cntsPVY) := by
    refine ⟨?_, ?_, ⟨j0, kwsAY, rfl⟩, ⟨j0, kwsBY, rfl⟩,
      ⟨valsPAX, rfl⟩, ⟨valsPBX, rfl⟩,
      ⟨valsPAY, rfl⟩, ⟨valsPBY, rfl⟩, ⟨cntsPVX, rfl⟩, ⟨cntsPVY, rfl⟩,
      ⟨c0, kwsVX, rfl⟩, ⟨j0, kwsVY, rfl⟩⟩
    · refine ⟨((I.α j0).length - 1) :: guessAXJsToKs I js, js.length, v1A, v2A, vB0A, ?_,
        inner0RestA, outerRestA, ⟨_, rfl, hlen1A⟩, hlen2A, ?_, houterLastCA, rfl⟩
      · simp only [List.length_cons]
        have : (guessAXJsToKs I js).length = js.length := by unfold guessAXJsToKs; simp
        omega
      · intro m hm
        obtain ⟨b, vs, km, hbv, hkm, hvs⟩ := houterCA m hm
        exact ⟨b, vs, km, hbv, by simpa using hkm, hvs⟩
    · refine ⟨((I.β j0).length - 1) :: guessBXJsToKs I js, js.length, v1B, v2B, vB0B, ?_,
        inner0RestB, outerRestB, ⟨_, rfl, hlen1B⟩, hlen2B, ?_, houterLastCB, rfl⟩
      · simp only [List.length_cons]
        have : (guessBXJsToKs I js).length = js.length := by unfold guessBXJsToKs; simp
        omega
      · intro m hm
        obtain ⟨b, vs, km, hbv, hkm, hvs⟩ := houterCB m hm
        exact ⟨b, vs, km, hbv, by simpa using hkm, hvs⟩
  refine ⟨_, hshapes, ?_, ?_, ?_⟩
  · intro er her herop
    match het : er.tid with
    | .guessAX =>
        rcases traceRf_reads_guessAX I hshapes (mem_traceEvents_of_tid her het) herop with
          hloc | hloc
        · have hsum := guessAX_checkX_rf_total I j0 js c0 cs hflat inner0RestA outerRestA
            hlen1A hlen2A houterCA houterLastCA kwsVX hlenVX
          exact traceRf_total_guessAX_zAxx' I v1A v2A vB0A inner0RestA outerRestA rfl valsPAX rfl
            (primeAX_guessAX_zAxx'_rf_total I cs inner0RestA outerRestA kwsVX hlenVX hsum valsPAX
              hlenPAX)
            het hloc her herop
        · exact traceRf_total_guessAX_ellAyx I v1A v2A vB0A inner0RestA outerRestA rfl j0 kwsAY
            rfl (guessAY_guessAX_ellAyx_rf_total I js kwsAY hlenAY outerRestA hlen2A)
            het hloc her herop
    | .guessBX =>
        rcases traceRf_reads_guessBX I hshapes (mem_traceEvents_of_tid her het) herop with
          hloc | hloc
        · have hsum := guessBX_checkX_rf_total I j0 js c0 cs hflatβ inner0RestB outerRestB
            hlen1B hlen2B houterCB houterLastCB kwsVX hlenVX
          exact traceRf_total_guessBX_zBxx' I v1B v2B vB0B inner0RestB outerRestB rfl valsPBX rfl
            (primeBX_guessBX_zBxx'_rf_total I cs inner0RestB outerRestB kwsVX hlenVX hsum valsPBX
              hlenPBX)
            het hloc her herop
        · exact traceRf_total_guessBX_ellByx I v1B v2B vB0B inner0RestB outerRestB rfl j0 kwsBY
            rfl (guessBY_guessBX_ellByx_rf_total I js kwsBY hlenBY outerRestB hlen2B)
            het hloc her herop
    | .guessAY =>
        rcases traceRf_reads_guessAY I hshapes (mem_traceEvents_of_tid her het) herop with
          hloc | hloc
        · exact traceRf_total_guessAY_zAxy I j0 kwsAY rfl v1A v2A vB0A inner0RestA outerRestA rfl
            (guessAX_guessAY_zAxy_rf_total I js outerRestA hlen2A kwsAY hlenAY)
            het hloc her herop
        · exact traceRf_total_guessAY_zAyy' I j0 kwsAY rfl valsPAY rfl
            (primeAY_guessAY_zAyy'_rf_total I js valsPAY hlenPAY kwsAY hlenAY)
            het hloc her herop
    | .guessBY =>
        rcases traceRf_reads_guessBY I hshapes (mem_traceEvents_of_tid her het) herop with
          hloc | hloc
        · exact traceRf_total_guessBY_zBxy I j0 kwsBY rfl v1B v2B vB0B inner0RestB outerRestB rfl
            (guessBX_guessBY_zBxy_rf_total I js outerRestB hlen2B kwsBY hlenBY)
            het hloc her herop
        · exact traceRf_total_guessBY_zByy' I j0 kwsBY rfl valsPBY rfl
            (primeBY_guessBY_zByy'_rf_total I js valsPBY hlenPBY kwsBY hlenBY)
            het hloc her herop
    | .primeAX =>
        have hloc := traceRf_reads_primeAX I hshapes (mem_traceEvents_of_tid her het) herop
        exact traceRf_total_primeAX_zAx'x I valsPAX rfl v1A v2A vB0A inner0RestA outerRestA rfl
          (by
            have hsum := guessAX_checkX_rf_total I j0 js c0 cs hflat inner0RestA outerRestA
              hlen1A hlen2A houterCA houterLastCA kwsVX hlenVX
            exact guessAX_primeAX_zAx'x_rf_total I cs inner0RestA outerRestA kwsVX hlenVX hsum
              valsPAX hlenPAX)
          het hloc her herop
    | .primeBX =>
        have hloc := traceRf_reads_primeBX I hshapes (mem_traceEvents_of_tid her het) herop
        exact traceRf_total_primeBX_zBx'x I valsPBX rfl v1B v2B vB0B inner0RestB outerRestB rfl
          (by
            have hsum := guessBX_checkX_rf_total I j0 js c0 cs hflatβ inner0RestB outerRestB
              hlen1B hlen2B houterCB houterLastCB kwsVX hlenVX
            exact guessBX_primeBX_zBx'x_rf_total I cs inner0RestB outerRestB kwsVX hlenVX hsum
              valsPBX hlenPBX)
          het hloc her herop
    | .primeAY =>
        have hloc := traceRf_reads_primeAY I hshapes (mem_traceEvents_of_tid her het) herop
        exact traceRf_total_primeAY_zAy'y I valsPAY rfl j0 kwsAY rfl
          (guessAY_primeAY_zAy'y_rf_total I js kwsAY hlenAY valsPAY hlenPAY)
          het hloc her herop
    | .primeBY =>
        have hloc := traceRf_reads_primeBY I hshapes (mem_traceEvents_of_tid her het) herop
        exact traceRf_total_primeBY_zBy'y I valsPBY rfl j0 kwsBY rfl
          (guessBY_primeBY_zBy'y_rf_total I js kwsBY hlenBY valsPBY hlenPBY)
          het hloc her herop
    | .checkX =>
        rcases traceRf_reads_checkX I hshapes (mem_traceEvents_of_tid her het) herop with
          hloc | hloc | hloc | hloc
        · exact traceRf_total_checkX_xA I c0 kwsVX rfl v1A v2A vB0A inner0RestA outerRestA rfl
            (by
              have hsum := guessAX_checkX_rf_total I j0 js c0 cs hflat inner0RestA outerRestA
                hlen1A hlen2A houterCA houterLastCA kwsVX hlenVX
              omega)
            het hloc her herop
        · exact traceRf_total_checkX_xB I c0 kwsVX rfl v1B v2B vB0B inner0RestB outerRestB rfl
            (by
              have hsum := guessBX_checkX_rf_total I j0 js c0 cs hflatβ inner0RestB outerRestB
                hlen1B hlen2B houterCB houterLastCB kwsVX hlenVX
              omega)
            het hloc her herop
        · exact traceRf_total_checkX_xAprime I cs c0 kwsVX hlenVX rfl cntsPVX hlenPVX rfl
            het hloc her herop
        · exact traceRf_total_checkX_xBprime I cs c0 kwsVX hlenVX rfl cntsPVX hlenPVX rfl
            het hloc her herop
    | .checkY =>
        rcases traceRf_reads_checkY I hshapes (mem_traceEvents_of_tid her het) herop with
          hloc | hloc | hloc | hloc
        · exact traceRf_total_checkY_yA I js j0 kwsAY hlenAY rfl j0 kwsVY hlenVY rfl
            het hloc her herop
        · exact traceRf_total_checkY_yB I js j0 kwsBY hlenBY rfl j0 kwsVY hlenVY rfl
            het hloc her herop
        · exact traceRf_total_checkY_yAprime I js j0 kwsVY hlenVY rfl cntsPVY hlenPVY rfl
            het hloc her herop
        · exact traceRf_total_checkY_yBprime I js j0 kwsVY hlenVY rfl cntsPVY hlenPVY rfl
            het hloc her herop
    | .primeCheckX =>
        rcases traceRf_reads_primeCheckX I hshapes (mem_traceEvents_of_tid her het) herop with
          hloc | hloc | hloc | hloc
        · exact traceRf_total_primeCheckX_xAprime I cs cntsPVX hlenPVX rfl valsPAX hlenPAX rfl
            het hloc her herop
        · exact traceRf_total_primeCheckX_xBprime I cs cntsPVX hlenPVX rfl valsPBX hlenPBX rfl
            het hloc her herop
        · exact traceRf_total_primeCheckX_xA I cs cntsPVX hlenPVX rfl c0 kwsVX hlenVX rfl
            het hloc her herop
        · exact traceRf_total_primeCheckX_xB I cs cntsPVX hlenPVX rfl c0 kwsVX hlenVX rfl
            het hloc her herop
    | .primeCheckY =>
        rcases traceRf_reads_primeCheckY I hshapes (mem_traceEvents_of_tid her het) herop with
          hloc | hloc | hloc | hloc
        · exact traceRf_total_primeCheckY_yAprime I js cntsPVY hlenPVY rfl valsPAY hlenPAY rfl
            het hloc her herop
        · exact traceRf_total_primeCheckY_yBprime I js cntsPVY hlenPVY rfl valsPBY hlenPBY rfl
            het hloc her herop
        · exact traceRf_total_primeCheckY_yA I js cntsPVY hlenPVY rfl j0 kwsVY hlenVY rfl
            het hloc her herop
        · exact traceRf_total_primeCheckY_yB I js cntsPVY hlenPVY rfl j0 kwsVY hlenVY rfl
            het hloc her herop
  · intro ew er h
    unfold traceRf at h
    match het : er.tid with
    | .guessAX =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            exact traceRf_matches_guessAX_zAxx'_general I cs valsPAX rfl hlenPAX hvalsPAX v1A v2A vB0A
              inner0RestA outerRestA rfl _ hlen1A js hlen2A houterCA houterLastCA hinnerCntA houterCntA
              h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            exact traceRf_matches_guessAX_guessAY_ellAyx_general I j0 js kwsAY rfl hlenAY hvalAY v1A v2A vB0A
              inner0RestA outerRestA rfl hlen2A hvB02A houterBA
              h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .guessAY =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            exact traceRf_matches_primeAY_guessAY_zAyy'_general I valsPAY rfl hvalsPAY j0 kwsAY rfl
              (fun i hi => (hvalAY i hi).imp (fun w hw => hw.1)) h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            exact traceRf_matches_guessAY_guessAX_zAxy_general I v1A v2A vB0A inner0RestA outerRestA rfl
              hvB01A
              (fun m hm => by
                rw [hlen2A] at hm; obtain ⟨b, vs, hbv, hb1, _⟩ := houterBA m hm
                exact ⟨b, vs, hbv, hb1⟩)
              j0 kwsAY rfl (fun i hi => (hvalAY i hi).imp (fun w hw => hw.1))
              h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .guessBX =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            exact traceRf_matches_guessBX_zBxx'_general I cs valsPBX rfl hlenPBX hvalsPBX v1B v2B vB0B
              inner0RestB outerRestB rfl _ hlen1B js hlen2B houterCB houterLastCB hinnerCntB houterCntB
              h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            exact traceRf_matches_guessBX_guessBY_ellByx_general I j0 js kwsBY rfl hlenBY hvalBY v1B v2B vB0B
              inner0RestB outerRestB rfl hlen2B hvB02B houterBB
              h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .guessBY =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            exact traceRf_matches_primeBY_guessBY_zByy'_general I valsPBY rfl hvalsPBY j0 kwsBY rfl
              (fun i hi => (hvalBY i hi).imp (fun w hw => hw.1)) h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            exact traceRf_matches_guessBY_guessBX_zBxy_general I v1B v2B vB0B inner0RestB outerRestB rfl
              hvB01B
              (fun m hm => by
                rw [hlen2B] at hm; obtain ⟨b, vs, hbv, hb1, _⟩ := houterBB m hm
                exact ⟨b, vs, hbv, hb1⟩)
              j0 kwsBY rfl (fun i hi => (hvalBY i hi).imp (fun w hw => hw.1))
              h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .primeAX =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            exact traceRf_matches_guessAX_primeAX_zAx'x_general I v1A v2A vB0A inner0RestA outerRestA
              rfl _ hlen1A js hlen2A houterCA houterLastCA hv2A hinnerCntA houterCntA valsPAX rfl hvalsPAX
              h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .primeAY =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            exact traceRf_matches_guessAY_primeAY_zAy'y_general I j0 kwsAY rfl
              (fun i hi => (hvalAY i hi).imp (fun w hw => hw.1)) valsPAY rfl hvalsPAY h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .primeBX =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            exact traceRf_matches_guessBX_primeBX_zBx'x_general I v1B v2B vB0B inner0RestB outerRestB
              rfl _ hlen1B js hlen2B houterCB houterLastCB hv2B hinnerCntB houterCntB valsPBX rfl hvalsPBX
              h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .primeBY =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            exact traceRf_matches_guessBY_primeBY_zBy'y_general I j0 kwsBY rfl
              (fun i hi => (hvalBY i hi).imp (fun w hw => hw.1)) valsPBY rfl hvalsPBY h
    | .checkX =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            exact traceRf_matches_checkX_guessAX_xA_general I j0 js _ hlenA v1A v2A vB0A inner0RestA
              outerRestA rfl hlen1A hlen2A houterCA houterLastCA hv1rawA hinnerrawA houterrawA c0 kwsVX rfl
              c0 cs hflat rfl hvalVX h
        | .xB =>
            rw [hel] at h
            exact traceRf_matches_checkX_guessBX_xB_general I j0 js _ hlenB v1B v2B vB0B inner0RestB
              outerRestB rfl hlen1B hlen2B houterCB houterLastCB hv1rawB hinnerrawB houterrawB c0 kwsVX rfl
              c0 cs hflatβ rfl hvalVX h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            exact traceRf_matches_primeCheckX_checkX_xAprime_general I cntsPVX rfl hvalsPVX c0 kwsVX rfl
              (fun i hi => (hvalVX i hi).imp (fun w hw => hw.1)) h
        | .xB' =>
            rw [hel] at h
            exact traceRf_matches_primeCheckX_checkX_xBprime_general I cntsPVX rfl hvalsPVX c0 kwsVX rfl
              (fun i hi => (hvalVX i hi).imp (fun w hw => hw.1)) h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .checkY =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            exact traceRf_matches_checkY_guessAY_yA_general I j0 js kwsAY rfl hlenAY hvalAY kwsVY rfl
              hlenVY hvalVY h
        | .yB =>
            rw [hel] at h
            exact traceRf_matches_checkY_guessBY_yB_general I j0 js kwsBY rfl hlenBY hvalBY kwsVY rfl
              hlenVY hvalVY h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            exact traceRf_matches_primeCheckY_checkY_yAprime_general I cntsPVY rfl hvalsPVY j0 kwsVY rfl
              (fun i hi => (hvalVY i hi).imp (fun w hw => hw.1)) h
        | .yB' =>
            rw [hel] at h
            exact traceRf_matches_primeCheckY_checkY_yBprime_general I cntsPVY rfl hvalsPVY j0 kwsVY rfl
              (fun i hi => (hvalVY i hi).imp (fun w hw => hw.1)) h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .primeCheckX =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            exact traceRf_matches_checkX_primeCheckX_xA_general I c0 kwsVX rfl
              (fun i hi => (hvalVX i hi).imp (fun w hw => hw.1)) cntsPVX rfl hvalsPVX h
        | .xB =>
            rw [hel] at h
            exact traceRf_matches_checkX_primeCheckX_xB_general I c0 kwsVX rfl
              (fun i hi => (hvalVX i hi).imp (fun w hw => hw.1)) cntsPVX rfl hvalsPVX h
        | .yA =>
            rw [hel] at h
            simp at h
        | .yB =>
            rw [hel] at h
            simp at h
        | .xA' =>
            rw [hel] at h
            exact traceRf_matches_primeCheckX_xA' I valsPAX rfl cntsPVX rfl h
        | .xB' =>
            rw [hel] at h
            exact traceRf_matches_primeCheckX_xB' I valsPBX rfl cntsPVX rfl h
        | .yA' =>
            rw [hel] at h
            simp at h
        | .yB' =>
            rw [hel] at h
            simp at h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
    | .primeCheckY =>
        rw [het] at h
        match hel : er.loc with
        | .xA =>
            rw [hel] at h
            simp at h
        | .xB =>
            rw [hel] at h
            simp at h
        | .yA =>
            rw [hel] at h
            exact traceRf_matches_checkY_primeCheckY_yA_general I j0 kwsVY rfl
              (fun i hi => (hvalVY i hi).imp (fun w hw => hw.1)) cntsPVY rfl hvalsPVY h
        | .yB =>
            rw [hel] at h
            exact traceRf_matches_checkY_primeCheckY_yB_general I j0 kwsVY rfl
              (fun i hi => (hvalVY i hi).imp (fun w hw => hw.1)) cntsPVY rfl hvalsPVY h
        | .xA' =>
            rw [hel] at h
            simp at h
        | .xB' =>
            rw [hel] at h
            simp at h
        | .yA' =>
            rw [hel] at h
            exact traceRf_matches_primeCheckY_yA' I valsPAY rfl cntsPVY rfl h
        | .yB' =>
            rw [hel] at h
            exact traceRf_matches_primeCheckY_yB' I valsPBY rfl cntsPVY rfl h
        | .zAxx' =>
            rw [hel] at h
            simp at h
        | .zAyy' =>
            rw [hel] at h
            simp at h
        | .zBxx' =>
            rw [hel] at h
            simp at h
        | .zByy' =>
            rw [hel] at h
            simp at h
        | .zAxy =>
            rw [hel] at h
            simp at h
        | .zBxy =>
            rw [hel] at h
            simp at h
        | .ellAyx =>
            rw [hel] at h
            simp at h
        | .ellByx =>
            rw [hel] at h
            simp at h
        | .zAx'x =>
            rw [hel] at h
            simp at h
        | .zAy'y =>
            rw [hel] at h
            simp at h
        | .zBx'x =>
            rw [hel] at h
            simp at h
        | .zBy'y =>
            rw [hel] at h
            simp at h
  · refine ⟨?_, ?_⟩ <;> intro t <;> cases t with
    | guessAX => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastA _ hrunA; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastA _ hrunA
    | guessBX => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastB _ hrunB; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastB _ hrunB
    | guessAY => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastAY _ hrunAY; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastAY _ hrunAY
    | guessBY => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastBY _ hrunBY; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastBY _ hrunBY
    | checkX => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastVX _ hrunVX; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastVX _ hrunVX
    | checkY => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastVY _ hrunVY; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastVY _ hrunVY
    | primeAX => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastPAX _ hrunPAX; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastPAX _ hrunPAX
    | primeBX => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastPBX _ hrunPBX; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastPBX _ hrunPBX
    | primeAY => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastPAY _ hrunPAY; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastPAY _ hrunPAY
    | primeBY => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastPBY _ hrunPBY; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastPBY _ hrunPBY
    | primeCheckX => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastPVX _ hrunPVX; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastPVX _ hrunPVX
    | primeCheckY => first
      | (obtain ⟨q, _, hq⟩ := resolution_sound _ _ _ cLastPVY _ hrunPVY; exact ⟨q, hq⟩)
      | exact resolution_reaches_final _ _ _ cLastPVY _ hrunPVY

/-- **Paper:** §3.5, ¶ The execution graph G.

the execution graph `G` (§3.5): for a solved `I`, the execution graph whose
`Events`/`po`/`rf`/`mo` are read off the trace of `traceRf_valid_general`.
`po_subset`/`po_total`/`rf_subset`/`rf_unique`/`mo_subset`/`ids_unique` hold for
any trace;
`mo_total` uses `traceMo_writers_confined`; `rf_total`/`rf_matches` are
`traceRf_valid_general`. RA-consistency is `executionGraphOf_consistent`
(`Completeness/Consistency.lean`). -/
noncomputable def executionGraphOf (I : PCPInstance) (hsol : I.HasSolution) :
    ExecutionGraph (domainOf I) :=
  let trace := (traceRf_valid_general I hsol).choose
  { Events := traceEvents trace
    po := traceEventsPo trace
    rf := traceRf I trace
    mo := traceEventsMo I trace
    po_subset := traceEventsPo_subset
    po_total := traceEventsPo_total trace
    rf_subset := traceRf_subset I
    rf_matches := (traceRf_valid_general I hsol).choose_spec.2.2.1
    rf_unique := traceRf_unique
    rf_total := (traceRf_valid_general I hsol).choose_spec.2.1
    mo_subset := traceEventsMo_subset I
    mo_total := traceEventsMo_total I trace
      (traceMo_writers_confined I (traceRf_valid_general I hsol).choose_spec.1)
    ids_unique := traceEvents_ids_unique }

/-- Every thread's word in `executionGraphOf I hsol` is a word of its program
(`traceRf_valid_general`, via `ExecutionGraph.threadWord_eq_trace`). -/
theorem executionGraphOf_isWord (I : PCPInstance) (hsol : I.HasSolution)
    (t : (domainOf I).Tid) :
    (ConcProgOf I t).IsWord ((executionGraphOf I hsol).threadWord t) := by
  have hEvents : (executionGraphOf I hsol).Events =
      traceEvents (traceRf_valid_general I hsol).choose := rfl
  have hpoEq : (executionGraphOf I hsol).po =
      traceEventsPo (traceRf_valid_general I hsol).choose := rfl
  rw [(executionGraphOf I hsol).threadWord_eq_trace
    (traceRf_valid_general I hsol).choose hEvents hpoEq]
  exact (traceRf_valid_general I hsol).choose_spec.2.2.2.1 t

/-- Every thread's word in `executionGraphOf I hsol`, with `term` appended,
reaches its final state (§2.2). -/
theorem executionGraphOf_reaches_final (I : PCPInstance) (hsol : I.HasSolution)
    (t : (domainOf I).Tid) :
    (ConcProgOf I t).Reaches ((executionGraphOf I hsol).threadWord t ++ [none])
      (ConcProgOf I t).final := by
  have hEvents : (executionGraphOf I hsol).Events =
      traceEvents (traceRf_valid_general I hsol).choose := rfl
  have hpoEq : (executionGraphOf I hsol).po =
      traceEventsPo (traceRf_valid_general I hsol).choose := rfl
  rw [(executionGraphOf I hsol).threadWord_eq_trace
    (traceRf_valid_general I hsol).choose hEvents hpoEq]
  exact (traceRf_valid_general I hsol).choose_spec.2.2.2.2 t

/-- **Paper:** Lemma 3.4.

Lemma 3.4 for `G := executionGraphOf I hsol`, in terms of
`G.po`/`G.index`: `po_monotone_of_traceShapes` at `G`'s trace, with
`ExecutionGraph.index_eq_rawIndex`. -/
theorem executionGraphOf_po_monotone (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (hpo : (executionGraphOf I hsol).po e1 e2)
    (hwt2 : e2.op = .wt) (hnb2 : ¬ e2.IsBridge) :
    (executionGraphOf I hsol).index e1 ≤ (executionGraphOf I hsol).index e2 ∧
      (e1.op = .rd → (executionGraphOf I hsol).index e1 <
        (executionGraphOf I hsol).index e2) := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  have hraw := po_monotone_of_traceShapes I trace hshapes he1 he2 hpo' hwt2 hnb2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `guessAX_po_monotone_read_gap` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_guessAX_read_write_gap (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (ht1 : e1.tid = Tid.guessAX) (ht2 : e2.tid = Tid.guessAX)
    (hpo : (executionGraphOf I hsol).po e1 e2)
    (hrd1 : e1.op = .rd) (hnb1 : ¬ e1.IsBridge) (hwt2 : e2.op = .wt) (hnb2 : ¬ e2.IsBridge) :
    (executionGraphOf I hsol).index e1 + 1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [ht1] at he1
  rw [ht2] at he2
  obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
    htrace⟩ := hshapes.guessAX
  have hraw := guessAX_po_monotone_read_gap I trace ks N v1 v2 vB0 hks inner0Rest outerRest
    hinner0 houterLen houter houterLast htrace he1 he2 hpo' hrd1 hnb1 hwt2 hnb2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `guessAY_po_monotone_read_gap` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_guessAY_read_write_gap (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (ht1 : e1.tid = Tid.guessAY) (ht2 : e2.tid = Tid.guessAY)
    (hpo : (executionGraphOf I hsol).po e1 e2)
    (hrd1 : e1.op = .rd) (hwt2 : e2.op = .wt) :
    (executionGraphOf I hsol).index e1 + 1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [ht1] at he1
  rw [ht2] at he2
  obtain ⟨v0, kws, htrace⟩ := hshapes.guessAY
  have hraw := guessAY_po_monotone_read_gap I trace v0 kws htrace he1 he2 hpo' hrd1 hwt2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `guessBX_po_monotone_read_gap` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_guessBX_read_write_gap (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (ht1 : e1.tid = Tid.guessBX) (ht2 : e2.tid = Tid.guessBX)
    (hpo : (executionGraphOf I hsol).po e1 e2)
    (hrd1 : e1.op = .rd) (hnb1 : ¬ e1.IsBridge) (hwt2 : e2.op = .wt) (hnb2 : ¬ e2.IsBridge) :
    (executionGraphOf I hsol).index e1 + 1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [ht1] at he1
  rw [ht2] at he2
  obtain ⟨ks, N, v1, v2, vB0, hks, inner0Rest, outerRest, hinner0, houterLen, houter, houterLast,
    htrace⟩ := hshapes.guessBX
  have hraw := guessBX_po_monotone_read_gap I trace ks N v1 v2 vB0 hks inner0Rest outerRest
    hinner0 houterLen houter houterLast htrace he1 he2 hpo' hrd1 hnb1 hwt2 hnb2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- `guessBY_po_monotone_read_gap` at the level of `G.po`/`G.index`. -/
theorem executionGraphOf_guessBY_read_write_gap (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (ht1 : e1.tid = Tid.guessBY) (ht2 : e2.tid = Tid.guessBY)
    (hpo : (executionGraphOf I hsol).po e1 e2)
    (hrd1 : e1.op = .rd) (hwt2 : e2.op = .wt) :
    (executionGraphOf I hsol).index e1 + 1 < (executionGraphOf I hsol).index e2 := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  rw [ht1] at he1
  rw [ht2] at he2
  obtain ⟨v0, kws, htrace⟩ := hshapes.guessBY
  have hraw := guessBY_po_monotone_read_gap I trace v0 kws htrace he1 he2 hpo' hrd1 hwt2
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2]
  exact hraw

/-- Lemma 3.5's closing sentence, "all decreasing edges
`r_i ⟶po r_j` between non-bridge read events are such that `r_i`
reads from a guesser thread": a read of `checkX`/`checkY` at
`xA`/`xB`/`yA`/`yB` reads from a guesser (unfolding `traceRf` at the
reader's `(tid, loc)`). -/
theorem executionGraphOf_checker_read_from_guesser (I : PCPInstance) (hsol : I.HasSolution)
    {e : Event (domainOf I)} (he : e ∈ (executionGraphOf I hsol).Events) (hrd : e.op = .rd)
    (htid : e.tid = Tid.checkX ∨ e.tid = Tid.checkY)
    (hloc : e.loc = Loc.xA ∨ e.loc = Loc.xB ∨ e.loc = Loc.yA ∨ e.loc = Loc.yB) :
    ∃ w, (executionGraphOf I hsol).rf w e ∧
      (w.tid = Tid.guessAX ∨ w.tid = Tid.guessAY ∨ w.tid = Tid.guessBX ∨ w.tid = Tid.guessBY) := by
  obtain ⟨w, hrf⟩ := (executionGraphOf I hsol).rf_total he hrd
  refine ⟨w, hrf, ?_⟩
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hrfEq : (executionGraphOf I hsol).rf = traceRf I trace := rfl
  rw [hrfEq] at hrf
  unfold traceRf at hrf
  rcases het : e.tid with _|_|_|_|_|_|_|_|_|_|_|_ <;> rw [het] at hrf htid <;>
    rcases hel : e.loc with
      _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_ <;>
    rw [hel] at hrf hloc <;>
    first
      | (obtain ⟨i, hw, -⟩ := hrf
         rw [(rawNthEvent_mem hw).2.1]
         first
           | exact Or.inl rfl
           | exact Or.inr (Or.inl rfl)
           | exact Or.inr (Or.inr (Or.inl rfl))
           | exact Or.inr (Or.inr (Or.inr rfl)))
      | exact hrf.elim
      | (rcases htid with h | h <;> injection h <;> done)
      | (rcases hloc with h | h | h | h <;> injection h)

/-- **Paper:** Lemma 3.5.

Lemma 3.5 for `G := executionGraphOf I hsol`, in terms of
`G.po`/`G.index`: `po_reads_decreasing_of_traceShapes` at `G`'s trace, with
the closing sentence from `executionGraphOf_checker_read_from_guesser`. -/
theorem executionGraphOf_po_reads_decreasing (I : PCPInstance) (hsol : I.HasSolution)
    {e1 e2 : Event (domainOf I)} (hpo : (executionGraphOf I hsol).po e1 e2)
    (hrd1 : e1.op = .rd) (hrd2 : e2.op = .rd)
    (hnb1 : ¬ e1.IsBridge) (hnb2 : ¬ e2.IsBridge)
    (hdec : (executionGraphOf I hsol).index e2 < (executionGraphOf I hsol).index e1) :
    (executionGraphOf I hsol).index e1 = (executionGraphOf I hsol).index e2 + 1 ∧
      (((e1.loc = Loc.xA ∧ e2.loc = Loc.xA') ∨ (e1.loc = Loc.xA ∧ e2.loc = Loc.xB') ∨
        (e1.loc = Loc.xB ∧ e2.loc = Loc.xA') ∨ (e1.loc = Loc.xB ∧ e2.loc = Loc.xB')) ∨
       ((e1.loc = Loc.yA ∧ e2.loc = Loc.yA') ∨ (e1.loc = Loc.yA ∧ e2.loc = Loc.yB') ∨
        (e1.loc = Loc.yB ∧ e2.loc = Loc.yA') ∨ (e1.loc = Loc.yB ∧ e2.loc = Loc.yB'))) ∧
      (∃ w, (executionGraphOf I hsol).rf w e1 ∧
        (w.tid = Tid.guessAX ∨ w.tid = Tid.guessAY ∨ w.tid = Tid.guessBX ∨ w.tid = Tid.guessBY)) := by
  set trace := (traceRf_valid_general I hsol).choose with htraceDef
  have hshapes := (traceRf_valid_general I hsol).choose_spec.1
  have hEvents : (executionGraphOf I hsol).Events = traceEvents trace := rfl
  have hpoEq : (executionGraphOf I hsol).po = traceEventsPo trace := rfl
  rw [hpoEq] at hpo
  obtain ⟨hmem1, hmem2, hpo'⟩ := hpo
  have he1 : e1 ∈ traceEventsOf trace e1.tid := mem_traceEvents_of_tid hmem1 rfl
  have he2 : e2 ∈ traceEventsOf trace e2.tid := mem_traceEvents_of_tid hmem2 rfl
  have hi1 : (executionGraphOf I hsol).index e1 = rawIndex trace e1 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem1
  have hi2 : (executionGraphOf I hsol).index e2 = rawIndex trace e2 :=
    (executionGraphOf I hsol).index_eq_rawIndex trace hEvents hpoEq hmem2
  rw [hi1, hi2] at hdec
  obtain ⟨hidx, hloc, htid⟩ :=
    po_reads_decreasing_of_traceShapes I trace hshapes he1 he2 hpo' hrd1 hrd2 hnb1 hnb2 hdec
  refine ⟨by rw [hi1, hi2]; exact hidx, hloc, ?_⟩
  have hloc' : e1.loc = Loc.xA ∨ e1.loc = Loc.xB ∨ e1.loc = Loc.yA ∨ e1.loc = Loc.yB := by
    rcases hloc with (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inr h))
  exact executionGraphOf_checker_read_from_guesser I hsol hmem1 hrd1 htid hloc'

/-- The thread-level `rf` topology (Fig. 4), `t →rf t'` ("`G` has an `rf`-edge from an event
of `t` to an event of `t'`"), for `G := executionGraphOf I hsol`. -/
def executionGraphOf_ThreadRf (I : PCPInstance) (hsol : I.HasSolution)
    (t t' : Tid) : Prop :=
  ∃ ew er, (executionGraphOf I hsol).rf ew er ∧ ew.tid = t ∧ er.tid = t'

/-- `executionGraphOf_ThreadRf` is `ThreadRf` at `G`'s trace. -/
theorem executionGraphOf_ThreadRf_eq (I : PCPInstance) (hsol : I.HasSolution) :
    executionGraphOf_ThreadRf I hsol =
      ThreadRf I (traceRf_valid_general I hsol).choose := rfl

/-- The thread-level `rf` topology (Fig. 4), first half, for `G := executionGraphOf I hsol`: `t →rf
t'` holds exactly for the eight bidirectional pairs and the eight
one-directional guesser-to-checker edges. -/
theorem executionGraphOf_threadRf_pairs (I : PCPInstance) (hsol : I.HasSolution)
    {t t' : Tid} (h : executionGraphOf_ThreadRf I hsol t t') :
    (t = Tid.primeAX ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessAX ∧ t' = Tid.primeAX) ∨
      (t = Tid.primeAY ∧ t' = Tid.guessAY) ∨
      (t = Tid.guessAY ∧ t' = Tid.primeAY) ∨
      (t = Tid.primeBX ∧ t' = Tid.guessBX) ∨
      (t = Tid.guessBX ∧ t' = Tid.primeBX) ∨
      (t = Tid.primeBY ∧ t' = Tid.guessBY) ∨
      (t = Tid.guessBY ∧ t' = Tid.primeBY) ∨
      (t = Tid.guessAX ∧ t' = Tid.guessAY) ∨
      (t = Tid.guessAY ∧ t' = Tid.guessAX) ∨
      (t = Tid.guessBX ∧ t' = Tid.guessBY) ∨
      (t = Tid.guessBY ∧ t' = Tid.guessBX) ∨
      (t = Tid.checkX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.primeCheckX ∧ t' = Tid.checkX) ∨
      (t = Tid.checkY ∧ t' = Tid.primeCheckY) ∨
      (t = Tid.primeCheckY ∧ t' = Tid.checkY) ∨
      (t = Tid.guessAX ∧ t' = Tid.checkX) ∨
      (t = Tid.primeAX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.guessBX ∧ t' = Tid.checkX) ∨
      (t = Tid.primeBX ∧ t' = Tid.primeCheckX) ∨
      (t = Tid.guessAY ∧ t' = Tid.checkY) ∨
      (t = Tid.primeAY ∧ t' = Tid.primeCheckY) ∨
      (t = Tid.guessBY ∧ t' = Tid.checkY) ∨
      (t = Tid.primeBY ∧ t' = Tid.primeCheckY) := by
  rw [executionGraphOf_ThreadRf_eq] at h
  exact threadRf_pairs I h

/-- The thread-level `rf` topology (Fig. 4), second half, for `G := executionGraphOf I hsol`: every
cyclic sequence of pairwise distinct threads under `→rf` has length `2`. -/
theorem executionGraphOf_rf_cycle_length_two (I : PCPInstance) (hsol : I.HasSolution)
    (l : List Tid) (hne : l ≠ []) (hnodup : l.Nodup)
    (hcycle : List.IsChain (executionGraphOf_ThreadRf I hsol) (l ++ [l.headI])) :
    l.length = 2 := by
  rw [executionGraphOf_ThreadRf_eq] at hcycle
  exact traceRf_cycle_length_two I l hne hnodup hcycle

/-- The thread-level `hb` separation (Fig. 4), first part, for `G := executionGraphOf I hsol`: an
`hb`-edge between events of distinct threads gives a `→rf`-path between the
threads (as `Relation.TransGen`), since `po` stays within a thread. -/
theorem executionGraphOf_hb_threadRf (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (htid : a.tid ≠ b.tid)
    (hhb : (executionGraphOf I hsol).hb a b) :
    Relation.TransGen (executionGraphOf_ThreadRf I hsol) a.tid b.tid := by
  suffices h : a.tid = b.tid ∨
      Relation.TransGen (executionGraphOf_ThreadRf I hsol) a.tid b.tid by
    rcases h with heq | htg
    · exact absurd heq htid
    · exact htg
  clear htid
  induction hhb with
  | single h =>
      rcases h with hpo | hrf
      · exact Or.inl (traceEventsPo_subset hpo).2.2
      · exact Or.inr (Relation.TransGen.single ⟨_, _, hrf, rfl, rfl⟩)
  | tail h h' ih =>
      rcases h' with hpo | hrf
      · have hteq := (traceEventsPo_subset hpo).2.2
        rcases ih with iheq | ihtg
        · exact Or.inl (iheq.trans hteq)
        · right; rw [← hteq]; exact ihtg
      · rcases ih with iheq | ihtg
        · right; rw [iheq]; exact Relation.TransGen.single ⟨_, _, hrf, rfl, rfl⟩
        · exact Or.inr (ihtg.tail ⟨_, _, hrf, rfl, rfl⟩)

/-- The thread-level `hb` separation (Fig. 4), first consequence, one direction: no event of an
`AlphaGuesserTids` thread is `hb`-before an event of a `BetaGuesserTids`
thread. -/
theorem executionGraphOf_alpha_not_hb_beta (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid ∈ AlphaGuesserTids)
    (hb : b.tid ∈ BetaGuesserTids) :
    ¬ (executionGraphOf I hsol).hb a b := by
  intro hhb
  have htid : a.tid ≠ b.tid := by
    intro heq
    rw [heq] at ha
    exact alpha_not_betaOrChecker b.tid ha (Or.inl hb)
  have htg := executionGraphOf_hb_threadRf I hsol htid hhb
  rw [executionGraphOf_ThreadRf_eq] at htg
  have hmem := threadRf_transGen_alphaOrChecker_closed I (Or.inl ha) htg
  exact beta_not_alphaOrChecker b.tid hb hmem

/-- The thread-level `hb` separation (Fig. 4), first consequence, the other direction. -/
theorem executionGraphOf_beta_not_hb_alpha (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid ∈ BetaGuesserTids)
    (hb : b.tid ∈ AlphaGuesserTids) :
    ¬ (executionGraphOf I hsol).hb a b := by
  intro hhb
  have htid : a.tid ≠ b.tid := by
    intro heq
    rw [heq] at ha
    exact beta_not_alphaOrChecker b.tid ha (Or.inl hb)
  have htg := executionGraphOf_hb_threadRf I hsol htid hhb
  rw [executionGraphOf_ThreadRf_eq] at htg
  have hmem := threadRf_transGen_betaOrChecker_closed I (Or.inl ha) htg
  exact alpha_not_betaOrChecker b.tid hb hmem

/-- The thread-level `hb` separation (Fig. 4), second consequence, one direction: no event of an
`XCheckerTids` thread is `hb`-before an event of a `YCheckerTids` thread. -/
theorem executionGraphOf_xChecker_not_hb_yChecker (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid ∈ XCheckerTids)
    (hb : b.tid ∈ YCheckerTids) :
    ¬ (executionGraphOf I hsol).hb a b := by
  intro hhb
  have htid : a.tid ≠ b.tid := by
    intro heq
    rw [heq] at ha
    exact yChecker_not_xChecker b.tid hb ha
  have htg := executionGraphOf_hb_threadRf I hsol htid hhb
  rw [executionGraphOf_ThreadRf_eq] at htg
  have hmem := threadRf_transGen_xChecker_closed I ha htg
  exact yChecker_not_xChecker b.tid hb hmem

/-- The thread-level `hb` separation (Fig. 4), second consequence, the other direction. -/
theorem executionGraphOf_yChecker_not_hb_xChecker (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid ∈ YCheckerTids)
    (hb : b.tid ∈ XCheckerTids) :
    ¬ (executionGraphOf I hsol).hb a b := by
  intro hhb
  have htid : a.tid ≠ b.tid := by
    intro heq
    rw [heq] at ha
    exact xChecker_not_yChecker b.tid hb ha
  have htg := executionGraphOf_hb_threadRf I hsol htid hhb
  rw [executionGraphOf_ThreadRf_eq] at htg
  have hmem := threadRf_transGen_yChecker_closed I ha htg
  exact xChecker_not_yChecker b.tid hb hmem

/-- No `hb`-edge leaves the `XCheckerTids` threads (from the proof of
the thread-level `rf` topology (Fig. 4)): the fact `rr_bridge_monotonic`'s proof cites as "there are
no outgoing `hb`-edges from `{c^x,c^{x'}}` ... to any other thread". -/
theorem executionGraphOf_xChecker_not_hb_outside (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid ∈ XCheckerTids)
    (hb : b.tid ∉ XCheckerTids) :
    ¬ (executionGraphOf I hsol).hb a b := by
  intro hhb
  have htid : a.tid ≠ b.tid := by
    intro heq
    rw [heq] at ha
    exact hb ha
  have htg := executionGraphOf_hb_threadRf I hsol htid hhb
  rw [executionGraphOf_ThreadRf_eq] at htg
  exact hb (threadRf_transGen_xChecker_closed I ha htg)

/-- No `hb`-edge leaves the `YCheckerTids` threads. -/
theorem executionGraphOf_yChecker_not_hb_outside (I : PCPInstance) (hsol : I.HasSolution)
    {a b : Event (domainOf I)} (ha : a.tid ∈ YCheckerTids)
    (hb : b.tid ∉ YCheckerTids) :
    ¬ (executionGraphOf I hsol).hb a b := by
  intro hhb
  have htid : a.tid ≠ b.tid := by
    intro heq
    rw [heq] at ha
    exact hb ha
  have htg := executionGraphOf_hb_threadRf I hsol htid hhb
  rw [executionGraphOf_ThreadRf_eq] at htg
  exact hb (threadRf_transGen_yChecker_closed I ha htg)

end RAUndecidability
