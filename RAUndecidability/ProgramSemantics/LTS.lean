import RAUndecidability.ProgramSemantics.Step
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finite.Prod

/-!
# The induced LTS

The induced LTS, as in an earlier version of the paper. The paper
(App. A, "The induced LTS") defines the LTS without the symbol `term`, entering `q_fn` on the thread's last event label instead;
this development follows the `term`-based version (see
sequential programs (§2.1) and the README):

* App. A, The induced LTS: absorbing silent steps;
* App. A: the LTS induced by a thread command;
* App. A: finiteness of its state set;
* `inducedSeqProgram`: the induced LTS (App. A) packaged as a `SequentialProgram`
  (§2.1).

The proof of finiteness of the induced LTS (App. A): stores are finite, and the commands occurring in
reachable configurations lie in the finite over-approximation `Command.res`.
-/

namespace RAUndecidability

variable {D : Domains} {V : Vocabulary D}

/-! ## `⇒^a` (App. A, The induced LTS) -/

/-- `c ⇒^a c'` (App. A, The induced LTS): `c` reaches `c'` via zero or more silent
steps followed by one step labelled `a`. -/
def Reaches (t : D.Tid) (a : Option (ThreadLabel D t)) (c : Config D V)
    (c' : Option (Config D V)) : Prop :=
  ∃ c'', Relation.ReflTransGen (SilentTo t) c c'' ∧ StepTo t a c'' c'

/-- `c ⇓ term` (App. A, The induced LTS): `c` can silently reach the command
`term`. -/
def Halts (t : D.Tid) (c : Config D V) : Prop :=
  ∃ φ, Relation.ReflTransGen (SilentTo t) c (.term, φ)

/-! ## The induced LTS (App. A) -/

/-- `c₀ ⟶* c` under either kind of step: `c` is reachable from `c₀` via any
mixture of silent and labelled steps. -/
def Reachable (t : D.Tid) (c₀ c : Config D V) : Prop :=
  Relation.ReflTransGen (fun x y => SilentTo t x y ∨ ∃ a, StepTo t a x (some y)) c₀ c

/-- `States_t` (App. A): the reachable configurations from
`⟨C_t, φ₀⟩`, together with `FinalState`. A subtype of `Option (Config D V)`,
with `none` standing for `FinalState`/`qfn` — the same `Option`-encoding used
for the alphabet in `SequentialProgram` and for `Step`'s target: `qfn` is not
of the form `⟨C, φ⟩` because `none ≠ some c` for any `c`, by construction,
with no side condition needed. -/
def InducedState (D : Domains) (V : Vocabulary D) (t : D.Tid) (C_t : Command D V)
    (φ₀ : V.Store) : Type :=
  {oc : Option (Config D V) // oc = none ∨ ∃ c, oc = some c ∧ Reachable t (C_t, φ₀) c}

variable {t : D.Tid} {C_t : Command D V} {φ₀ : V.Store}

/-- `Trans_t` (App. A): a real label `a = some l` steps via
`Reaches`; the label `a = none` (`term`) steps to `FinalState` exactly when
the source halts. `FinalState` (`s.1 = none`) has no outgoing transitions,
again with no side condition: the match simply has no case for it. -/
def inducedTrans (s : InducedState D V t C_t φ₀) (a : Option (ThreadLabel D t))
    (s' : InducedState D V t C_t φ₀) : Prop :=
  match s.1 with
  | none => False
  | some c =>
    match a with
    | some l => ∃ c', s'.1 = some c' ∧ Reaches t (some l) c (some c')
    | none => s'.1 = none ∧ Halts t c

/-- `InitState = ⟨C_t, φ₀⟩` (App. A). -/
def inducedInit : InducedState D V t C_t φ₀ :=
  ⟨some (C_t, φ₀), Or.inr ⟨(C_t, φ₀), rfl, Relation.ReflTransGen.refl⟩⟩

/-- `FinalState` (App. A): the distinguished state not of the form
`⟨C, φ⟩`. -/
def inducedFinal : InducedState D V t C_t φ₀ := ⟨none, Or.inl rfl⟩

/-- **Paper:** App. A, ¶ The induced LTS.

The induced LTS (App. A): `Prog_t`, over the alphabet
`LabelDom^t ∪ {term}`. Its finiteness is finiteness of the induced LTS (App. A), below. -/
def inducedLTS : LTS (Option (ThreadLabel D t)) (InducedState D V t C_t φ₀) where
  trans := inducedTrans
  init := inducedInit
  final := inducedFinal

/-! ## Finiteness of the induced LTS (App. A) -/

/-- A finite over-approximation of the commands occurring in configurations
reachable from a command `C`: `C` itself, closed under subcommands, with
`while`-bodies additionally wrapped in `loopSeq` against their own enclosing
`whileLoop` (the runtime form reached by `whileTrue`).

Beyond the paper's "`res(C)` contains `C`, its subcommands, and, for each
`while b do C'` in `C`, the commands `C'' ▷ (while b do C')` for
`C'' ∈ res(C')`", closure under `Step` needs, in the `seq`/`loopSeq` clauses:

* the escape value (`.brk` for `seq`, `.skip` for `loopSeq`) must be inserted
  *unconditionally*, not only reached through the wrapping image: if `C1` can
  reach `.brk`, `seq C1 C2` reaches `seq brk C2`, which steps via `seqBreak`
  straight to bare `.brk` — outside `{seq x C2 : x ∈ res C1}`;
* `res C2` must be unioned in directly, not only reached through the
  wrapping: if `C1` can reach `.skip`, `seq C1 C2` reaches `seq skip C2`,
  which steps via `seqSkip` to bare `C2` — again outside the wrapped image.

Nested loops need no special handling: `res (whileLoop b C)` wraps all of
`res C`, which already contains the inner `loopSeq`-wrapped commands. -/
def Command.res : Command D V → Set (Command D V)
  | .skip => {.skip}
  | .brk => {.brk}
  | .term => {.term}
  | .assign v e => {.assign v e, .skip}
  | .ndetAssign v X hX => {.ndetAssign v X hX, .skip}
  | .write u e => {.write u e, .skip}
  | .read u e => {.read u e, .skip}
  | .seq .skip C2 => insert (.seq .skip C2) (Command.res C2)
  | .seq .brk C2 => {.seq .brk C2, .brk}
  | .seq C1 C2 => insert (.seq C1 C2)
      (insert .brk ((fun x => Command.seq x C2) '' Command.res C1 ∪ Command.res C2))
  | .ite b C1 C2 => insert (.ite b C1 C2) (Command.res C1 ∪ Command.res C2)
  | .whileLoop b C => insert (.whileLoop b C)
      (insert .skip ((fun x => Command.loopSeq x (.whileLoop b C)) '' Command.res C))
  | .loopSeq .skip C2 => insert (.loopSeq .skip C2) (Command.res C2)
  | .loopSeq .brk C2 => {.loopSeq .brk C2, .skip}
  | .loopSeq C1 C2 => insert (.loopSeq C1 C2)
      (insert .skip ((fun x => Command.loopSeq x C2) '' Command.res C1 ∪ Command.res C2))

/-- `res C` is finite, by structural induction on `C`. Here and in
`Command.mem_res_self` and `Command.res_trans`, the cases `case1`-`case15` of
`Command.res.induct` are the branches of `Command.res` in order; the comment
before each names its command. -/
theorem Command.res_finite (C : Command D V) : (Command.res C).Finite := by
  induction C using Command.res.induct with
  -- `skip`
  | case1 => exact Set.finite_singleton _
  -- `break`
  | case2 => exact Set.finite_singleton _
  -- `term`
  | case3 => exact Set.finite_singleton _
  -- `v ← e`
  | case4 v e => exact (Set.finite_singleton _).insert _
  -- `v ← NDet(X)`
  | case5 v X hX => exact (Set.finite_singleton _).insert _
  -- `w(u, e)`
  | case6 u e => exact (Set.finite_singleton _).insert _
  -- `r(u, e)`
  | case7 u e => exact (Set.finite_singleton _).insert _
  -- `skip ; C2`
  | case8 C2 ih => simp only [Command.res]; exact ih.insert _
  -- `break ; C2`
  | case9 C2 => exact (Set.finite_singleton _).insert _
  -- `C1 ; C2`, `C1` neither `skip` nor `break`
  | case10 C1 C2 hne1 hne2 ih1 ih2 =>
      simp only [Command.res, hne1, hne2]
      exact ((ih1.image _).union ih2 |>.insert _).insert _
  -- `if b then C1 else C2`
  | case11 b C1 C2 ih1 ih2 => exact (ih1.union ih2).insert _
  -- `while b do C`
  | case12 b C ih => simp only [Command.res]; exact ((ih.image _).insert _).insert _
  -- `skip ▷ C2`
  | case13 C2 ih => simp only [Command.res]; exact ih.insert _
  -- `break ▷ C2`
  | case14 C2 => exact (Set.finite_singleton _).insert _
  -- `C1 ▷ C2`, `C1` neither `skip` nor `break`
  | case15 C1 C2 hne1 hne2 ih1 ih2 =>
      simp only [Command.res, hne1, hne2]
      exact ((ih1.image _).union ih2 |>.insert _).insert _

/-- `C ∈ res C`: every command is in its own closure. -/
theorem Command.mem_res_self (C : Command D V) : C ∈ Command.res C := by
  induction C using Command.res.induct with
  -- `skip`
  | case1 => rfl
  -- `break`
  | case2 => rfl
  -- `term`
  | case3 => rfl
  -- `v ← e`
  | case4 v e => left; rfl
  -- `v ← NDet(X)`
  | case5 v X hX => left; rfl
  -- `w(u, e)`
  | case6 u e => left; rfl
  -- `r(u, e)`
  | case7 u e => left; rfl
  -- `skip ; C2`
  | case8 C2 ih => simp only [Command.res]; left; rfl
  -- `break ; C2`
  | case9 C2 => left; rfl
  -- `C1 ; C2`, `C1` neither `skip` nor `break`
  | case10 C1 C2 hne1 hne2 ih1 ih2 => simp only [Command.res]; left; rfl
  -- `if b then C1 else C2`
  | case11 b C1 C2 ih1 ih2 => left; rfl
  -- `while b do C`
  | case12 b C ih => simp only [Command.res]; left; rfl
  -- `skip ▷ C2`
  | case13 C2 ih => simp only [Command.res]; left; rfl
  -- `break ▷ C2`
  | case14 C2 => left; rfl
  -- `C1 ▷ C2`, `C1` neither `skip` nor `break`
  | case15 C1 C2 hne1 hne2 ih1 ih2 => simp only [Command.res]; left; rfl

/-- `res` is transitively closed: everything in `res C` for some `C ∈ res D`
was already in `res D`. Structural induction on `D`. -/
theorem Command.res_trans (Dm : Command D V) :
    ∀ C ∈ Command.res Dm, Command.res C ⊆ Command.res Dm := by
  induction Dm using Command.res.induct with
  -- `skip`
  | case1 =>
      intro C hC; simp only [Command.res, Set.mem_singleton_iff] at hC; subst hC
      exact Set.Subset.refl _
  -- `break`
  | case2 =>
      intro C hC; simp only [Command.res, Set.mem_singleton_iff] at hC; subst hC
      exact Set.Subset.refl _
  -- `term`
  | case3 =>
      intro C hC; simp only [Command.res, Set.mem_singleton_iff] at hC; subst hC
      exact Set.Subset.refl _
  -- `v ← e`
  | case4 v e =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
      rcases hC with hC | hC <;> subst hC
      · rfl
      · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  -- `v ← NDet(X)`
  | case5 v X hX =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
      rcases hC with hC | hC <;> subst hC
      · rfl
      · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  -- `w(u, e)`
  | case6 u e =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
      rcases hC with hC | hC <;> subst hC
      · rfl
      · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  -- `r(u, e)`
  | case7 u e =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
      rcases hC with hC | hC <;> subst hC
      · rfl
      · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  -- `skip ; C2`
  | case8 C2 ih =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff] at hC
      rcases hC with hC | hC
      · subst hC; rfl
      · exact (ih _ hC).trans (Set.subset_insert _ _)
  -- `break ; C2`
  | case9 C2 =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
      rcases hC with hC | hC <;> subst hC
      · rfl
      · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  -- `C1 ; C2`, `C1` neither `skip` nor `break`
  | case10 C1 C2 hne1 hne2 ih1 ih2 =>
      have hDbrk : Command.brk ∈ Command.res (Command.seq C1 C2) := by
        simp only [Command.res, hne1, hne2]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      have hDimg : ∀ z ∈ Command.res C1,
          Command.seq z C2 ∈ Command.res (Command.seq C1 C2) := by
        intro z hz
        simp only [Command.res, hne1, hne2]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_union_left _ ⟨z, hz, rfl⟩))
      have hDC2 : Command.res C2 ⊆ Command.res (Command.seq C1 C2) := by
        intro y hy
        simp only [Command.res, hne1, hne2]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_union_right _ hy))
      intro C hC
      simp only [Command.res, hne1, hne2, Set.mem_insert_iff, Set.mem_union, Set.mem_image] at hC
      rcases hC with hC | hC | ⟨x, hx, hCeq⟩ | hC
      · subst hC; exact Set.Subset.refl _
      · subst hC
        conv_lhs => simp only [Command.res]
        exact Set.singleton_subset_iff.mpr hDbrk
      · subst hCeq
        rcases Classical.em (x = Command.skip) with hxs | hxs
        · subst hxs
          conv_lhs => simp only [Command.res]
          exact Set.insert_subset_iff.mpr ⟨hDimg _ hx, hDC2⟩
        · rcases Classical.em (x = Command.brk) with hxb | hxb
          · subst hxb
            show ({Command.seq Command.brk C2, Command.brk} : Set (Command D V)) ⊆
              Command.res (Command.seq C1 C2)
            exact Set.insert_subset_iff.mpr ⟨hDimg _ hx, Set.singleton_subset_iff.mpr hDbrk⟩
          · conv_lhs => simp only [Command.res, hxs, hxb]
            refine Set.insert_subset_iff.mpr ⟨hDimg _ hx, Set.insert_subset_iff.mpr ⟨hDbrk, ?_⟩⟩
            refine Set.union_subset ?_ hDC2
            rintro y ⟨z, hz, rfl⟩
            exact hDimg _ ((ih1 x hx) hz)
      · exact Set.Subset.trans (ih2 _ hC) hDC2
  -- `if b then C1 else C2`
  | case11 b C1 C2 ih1 ih2 =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff, Set.mem_union] at hC
      rcases hC with hC | hC | hC
      · subst hC; rfl
      · refine (ih1 _ hC).trans ?_
        intro y hy
        exact Set.mem_insert_of_mem _ (Set.mem_union_left _ hy)
      · refine (ih2 _ hC).trans ?_
        intro y hy
        exact Set.mem_insert_of_mem _ (Set.mem_union_right _ hy)
  -- `while b do C`
  | case12 b C ih =>
      have hDskip : Command.skip ∈ Command.res (Command.whileLoop b C) := by
        simp only [Command.res]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      have hDimg : ∀ z ∈ Command.res C,
          Command.loopSeq z (Command.whileLoop b C) ∈ Command.res (Command.whileLoop b C) := by
        intro z hz
        simp only [Command.res]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨z, hz, rfl⟩)
      intro C' hC'
      simp only [Command.res, Set.mem_insert_iff, Set.mem_image] at hC'
      rcases hC' with hC' | hC' | ⟨x, hx, hCeq⟩
      · subst hC'; exact Set.Subset.refl _
      · subst hC'
        conv_lhs => simp only [Command.res]
        exact Set.singleton_subset_iff.mpr hDskip
      · subst hCeq
        rcases Classical.em (x = Command.skip) with hxs | hxs
        · subst hxs
          conv_lhs => simp only [Command.res]
          exact Set.insert_subset_iff.mpr ⟨hDimg _ hx, Set.Subset.refl _⟩
        · rcases Classical.em (x = Command.brk) with hxb | hxb
          · subst hxb
            show ({Command.loopSeq Command.brk (Command.whileLoop b C), Command.skip} :
              Set (Command D V)) ⊆ Command.res (Command.whileLoop b C)
            exact Set.insert_subset_iff.mpr ⟨hDimg _ hx, Set.singleton_subset_iff.mpr hDskip⟩
          · conv_lhs => simp only [Command.res, hxs, hxb]
            refine Set.insert_subset_iff.mpr
              ⟨hDimg _ hx, Set.insert_subset_iff.mpr ⟨hDskip, ?_⟩⟩
            refine Set.union_subset ?_ (Set.Subset.refl _)
            rintro y ⟨z, hz, rfl⟩
            exact hDimg _ ((ih x hx) hz)
  -- `skip ▷ C2`
  | case13 C2 ih =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff] at hC
      rcases hC with hC | hC
      · subst hC; rfl
      · exact (ih _ hC).trans (Set.subset_insert _ _)
  -- `break ▷ C2`
  | case14 C2 =>
      intro C hC
      simp only [Command.res, Set.mem_insert_iff, Set.mem_singleton_iff] at hC
      rcases hC with hC | hC <;> subst hC
      · rfl
      · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  -- `C1 ▷ C2`, `C1` neither `skip` nor `break`
  | case15 C1 C2 hne1 hne2 ih1 ih2 =>
      have hDskip : Command.skip ∈ Command.res (Command.loopSeq C1 C2) := by
        simp only [Command.res, hne1, hne2]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      have hDimg : ∀ z ∈ Command.res C1,
          Command.loopSeq z C2 ∈ Command.res (Command.loopSeq C1 C2) := by
        intro z hz
        simp only [Command.res, hne1, hne2]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_union_left _ ⟨z, hz, rfl⟩))
      have hDC2 : Command.res C2 ⊆ Command.res (Command.loopSeq C1 C2) := by
        intro y hy
        simp only [Command.res, hne1, hne2]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_union_right _ hy))
      intro C hC
      simp only [Command.res, hne1, hne2, Set.mem_insert_iff, Set.mem_union, Set.mem_image] at hC
      rcases hC with hC | hC | ⟨x, hx, hCeq⟩ | hC
      · subst hC; exact Set.Subset.refl _
      · subst hC
        conv_lhs => simp only [Command.res]
        exact Set.singleton_subset_iff.mpr hDskip
      · subst hCeq
        rcases Classical.em (x = Command.skip) with hxs | hxs
        · subst hxs
          conv_lhs => simp only [Command.res]
          exact Set.insert_subset_iff.mpr ⟨hDimg _ hx, hDC2⟩
        · rcases Classical.em (x = Command.brk) with hxb | hxb
          · subst hxb
            show ({Command.loopSeq Command.brk C2, Command.skip} : Set (Command D V)) ⊆
              Command.res (Command.loopSeq C1 C2)
            exact Set.insert_subset_iff.mpr ⟨hDimg _ hx, Set.singleton_subset_iff.mpr hDskip⟩
          · conv_lhs => simp only [Command.res, hxs, hxb]
            refine Set.insert_subset_iff.mpr ⟨hDimg _ hx, Set.insert_subset_iff.mpr ⟨hDskip, ?_⟩⟩
            refine Set.union_subset ?_ hDC2
            rintro y ⟨z, hz, rfl⟩
            exact hDimg _ ((ih1 x hx) hz)
      · exact Set.Subset.trans (ih2 _ hC) hDC2

/-- `x ∈ res C1 → seq x C2 ∈ res (seq C1 C2)`, for any shape of `C1` -/
theorem Command.res_seq_mem {C1 C2 x : Command D V} (hx : x ∈ Command.res C1) :
    Command.seq x C2 ∈ Command.res (Command.seq C1 C2) := by
  rcases Classical.em (C1 = Command.skip) with h1 | h1
  · subst h1
    simp only [Command.res, Set.mem_singleton_iff] at hx
    subst hx
    simp only [Command.res]
    exact Set.mem_insert _ _
  · rcases Classical.em (C1 = Command.brk) with h2 | h2
    · subst h2
      simp only [Command.res, Set.mem_singleton_iff] at hx
      subst hx
      simp only [Command.res]
      exact Set.mem_insert _ _
    · simp only [Command.res, h1, h2]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_union_left _ ⟨x, hx, rfl⟩))

/-- The `loopSeq` analogue of `res_seq_mem`. -/
theorem Command.res_loopSeq_mem {C1 C2 x : Command D V} (hx : x ∈ Command.res C1) :
    Command.loopSeq x C2 ∈ Command.res (Command.loopSeq C1 C2) := by
  rcases Classical.em (C1 = Command.skip) with h1 | h1
  · subst h1
    simp only [Command.res, Set.mem_singleton_iff] at hx
    subst hx
    simp only [Command.res]
    exact Set.mem_insert _ _
  · rcases Classical.em (C1 = Command.brk) with h2 | h2
    · subst h2
      simp only [Command.res, Set.mem_singleton_iff] at hx
      subst hx
      simp only [Command.res]
      exact Set.mem_insert _ _
    · simp only [Command.res, h1, h2]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_union_left _ ⟨x, hx, rfl⟩))

/-- The local closure property: a single `Step` lands in the source's `res`
(`term`-labelled steps excluded, since their target is `qfn` = `none`, not
`some ⟨C',φ'⟩`). Stated over a generic `Config`/`Option Config` pair so
that `induction` applies. -/
theorem Command.step_mem_res {t : D.Tid} :
    ∀ {a : Option (Option (ThreadLabel D t))} {c : Config D V} {oc' : Option (Config D V)},
      Step t a c oc' → ∀ C' φ', oc' = some (C', φ') → C' ∈ Command.res c.1 := by
  intro a c oc' h
  induction h with
  | assign =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ rfl
  | ndet hc =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ rfl
  | seqSkip =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ (Command.mem_res_self _)
  | seqBreak =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ rfl
  | iteTrue h =>
      intro C' φ' heq; cases heq
      simp only [Command.res]
      exact Set.mem_insert_of_mem _ (Set.mem_union_left _ (Command.mem_res_self _))
  | iteFalse h =>
      intro C' φ' heq; cases heq
      simp only [Command.res]
      exact Set.mem_insert_of_mem _ (Set.mem_union_right _ (Command.mem_res_self _))
  | whileTrue h =>
      intro C' φ' heq; cases heq
      simp only [Command.res]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨_, Command.mem_res_self _, rfl⟩)
  | whileFalse h =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  | loopSkip =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ (Command.mem_res_self _)
  | loopBreak =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ rfl
  | write =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ rfl
  | read =>
      intro C' φ' heq; cases heq
      simp only [Command.res]; exact Set.mem_insert_of_mem _ rfl
  | termStep => intro C' φ' heq; cases heq
  | seqCongr _ ih =>
      intro C' φ' heq; cases heq
      exact Command.res_seq_mem (ih _ _ rfl)
  | loopCongr _ ih =>
      intro C' φ' heq; cases heq
      exact Command.res_loopSeq_mem (ih _ _ rfl)

/-- Every command occurring in a configuration reachable from `⟨C_t, φ₀⟩` lies
in `res C_t`: an induction over the
step relation (via `Relation.ReflTransGen`'s `tail` induction), combining
`mem_res_self` (the base case), `step_mem_res` (extending by one step from an
already-known-in-`res C_t` command), and `res_trans` (to fold the resulting
membership in `res <intermediate command>` back down to `res C_t`). -/
theorem Command.reachable_mem_res {t : D.Tid} {C_t : Command D V} {φ₀ : V.Store} :
    ∀ {c : Config D V}, Reachable t (C_t, φ₀) c → c.1 ∈ Command.res C_t := by
  intro c h
  induction h with
  | refl => exact Command.mem_res_self C_t
  | @tail b c hab hbc ih =>
      have hmem : c.1 ∈ Command.res b.1 := by
        rcases hbc with hsilent | ⟨a, hstep⟩
        · exact Command.step_mem_res hsilent c.1 c.2 rfl
        · exact Command.step_mem_res hstep c.1 c.2 rfl
      exact (Command.res_trans C_t b.1 ih) hmem

/-- `States_t` is finite (App. A): reachable configurations have
their command component in the finite set `res C_t` (`reachable_mem_res`) and
their store component in the finite `V.Store`, so the set of reachable
configurations embeds in the finite `res C_t ×ˢ Set.univ`; `InducedState`
adds only the single extra point `FinalState` (`none`) on top. -/
theorem lts_finite : Finite (InducedState D V t C_t φ₀) := by
  have hprod : {c : Config D V | c.1 ∈ Command.res C_t}.Finite := by
    have heq : {c : Config D V | c.1 ∈ Command.res C_t}
        = (Command.res C_t) ×ˢ (Set.univ : Set V.Store) := by
      ext c; simp [Set.mem_prod]
    rw [heq]
    exact (Command.res_finite C_t).prod Set.finite_univ
  have hreach : {c : Config D V | Reachable t (C_t, φ₀) c}.Finite :=
    hprod.subset (fun c hc => Command.reachable_mem_res hc)
  have hset : {oc : Option (Config D V) |
      oc = none ∨ ∃ c, oc = some c ∧ Reachable t (C_t, φ₀) c}.Finite := by
    have heq2 : {oc : Option (Config D V) |
        oc = none ∨ ∃ c, oc = some c ∧ Reachable t (C_t, φ₀) c}
        = insert none (some '' {c : Config D V | Reachable t (C_t, φ₀) c}) := by
      ext oc
      constructor
      · rintro (h | ⟨c, hc, hreach'⟩)
        · left; exact h
        · right; exact ⟨c, hreach', hc.symm⟩
      · rintro (h | ⟨c, hreach', hc⟩)
        · left; exact h
        · right; exact ⟨c, hc.symm, hreach'⟩
    rw [heq2]
    exact (hreach.image _).insert _
  exact hset.to_subtype

/-! ## Sequential programs (§2.1), instantiated -/

/-- A transition of `inducedTrans` is labelled `term` (`none`) iff its target
is `inducedFinal`. -/
theorem induced_term_iff_final :
    ∀ {p : InducedState D V t C_t φ₀} {a : Option (ThreadLabel D t)}
      {q : InducedState D V t C_t φ₀}, inducedTrans p a q → (a = none ↔ q = inducedFinal) := by
  intro p a q h
  unfold inducedTrans at h
  cases hp : p.1 with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some c =>
      rw [hp] at h
      cases a with
      | none =>
          obtain ⟨hq, _⟩ := h
          constructor
          · intro _
            exact Subtype.ext (by rw [hq]; rfl)
          · intro _
            rfl
      | some l =>
          obtain ⟨c', hq, _⟩ := h
          constructor
          · intro hcontra
            cases hcontra
          · intro hqfinal
            exfalso
            have hnone : q.1 = none := by rw [hqfinal]; rfl
            rw [hq] at hnone
            exact absurd hnone (by simp)

/-- `inducedFinal` has no outgoing `inducedTrans` transitions (`inducedTrans` matches
`none` to `False` on its source). -/
theorem induced_final_no_outgoing :
    ∀ {a : Option (ThreadLabel D t)} {q : InducedState D V t C_t φ₀},
      ¬ inducedTrans inducedFinal a q := by
  intro a q h
  unfold inducedTrans at h
  simp only [inducedFinal] at h

/-- The induced LTS packaged as a `SequentialProgram` (sequential programs (§2.1),
instantiated for the induced LTS (App. A)). -/
def inducedSeqProgram : SequentialProgram D t (InducedState D V t C_t φ₀) where
  toLTS := inducedLTS
  stateFinite := lts_finite
  term_iff_final := fun {p a q} h => induced_term_iff_final (p := p) (a := a) (q := q) h
  final_no_outgoing := fun {a q} h => induced_final_no_outgoing (a := a) (q := q) h

end RAUndecidability
