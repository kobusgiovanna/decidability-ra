import RAUndecidability.ProgramSemantics.Syntax
import Mathlib.Logic.Function.Basic

/-!
# Step

The "Operational semantics" paragraph of the paper's Appendix A:

* App. A: configurations;
* App. A: the silent and
  labelled step relations, and the congruences closing both.
-/

namespace RAUndecidability

variable {D : Domains} {V : Vocabulary D}

/-! ## Configurations (App. A) -/

/-- A configuration (App. A): a pair of a command and a store. -/
abbrev Config (D : Domains) (V : Vocabulary D) := Command D V × V.Store

/-! ## Silent steps (App. A), labelled steps (App. A), the congruence rules (App. A) -/

/-- **Paper:** App. A, ¶ Operational semantics.

The step relation underlying both silent steps (App. A) and labelled steps (App. A)
(`Step t a c c'`), together with the two congruences of the congruence rules (App. A).

The paper treats `⇝` and `→^a` as two relations, unified only informally by
writing `→^λ` "for either, with `λ` ranging over labels and the silent
action" when stating the congruences. Formalizing them as two separate
inductive relations would force the two congruence constructors
(`seq-step`/`loop-step`) to be duplicated verbatim into both. Instead `Step`
is the single relation the paper's `→^λ` notation already points to, and
`SilentTo`/`StepTo` below recover the paper's two named relations from it.

The label index `a : Option (Option (ThreadLabel D t))` has to be *doubly*
optional, not singly: there are three cases, not two, since the labelled
alphabet `Option (ThreadLabel D t)` (`SequentialProgram`'s alphabet) already
uses its own `none` for `term`, and colliding that with "no label at all"
would conflate the silent case with the term case. So:
* `none` — a silent step;
* `some none` — the labelled step on `term`;
* `some (some l)` — the labelled step on a real event label `l`.

The target is `Option (Config D V)`, not `Config D V`: the `term` rule steps
to `qfn`, which — as for `term ∉ LabelDom^t` and for the alphabet in
`SequentialProgram` — is encoded as `none` rather than as a side condition,
so that "`qfn` is not a configuration" and "`qfn` has no outgoing
transitions" both hold by construction (no constructor has `none` as a
source). -/
inductive Step (t : D.Tid) :
    Option (Option (ThreadLabel D t)) → Config D V → Option (Config D V) → Prop
  | assign {v e φ} :
      Step t none ⟨.assign v e, φ⟩ (some ⟨.skip, Function.update φ v (V.eval e φ)⟩)
  | ndet {v X hX c φ} (hc : c ∈ X) :
      Step t none ⟨.ndetAssign v X hX, φ⟩ (some ⟨.skip, Function.update φ v c⟩)
  | seqSkip {C φ} : Step t none ⟨.seq .skip C, φ⟩ (some ⟨C, φ⟩)
  | seqBreak {C φ} : Step t none ⟨.seq .brk C, φ⟩ (some ⟨.brk, φ⟩)
  | iteTrue {b C1 C2 φ} (h : V.evalB b φ = true) :
      Step t none ⟨.ite b C1 C2, φ⟩ (some ⟨C1, φ⟩)
  | iteFalse {b C1 C2 φ} (h : V.evalB b φ = false) :
      Step t none ⟨.ite b C1 C2, φ⟩ (some ⟨C2, φ⟩)
  | whileTrue {b C φ} (h : V.evalB b φ = true) :
      Step t none ⟨.whileLoop b C, φ⟩ (some ⟨.loopSeq C (.whileLoop b C), φ⟩)
  | whileFalse {b C φ} (h : V.evalB b φ = false) :
      Step t none ⟨.whileLoop b C, φ⟩ (some ⟨.skip, φ⟩)
  | loopSkip {C φ} : Step t none ⟨.loopSeq .skip C, φ⟩ (some ⟨C, φ⟩)
  | loopBreak {C φ} : Step t none ⟨.loopSeq .brk C, φ⟩ (some ⟨.skip, φ⟩)
  | write {u e φ} :
      Step t (some (some ⟨EventLabel.wt t u (V.evalV e φ), rfl⟩)) ⟨.write u e, φ⟩
        (some ⟨.skip, φ⟩)
  | read {u e φ} :
      Step t (some (some ⟨EventLabel.rd t u (V.evalV e φ), rfl⟩)) ⟨.read u e, φ⟩
        (some ⟨.skip, φ⟩)
  | termStep {φ} : Step t (some none) ⟨.term, φ⟩ none
  | seqCongr {a C1 C1' C2 φ φ'} :
      Step t a ⟨C1, φ⟩ (some ⟨C1', φ'⟩) → Step t a ⟨.seq C1 C2, φ⟩ (some ⟨.seq C1' C2, φ'⟩)
  | loopCongr {a C1 C1' C2 φ φ'} :
      Step t a ⟨C1, φ⟩ (some ⟨C1', φ'⟩) →
        Step t a ⟨.loopSeq C1 C2, φ⟩ (some ⟨.loopSeq C1' C2, φ'⟩)

/-- Silent steps (App. A): `Step` carrying no label. -/
def SilentTo (t : D.Tid) (c1 c2 : Config D V) : Prop := Step t none c1 (some c2)

/-- Labelled steps (App. A): `Step` labelled by `a`, where
`a = none` is the label `term` and `a = some l` is the real event label `l`.
The target stays `Option (Config D V)` here too, since `a = none` (`term`)
steps to `qfn`. -/
def StepTo (t : D.Tid) (a : Option (ThreadLabel D t)) (c1 : Config D V)
    (c2 : Option (Config D V)) : Prop := Step t (some a) c1 c2

end RAUndecidability
