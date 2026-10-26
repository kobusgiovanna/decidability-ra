import RAUndecidability
import Lean.Util.CollectAxioms

/-!
# Verify

Run as part of `lake build` (its own `lean_lib`, see `lakefile.toml`), so the
build fails unless:

* no declaration of the library (any module `RAUndecidability.*`) is an
  `axiom`;
* every declaration of the library depends on no axioms beyond `propext`,
  `Classical.choice` and `Quot.sound`. A `sorry` would appear as a dependency
  on `sorryAx`;
* the main results listed in `mainResults` exist (so that a renaming cannot
  silently remove them from the check).
-/

open Lean

set_option linter.hashCommand false

/-- Axioms every result may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The results cited in the README's "Verifying the results". -/
def mainResults : List Name :=
  [``RAUndecidability.reduction, ``RAUndecidability.soundness,
    ``RAUndecidability.completeness, ``RAUndecidability.no_skipping_pairs,
    ``RAUndecidability.executionGraphOf_consistent]

/-- Fail unless `c`'s axioms are among `allowedAxioms`. -/
def checkAxioms (c : Name) : CoreM Unit := do
  let bad := (← collectAxioms (m := CoreM) c).toList.filter (· ∉ allowedAxioms)
  unless bad.isEmpty do
    throwError "{c} depends on axioms outside the allowed set: {bad}"

#eval show CoreM Unit from do
  let env ← getEnv
  for c in mainResults do
    unless env.contains c do throwError "{c} is not declared"
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless (`RAUndecidability).isPrefixOf mod do continue
    for c in data.constNames do
      if let some (.axiomInfo _) := env.find? c then throwError "{c} is an axiom"
      checkAxioms c
