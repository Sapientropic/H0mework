import Mathlib.Data.Finset.Basic

/-!
# Genuine actionable-freedom change on one common code carrier

Power cannot be inferred from a phase label, payoff difference or constraint
owner readout alone.  Its future-facing witness must exhibit an actionable
code that is genuinely lost or restored, or a pair of genuinely exchanged
codes.  Source and target are compared on the same finite carrier; no completed
future, representative selector or caller-supplied change verdict is stored.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Power

universe u

/-- A code is actionable when it is admitted by the generated freedom fibre
and is not the distinguished idle code. -/
def ActionableAt {Code : Type u} [DecidableEq Code]
    (idle : Code → Prop) (freedom : Finset Code) (code : Code) : Prop :=
  code ∈ freedom ∧ ¬ idle code

/-- The three possible shapes of a genuine change.  This is a readout of the
witness below, not an input used to classify equal fibres. -/
inductive FreedomChangeKind where
  | lost
  | restored
  | redirected
  deriving DecidableEq, Repr

/-- Exact actionable change between two generated freedom fibres.

The redirected constructor requires a source-only actionable code and a
target-only actionable code.  Consequently every constructor proves the two
fibres unequal; a mere relabelling of an unchanged fibre is unrepresentable.
-/
inductive ActionableFreedomChange {Code : Type u} [DecidableEq Code]
    (idle : Code → Prop) (source target : Finset Code) : Type u where
  | lost (code : Code)
      (sourceActionable : ActionableAt idle source code)
      (targetAbsent : code ∉ target) :
      ActionableFreedomChange idle source target
  | restored (code : Code)
      (sourceAbsent : code ∉ source)
      (targetActionable : ActionableAt idle target code) :
      ActionableFreedomChange idle source target
  | redirected (sourceCode targetCode : Code)
      (sourceActionable : ActionableAt idle source sourceCode)
      (sourceCodeAbsentAtTarget : sourceCode ∉ target)
      (targetCodeAbsentAtSource : targetCode ∉ source)
      (targetActionable : ActionableAt idle target targetCode) :
      ActionableFreedomChange idle source target

namespace ActionableFreedomChange

def kind {Code : Type u} [DecidableEq Code]
    {idle : Code → Prop} {source target : Finset Code} :
    ActionableFreedomChange idle source target → FreedomChangeKind
  | .lost _ _ _ => .lost
  | .restored _ _ _ => .restored
  | .redirected _ _ _ _ _ _ => .redirected

/-- Every genuine change refutes equality of the compared fibres. -/
theorem freedom_ne {Code : Type u} [DecidableEq Code]
    {idle : Code → Prop} {source target : Finset Code}
    (change : ActionableFreedomChange idle source target) :
    source ≠ target := by
  intro equal
  cases change with
  | lost code sourceActionable targetAbsent =>
      exact targetAbsent (equal ▸ sourceActionable.1)
  | restored code sourceAbsent targetActionable =>
      exact sourceAbsent (equal.symm ▸ targetActionable.1)
  | redirected sourceCode targetCode sourceActionable sourceAbsent
      targetAbsent targetActionable =>
      exact sourceAbsent (equal ▸ sourceActionable.1)

/-- Redirected freedom really exchanges two different common-carrier codes. -/
theorem redirected_codes_ne {Code : Type u} [DecidableEq Code]
    {idle : Code → Prop} {source _target : Finset Code}
    {sourceCode targetCode : Code}
    (sourceActionable : ActionableAt idle source sourceCode)
    (targetCodeAbsentAtSource : targetCode ∉ source) :
    sourceCode ≠ targetCode := by
  intro equal
  subst targetCode
  exact targetCodeAbsentAtSource sourceActionable.1

/-- Equal generated fibres admit no fabricated actionable change. -/
theorem isEmpty_of_eq {Code : Type u} [DecidableEq Code]
    {idle : Code → Prop} {source target : Finset Code}
    (equal : source = target) :
    IsEmpty (ActionableFreedomChange idle source target) :=
  ⟨fun change => change.freedom_ne equal⟩

/-- An empty source and target pair has no actionable change, independently
of how idleness is defined. -/
theorem isEmpty_empty {Code : Type u} [DecidableEq Code]
    (idle : Code → Prop) :
    IsEmpty (ActionableFreedomChange idle (∅ : Finset Code) ∅) :=
  isEmpty_of_eq rfl

end ActionableFreedomChange
end Power
end Society
end ProcessGame
end SaturationMonoid
