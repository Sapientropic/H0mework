import H0mework.Versions.AB.Chemistry.LAlanineBasinPartition.SourceSourceBoundBasinPartition

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinPartition.Attractors

open SourceData Force.Interface
open scoped BigOperators
noncomputable section

/-- Integer receipts of the source's local maximum tests, not exact critical-point equations. -/
def sourceMaximumReceipt (atom : Atom) : Prop :=
  0 < Source.attractorDensityNano atom ∧
  0 ≤ Source.attractorSourceDistanceUpper atom ∧
  Source.attractorSourceDistanceUpper atom < Source.attractorOtherDistanceLower atom ∧
  (∀ axis : Fin 3, 0 ≤ Source.attractorGradientUpperFemto atom axis ∧
    Source.attractorGradientUpperFemto atom axis < 100000000) ∧
  (∀ i j : Fin 3, Source.attractorHessianNano atom i j = Source.attractorHessianNano atom j i) ∧
  (∀ axis : Fin 3, Source.attractorGershgorinUpper atom axis =
    Source.attractorHessianNano atom axis axis +
      (∑ j : Fin 3, |Source.attractorHessianNano atom axis j|) -
        |Source.attractorHessianNano atom axis axis| ∧
    Source.attractorGershgorinUpper atom axis < 0)

set_option maxHeartbeats 2000000 in
theorem allSourceMaximumReceipts : ∀ atom : Atom, sourceMaximumReceipt atom := by
  intro atom
  fin_cases atom
  all_goals
    refine ⟨by decide, by decide, by decide, ?_, ?_, ?_⟩
    · intro axis
      fin_cases axis <;> decide
    · intro i j
      fin_cases i <;> fin_cases j <;> decide
    · intro axis
      fin_cases axis <;> constructor <;> decide

theorem exactSourceIncidence (atom : Atom) :
    Source.attractorSourceDistanceUpper atom < Source.attractorOtherDistanceLower atom :=
  (allSourceMaximumReceipts atom).2.2.1

theorem strictHessianRowReceipts (atom : Atom) (axis : Fin 3) :
    Source.attractorGershgorinUpper atom axis < 0 :=
  ((allSourceMaximumReceipts atom).2.2.2.2.2 axis).2

theorem actualStableDisposition :
    Source.stablePointCount = 233649 ∧ Source.residualPointCount = 7 ∧
    Source.stablePointCount + Source.residualPointCount = 233656 ∧
    Source.endpointDisagreements = 0 ∧ Source.zeroWeightPointCount = 7 := by decide

theorem actualNearestCounterexample :
    Source.nearestDisagreementCount = 47062 ∧
    Source.nearestCounterexamples[0]! = (1031, 1, 0) := by decide

end
end LAlanine40K2025.BasinPartition.Attractors
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
