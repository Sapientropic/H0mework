import H0mework.Fock.HistoryModel.RecordedAcquisition

/-! An actual record produces its native unit; a zero raw packet does not receive that occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourcePrimeCalculation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

theorem sourceWord_recorded_ne_zero (bound : Nat) (actor : Fin (bound + 1)) :
    sourceWord bound (recordedQuery bound actor) ≠ 0 := by
  rw [sourceWord_actual_point]
  change Finsupp.single ((runtimeAt (actor.val + 1)).current.visit.current : Current) (1 : ℤ) ≠ 0
  exact Finsupp.single_ne_zero.mpr one_ne_zero

theorem recordedQuery_ne_zero (bound : Nat) (actor : Fin (bound + 1)) : recordedQuery bound actor ≠ 0 := by
  intro zero
  apply sourceWord_recorded_ne_zero bound actor
  rw [zero, map_zero]

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
