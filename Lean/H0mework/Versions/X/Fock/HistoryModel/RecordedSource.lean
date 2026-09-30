import H0mework.Versions.X.Fock.PrimeFieldCalculation.CalculationBirth

/-! The recorded source-born coefficients reconstruct the original actual update in its existing free source carrier. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourcePrimeHistoryRecovery SourcePrimeCalculation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

def sourceWord (bound : Nat) : Raw sourceOwner bound →ₗ[ℤ] Carrier Current :=
  ∑ index : Fin (bound + 1),
    (LinearMap.toSpanSingleton ℤ (Carrier Current)
      (sourceAction nativeStep (sourcePoint ((runtimeAt index.val).current.visit.current : Current)))).comp
        (coefficient sourceOwner bound index)

theorem sourceWord_actual_birth (bound : Nat) (actor : Fin (bound + 1)) :
    sourceWord bound (recordedQuery bound actor) =
      ∑ index : Fin (bound + 1), birthCoefficient bound index actor •
        sourceAction nativeStep (sourcePoint ((runtimeAt index.val).current.visit.current : Current)) := by
  change (∑ index : Fin (bound + 1),
    (LinearMap.toSpanSingleton ℤ (Carrier Current)
      (sourceAction nativeStep (sourcePoint ((runtimeAt index.val).current.visit.current : Current)))).comp
        (coefficient sourceOwner bound index)) (recordedQuery bound actor) = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro index _
  change coefficient sourceOwner bound index (recordedQuery bound actor) •
    sourceAction nativeStep (sourcePoint ((runtimeAt index.val).current.visit.current : Current)) = _
  rw [recorded_coefficient_is_birth]

theorem sourceWord_actual_update (bound : Nat) (actor : Fin (bound + 1)) :
    sourceWord bound (recordedQuery bound actor) =
      sourceAction nativeStep (sourcePoint ((runtimeAt actor.val).current.visit.current : Current)) := by
  rw [sourceWord_actual_birth]
  let term : Fin (bound + 1) → Carrier Current := fun index =>
    sourceAction nativeStep (sourcePoint ((runtimeAt index.val).current.visit.current : Current))
  change (∑ index : Fin (bound + 1), birthCoefficient bound index actor • term index) = term actor
  classical
  simp only [birth_coefficient_is_delta, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single actor]
  · exact if_pos rfl
  · intro index _ different
    exact if_neg (Ne.symm different)
  · intro absent
    exact (absent (Finset.mem_univ actor)).elim

theorem sourceWord_actual_point (bound : Nat) (actor : Fin (bound + 1)) :
    sourceWord bound (recordedQuery bound actor) =
      sourcePoint ((runtimeAt (actor.val + 1)).current.visit.current : Current) := by
  let current : Current := (runtimeAt actor.val).current.visit.current
  exact (sourceWord_actual_update bound actor).trans (sourceAction_point nativeStep current)

end
end SourceGeneratedActionWords.Fock.OriginalHilbert.Recorded
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
