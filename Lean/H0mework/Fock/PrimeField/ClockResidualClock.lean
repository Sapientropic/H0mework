import H0mework.Fock.PrimeField.ClockResidualProjection
import H0mework.Realization.ScalarCofinal.FiniteLift

/-! The original source clock law survives in the paired completion with mass supplied by its prime face. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

private def two : Nat.Primes := ⟨2, Nat.prime_two⟩

def clockAt (stage : Nat) (value : JointField) : ℤ :=
  (stageRead nativeAction jointObservation stage value (Fin.last stage)).2

theorem finite_source_prefixes (value : JointField) (bound : Nat) :
    ∃ source, ∀ stage ≤ bound,
      prefixEvaluator nativeAction jointObservation stage source = stageRead nativeAction jointObservation stage value := by
  obtain ⟨source, agrees⟩ := jointData.finite_lift jointLaws value bound
  refine ⟨source, ?_⟩
  intro stage inside
  exact congrArg (jointData.stageRealization stage) (agrees stage inside)

theorem clock_prefix_read (value : JointField) (bound : Nat) (index : Fin (bound + 1)) :
    (stageRead nativeAction jointObservation bound value index).2 = clockAt index.val value := by
  obtain ⟨source, agrees⟩ := finite_source_prefixes value bound
  have high := congrArg Prod.snd (congrFun (agrees bound le_rfl) index)
  have low := congrArg Prod.snd (congrFun (agrees index.val (Nat.le_of_lt_succ index.isLt)) (Fin.last index.val))
  exact high.symm.trans low

theorem prime_mass_read (value : JointField) :
    SourcePrimeCompletion.mass (primeProjection value) =
      primeRead two (stageRead nativeAction jointObservation 0 value 0).1 := by
  change primeRead two (stageRead nativeAction observation 0 (primeProjection value) 0) = _
  rw [projection_prefix]

theorem clock_law (value : JointField) (stage : Nat) :
    clockAt stage value = clockRead value + (stage : ℤ) * SourcePrimeCompletion.mass (primeProjection value) := by
  obtain ⟨source, agrees⟩ := finite_source_prefixes value stage
  have first := congrFun (agrees 0 (Nat.zero_le _)) (0 : Fin 1)
  change jointObservation source = stageRead nativeAction jointObservation 0 value 0 at first
  have firstPair : (observation source, SourceClockModel.clock source) = stageRead nativeAction jointObservation 0 value 0 :=
    (LinearMap.congr_fun observation_joint source).symm.trans first
  have firstClock : SourceClockModel.clock source = clockRead value := congrArg Prod.snd firstPair
  have originalMass : SourceSuccessorBoundary.mass ℤ source = primeRead two (observation source) :=
    LinearMap.congr_fun (SourcePrimeCompletion.source_row_is_prime_read two 0) source
  have firstMass : SourceSuccessorBoundary.mass ℤ source = SourcePrimeCompletion.mass (primeProjection value) := by
    rw [prime_mass_read]
    exact originalMass.trans (congrArg (primeRead two) (congrArg Prod.fst firstPair))
  have last := congrFun (agrees stage le_rfl) (Fin.last stage)
  change jointObservation ((nativeAction ^ stage) source) = stageRead nativeAction jointObservation stage value (Fin.last stage) at last
  have lastClock : SourceClockModel.clock ((nativeAction ^ stage) source) = clockAt stage value :=
    congrArg Prod.snd ((LinearMap.congr_fun observation_joint ((nativeAction ^ stage) source)).symm.trans last)
  calc
    _ = SourceClockModel.clock ((SourceSuccessorBoundary.push ℤ ^ stage) source) := lastClock.symm
    _ = SourceClockModel.clock source + (stage : ℤ) * SourceSuccessorBoundary.mass ℤ source := SourceClockModel.clock_pow stage source
    _ = _ := by rw [firstClock, firstMass]

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
