import H0mework.Fock.PrimeFieldCalculation.CalculationBirth

/-! Actual source-born calculation coefficients generate the original complete conditional transfer weights. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCalculation

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourcePrimeHistoryRecovery
open SourceGeneratedActionObservationHistory SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceConditionalTransfer

noncomputable section

theorem conditional_weight_is_birth (bound : Nat) (index candidate : Fin (bound + 1)) :
    ((FiniteRecurrence.Native.conditional (process := process) rawField (windowBound sourceOwner bound) runtimeSeed bound index candidate).toReal : ℂ) =
      (birthCoefficient bound candidate index : ℂ) := by
  rw [conditional_pure, birth_coefficient_is_delta, PMF.pure_apply]
  by_cases same : candidate = index
  · subst candidate
    simp
  · simp [same, Ne.symm same]

theorem transfer_from_birth (bound : Nat) (task : Fin (bound + 1) → ℂ) (index : Fin (bound + 1)) :
    SourceGeneratedEmpiricalHilbert.transfer (process := process) rawField runtimeSeed bound
      (Runtime.Actor.actorTransfer (process := process) rawField runtimeSeed bound (taskValue (historyPMF bound) task))
      (nextAtom (process := process) rawField runtimeSeed bound index) = sourceAnswer bound task index := by
  rw [complete_transfer sourceOwner]
  unfold sourceAnswer
  apply Finset.sum_congr rfl
  intro candidate _
  rw [Complex.real_smul, conditional_weight_is_birth]

end
end SourcePrimeCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
