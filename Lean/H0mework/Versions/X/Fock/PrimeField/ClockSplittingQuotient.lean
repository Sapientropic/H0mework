import H0mework.Versions.X.Fock.PrimeField.ClockSplittingCorrection

/-! Source correction descends through the original prime kernel into the existing paired quotient. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockSplitting

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery SourcePrimeClockResidual

noncomputable section

abbrev primeData := data nativeAction observation
abbrev primeLaws := compatible nativeAction observation

private def two : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem prime_kernel_mass (stage : Nat) (source : SourceOperationNative.Carrier process)
    (hidden : source ∈ primeData.stageKernel stage) : SourceSuccessorBoundary.mass ℤ source = 0 := by
  have first := congrFun (LinearMap.mem_ker.mp hidden) (0 : Fin (stage + 1))
  change observation source = 0 at first
  have mass := LinearMap.congr_fun (SourcePrimeCompletion.source_row_is_prime_read two 0) source
  change SourceSuccessorBoundary.mass ℤ source = primeRead two (observation source) at mass
  rw [mass, first, map_zero]

theorem correction_descends (stage : Nat) :
    primeData.stageKernel stage ≤ LinearMap.ker ((jointData.quotientMap stage).comp (correction stage)) := by
  intro source hidden
  apply (Submodule.Quotient.mk_eq_zero _).2
  apply LinearMap.mem_ker.mpr
  change prefixEvaluator nativeAction jointObservation stage (correction stage source) = 0
  rw [corrected_prefix stage stage le_rfl]
  funext index
  have prime := congrFun (LinearMap.mem_ker.mp hidden) index
  change observation ((nativeAction ^ index.val) source) = 0 at prime
  simp only [prime, prime_kernel_mass stage source hidden, mul_zero, Pi.zero_apply, Prod.mk_zero_zero]

def quotientSection (stage : Nat) : primeData.StageQuotient stage →ₗ[ℤ] jointData.StageQuotient stage :=
  (primeData.stageKernel stage).liftQ ((jointData.quotientMap stage).comp (correction stage)) (correction_descends stage)

theorem quotient_section_source (stage : Nat) (source : SourceOperationNative.Carrier process) :
    quotientSection stage (primeData.quotientMap stage source) = jointData.quotientMap stage (correction stage source) := rfl

theorem quotient_section_transition (stage : Nat) :
    (quotientSection stage).comp (primeData.quotientTransition primeLaws stage) =
      (jointData.quotientTransition jointLaws stage).comp (quotientSection (stage + 1)) := by
  apply LinearMap.ext
  intro value
  obtain ⟨source, rfl⟩ := Submodule.mkQ_surjective (primeData.stageKernel (stage + 1)) value
  change jointData.quotientMap stage (correction stage source) = jointData.quotientMap stage (correction (stage + 1) source)
  apply jointData.stageRealization_injective stage
  change prefixEvaluator nativeAction jointObservation stage (correction stage source) =
    prefixEvaluator nativeAction jointObservation stage (correction (stage + 1) source)
  rw [corrected_prefix stage stage le_rfl, corrected_prefix (stage + 1) stage (Nat.le_succ stage)]

end
end SourcePrimeClockSplitting
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
