import H0mework.Fock.PrimeField.RecoveryConsumer
import H0mework.Realization.ScalarCofinal.FiniteLift

/-! The existing complete Field supplies common finite source witnesses for its original prime reads. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState
open ParticleWaveFock ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery

noncomputable section

abbrev Field := SourceGeneratedScalarCofinalTopology.NativeProbability.Field (process := process) rawField

def read (stage : Nat) : Field →ₗ[ℤ] IntegralOneParticle :=
  (LinearMap.proj (Fin.last stage)).comp (stageRead nativeAction observation stage)

theorem read_source (stage : Nat) (word : SourceOperationNative.Carrier process) :
    read stage (sourceMap nativeAction observation word) = observation ((nativeAction ^ stage) word) :=
  source_reads_stage nativeAction observation stage word (Fin.last stage)

def coefficient (owner : GlobalParentOwner) (index : Nat) : Field →ₗ[ℤ] ℤ :=
  (primeRead (selectedPrime owner index)).comp (read (delay owner index + 1) - read (delay owner index))

theorem coefficient_source (owner : GlobalParentOwner) (index : Nat) (word : SourceOperationNative.Carrier process) :
    coefficient owner index (sourceMap nativeAction observation word) = word index := by
  change primeRead (selectedPrime owner index)
    (read (delay owner index + 1) (sourceMap nativeAction observation word) -
      read (delay owner index) (sourceMap nativeAction observation word)) = _
  rw [read_source, read_source]
  exact recovers_source_word owner index word

theorem finite_source_prefixes (value : Field) (bound : Nat) :
    ∃ word : SourceOperationNative.Carrier process, ∀ stage ≤ bound,
      prefixEvaluator nativeAction observation stage word = stageRead nativeAction observation stage value := by
  obtain ⟨word, agrees⟩ := (data nativeAction observation).finite_lift (compatible nativeAction observation) value bound
  refine ⟨word, ?_⟩
  intro stage inside
  have actual := congrArg ((data nativeAction observation).stageRealization stage) (agrees stage inside)
  change prefixEvaluator nativeAction observation stage word = stageRead nativeAction observation stage value at actual
  exact actual

theorem finite_source_reads (value : Field) (bound : Nat) :
    ∃ word : SourceOperationNative.Carrier process, ∀ stage ≤ bound,
      read stage (sourceMap nativeAction observation word) = read stage value := by
  obtain ⟨word, agrees⟩ := finite_source_prefixes value bound
  exact ⟨word, fun stage inside => (read_source stage word).trans (congrFun (agrees stage inside) (Fin.last stage))⟩

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
