import H0mework.Fock.HistoryPolynomial.Native
import H0mework.Fock.HistoryPolynomial.Clock

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCyclicModule

open SourcePrimeHistoryRecovery SourceGeneratedActionObservationHistory
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def NativeAt (runtime : LivingRuntimeState process) : Prop :=
    type_of% (native_program runtime) ∧ type_of% (native_program_next runtime) ∧
      type_of% (native_observation runtime) ∧ type_of% (SourceOperationNative.point_factorizes runtime) ∧
      type_of% (SourceOperationNative.Observed.model_factorizes (process := process) rawField runtime) ∧
      type_of% (coversAt_factorizes runtime .particleWave) ∧
      type_of% (coversAt_factorizes runtime.tick.next .particleWave)

theorem native_consumed (runtime : LivingRuntimeState process) : NativeAt runtime :=
  ⟨native_program runtime, native_program_next runtime, native_observation runtime,
    SourceOperationNative.point_factorizes runtime,
    SourceOperationNative.Observed.model_factorizes (process := process) rawField runtime,
    coversAt_factorizes runtime .particleWave, coversAt_factorizes runtime.tick.next .particleWave⟩

def RecoveryAt (round : Nat) : Prop :=
    type_of% original_root ∧ type_of% program_injective ∧ type_of% program_surjective ∧
    type_of% generator_is_one ∧
    (∀ word : DynamicSource, type_of% (single_generator word)) ∧
    (∀ polynomial : Polynomial ℤ,
      type_of% (program_is_action polynomial) ∧ type_of% (model_program polynomial) ∧
      type_of% (model_coefficients polynomial) ∧
      (∀ index : Nat, type_of% (program_coefficient polynomial index) ∧ type_of% (original_selector_reads polynomial index)) ∧
      ProgramAt round polynomial) ∧
    (∀ (B : Type) [AddCommGroup B], ∀ read : process.State → B,
      type_of% (relations_finite read) ∧ type_of% (ideal_finite read) ∧
      ∀ polynomial : Polynomial ℤ,
        type_of% (ideal_is_source read polynomial) ∧ type_of% (presentation_reads read polynomial)) ∧
    type_of% prime_ideal_zero ∧ type_of% clock_relation_nonzero ∧
    type_of% clock_model_erases ∧ type_of% prime_model_retains ∧ type_of% prime_selector_recovers ∧
    NativeAt (roundRuntime round) ∧
    type_of% (SourceFixedInventoryRecovery.sourceGeneratedFixedInventoryRecovery (roundRuntime round))

theorem sourceGeneratedCyclicModuleRecovery (round : Nat) : RecoveryAt round := by
  dsimp only [RecoveryAt]
  exact ⟨original_root, program_injective, program_surjective, generator_is_one, single_generator,
    (fun polynomial => ⟨program_is_action polynomial, model_program polynomial, model_coefficients polynomial,
      (fun index => ⟨program_coefficient polynomial index, original_selector_reads polynomial index⟩),
      original_program_consumed round polynomial⟩),
    (fun _B _instance read => ⟨relations_finite read, ideal_finite read,
      fun polynomial => ⟨ideal_is_source read polynomial, presentation_reads read polynomial⟩⟩),
    prime_ideal_zero, clock_relation_nonzero, clock_model_erases, prime_model_retains, prime_selector_recovers,
    native_consumed (roundRuntime round),
    SourceFixedInventoryRecovery.sourceGeneratedFixedInventoryRecovery (roundRuntime round)⟩

end
end SourceCyclicModule
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
