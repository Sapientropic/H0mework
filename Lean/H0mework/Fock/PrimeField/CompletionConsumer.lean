import H0mework.Fock.PrimeField.CompletionConditional
import H0mework.Fock.SourceHistory.PrimeCompletionRegression

/-! Original K/T and the source-controlled next consume the complete Field's faithful coefficient action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

theorem native_coefficients (runtime : LivingRuntimeState process) :
    coefficients sourceOwner (fieldPoint (process := process) rawField runtime.state) =
      fun index => SourceOperationNative.point runtime index :=
  coefficients_source sourceOwner (SourceOperationNative.point runtime)

theorem complete_information_consumed (bound : Nat) :
    let target := (SourcePrimeCalculation.normal bound).targetRuntime
    type_of% (coefficients_injective sourceOwner) ∧
      (∀ value : Field, ∀ prime stage, type_of% (source_row_on_completion sourceOwner value prime stage)) ∧
      (∀ value : Field, type_of% (mass_advance sourceOwner value) ∧
        type_of% (coefficient_zero_advance sourceOwner value) ∧
        ∀ index, type_of% (coefficient_successor_advance sourceOwner value index)) ∧
      type_of% (field_action_injective sourceOwner) ∧
      type_of% (original_unit_coefficient sourceOwner) ∧ type_of% original_unit_mass ∧
      type_of% (advanced_unit_mass sourceOwner) ∧ type_of% (no_preimage_original_unit sourceOwner) ∧
      (∀ task : Fin (bound + 1) → ℂ, ∀ actor : Fin (bound + 1),
        type_of% (transfer_reads_complete_coefficients bound task actor)) ∧
      (∀ task : Fin (bound + 1) → ℂ, type_of% (SourcePrimeHistoryRecovery.residuals_zero sourceOwner bound task) ∧
        type_of% (SourcePrimeHistoryRecovery.original_actor_reconstructed sourceOwner bound task)) ∧
      coefficients sourceOwner (fieldPoint (process := process) rawField target.state) =
        (fun index => SourceOperationNative.point target index) ∧
      type_of% (SourceOperationNative.Observed.model_factorizes (process := process) rawField target) ∧
      type_of% (SourcePrimeCalculation.source_calculation_consumed bound) := by
  exact ⟨coefficients_injective sourceOwner, source_row_on_completion sourceOwner,
    (fun value => ⟨mass_advance sourceOwner value, coefficient_zero_advance sourceOwner value,
      coefficient_successor_advance sourceOwner value⟩),
    field_action_injective sourceOwner, original_unit_coefficient sourceOwner, original_unit_mass,
    advanced_unit_mass sourceOwner, no_preimage_original_unit sourceOwner, transfer_reads_complete_coefficients bound,
    (fun task => ⟨SourcePrimeHistoryRecovery.residuals_zero sourceOwner bound task,
      SourcePrimeHistoryRecovery.original_actor_reconstructed sourceOwner bound task⟩),
    native_coefficients _, SourceOperationNative.Observed.model_factorizes (process := process) rawField _,
    SourcePrimeCalculation.source_calculation_consumed bound⟩

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
