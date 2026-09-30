import H0mework.Fock.PrimeField.CompletionAction

/-! The original native unit keeps its mass while witnessing the completed action's missing inverse fibre. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeCompletion

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedScalarCofinalTopology.NativeProbability

noncomputable section

theorem original_unit_coefficient (owner : GlobalParentOwner) :
    coefficient owner 0 (fieldPoint (process := process) rawField 0) = 1 :=
  (coefficient_source owner 0 (SourceOperationNative.statePoint process 0)).trans (Finsupp.single_eq_same)

theorem original_unit_mass : mass (fieldPoint (process := process) rawField 0) = 1 :=
  (mass_source (SourceOperationNative.statePoint process 0)).trans (SourceSuccessorBoundary.mass_unit ℤ)

theorem advanced_unit_mass (owner : GlobalParentOwner) :
    mass (fieldAction (process := process) rawField (fieldPoint (process := process) rawField 0)) = 1 :=
  (mass_advance owner _).trans original_unit_mass

theorem no_preimage_original_unit (owner : GlobalParentOwner) :
    ¬ ∃ value : Field, fieldAction (process := process) rawField value = fieldPoint (process := process) rawField 0 := by
  rintro ⟨value, source⟩
  have coordinate := congrArg (coefficient owner 0) source
  rw [coefficient_zero_advance, original_unit_coefficient] at coordinate
  exact zero_ne_one coordinate

end
end SourcePrimeCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
