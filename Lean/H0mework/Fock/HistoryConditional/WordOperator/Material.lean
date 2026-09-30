import H0mework.Fock.HistoryConditional.Image

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledWordOperator

open SourceGeneratedAcquisitionContinuation SourceGeneratedActionWords SourceOwnedObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  type_of% (shift_root_residual (inventoryBound runtime)) ∧ type_of% (no_shift_root_preimage (inventoryBound runtime)) ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    type_of% (action_original (inventoryBound runtime) word) ∧
    (∀ p : Polynomial ℤ, type_of% (polynomial_formula (inventoryBound runtime) word p) ∧
      type_of% (complete_polynomial (inventoryBound runtime) word p)) ∧
    ∀ target : SourceOperationNative.Carrier process,
      type_of% (whole_action (inventoryBound runtime) word target) ∧
      type_of% (complete_action (inventoryBound runtime) word target) ∧
      type_of% (recover_source (inventoryBound runtime) word target) ∧
      type_of% (source_image (inventoryBound runtime) word target) ∧
      (∀ proposal : SourceOperationNative.Carrier process, type_of% (original_fibre (inventoryBound runtime) word target proposal)) ∧
      type_of% (complete_reconstruction (inventoryBound runtime) word target) ∧
      type_of% (model_reconstruction (inventoryBound runtime) word target) ∧
      ∀ index : FamilyModel.Fock.Index (inventoryBound runtime),
        type_of% (reader_reconstruction (inventoryBound runtime) word target index)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, shift_root_residual (inventoryBound runtime), no_shift_root_preimage (inventoryBound runtime),
    fun word => ⟨action_original (inventoryBound runtime) word,
      (fun p => ⟨polynomial_formula (inventoryBound runtime) word p, complete_polynomial (inventoryBound runtime) word p⟩),
      fun target => ⟨whole_action (inventoryBound runtime) word target, complete_action (inventoryBound runtime) word target,
        recover_source (inventoryBound runtime) word target, source_image (inventoryBound runtime) word target,
        original_fibre (inventoryBound runtime) word target, complete_reconstruction (inventoryBound runtime) word target,
        model_reconstruction (inventoryBound runtime) word target, reader_reconstruction (inventoryBound runtime) word target⟩⟩⟩

end
end SourceCompiledWordOperator
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
