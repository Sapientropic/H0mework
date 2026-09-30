import H0mework.Versions.X.Fock.HistoryConditional.GWordConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompiledGWord

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ word : List (Fock.Letter (inventoryBound runtime)),
    ((∀ source : SourceOperationNative.Carrier process, type_of% (source_effect (inventoryBound runtime) word source)) ∧
      ∀ other : List (Fock.Letter (inventoryBound runtime)), type_of% (effect_kernel (inventoryBound runtime) word other)) ∧
    (∀ value : SourceJointClockGraph.Carrier, type_of% (energy_expanded (inventoryBound runtime) word value)) ∧
    type_of% (image_original runtime (inventoryBound runtime) word) ∧
    (∀ actor : SourceConditionalModel.Actors runtime, type_of% (history_recovers runtime (inventoryBound runtime) word actor)) ∧
    ∀ observationDepth : Nat,
      type_of% (field_optimal runtime (inventoryBound runtime) word observationDepth) ∧
      type_of% (field_amplification runtime (inventoryBound runtime) word observationDepth) ∧
      ∀ decoder : Field parity → SourceJointClockGraph.Carrier,
        type_of% (field_error_account runtime (inventoryBound runtime) word observationDepth decoder) ∧
        type_of% (field_information runtime (inventoryBound runtime) word observationDepth decoder)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material :=
  ⟨material.factorizes, fun word => ⟨⟨source_effect (inventoryBound runtime) word, effect_kernel (inventoryBound runtime) word⟩,
    energy_expanded (inventoryBound runtime) word, image_original runtime (inventoryBound runtime) word,
    history_recovers runtime (inventoryBound runtime) word,
    fun observationDepth => ⟨field_optimal runtime (inventoryBound runtime) word observationDepth,
      field_amplification runtime (inventoryBound runtime) word observationDepth,
      fun decoder => ⟨field_error_account runtime (inventoryBound runtime) word observationDepth decoder,
        field_information runtime (inventoryBound runtime) word observationDepth decoder⟩⟩⟩⟩

end
end SourceCompiledGWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
