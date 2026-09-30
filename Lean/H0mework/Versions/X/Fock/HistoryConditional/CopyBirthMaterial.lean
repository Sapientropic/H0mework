import H0mework.Versions.X.Fock.HistoryConditional.CopyBirthFeedback

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCopyBirth

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
local instance : MeasurableSpace ParentCarrier := ⊤
local instance : MeasurableSingletonClass ParentCarrier := ⟨fun _ => trivial⟩

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ index : SourceCopyObservation.Index (inventoryBound runtime),
    let read := SourceCopyInventory.read (NativeCopy.Fock.material (inventoryBound runtime) index)
    type_of% (updated_model runtime index) ∧
    (∀ value : ParentCarrier × ParentCarrier, ∀ supported : value ∈ ((historyPMF (inventoryBound runtime)).map
      (SourceCopyObservation.joint (inventoryBound runtime) (inventoryBound runtime) index)).support,
      type_of% (original_joint_posterior runtime index value supported)) ∧
    type_of% (joint_stale runtime index) ∧
    type_of% (SourceConditionalNativeBirth.minimum_update runtime read) ∧
    type_of% (SourceConditionalNativeBirth.information_next runtime read) ∧
    type_of% (SourceConditionalNativeBirth.gap_next runtime read Prod.fst) ∧
    type_of% (SourceConditionalNativeBirth.amount_next runtime read Prod.fst) ∧
    type_of% (SourceConditionalNativeBirth.next_budget runtime read Prod.fst)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  refine ⟨material.factorizes, ?_⟩
  intro index
  dsimp only
  exact ⟨updated_model runtime index, original_joint_posterior runtime index, joint_stale runtime index,
    SourceConditionalNativeBirth.minimum_update runtime _,
    SourceConditionalNativeBirth.information_next runtime _,
    SourceConditionalNativeBirth.gap_next runtime _ Prod.fst,
    SourceConditionalNativeBirth.amount_next runtime _ Prod.fst,
    SourceConditionalNativeBirth.next_budget runtime _ Prod.fst⟩

end
end SourceConditionalCopyBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
