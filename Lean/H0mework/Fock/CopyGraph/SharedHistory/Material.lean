import H0mework.Fock.CopyGraph.Budget

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedHistory

open SourceCopyCurrentCoordinates (shared expand)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage)) : Prop :=
  history runtime (stage + 1) = shared material.next ∧
    expand material.next (history runtime (stage + 1)) = SourceCopyLiveModelFamily.family material.next ∧
    type_of% (model_history_step runtime stage) ∧ type_of% (history_budget runtime (stage + 1)) ∧
    type_of% (history_native_step runtime stage) ∧ type_of% (model_history_native_step runtime stage) ∧
    type_of% (history_native_energy runtime stage) ∧ type_of% material.factorizes

theorem stage_law (runtime : LivingRuntimeState process) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage)) : StageLaw runtime stage material := by
  dsimp only [StageLaw]
  refine ⟨history_at_material runtime stage material, ?_, ?_⟩
  · exact history_family runtime (stage + 1)
  · with_reducible exact ⟨model_history_step runtime stage, history_budget runtime (stage + 1),
      history_native_step runtime stage, model_history_native_step runtime stage,
      history_native_energy runtime stage, material.factorizes⟩

end
end SourceCopySharedHistory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
