import H0mework.Fock.HistoryConditional.FiniteObservationMinimumCapacity
import H0mework.Fock.HistoryConditional.OperatorAcquisition.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObservationMinimum

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def StageLaw (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) : Prop :=
  type_of% material.factorizes ∧
  ∀ index : Index (inventoryBound runtime), ∀ nonunit : index.val ≠ 0, ∀ steps : Nat,
    type_of% (least_window runtime index nonunit steps) ∧
    (∀ length : Nat, ∀ shorter : length < index.val + 1, type_of% (no_short_update runtime index steps length shorter)) ∧
    type_of% (SourceOperatorObservationAcquisition.native_next runtime index nonunit steps) ∧
    type_of% (SourceOperatorObservationAcquisition.native_acquired_next runtime index nonunit steps) ∧
    ∀ key : ZMod 2, type_of% (SourceOperatorObservationAcquisition.model_feedback runtime index nonunit steps
      (fun index : Nat => (index : ZMod 2)) key)

theorem stage_law (runtime : LivingRuntimeState process) (material : SourceGeneratedRuntimeMaterialStageAt runtime) :
    StageLaw runtime material := by
  dsimp only [StageLaw]
  with_reducible exact ⟨material.factorizes, fun index nonunit steps =>
    ⟨least_window runtime index nonunit steps, fun length shorter => no_short_update runtime index steps length shorter,
      SourceOperatorObservationAcquisition.native_next runtime index nonunit steps,
      SourceOperatorObservationAcquisition.native_acquired_next runtime index nonunit steps,
      fun key => SourceOperatorObservationAcquisition.model_feedback runtime index nonunit steps (fun index : Nat => (index : ZMod 2)) key⟩⟩

end
end SourceFiniteObservationMinimum
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
