import H0mework.Fock.HistoryConditional.InventoryMaterial
import H0mework.Fock.CopyGraph.SharedNextSourceStepModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors NextModel nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (jointModelEquiv maximumIndex sourceRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev Image (runtime : LivingRuntimeState process) := SourceConditionalNext.Image.Values (nextRead runtime)

theorem next_bound (runtime : LivingRuntimeState process) : inventoryBound runtime.tick.next = inventoryBound runtime + 1 := by
  rw [← SourceConditionalInventory.next_runtime, SourceConditionalInventory.runtime_bound]

def advanceIndex (runtime : LivingRuntimeState process) (index : Actors runtime) : Actors runtime.tick.next :=
  ⟨index.val + 1, by
    have source := index.isLt
    have next := next_bound runtime
    omega⟩

theorem model_step_source (runtime : LivingRuntimeState process) (index : Actors runtime) :
    SourceCopyNativeSharedUpdate.modelStep runtime.tick.next (nextRead runtime index) =
      nextRead runtime.tick.next (advanceIndex runtime index) := by
  apply (jointModelEquiv runtime.tick.next.tick.next).injective
  rw [SourceCopyNativeSharedUpdate.modelStep, LinearEquiv.apply_symm_apply]
  rw [nextRead, SourceCopyCurrentCoordinates.joint_model_source]
  change SourceCopyNativeSharedUpdate.step runtime.tick.next
    (jointModelEquiv runtime.tick.next (nextRead runtime index)) =
      sourceRead runtime.tick.next.tick.next (maximumIndex runtime.tick.next.tick.next) 0
        (SourceCopyNativeModelStep.sourceValue ((history runtimeSeed (inventoryBound runtime.tick.next)).stageAt (advanceIndex runtime index)).next)
  rw [SourceCopyNativeSharedUpdate.step]
  change sourceRead runtime.tick.next.tick.next (maximumIndex runtime.tick.next.tick.next) 0
    (SourceJointClockGraph.action (SourceConditionalVector.realizeModel runtime (nextRead runtime index))) = _
  rw [SourceConditionalVector.realized_next, SourceConditionalVector.actor, SourceCopyNativeModelStep.source_value_next,
    SourceCopyNativeModelStep.source_value_next]
  rfl

def step (runtime : LivingRuntimeState process) (value : Image runtime) : Image runtime.tick.next :=
  ⟨SourceCopyNativeSharedUpdate.modelStep runtime.tick.next value.val, by
    obtain ⟨index, same⟩ := value.property
    exact ⟨advanceIndex runtime index, (model_step_source runtime index).symm.trans
      (congrArg (SourceCopyNativeSharedUpdate.modelStep runtime.tick.next) same)⟩⟩

theorem step_actual (runtime : LivingRuntimeState process) (index : Actors runtime) :
    step runtime (SourceConditionalNext.Image.actual (nextRead runtime) index) =
      SourceConditionalNext.Image.actual (nextRead runtime.tick.next) (advanceIndex runtime index) :=
  Subtype.ext (model_step_source runtime index)

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
