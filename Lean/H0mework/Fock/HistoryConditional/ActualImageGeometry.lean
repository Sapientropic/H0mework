import H0mework.Fock.HistoryConditional.ActualImageSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors NextModel nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (jointModelEquiv maximumIndex sourceRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def read (runtime : LivingRuntimeState process) (value : Image runtime) : SourceJointClockGraph.Carrier :=
  SourceConditionalVector.realizeModel runtime value.val

theorem realize_injective (runtime : LivingRuntimeState process) : Function.Injective (SourceConditionalVector.realizeModel runtime) := by
  have realization := Function.LeftInverse.injective
    (SourceCopyCurrentCoordinates.realize_source runtime.tick.next (maximumIndex runtime.tick.next) 0)
  unfold SourceConditionalVector.realizeModel
  exact realization.comp (jointModelEquiv runtime.tick.next).injective

theorem read_injective (runtime : LivingRuntimeState process) : Function.Injective (read runtime) := by
  intro left right same
  exact Subtype.ext (realize_injective runtime same)

theorem step_read (runtime : LivingRuntimeState process) (value : Image runtime) :
    read runtime.tick.next (step runtime value) = SourceJointClockGraph.action (read runtime value) := by
  change SourceCopyCurrentCoordinates.realize runtime.tick.next.tick.next (maximumIndex runtime.tick.next.tick.next) 0
    (jointModelEquiv runtime.tick.next.tick.next
      (SourceCopyNativeSharedUpdate.modelStep runtime.tick.next value.val)) = _
  rw [SourceCopyNativeSharedUpdate.modelStep, LinearEquiv.apply_symm_apply, SourceCopyNativeSharedUpdate.step_realize]
  rfl

theorem step_injective (runtime : LivingRuntimeState process) : Function.Injective (step runtime) := by
  intro left right same
  apply read_injective runtime
  have source := congrArg (fun value => SourceJointClockGraph.recover (read runtime.tick.next value)) same
  simpa only [step_read, SourceJointClockGraph.recover_action] using source

theorem read_actual (runtime : LivingRuntimeState process) (index : Actors runtime) :
    read runtime (SourceConditionalNext.Image.actual (nextRead runtime) index) =
      SourceConditionalInventory.values (inventoryBound runtime) index :=
  (SourceConditionalInventory.values_original runtime index).symm

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
