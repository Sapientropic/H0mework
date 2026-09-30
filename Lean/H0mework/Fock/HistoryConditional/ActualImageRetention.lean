import H0mework.Fock.HistoryConditional.ActualImageGeometry

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors NextModel nextRead)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedActionObservationHistory (projection)
open SourceCopyCurrentCoordinates (jointObserver)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def keepIndex (runtime : LivingRuntimeState process) (index : Actors runtime) : Actors runtime.tick.next :=
  ⟨index.val, by
    have source := index.isLt
    have next := next_bound runtime
    omega⟩

def retainModel (runtime : LivingRuntimeState process) (value : NextModel runtime) : NextModel runtime.tick.next :=
  projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next.tick.next)
    (SourceConditionalVector.realizeModel runtime value)

theorem retain_model_source (runtime : LivingRuntimeState process) (index : Actors runtime) :
    retainModel runtime (nextRead runtime index) = nextRead runtime.tick.next (keepIndex runtime index) := by
  rw [retainModel, SourceConditionalVector.realized_next, SourceConditionalVector.actor_material]
  rfl

def retain (runtime : LivingRuntimeState process) (value : Image runtime) : Image runtime.tick.next :=
  ⟨retainModel runtime value.val, by
    obtain ⟨index, same⟩ := value.property
    exact ⟨keepIndex runtime index, (retain_model_source runtime index).symm.trans (congrArg (retainModel runtime) same)⟩⟩

theorem retain_actual (runtime : LivingRuntimeState process) (index : Actors runtime) :
    retain runtime (SourceConditionalNext.Image.actual (nextRead runtime) index) =
      SourceConditionalNext.Image.actual (nextRead runtime.tick.next) (keepIndex runtime index) :=
  Subtype.ext (retain_model_source runtime index)

theorem retain_read (runtime : LivingRuntimeState process) (value : Image runtime) :
    read runtime.tick.next (retain runtime value) = read runtime value := by
  obtain ⟨index, same⟩ := value.property
  have actual : value = SourceConditionalNext.Image.actual (nextRead runtime) index := Subtype.ext same.symm
  rw [actual, retain_actual, read_actual, read_actual]
  rfl

theorem retain_injective (runtime : LivingRuntimeState process) : Function.Injective (retain runtime) := by
  intro left right same
  apply read_injective runtime
  have source := congrArg (read runtime.tick.next) same
  simpa only [retain_read] using source

theorem retained_material (runtime : LivingRuntimeState process) (index : Actors runtime) :
    HEq ((history runtimeSeed (inventoryBound runtime.tick.next)).stageAt (keepIndex runtime index))
      ((history runtimeSeed (inventoryBound runtime)).stageAt index) := by
  rfl

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
