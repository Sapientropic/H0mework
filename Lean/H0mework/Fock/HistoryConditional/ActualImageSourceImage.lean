import H0mework.Fock.HistoryConditional.ActualImageBoundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceActualImageStep

open SourceConditionalModel (Actors nextRead)
open SourceConditionalVector (actor)
open SourceGeneratedActionObservationHistory (projection)
open SourceCopyCurrentCoordinates (jointObserver)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev SourceImage (runtime : LivingRuntimeState process) := SourceConditionalNext.Image.Values (actor runtime)

def act (runtime : LivingRuntimeState process) (value : SourceImage runtime) : Image runtime :=
  ⟨projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next)
    (SourceJointClockGraph.action value.val), by
      obtain ⟨index, same⟩ := value.property
      refine ⟨index, ?_⟩
      rw [SourceConditionalModel.next_action]
      change projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next)
        (SourceJointClockGraph.action (actor runtime index)) = _
      rw [same]⟩

def recover (runtime : LivingRuntimeState process) (value : Image runtime) : SourceImage runtime :=
  ⟨SourceJointClockGraph.recover (read runtime value), by
    obtain ⟨index, same⟩ := value.property
    have actual : value = SourceConditionalNext.Image.actual (nextRead runtime) index := Subtype.ext same.symm
    rw [actual]
    refine ⟨index, ?_⟩
    change actor runtime index = SourceJointClockGraph.recover
      (SourceConditionalVector.realizeModel runtime (nextRead runtime index))
    rw [SourceConditionalVector.realized_next, SourceJointClockGraph.recover_action]⟩

theorem act_actual (runtime : LivingRuntimeState process) (index : Actors runtime) :
    act runtime (SourceConditionalNext.Image.actual (actor runtime) index) =
      SourceConditionalNext.Image.actual (nextRead runtime) index :=
  Subtype.ext (SourceConditionalModel.next_action runtime index).symm

theorem recover_actual (runtime : LivingRuntimeState process) (index : Actors runtime) :
    recover runtime (SourceConditionalNext.Image.actual (nextRead runtime) index) =
      SourceConditionalNext.Image.actual (actor runtime) index := by
  apply Subtype.ext
  change SourceJointClockGraph.recover (SourceConditionalVector.realizeModel runtime (nextRead runtime index)) = actor runtime index
  rw [SourceConditionalVector.realized_next, SourceJointClockGraph.recover_action]

theorem act_read (runtime : LivingRuntimeState process) (value : SourceImage runtime) :
    read runtime (act runtime value) = SourceJointClockGraph.action value.val := by
  obtain ⟨index, same⟩ := value.property
  have actual : value = SourceConditionalNext.Image.actual (actor runtime) index := Subtype.ext same.symm
  rw [actual, act_actual]
  exact SourceConditionalVector.realized_next runtime index

theorem recover_act (runtime : LivingRuntimeState process) (value : SourceImage runtime) : recover runtime (act runtime value) = value := by
  apply Subtype.ext
  change SourceJointClockGraph.recover (read runtime (act runtime value)) = value.val
  rw [act_read, SourceJointClockGraph.recover_action]

theorem act_recover (runtime : LivingRuntimeState process) (value : Image runtime) : act runtime (recover runtime value) = value := by
  obtain ⟨index, same⟩ := value.property
  have actual : value = SourceConditionalNext.Image.actual (nextRead runtime) index := Subtype.ext same.symm
  rw [actual, recover_actual, act_actual]

theorem recover_first (runtime : LivingRuntimeState process) :
    (recover runtime.tick.next (first runtime)).val = SourceCopyNativeModelStep.sourceValue runtimeSeed := by
  change SourceJointClockGraph.recover (read runtime.tick.next (first runtime)) = _
  rw [first_read]
  have source := SourceCopyNativeModelStep.source_value_next runtimeSeed
  change SourceJointClockGraph.action (SourceCopyNativeModelStep.sourceValue runtimeSeed) =
    SourceCopyNativeModelStep.sourceValue (runtimeAt 1) at source
  rw [← source, SourceJointClockGraph.recover_action]

end
end SourceActualImageStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
