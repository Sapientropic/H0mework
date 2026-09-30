import H0mework.Fock.HistoryConditional.OperatorAcquisitionForecast

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObservationMinimum

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time)
open SourceCopyTemporalBoundary (observer recoveryMap recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def frame (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] (Fin (inventoryBound runtime + steps + 1) → ℂ) :=
  LinearMap.pi fun actor => (SourceHistoryWord.coefficient (inventoryBound runtime + steps) actor).comp
    ((Actor.currentPullback (inventoryBound runtime + steps) (inventoryBound runtime + steps)).toLinearMap.comp
      (recoveryMap runtime index steps))

theorem observer_frame (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : SourceJointClockGraph.Carrier) :
    observer runtime index steps value = SourceJointClockGraph.read
      (∑ actor : Fin (inventoryBound runtime + steps + 1), Finsupp.single actor.val (frame runtime index steps value actor)) := by
  change SourceJointClockGraph.read (SourceHistoryWord.word (inventoryBound runtime + steps)
    (Actor.currentPullback (inventoryBound runtime + steps) (inventoryBound runtime + steps)
      (recoveryMap runtime index steps value))) = _
  rw [SourceHistoryWord.word_sum]
  rfl

def samples (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps length : Nat) :
    SourceCopyCurrentCoordinates.Coordinates runtime index steps →ₗ[ℂ]
      (Fin (length + 1) → Fin (inventoryBound runtime + steps + 1) → ℂ) :=
  LinearMap.pi fun phase => (frame runtime index steps).comp ((time phase.val).toLinearMap.comp
    (SourceCopyCurrentCoordinates.realize runtime index steps))

theorem same_samples (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps length : Nat)
    (left right : SourceCopyCurrentCoordinates.Coordinates runtime index steps)
    (same : samples runtime index steps length left = samples runtime index steps length right) :
    recordedPrefix runtime index steps length (SourceCopyCurrentCoordinates.realize runtime index steps left) =
      recordedPrefix runtime index steps length (SourceCopyCurrentCoordinates.realize runtime index steps right) := by
  funext phase
  rw [SourceCopyTemporalBoundary.prefix_source, SourceCopyTemporalBoundary.prefix_source, observer_frame, observer_frame]
  apply congrArg SourceJointClockGraph.read
  apply Finset.sum_congr rfl
  intro actor _
  exact congrArg (Finsupp.single actor.val) (congrFun (congrFun same phase) actor)

end
end SourceFiniteObservationMinimum
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
