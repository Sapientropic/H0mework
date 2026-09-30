import H0mework.Fock.HistoryConditional.NativePosteriorModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativePosterior

open SourceConditionalNativeObservers (generate)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors NextModel nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def effect (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) : NextModel runtime.tick.next :=
  SourceCopyNativeSharedUpdate.modelStep runtime.tick.next (model runtime read value)

theorem effect_realization (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key) :
    SourceConditionalVector.realizeModel runtime.tick.next (effect runtime read value) =
      SourceJointClockGraph.action (decoder runtime read value) := by
  change SourceCopyCurrentCoordinates.realize runtime.tick.next.tick.next (SourceCopyCurrentCoordinates.maximumIndex runtime.tick.next.tick.next) 0
    (SourceCopyCurrentCoordinates.jointModelEquiv runtime.tick.next.tick.next
      (SourceCopyNativeSharedUpdate.modelStep runtime.tick.next (model runtime read value))) = _
  rw [SourceCopyNativeSharedUpdate.modelStep, LinearEquiv.apply_symm_apply, SourceCopyNativeSharedUpdate.step_realize]
  rfl

theorem source_effect (runtime : LivingRuntimeState process) (actor : Actors runtime) :
    SourceConditionalVector.realizeModel runtime.tick.next
      (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) =
        SourceJointClockGraph.action (SourceConditionalVector.realizeModel runtime (nextRead runtime actor)) := by
  have paid := SourceActualImageStep.step_read runtime (SourceConditionalNext.Image.actual (nextRead runtime) actor)
  rw [SourceActualImageStep.step_actual] at paid
  exact paid

theorem decoder_mean (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    decoder runtime read value =
      SourceVectorMoment.mean (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
        (fun actor : Actors runtime => read actor.val) value supported)
        (fun actor => SourceConditionalVector.realizeModel runtime (nextRead runtime actor)) := by
  rw [decoder, model_original _ _ _ supported, SourceConditionalVector.estimate_realization]
  rfl

theorem error_decomposition (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (candidate : SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) value).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - candidate‖ ^ 2) =
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) value).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime read value‖ ^ 2) +
        ‖decoder runtime read value - candidate‖ ^ 2 := by
  simp only [posterior read (inventoryBound runtime) value supported]
  have paid := SourceVectorMoment.error_decomposition
    (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => read actor.val) value supported)
    (fun actor => SourceConditionalVector.realizeModel runtime (nextRead runtime actor)) candidate
  simpa only [SourceVectorMoment.variance, SourceVectorMoment.error, ← decoder_mean runtime read value supported] using paid

theorem effect_residual (runtime : LivingRuntimeState process) (read : Nat → Key) (value : Key)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) value).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next
        (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) -
          SourceConditionalVector.realizeModel runtime.tick.next (effect runtime read value)‖ ^ 2) =
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) value).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime read value‖ ^ 2) := by
  have mass (actor : Actors runtime) :
      SourceVectorMoment.massMap (SourceConditionalVector.realizeModel runtime (nextRead runtime actor)) = 1 := by
    rw [SourceConditionalVector.realized_next]
    change SourceVectorMoment.massMap (SourceConditionalVector.actor runtime actor) = 1
    exact SourceConditionalVector.actor_mass runtime actor
  have paid := SourceVectorMoment.constant_mass_variance
    (SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (fun actor : Actors runtime => read actor.val) value supported)
    (fun actor => SourceConditionalVector.realizeModel runtime (nextRead runtime actor)) 1 mass
  simp only [SourceVectorMoment.variance, SourceVectorMoment.error, SourceVectorMoment.mean_action,
    Function.comp_apply, ← decoder_mean runtime read value supported] at paid
  simpa only [posterior read (inventoryBound runtime) value supported, source_effect, effect_realization] using paid

end
end SourceConditionalNativePosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
