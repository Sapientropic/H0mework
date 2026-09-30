import H0mework.Versions.X.Fock.HistoryConditional.MinimumWindowErrorConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumWindowError

open SourceCopyCurrentCoordinates (maximumIndex residual)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open SourceConditionalNativeObservers (generate)
open SourceConditionalNativePosterior (decoder)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

theorem conditional_effect_decomposition (runtime : LivingRuntimeState process) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (candidate : SourceJointClockGraph.Carrier) :
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next
        (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) - candidate‖ ^ 2) =
      (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime read key‖ ^ 2) +
        ‖SourceJointClockGraph.action (decoder runtime read key) - candidate‖ ^ 2 := by
  let p := SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime))
    (fun actor : Actors runtime => read actor.val) key supported
  let values : Actors runtime → SourceJointClockGraph.Carrier :=
    fun actor => SourceConditionalVector.realizeModel runtime (nextRead runtime actor)
  have average : SourceVectorMoment.mean p (SourceJointClockGraph.action ∘ values) =
      SourceJointClockGraph.action (decoder runtime read key) := by
    rw [SourceVectorMoment.mean_action]
    exact congrArg SourceJointClockGraph.action (SourceConditionalNativePosterior.decoder_mean runtime read key supported).symm
  have generic := SourceVectorMoment.error_decomposition p (SourceJointClockGraph.action ∘ values) candidate
  dsimp only [SourceVectorMoment.variance, SourceVectorMoment.error] at generic
  rw [average] at generic
  have normalized :
      (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime.tick.next
          (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) - candidate‖ ^ 2) =
        (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
          ‖SourceConditionalVector.realizeModel runtime.tick.next
            (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) -
              SourceJointClockGraph.action (decoder runtime read key)‖ ^ 2) +
          ‖SourceJointClockGraph.action (decoder runtime read key) - candidate‖ ^ 2 := by
    simpa only [p, values, Function.comp_apply, SourceConditionalNativePosterior.posterior read (inventoryBound runtime) key supported,
      SourceConditionalNativePosterior.source_effect] using generic
  have transported := SourceConditionalNativePosterior.effect_residual runtime read key supported
  rw [SourceConditionalNativePosterior.effect_realization] at transported
  rw [transported] at normalized
  exact normalized

theorem conditional_next_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support)
    (error : Window runtime (maximumIndex runtime)) :
    (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next
        (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) -
        readout runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) 0
          (SourceMinimumSharedNext.step runtime nonunit
            (recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (decoder runtime read key) + error))‖ ^ 2) =
      (∑ actor : Actors runtime, ((generate read (inventoryBound runtime) key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - decoder runtime read key‖ ^ 2) +
        ‖residual runtime (maximumIndex runtime) 0 (decoder runtime read key)‖ ^ 2 +
        ‖SourceJointClockGraph.action (readout runtime (maximumIndex runtime) nonunit 0 error)‖ ^ 2 := by
  rw [conditional_effect_decomposition runtime read key supported, step_error]
  exact (add_assoc _ _ _).symm

end
end SourceMinimumWindowError
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
