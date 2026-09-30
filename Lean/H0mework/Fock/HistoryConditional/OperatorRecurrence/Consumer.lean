import H0mework.Fock.HistoryConditional.Minimum
import H0mework.Fock.HistoryConditional.NativePosteriorField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperatorObservationRecurrence

open SourceGeneratedActionWords SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem native_next (runtime : LivingRuntimeState process) (depth : Nat) (word : List (Fock.Letter depth)) :
    next depth word (SourceInverseObservationHistory.window depth word
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime)))) =
      SourceInverseObservationHistory.window depth word
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime.tick.next))) := by
  rw [next_source, SourceJointClockGraph.native_next]

theorem model_effect {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key) :
    SourceInverseObservationHistory.readWindow (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
      (SourceCompiledWordOperator.slope_positive _) (next depth word
        (SourceInverseObservationHistory.window depth word (SourceConditionalNativePosterior.decoder runtime read key))) =
      SourceConditionalVector.realizeModel runtime.tick.next (SourceConditionalNativePosterior.effect runtime read key) := by
  rw [next_source, SourceInverseObservationHistory.read_window, SourceConditionalNativePosterior.effect_realization]

theorem next_error {Key : Type*} [DecidableEq Key] (runtime : LivingRuntimeState process)
    (depth : Nat) (word : List (Fock.Letter depth)) (read : Nat → Key) (key : Key)
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime.tick.next (nextRead runtime.tick.next (SourceActualImageStep.advanceIndex runtime actor)) -
        SourceInverseObservationHistory.readWindow (SourceCopyWordAffine.compile (word.map SourceCopyNativeWord.encode))
          (SourceCompiledWordOperator.slope_positive _) (next depth word
            (SourceInverseObservationHistory.window depth word (SourceConditionalNativePosterior.decoder runtime read key)))‖ ^ 2) =
    (∑ actor : Actors runtime, ((SourceConditionalNativeObservers.generate read (inventoryBound runtime) key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - SourceConditionalNativePosterior.decoder runtime read key‖ ^ 2) := by
  rw [model_effect]
  exact SourceConditionalNativePosterior.effect_residual runtime read key supported

end
end SourceOperatorObservationRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
