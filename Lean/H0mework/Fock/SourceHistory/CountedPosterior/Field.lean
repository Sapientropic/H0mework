import H0mework.Fock.SourceHistory.CountedRecovery.Field
import H0mework.Fock.SourceHistory.CountedPosterior.Source

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedPosterior

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors)
open SourceRetainedReceiver (At)
open SourceConditionalNativeObservers (clockRead)
open SourceConditionalNativeMerge (forgetClock)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

private theorem model_matches {Key : Type*} [DecidableEq Key]
    (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table Key) (frame : At runtime Key) (read : Nat → Key)
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2)
    (key : Key) : SourceRetainedReceiver.model runtime frame key = model runtime nonunit table key :=
  (SourceRetainedReceiver.model_source runtime frame read key native).trans
    (model_source runtime nonunit table frame read key source native (margins key)).symm

theorem field_update (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2)
    (depth : Nat) :
    let bornKey := forgetClock (clockRead 0 runtime.tick.next.state)
    let count := SourceCountedObservation.total table forgetClock bornKey
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth
      (SourceCountedObservation.observationTable runtime.tick.next
        (SourceCountedObservation.step (inventoryBound runtime) table (clockRead 0 runtime.tick.next.state)) depth) =
      ((inventoryBound runtime + 1 : Nat) : ℝ) *
        SourceConditionalVector.dynamicError runtime depth (SourceCountedObservation.observationTable runtime table depth) +
      SourceConditionalNativeBirth.innovation runtime (forgetClock ∘ clockRead 0) -
        (count : ℝ) / (count + 1) *
          ‖∑ key ∈ table.keys.toFinset, (SourceCountedObservation.weight table forgetClock bornKey key : ℂ) •
            (SourceCountedObservation.readValue runtime table key -
              SourceConditionalVector.realizeModel runtime (model runtime nonunit table key))‖ ^ 2 := by
  have paid := SourceCountedRecovery.field_update runtime table frame source native keys depth
  simpa only [model_matches runtime nonunit table frame (clockRead 0) source native margins] using paid

theorem field_balance (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : SourceCountedObservation.Table (ℤ × ℤ)) (frame : At runtime (ℤ × ℤ))
    (source : SourceCountedObservation.Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate (clockRead 0) (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val))
    (margins : ∀ key, ‖((frame.native key).1 : ℂ) • SourceRetainedReceiver.residual runtime frame key‖ < 1 / 2)
    (depth : Nat) :
    SourceConditionalVector.dynamicError runtime depth (SourceCountedObservation.observationTable runtime table depth) =
      SourceConditionalVector.dynamicVariance runtime depth +
      ∑ actor : Actors runtime, (historyPMF (inventoryBound runtime) actor).toReal *
        ‖∑ key ∈ table.keys.toFinset, (SourceCountedObservation.weight table forgetClock (actor.val : ZMod 2) key : ℂ) •
          (SourceCountedObservation.readValue runtime table key -
            SourceConditionalVector.realizeModel runtime (model runtime nonunit table key))‖ ^ 2 := by
  have paid := SourceCountedObservation.field_balance runtime table frame source native keys depth
  simpa only [model_matches runtime nonunit table frame (clockRead 0) source native margins] using paid

end
end SourceCountedPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
