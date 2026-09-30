import H0mework.Versions.X.Fock.SourceHistory.CountedObservation.Continuation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedObservation

open SourceRetainedReceiver (At model)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Key : Type*} [DecidableEq Key]
noncomputable section

theorem conditional_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (table : Table Key) (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : Simulates (inventoryBound runtime) (maximumIndex runtime).val table frame)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    (∑ actor : Actors runtime, ((frame.native key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - readValue runtime table key‖ ^ 2) =
      (∑ actor : Actors runtime, ((frame.native key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalVector.realizeModel runtime (model runtime frame key)‖ ^ 2) +
        ‖readValue runtime table key - SourceConditionalVector.realizeModel runtime (model runtime frame key)‖ ^ 2 := by
  rw [readValue_source runtime table frame read source native keys key]
  have paid := SourceRetainedReceiver.conditional_error runtime nonunit frame read key native supported
  rw [SourceRetainedReceiver.observed_realization, SourceRetainedReceiver.residual] at paid
  exact paid

end
end SourceCountedObservation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
