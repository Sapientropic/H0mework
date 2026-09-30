import H0mework.Versions.X.Fock.RationalWindow.Recovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRationalWindowReadout

open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem decoded_readout (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Samples (inventoryBound runtime + steps) (index.val + 1)) :
    SourceCopyCurrentCoordinates.realize runtime index steps
      (coordinates runtime index steps (decode (inventoryBound runtime + steps) index.val samples)) =
        SourceMinimumWindowError.readout runtime index nonunit steps (embed runtime index steps samples) := by
  rw [decode_source runtime index nonunit steps]
  rfl

theorem decoded_reconstruction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key) :
    SourceCopyCurrentCoordinates.realize runtime index 0
      (coordinates runtime index 0 (decode (inventoryBound runtime) index.val
        (fun phase => SourceFiniteObserverCalculation.posteriorCalculate (inventoryBound runtime) (index.val + 1) 0 phase.val read key))) +
      SourceCopyCurrentCoordinates.residual runtime index 0 (SourceConditionalNativePosterior.decoder runtime read key) =
        SourceConditionalNativePosterior.decoder runtime read key := by
  have actual := decoded_readout runtime index nonunit 0
    (fun phase => SourceFiniteObserverCalculation.posteriorCalculate (inventoryBound runtime) (index.val + 1) 0 phase.val read key)
  have original : SourceMinimumWindowError.readout runtime index nonunit 0
      (embed runtime index 0
        (fun phase => SourceFiniteObserverCalculation.posteriorCalculate (inventoryBound runtime) (index.val + 1) 0 phase.val read key)) +
        SourceCopyCurrentCoordinates.residual runtime index 0 (SourceConditionalNativePosterior.decoder runtime read key) =
          SourceConditionalNativePosterior.decoder runtime read key := by
    rw [posterior_samples, SourceMinimumWindowError.readout_source]
    exact SourceCopyCurrentCoordinates.reconstruction runtime index 0 _
  exact (congrArg (fun value : SourceJointClockGraph.Carrier =>
    value + SourceCopyCurrentCoordinates.residual runtime index 0 (SourceConditionalNativePosterior.decoder runtime read key)) actual).trans original

theorem decoded_model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1)) :
    SourceCopyCurrentCoordinates.realize runtime (maximumIndex runtime) 0
      (coordinates runtime (maximumIndex runtime) 0 (decode (inventoryBound runtime) (maximumIndex runtime).val samples)) =
        SourceConditionalVector.realizeModel runtime
          (SourceWindowPosterior.model runtime nonunit (embed runtime (maximumIndex runtime) 0 samples)) := by
  have actual := decoded_readout runtime (maximumIndex runtime) nonunit 0 samples
  have original := congrArg
    (fun map : SourceOperatorObservationAcquisition.Window runtime (maximumIndex runtime) →ₗ[ℂ] SourceJointClockGraph.Carrier =>
      map (embed runtime (maximumIndex runtime) 0 samples))
    (SourceWindowPrecision.reader_original runtime (maximumIndex runtime) nonunit 0)
  exact actual.trans (original.symm.trans
    (SourceWindowPosterior.model_realization runtime nonunit (embed runtime (maximumIndex runtime) 0 samples)).symm)

theorem next_recovered (runtime : LivingRuntimeState process) {Key : Type*} [DecidableEq Key] (read : Nat → Key) (key : Key) :
    recover (inventoryBound runtime.tick.next) (maximumIndex runtime.tick.next).val (SourceMinimumSharedNext.next_nonunit runtime)
      (fun phase => SourceFiniteObserverCalculation.posteriorCalculate (inventoryBound runtime.tick.next)
        ((maximumIndex runtime.tick.next).val + 1) 0 phase.val read key) =
      (SourceConditionalNativeObservers.generate read (inventoryBound runtime.tick.next) key).2 :=
  recovered_posterior runtime.tick.next (maximumIndex runtime.tick.next) (SourceMinimumSharedNext.next_nonunit runtime) read key

end
end SourceRationalWindowReadout
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
