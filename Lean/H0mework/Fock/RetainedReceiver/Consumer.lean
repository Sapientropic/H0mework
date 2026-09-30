import H0mework.Fock.RetainedReceiver.Continuous

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedReceiver

variable {Key : Type*} [DecidableEq Key]
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem conditional_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (frame : At runtime Key) (read : Nat → Key) (key : Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (supported : key ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => read actor.val)).support) :
    (∑ actor : Actors runtime, ((frame.native key).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
        SourceConditionalVector.realizeModel runtime (observed runtime nonunit frame key)‖ ^ 2) =
      (∑ actor : Actors runtime, ((frame.native key).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalVector.realizeModel runtime (model runtime frame key)‖ ^ 2) +
        ‖residual runtime frame key‖ ^ 2 := by
  rw [observed_realization, residual, model_source runtime frame read key source]
  rw [source]
  have paid := SourceConditionalNativePosterior.error_decomposition runtime read key supported (value runtime frame key)
  rw [norm_sub_rev (SourceConditionalNativePosterior.decoder runtime read key)] at paid
  exact paid

theorem trajectory_nonunit (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0) (steps : Nat) :
    (maximumIndex (runtime.advance steps)).val ≠ 0 := by
  rw [maximum_advance]
  omega

end
end SourceRetainedReceiver
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
