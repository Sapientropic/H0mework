import H0mework.Fock.RetainedCoarsening.Trajectory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceRetainedCoarsening

open SourceRetainedReceiver (At value model residual)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalModel (Actors nextRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]
noncomputable section

theorem conditional_error (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (frame : At runtime Fine) (read : Nat → Fine) (forget : Fine → Coarse) (coarse : Coarse)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
    (supported : coarse ∈ ((historyPMF (inventoryBound runtime)).map (fun actor : Actors runtime => forget (read actor.val))).support) :
    let combined := merge (inventoryBound runtime) (maximumIndex runtime).val frame forget
    (∑ actor : Actors runtime, ((combined.native coarse).2 actor : ℝ) *
      ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) - value runtime combined coarse‖ ^ 2) =
      (∑ actor : Actors runtime, ((combined.native coarse).2 actor : ℝ) *
        ‖SourceConditionalVector.realizeModel runtime (nextRead runtime actor) -
          SourceConditionalVector.realizeModel runtime (model runtime combined coarse)‖ ^ 2) +
        ‖∑ key ∈ frame.keys, (weight (inventoryBound runtime) (maximumIndex runtime).val frame forget coarse key : ℂ) •
          residual runtime frame key‖ ^ 2 := by
  have paid := SourceRetainedReceiver.conditional_error runtime nonunit
    (merge (inventoryBound runtime) (maximumIndex runtime).val frame forget) (forget ∘ read) coarse
      (native_source _ _ frame read forget source keys) supported
  rw [SourceRetainedReceiver.observed_realization, residual_merge] at paid
  exact paid

end
end SourceRetainedCoarsening
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
