import H0mework.Fock.HistoryConditional.WindowPrecisionMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPosterior

open SourceCopyCurrentCoordinates (maximumIndex jointObserver residual)
open SourceConditionalModel (NextModel)
open SourceGeneratedActionObservationHistory (projection)
open SourceOperatorObservationAcquisition (Window)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def model (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Window runtime (maximumIndex runtime)) : NextModel runtime :=
  projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next)
    (SourceWindowPrecision.reader runtime (maximumIndex runtime) nonunit 0 samples)

theorem readout_next_tail (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Window runtime (maximumIndex runtime)) :
    residual runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceMinimumWindowError.readout runtime (maximumIndex runtime) nonunit 0 samples) = 0 := by
  apply (SourceCopyCurrentCoordinates.complete_fibre runtime.tick.next (maximumIndex runtime.tick.next) 0 _ 0).mpr
  refine ⟨?_, ?_⟩
  · rw [SourceCopyCurrentCoordinates.residual_source, map_zero]
  · intro coordinate beyond
    rw [SourceCopyCurrentCoordinates.residual_outside _ _ _ _ _ beyond]
    change SourceCopyCurrentCoordinates.hilbertLift runtime (maximumIndex runtime) 0
      (SourceOperatorObservationAcquisition.decode runtime (maximumIndex runtime) nonunit 0 samples).1 coordinate = 0
    have growth := SourceCopySharedNext.cutoff_growth runtime
    exact SourceCopyCurrentCoordinates.hilbert_lift_outside runtime (maximumIndex runtime) 0 _ coordinate (by omega)

theorem model_realization (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (samples : Window runtime (maximumIndex runtime)) :
    SourceConditionalVector.realizeModel runtime (model runtime nonunit samples) =
      SourceWindowPrecision.reader runtime (maximumIndex runtime) nonunit 0 samples := by
  change SourceCopyCurrentCoordinates.realize runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceCopyCurrentCoordinates.jointModelEquiv runtime.tick.next
      (projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next)
        (SourceWindowPrecision.reader runtime (maximumIndex runtime) nonunit 0 samples))) = _
  rw [SourceCopyCurrentCoordinates.joint_model_source]
  have source := SourceCopyCurrentCoordinates.reconstruction runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceWindowPrecision.reader runtime (maximumIndex runtime) nonunit 0 samples)
  have actual : SourceWindowPrecision.reader runtime (maximumIndex runtime) nonunit 0 samples =
      SourceMinimumWindowError.readout runtime (maximumIndex runtime) nonunit 0 samples :=
    congrArg (fun map : Window runtime (maximumIndex runtime) →ₗ[ℂ] SourceJointClockGraph.Carrier => map samples)
      (SourceWindowPrecision.reader_original runtime (maximumIndex runtime) nonunit 0)
  have tail : residual runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceWindowPrecision.reader runtime (maximumIndex runtime) nonunit 0 samples) = 0 := by
    rw [actual]
    exact readout_next_tail runtime nonunit samples
  rw [tail, add_zero] at source
  exact source

end
end SourceWindowPosterior
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
