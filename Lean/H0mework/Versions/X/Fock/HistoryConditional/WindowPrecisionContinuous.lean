import H0mework.Versions.X.Fock.HistoryConditional.WindowPrecisionReadout

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index)
open SourceOperatorObservationAcquisition (Window)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def continuousEvaluate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) : Window runtime index →L[ℂ] ℂ :=
  ∑ phase, ∑ actor, coefficients phase actor • columnReader runtime index steps actor phase

theorem continuous_evaluate_apply (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coefficients : Coefficients runtime index steps) (samples : Window runtime index) :
    continuousEvaluate runtime index steps coefficients samples = evaluate runtime index steps coefficients samples := by
  simp only [continuousEvaluate, sum_apply, smul_apply, smul_eq_mul, evaluate_apply]

def reader (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Window runtime index →L[ℂ] SourceJointClockGraph.Carrier :=
  (SourceCopyCurrentCoordinates.realize runtime index steps).toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun coordinate => continuousEvaluate runtime index steps (hilbertCoefficients runtime index nonunit steps coordinate))).prod
      ((continuousEvaluate runtime index steps (massCoefficients runtime index nonunit steps)).prod
        (continuousEvaluate runtime index steps (clockCoefficients runtime index nonunit steps))))

theorem reader_original (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    (reader runtime index nonunit steps).toLinearMap = SourceMinimumWindowError.readout runtime index nonunit steps := by
  apply LinearMap.ext
  intro samples
  change SourceCopyCurrentCoordinates.realize runtime index steps
    ((fun coordinate => continuousEvaluate runtime index steps (hilbertCoefficients runtime index nonunit steps coordinate) samples),
      continuousEvaluate runtime index steps (massCoefficients runtime index nonunit steps) samples,
      continuousEvaluate runtime index steps (clockCoefficients runtime index nonunit steps) samples) = _
  simp only [continuous_evaluate_apply, hilbert_original, mass_original, clock_original]
  rfl

theorem readout_continuous (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : Continuous (SourceMinimumWindowError.readout runtime index nonunit steps) := by
  rw [← reader_original runtime index nonunit steps]
  exact (reader runtime index nonunit steps).continuous

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
