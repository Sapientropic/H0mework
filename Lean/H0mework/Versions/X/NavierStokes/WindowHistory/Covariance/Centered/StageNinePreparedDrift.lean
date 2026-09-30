import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedCreation
import H0mework.Versions.X.NavierStokes.WindowSchurMean.Drift

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativePhysicalPairing NativeCommonAdvectorAction NativePhysicalFourier
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowOperatorGreen (laplacian)
open NativeWindowHistoryMeanDrift (drift)
open NativeWindowHistoryMeanAction (meanValue)
open NativeWindowHistoryCreationGeometry (transport square gradientSquare)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section
local instance driftPhysicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance driftPhysicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem prepared_drift_bound (horizon eta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<eta) (M : ℕ) (time : ℝ)
    (inside : time∈Icc (-2 : ℝ) horizon) (v : physicalSpace (modes M)) :
    ‖drift stackedShortCurrent M time (includeCLM (modes M) (modes_closed M) v)‖^2≤
      eta*pairing (modes M)
        (laplacian (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity v)
        (laplacian (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity v)+
      preparedCreationBudget horizon eta*curlPair (modes M) v.1 v.1 := by
  have stress : ‖drift stackedShortCurrent M time
      (includeCLM (modes M) (modes_closed M) v)‖^2≤
      ∫point : Torus,NativeWindowTraceGradient.traceStress stackedShortCurrent time
        (integerWaveFrequencyCube M) point*
        gradientSquare (modes M) (modes_zero M) (modes_closed M) v point := by
    rw [NativeWindowHistoryMeanDrift.drift_original,restrict_include,
      include_norm (modes M) (modes_zero M)]
    apply (NativeWindowHistoryCreationGeometry.transport_bound (modes M)
      (modes_zero M) (modes_closed M) butterflyGainViscosity _ v).trans
    have square0 (point : Torus) : 0 ≤ square (modes M) (meanValue stackedShortCurrent M time) point := by
      simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
      exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    apply integral_mono_of_nonneg (Eventually.of_forall fun point => mul_nonneg
      (square0 point)
      (NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ v point))
      (((NativeWindowTraceGradient.traceStress stackedShortCurrent time
        (integerWaveFrequencyCube M)).continuous.mul
        (gradientSquare (modes M) (modes_zero M) (modes_closed M) v).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    exact Eventually.of_forall fun point => mul_le_mul_of_nonneg_right
      (mean_square_le_stress_total stackedShortCurrent M time point)
      (NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ v point)
  exact stress.trans (prepared_gradient_form horizon eta nonnegative positive M time inside v)
end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
