import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedTraceBudget
import H0mework.Versions.X.NavierStokes.WindowHistoryCreation.Source

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeCommonAdvectorAction
open NativePhysicalFourier
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowOperatorGreen (laplacian)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryCreationGeometry (gradientSquare)
open NativeWindowStressHeatSource (physical)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def preparedCreationBudget (horizon eta : ℝ) : ℝ :=
  NativeWindowHistoryCreationForm.budget (preparedTraceBudget horizon) (eta*(2*Real.pi)^2)

theorem preparedCreationBudget_nonnegative (horizon eta : ℝ) (positive : 0<eta) :
    0≤preparedCreationBudget horizon eta := by
  unfold preparedCreationBudget NativeWindowHistoryCreationForm.budget
  positivity

theorem prepared_gradient_form (horizon eta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<eta) (M : ℕ) (time : ℝ)
    (inside : time∈Icc (-2 : ℝ) horizon) (v : physicalSpace (modes M)) :
    (∫point : Torus,NativeWindowTraceGradient.traceStress stackedShortCurrent time
      (integerWaveFrequencyCube M) point*
      gradientSquare (modes M) (modes_zero M) (modes_closed M) v point)≤
      eta*pairing (modes M)
        (laplacian (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity v)
        (laplacian (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity v)+
      preparedCreationBudget horizon eta*curlPair (modes M) v.1 v.1 := by
  have absorbed:=NativeWindowHistoryCreationGeometry.gradient_absorption
    (NativeWindowTraceGradient.traceStress stackedShortCurrent time (integerWaveFrequencyCube M))
    (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity v eta positive
  have traceBound:=prepared_trace_bound horizon nonnegative M time inside
  have power:=pow_le_pow_left₀
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left traceBound
      (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap : NativeWindowHistoryCreationForm.budget
      ‖physical (NativeWindowTraceGradient.traceStress stackedShortCurrent time
        (integerWaveFrequencyCube M))‖ (eta*(2*Real.pi)^2)≤
        preparedCreationBudget horizon eta := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have gradient0 : 0≤curlPair (modes M) v.1 v.1 := by
    rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
    exact sq_nonneg _
  exact absorbed.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right cap gradient0))

theorem prepared_creation_bound (horizon eta : ℝ) (nonnegative : 0≤horizon)
    (positive : 0<eta) (M : ℕ) (time : ℝ)
    (inside : time∈Icc (-2 : ℝ) horizon) (v : physicalSpace (modes M)) :
    ‖creation stackedShortCurrent M time (includeCLM (modes M) (modes_closed M) v)‖^2≤
      eta*pairing (modes M)
        (laplacian (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity v)
        (laplacian (modes M) (modes_zero M) (modes_closed M) butterflyGainViscosity v)+
      preparedCreationBudget horizon eta*curlPair (modes M) v.1 v.1 := by
  have stress : ‖creation stackedShortCurrent M time
      (includeCLM (modes M) (modes_closed M) v)‖^2≤
      ∫point : Torus,NativeWindowTraceGradient.traceStress stackedShortCurrent time
        (integerWaveFrequencyCube M) point*
        gradientSquare (modes M) (modes_zero M) (modes_closed M) v point := by
    apply (NativeWindowHistoryCreationSource.covariance_bound stackedShortCurrent M time v).trans
    apply integral_mono_of_nonneg (Eventually.of_forall fun point => mul_nonneg
      (NativeWindowHistoryCreationCovariance.trace_nonnegative stackedShortCurrent M time point)
      (NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ v point))
      (((NativeWindowTraceGradient.traceStress stackedShortCurrent time
        (integerWaveFrequencyCube M)).continuous.mul
        (gradientSquare (modes M) (modes_zero M) (modes_closed M) v).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    exact Eventually.of_forall fun point => mul_le_mul_of_nonneg_right
      (trace_le_stress_total stackedShortCurrent M time point)
      (NativeWindowHistoryCreationSource.gradientSquare_nonnegative _ _ _ v point)
  exact stress.trans (prepared_gradient_form horizon eta nonnegative positive M time inside v)
end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedCovariance
