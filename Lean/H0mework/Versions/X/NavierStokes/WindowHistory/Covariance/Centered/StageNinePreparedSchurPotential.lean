import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedTemporalResidual
import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.StageNinePreparedTraceBudget
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.WeakPairing

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeStageNinePreparedSchurPotential
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativePhysicalFourier
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistorySchurWeakPairing (potential)
open NativeWindowHistoryCreationGeometry (square)
open NativeWindowHistoryCreationCovariance (trace)
open NativeWindowStressHeatSource (physical)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem potential_stress_total (M : ℕ) (time : ℝ)
    (v : physicalSpace (modes M)) :
    potential stackedShortCurrent M time v ≤
      ∫point : Torus,NativeWindowTraceGradient.traceStress stackedShortCurrent time
        (integerWaveFrequencyCube M) point*square (modes M) v point := by
  rw [potential]
  have paid := integral_mono (μ := (volume : Measure Torus))
    (((trace stackedShortCurrent M time).continuous.mul (square (modes M) v).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (((NativeWindowTraceGradient.traceStress stackedShortCurrent time
      (integerWaveFrequencyCube M)).continuous.mul (square (modes M) v).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun point => by
      apply mul_le_mul_of_nonneg_right
        (NativeStageNinePreparedCovariance.trace_le_stress_total stackedShortCurrent M time point)
      simp only [square,ContinuousMap.sum_apply,ContinuousMap.mul_apply]
      exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  simpa only [Pi.mul_apply,ContinuousMap.mul_apply] using paid

def potentialBudget (horizon epsilon : ℝ) : ℝ :=
  NativeWindowHistoryCreationForm.budget
    (NativeStageNinePreparedCovariance.preparedTraceBudget horizon)
    (epsilon*(2*Real.pi)^2)

theorem potentialBudget_nonnegative (horizon epsilon : ℝ) (positive : 0 < epsilon) :
    0 ≤ potentialBudget horizon epsilon := by
  unfold potentialBudget NativeWindowHistoryCreationForm.budget
  positivity

theorem source_potential_bound (horizon epsilon : ℝ) (nonnegative : 0 ≤ horizon)
    (positive : 0 < epsilon) (M : ℕ) (time : ℝ)
    (inside : time ∈ Icc (-2 : ℝ) horizon) (v : physicalSpace (modes M)) :
    potential stackedShortCurrent M time v ≤
      epsilon*curlPair (modes M) v.1 v.1+
        potentialBudget horizon epsilon*pairing (modes M) v v := by
  have paid := (potential_stress_total M time v).trans
    (NativeWindowHistoryCreationGeometry.square_absorption _
      (modes M) (modes_zero M) (modes_closed M) v epsilon positive)
  have traceBound := NativeStageNinePreparedCovariance.prepared_trace_bound horizon nonnegative M time inside
  have power := pow_le_pow_left₀
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left traceBound
      (Real.sqrt_nonneg NativeWindowGreenTestForm.testKernel.cap)) 8
  have cap : NativeWindowHistoryCreationForm.budget
      ‖physical (NativeWindowTraceGradient.traceStress stackedShortCurrent time
        (integerWaveFrequencyCube M))‖ (epsilon*(2*Real.pi)^2) ≤
      potentialBudget horizon epsilon := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right power (by positivity))
  have mass0 : 0 ≤ pairing (modes M) v v :=
    real_inner_self_nonneg (x := coefficients (modes M) v)
  exact paid.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right cap mass0))

def formBudget (horizon epsilon : ℝ) : ℝ :=
  butterflyGainViscosity.coeff⁻¹*
    potentialBudget horizon (butterflyGainViscosity.coeff*epsilon)

theorem formBudget_nonnegative (horizon epsilon : ℝ) (positive : 0 < epsilon) :
    0 ≤ formBudget horizon epsilon :=
  mul_nonneg (inv_nonneg.mpr butterflyGainViscosity.coeff_pos.le)
    (potentialBudget_nonnegative horizon _ (mul_pos butterflyGainViscosity.coeff_pos positive))

theorem source_form_bound (horizon epsilon : ℝ) (nonnegative : 0 ≤ horizon)
    (positive : 0 < epsilon) (M : ℕ) (time : ℝ)
    (inside : time ∈ Icc (-2 : ℝ) horizon) (v : physicalSpace (modes M)) :
    NativeWindowHistorySchurAction.cost stackedShortCurrent M time
        (includeCLM (modes M) (modes_closed M) v) ≤
      epsilon*curlPair (modes M) v.1 v.1+
        formBudget horizon epsilon*pairing (modes M) v v := by
  have paid := (NativeWindowHistorySchurTemporalControl.cost_potential stackedShortCurrent M time v).trans
    (mul_le_mul_of_nonneg_left
      (source_potential_bound horizon (butterflyGainViscosity.coeff*epsilon)
        nonnegative (mul_pos butterflyGainViscosity.coeff_pos positive) M time inside v)
      (inv_nonneg.mpr butterflyGainViscosity.coeff_pos.le))
  exact paid.trans_eq (by unfold formBudget; field_simp [butterflyGainViscosity.coeff_pos.ne'])

end
end SaturationMonoid.NavierStokes.NativeStageNinePreparedSchurPotential
