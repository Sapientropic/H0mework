import H0mework.NavierStokes.StressEvolutionUnfiltered.Variation
import H0mework.NavierStokes.StressEvolutionUnfiltered.Measure
import H0mework.NavierStokes.StressEvolutionUnfiltered.Interpolation

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalPhysicalTime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeResolventCompactness NativeWholeResolvent
open NativeOriginalResolventInput NativeWholeH1Mixed NativeWholeH1Pairing
open NativeOriginalTimeMeasure NativeOriginalTimeVariation NativeOriginalNegativeOneDerivative NativeOriginalNegativeOneBudget

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def difference (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) : wholePhysical :=
  physical source pointLe (time + shift) - physical source pointLe time

def negativeDifference (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) : State :=
  stateAt source pointLe (time + shift) - stateAt source pointLe time

def gradientMajorant (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) : ℝ :=
  2 * (2 * Real.pi) ^ 2 * (gradient source pointLe (time + shift) + gradient source pointLe time)

theorem difference_bound (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) :
    ‖difference source pointLe shift time‖ ≤ 2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖ :=
  (norm_sub_le _ _).trans ((add_le_add (physical_bound source pointLe (time + shift)) (physical_bound source pointLe time)).trans_eq (by ring))

theorem negative_original (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) :
    negativeDifference source pointLe shift time = inverseGradient (difference source pointLe shift time).1 :=
  (NativePhysicalTimeInterpolation.inverse_sub _ _).symm

theorem negative_continuous (source : StressAt escape) (pointLe : point ≤ 1) (shift : ℝ) :
    Continuous (negativeDifference source pointLe shift) :=
  ((stateAt_continuous source pointLe).comp (continuous_id.add continuous_const)).sub (stateAt_continuous source pointLe)

theorem negative_bound (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) :
    ‖negativeDifference source pointLe shift time‖ ≤ 2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖ := by
  rw [negative_original]
  exact (NativePhysicalTimeInterpolation.inverse_norm _).trans (difference_bound source pointLe shift time)

theorem gradientMajorant_nonnegative (source : StressAt escape) (pointLe : point ≤ 1) (shift time : ℝ) :
    0 ≤ gradientMajorant source pointLe shift time :=
  mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (add_nonneg (gradient_nonnegative source pointLe _) (gradient_nonnegative source pointLe _))

theorem difference_integrable (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun time => (difference source pointLe shift time).1) volume left right := by
  have first := shifted_integrable (physical_integrable source pointLe) (left := left) (right := right) (shift := 0)
    (by simpa only [add_zero] using firstInside (left_mem_Icc.mpr ordered))
    (by simpa only [add_zero] using firstInside (right_mem_Icc.mpr ordered))
  have last := shifted_integrable (physical_integrable source pointLe)
    (lastInside (left_mem_Icc.mpr ordered)) (lastInside (right_mem_Icc.mpr ordered))
  change IntervalIntegrable (fun time => (physical source pointLe (time + shift)).1 - (physical source pointLe time).1) volume left right
  simpa only [add_zero] using last.sub first

theorem gradientMajorant_integrable (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (gradientMajorant source pointLe shift) volume left right := by
  have first := shifted_integrable (gradient_integrable source pointLe) (left := left) (right := right) (shift := 0)
    (by simpa only [add_zero] using firstInside (left_mem_Icc.mpr ordered))
    (by simpa only [add_zero] using firstInside (right_mem_Icc.mpr ordered))
  have last := shifted_integrable (gradient_integrable source pointLe)
    (lastInside (left_mem_Icc.mpr ordered)) (lastInside (right_mem_Icc.mpr ordered))
  change IntervalIntegrable (fun time => 2 * (2 * Real.pi) ^ 2 *
    (gradient source pointLe (time + shift) + gradient source pointLe time)) volume left right
  simpa only [add_zero] using (last.add first).const_mul (2 * (2 * Real.pi) ^ 2)

theorem difference_interpolation_ae (source : StressAt escape) (pointLe : point ≤ 1)
    (left right shift : ℝ) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    ∀ᵐ time ∂volume.restrict (Icc left right), ‖difference source pointLe shift time‖ ^ 2 ≤
      ‖negativeDifference source pointLe shift time‖ * Real.sqrt (gradientMajorant source pointLe shift time) := by
  filter_upwards [NativeWholeH1ShiftedSource.source_faces_shifted_ae source pointLe left right shift firstInside lastInside]
    with time original
  have firstH1 : H1 (physical source pointLe time) := h1_of_curl_summable _ original.1.1
  have lastH1 : H1 (physical source pointLe (time + shift)) := h1_of_curl_summable _ original.2.1
  have regular := NativeWholeH1Approximation.H1_sub _ _ lastH1 firstH1
  have paid := NativePhysicalTimeInterpolation.physical_bound (difference source pointLe shift time) regular
  rw [← negative_original] at paid
  refine paid.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (norm_nonneg _))
  have spatial := NativePhysicalTimeInterpolation.gradient_sub_bound _ _ lastH1 firstH1
  exact (mul_le_mul_of_nonneg_left spatial (sq_nonneg (2 * Real.pi))).trans_eq (by
    unfold gradientMajorant NativeOriginalTimeMeasure.gradient
    ring)

end
end SaturationMonoid.NavierStokes.NativeOriginalPhysicalTime
