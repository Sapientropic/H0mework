import H0mework.NavierStokes.StressEvolutionUnfiltered.Physical

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalPhysicalTimeBudget

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeResolventCompactness NativeWholeResolvent
open NativeOriginalPhysicalTime NativeOriginalTimeMeasure NativeOriginalTimeVariation NativeOriginalNegativeOneBudget

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem negative_integral_bound (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (positive : 0 ≤ shift) (leftInside : 0 ≤ left)
    (rightInside : right + shift ≤ 1) :
    (∫ time in left..right, ‖negativeDifference source pointLe shift time‖ ^ 2) ≤
      2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖ * (shift * budget receipt) := by
  have continuous := (negative_continuous source pointLe shift).norm
  have pointwise (time : ℝ) : ‖negativeDifference source pointLe shift time‖ ^ 2 ≤
      (2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖) * ‖negativeDifference source pointLe shift time‖ := by
    have bound := negative_bound source pointLe shift time
    nlinarith [norm_nonneg (negativeDifference source pointLe shift time)]
  have actual := intervalIntegral.integral_mono_on ordered ((continuous.pow 2).intervalIntegrable (a := left) (b := right) (μ := volume))
    ((continuous.const_mul (2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖)).intervalIntegrable (a := left) (b := right) (μ := volume))
    (fun time _ => pointwise time)
  rw [intervalIntegral.integral_const_mul] at actual
  exact actual.trans (mul_le_mul_of_nonneg_left
    (source_L1_difference_bound source pointLe ordered positive leftInside rightInside) (by positivity))

theorem gradient_integral_bound (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    (∫ time in left..right, gradientMajorant source pointLe shift time) ≤
      4 * (2 * Real.pi) ^ 2 * gradientBudget receipt := by
  have firstMem := firstInside (left_mem_Icc.mpr ordered)
  have lastMem := firstInside (right_mem_Icc.mpr ordered)
  have shiftedFirst := lastInside (left_mem_Icc.mpr ordered)
  have shiftedLast := lastInside (right_mem_Icc.mpr ordered)
  have integrableFirst := shifted_integrable (gradient_integrable source pointLe) (left := left) (right := right) (shift := 0)
    (by simpa only [add_zero] using firstMem) (by simpa only [add_zero] using lastMem)
  have integrableLast := shifted_integrable (gradient_integrable source pointLe) shiftedFirst shiftedLast
  have boundFirst := shifted_integral_bound (gradient_integrable source pointLe) (gradient_nonnegative source pointLe)
    (gradient_budget source pointLe) (shift := 0) ordered (by simpa only [add_zero] using firstMem.1)
    (by simpa only [add_zero] using lastMem.2)
  have boundLast := shifted_integral_bound (gradient_integrable source pointLe) (gradient_nonnegative source pointLe)
    (gradient_budget source pointLe) ordered shiftedFirst.1 shiftedLast.2
  simp only [add_zero] at integrableFirst boundFirst
  unfold gradientMajorant
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add integrableLast integrableFirst]
  nlinarith [sq_nonneg (2 * Real.pi)]

theorem difference_mass_integrable (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (firstInside : Icc left right ⊆ Icc (0 : ℝ) 1)
    (lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1)) :
    Integrable (fun time => ‖difference source pointLe shift time‖ ^ 2) (volume.restrict (Icc left right)) := by
  have original := (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp
    (difference_integrable source pointLe ordered firstInside lastInside)
  apply Integrable.of_bound (original.aestronglyMeasurable.norm.pow 2)
    ((2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖) ^ 2)
  apply Eventually.of_forall
  intro time
  change ‖‖difference source pointLe shift time‖ ^ 2‖ ≤ (2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖) ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (difference_bound source pointLe shift time) 2

theorem source_physical_integral (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (positive : 0 ≤ shift) (leftInside : 0 ≤ left)
    (rightInside : right + shift ≤ 1) :
    (∫ time in left..right, ‖difference source pointLe shift time‖ ^ 2) ^ 2 ≤
      8 * ‖ledger.family.endpointReceipt.velocityEndpoint‖ * (2 * Real.pi) ^ 2 *
        gradientBudget receipt * budget receipt * shift := by
  have firstInside : Icc left right ⊆ Icc (0 : ℝ) 1 :=
    fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have lastInside : MapsTo (fun time : ℝ => time + shift) (Icc left right) (Icc (0 : ℝ) 1) :=
    fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩
  let measure := volume.restrict (Icc left right)
  let a := fun time => ‖negativeDifference source pointLe shift time‖
  let b := fun time => Real.sqrt (gradientMajorant source pointLe shift time)
  have aLp : MemLp a 2 measure :=
    (MemLp.of_bound (negative_continuous source pointLe shift).aestronglyMeasurable
      (2 * ‖ledger.family.endpointReceipt.velocityEndpoint‖) (Eventually.of_forall fun time => negative_bound source pointLe shift time)).norm
  have gInt := (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp
    (gradientMajorant_integrable source pointLe ordered firstInside lastInside)
  have bMeas : AEStronglyMeasurable b measure := Real.continuous_sqrt.comp_aestronglyMeasurable gInt.aestronglyMeasurable
  have bSquare (time : ℝ) : b time ^ 2 = gradientMajorant source pointLe shift time :=
    Real.sq_sqrt (gradientMajorant_nonnegative source pointLe shift time)
  have bLp : MemLp b 2 measure := (memLp_two_iff_integrable_sq bMeas).mpr
    (gInt.congr (Eventually.of_forall fun time => (bSquare time).symm))
  have targetInt := difference_mass_integrable source pointLe ordered firstInside lastInside
  have upper := integral_mono_ae targetInt (aLp.integrable_mul bLp)
    (difference_interpolation_ae source pointLe left right shift firstInside lastInside)
  have targetNonnegative : 0 ≤ ∫ time, ‖difference source pointLe shift time‖ ^ 2 ∂measure :=
    integral_nonneg fun _ => sq_nonneg _
  have holder := NativePhysicalTimeInterpolation.integral_product_square
    (μ := measure) (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun _ => Real.sqrt_nonneg _) aLp bLp
  have result := (pow_le_pow_left₀ targetNonnegative upper 2).trans holder
  simp_rw [Real.sq_sqrt (gradientMajorant_nonnegative source pointLe shift _)] at result
  have convertIntegral (f : ℝ → ℝ) : (∫ time, f time ∂measure) = ∫ time in left..right, f time := by
    rw [intervalIntegral.integral_of_le ordered, ← integral_Icc_eq_integral_Ioc]
  rw [convertIntegral, convertIntegral, convertIntegral] at result
  apply result.trans
  have aBound := negative_integral_bound source pointLe ordered positive leftInside rightInside
  have gBound := gradient_integral_bound source pointLe ordered firstInside lastInside
  have product := mul_le_mul aBound gBound
    (intervalIntegral.integral_nonneg_of_forall ordered (gradientMajorant_nonnegative source pointLe shift))
    (mul_nonneg (by positivity) (mul_nonneg positive budget_nonnegative))
  exact product.trans_eq (by ring)

end
end SaturationMonoid.NavierStokes.NativeOriginalPhysicalTimeBudget
