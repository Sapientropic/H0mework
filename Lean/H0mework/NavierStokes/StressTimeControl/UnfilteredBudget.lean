import H0mework.NavierStokes.StressNegativeOne.Write

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalNegativeOneBudget

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeOriginalResolventInput
open NativeWholeH1Mixed NativeOriginalGradientTime NativeNegativeOneMomentum
open NativeOriginalNegativeOneRate

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem carrier_integral : (∫ time, carrierCost receipt time ∂commonTimeMeasure 1) =
    wholeSpaceTimeVorticityGradientMass 1 receipt.core.stateLimit := by
  have paid := receipt.core.gradient_summable.congr
    (fun wave => (wholePointwiseCarrierGradientDensity_integral_norm 1 receipt.core.stateLimit wave).symm)
  change (∫ time, ∑' wave, wholePointwiseCarrierGradientDensity 1 receipt.core.stateLimit time wave ∂commonTimeMeasure 1) = _
  rw [← integral_tsum_of_summable_integral_norm
    (fun wave => wholePointwiseCarrierGradientDensity_integrable 1 receipt.core.stateLimit wave) paid]
  simp_rw [wholePointwiseCarrierGradientDensity_integral]
  rfl

def gradientBudget (_receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) : ℝ :=
  3 * ((1 / 2 : ℝ) * ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2) / (nu.coeff * (2 * Real.pi) ^ 2)

theorem gradientBudget_nonnegative : 0 ≤ gradientBudget receipt := by
  have viscosity := nu.coeff_pos.le
  unfold gradientBudget
  positivity

theorem gradient_integral_bound (source : StressAt escape) (pointLe : point ≤ 1) :
    (∫ time, gradientMass (meanInput source pointLe (.fixed time)) ∂commonTimeMeasure 1) ≤ gradientBudget receipt := by
  have actual := integral_mono_ae (gradient_integrable source pointLe)
    ((carrierCost_integrable (receipt := receipt)).const_mul 3) (gradient_dominated source pointLe)
  rw [integral_const_mul, carrier_integral] at actual
  apply actual.trans
  apply (le_div_iff₀ (mul_pos nu.coeff_pos (sq_pos_of_pos (by positivity)))).mpr
  have paid := mul_le_mul_of_nonneg_left receipt.core.viscous_gradient_mass_le (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

theorem common_mass : (commonTimeMeasure 1).real univ = 1 := by
  let terminal : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  have whole : Iic terminal = univ := by
    ext time
    simp only [mem_Iic, mem_univ, iff_true]
    exact time.2.2
  have paid := commonTimeMeasure_Iic_real 1 zero_le_one terminal
  simpa only [whole, Measure.restrict_univ] using paid

def budget (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger) : ℝ :=
  coefficient nu * (1 + gradientBudget receipt)

theorem budget_nonnegative : 0 ≤ budget receipt :=
  mul_nonneg (coefficient_nonnegative nu) (add_nonneg zero_le_one gradientBudget_nonnegative)

theorem rate_integral_bound (source : StressAt escape) (pointLe : point ≤ 1) :
    (∫ time, ‖rate source pointLe time‖ ∂commonTimeMeasure 1) ≤ budget receipt := by
  have actual := integral_mono_ae (rate_integrable source pointLe).norm
    (((integrable_const (1 : ℝ)).add (gradient_integrable source pointLe)).const_mul (coefficient nu))
    (Eventually.of_forall (rate_bound source pointLe))
  dsimp only [Pi.add_apply] at actual
  rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) (gradient_integrable source pointLe),
    integral_const, common_mass, one_smul] at actual
  exact actual.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (gradient_integral_bound source pointLe))
    (coefficient_nonnegative nu))

end
end SaturationMonoid.NavierStokes.NativeOriginalNegativeOneBudget
