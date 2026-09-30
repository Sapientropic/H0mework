import H0mework.NavierStokes.SourceAction.ReceiptProfile
import H0mework.NavierStokes.PhysicalReadout.EndpointVelocity

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalMomentumIntegral

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open NativeEndpointVelocityCarrier NativeStressSource NativeTimeJetCarrier NativeFullOrderTime NativeReceiptTimeProfile

noncomputable section

def momentumAt (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  projectedDivergenceCLM wave (quadraticFlux (wholeVelocity velocity) wave) -
    (nu.coeff * integerWaveViscousMultiplier wave) • wholeVelocity velocity wave

theorem momentum_norm_le (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) (bound : ℝ) (bounded : ‖velocity‖ ≤ bound) :
    ‖momentumAt nu velocity wave‖ ≤ ‖projectedDivergenceCLM wave‖ * bound ^ 2 +
      |nu.coeff * integerWaveViscousMultiplier wave| * bound := by
  have boundNonnegative : 0 ≤ bound := (norm_nonneg _).trans bounded
  have stressBound : ‖quadraticFlux (wholeVelocity velocity) wave‖ ≤ bound ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (sq_nonneg bound)).mpr
    intro output
    apply (pi_norm_le_iff_of_nonneg (sq_nonneg bound)).mpr
    intro input
    have source := quadraticFlux_norm_le_mass (wholeVelocity velocity) wave output input
    rw [wholeVelocity_mass] at source
    exact source.trans ((sq_le_sq₀ (norm_nonneg _) boundNonnegative).mpr bounded)
  have velocityBound : ‖wholeVelocity velocity wave‖ ≤ bound :=
    ((lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (wholeVelocity velocity) wave).trans
      (wholeVelocity_norm_le velocity)).trans bounded
  exact (norm_sub_le _ _).trans (add_le_add
    (((projectedDivergenceCLM wave).le_opNorm _).trans (mul_le_mul_of_nonneg_left stressBound (norm_nonneg _)))
    (by simpa only [norm_smul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left velocityBound (abs_nonneg _)))

def receiptVelocity {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (time : ℝ) : WholeRestartVelocityEndpointState :=
  puncturedWholeVelocityEuclideanState (receipt.wholePath (projIcc (0 : ℝ) duration receipt.requestedTimePos.le time))

theorem receipt_action {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) duration) :
    momentumAt nu (receiptVelocity receipt time.1) wave = receiptMomentumAction receipt wave time.1 := by
  rw [receiptVelocity, projIcc_of_mem receipt.requestedTimePos.le time.2, momentumAt, wholeVelocity_punctured]
  exact (receipt_momentum_action time wave).symm

theorem receipt_row {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) duration) :
    wholeVelocity (receiptVelocity receipt time.1) wave = receiptVelocityRow receipt wave time.1 := by
  rw [receiptVelocity, projIcc_of_mem receipt.requestedTimePos.le time.2, wholeVelocity_punctured]
  exact (receipt_velocity_row_eq receipt wave time).symm

theorem receipt_integrable {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector) :
    IntervalIntegrable (fun actual => momentumAt nu (receiptVelocity receipt actual) wave) volume 0 duration := by
  apply ((receiptMomentumAction_continuous receipt wave).intervalIntegrable 0 duration).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with actual inside
  rw [uIoc_of_le receipt.requestedTimePos.le] at inside
  exact (receipt_action receipt wave ⟨actual, inside.1.le, inside.2⟩).symm

theorem receipt_primitive {nu : Viscosity} {initial : ComplexVorticityHilbertState} {duration : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initial duration) (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) duration) :
    wholeVelocity (receiptVelocity receipt time.1) wave - wholeVelocity (receiptVelocity receipt 0) wave =
      ∫ actual in 0..time.1, momentumAt nu (receiptVelocity receipt actual) wave := by
  have source := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := receiptVelocityRow receipt wave) (f' := receiptMomentumAction receipt wave)
    (a := 0) (b := time.1) (fun actual inside => receipt_velocity_row_hasDerivAt receipt wave
      ⟨actual, by rw [uIcc_of_le time.2.1] at inside; exact ⟨inside.1, inside.2.trans time.2.2⟩⟩)
    ((receiptMomentumAction_continuous receipt wave).intervalIntegrable _ _)
  rw [receipt_row receipt wave time, receipt_row receipt wave ⟨0, le_rfl, receipt.requestedTimePos.le⟩]
  rw [← source]
  apply intervalIntegral.integral_congr
  intro actual inside
  rw [uIcc_of_le time.2.1] at inside
  exact (receipt_action receipt wave ⟨actual, inside.1, inside.2.trans time.2.2⟩).symm

end
end SaturationMonoid.NavierStokes.NativeOriginalMomentumIntegral
