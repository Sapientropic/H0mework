import H0mework.NavierStokes.StressWholeH1.OriginalSource
import H0mework.NavierStokes.StressWholeH1.Pairing
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalGradientTime

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeOriginalResolventInput NativeWholeH1Mixed NativeWholeH1Pairing NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem mean_measurable (source : StressAt escape) (pointLe : point ≤ 1) :
    AEStronglyMeasurable (fun time : Icc (0 : ℝ) 1 => (meanInput source pointLe (.fixed time)).1) (commonTimeMeasure 1) := by
  have original := (puncturedEuclideanizeCLM.restrictScalars ℝ).continuous.comp_aestronglyMeasurable
    (Lp.memLp receipt.core.stateLimit).aestronglyMeasurable
  apply original.congr
  filter_upwards [receipt.stateLimit_ae] with time same
  change puncturedEuclideanize (receipt.core.stateLimit time) = puncturedEuclideanize (receipt.wholePath time)
  rw [same]

theorem mean_whole (source : StressAt escape) (pointLe : point ≤ 1) (time : Icc (0 : ℝ) 1) :
    wholeVelocity (meanInput source pointLe (.fixed time)).1 = receipt.wholePath time :=
  NativeRecoveryPhysical.wholeVelocity_puncturedEuclideanize _ (NativeRecoveryPhysical.wholeMild_zero ledger receipt time)

def carrierCost (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1) : ℝ := ∑' wave, wholePointwiseCarrierGradientDensity 1 receipt.core.stateLimit time wave

theorem carrierCost_integrable : Integrable (carrierCost receipt) (commonTimeMeasure 1) := by
  let g := fun wave time => wholePointwiseCarrierGradientDensity 1 receipt.core.stateLimit time wave
  have integrable (wave : IntegerWavevector) : Integrable (g wave) (commonTimeMeasure 1) :=
    wholePointwiseCarrierGradientDensity_integrable 1 receipt.core.stateLimit wave
  refine ⟨(AEMeasurable.tsum (fun wave => (integrable wave).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable, ?_⟩
  change (∫⁻ time, ‖∑' wave, g wave time‖ₑ ∂commonTimeMeasure 1) < ⊤
  apply lt_of_le_of_lt (lintegral_mono fun _ => enorm_tsum_le_tsum_enorm) ?_
  rw [lintegral_tsum (fun wave => (integrable wave).aestronglyMeasurable.enorm)]
  have rows (wave : IntegerWavevector) : (∫⁻ time, ‖g wave time‖ₑ ∂commonTimeMeasure 1) =
      ‖∫ time, ‖g wave time‖ ∂commonTimeMeasure 1‖ₑ := by
    rw [Real.enorm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact (ofReal_integral_norm_eq_lintegral_enorm (integrable wave)).symm
  simp_rw [rows]
  apply lt_top_iff_ne_top.mpr
  apply ENNReal.tsum_coe_ne_top_iff_summable.mpr
  apply NNReal.summable_coe.mp
  have paid := receipt.core.gradient_summable.congr
    (fun wave => (wholePointwiseCarrierGradientDensity_integral_norm 1 receipt.core.stateLimit wave).symm)
  exact paid.abs

theorem gradient_measurable (source : StressAt escape) (pointLe : point ≤ 1) :
    AEStronglyMeasurable (fun time : Icc (0 : ℝ) 1 => gradientMass (meanInput source pointLe (.fixed time)))
      (commonTimeMeasure 1) := by
  have field := wholeVelocityCLM.continuous.comp_aestronglyMeasurable (mean_measurable source pointLe)
  apply AEMeasurable.aestronglyMeasurable
  apply AEMeasurable.tsum
  intro wave
  have coordinate := NativeCompleteStressAction.euclideanCLM.continuous.comp_aestronglyMeasurable
    ((NativeCommonAdvectorAction.evaluation wave).continuous.comp_aestronglyMeasurable field)
  exact (coordinate.norm.aemeasurable.pow_const 2).const_mul (integerWaveNormSq wave)

theorem gradient_dominated (source : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time ∂commonTimeMeasure 1, gradientMass (meanInput source pointLe (.fixed time)) ≤ 3 * carrierCost receipt time := by
  have rows := eventually_countable_forall.mpr
    (fun wave => fixedWaveSpaceTimeRestriction_coeFn 1 wave receipt.core.stateLimit)
  filter_upwards [rows, receipt.stateLimit_ae,
    wholePointwiseCarrierGradientDensity_ae_summable 1 receipt.core.stateLimit receipt.core.gradient_summable,
    NativeWholeH1OriginalSource.meanInput_curl_summable_ae source pointLe] with time equal same summable regular
  rw [carrierCost, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (h1_of_curl_summable _ regular) (summable.mul_left 3)
  intro wave
  rw [gradientDensity, NativeMovingCriticalProduct.amplitude, mean_whole source pointLe time,
    same, ← equal wave, euclideanCoordinateRow_norm_sq]
  have amplitude := complexCoordinateAmplitudeSq_le_three_mul_norm_sq (fixedWaveSpaceTimeRestriction 1 wave receipt.core.stateLimit time)
  exact (mul_le_mul_of_nonneg_left amplitude (integerWaveNormSq_nonneg wave)).trans_eq (by
    unfold wholePointwiseCarrierGradientDensity
    ring)

theorem gradient_integrable (source : StressAt escape) (pointLe : point ≤ 1) :
    Integrable (fun time : Icc (0 : ℝ) 1 => gradientMass (meanInput source pointLe (.fixed time))) (commonTimeMeasure 1) := by
  apply (carrierCost_integrable (receipt := receipt)).const_mul 3 |>.mono'
    (gradient_measurable source pointLe)
  filter_upwards [gradient_dominated source pointLe] with time paid
  have nonnegative : 0 ≤ gradientMass (meanInput source pointLe (.fixed time)) :=
    tsum_nonneg (gradient_nonnegative _)
  rw [Real.norm_of_nonneg nonnegative]
  exact paid

end
end SaturationMonoid.NavierStokes.NativeOriginalGradientTime
