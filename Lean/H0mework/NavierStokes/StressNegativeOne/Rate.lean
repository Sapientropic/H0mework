import H0mework.NavierStokes.StressNegativeOne.GradientTime
import H0mework.NavierStokes.StressNegativeOne.Momentum
import H0mework.NavierStokes.UnifiedAction.UnifiedSourceActionFeed

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalNegativeOneRate

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw
open NativeOriginalResolventInput NativeWholeH1Mixed NativeWholeH1Pairing NativeResolventCompactness
open NativeOriginalGradientTime NativeNegativeOneInclusion NativeNegativeOneMomentum
open NativeOriginalStressAction NativeCompleteStressAction NativeCompleteStressBilinear NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

/-- An a.e. representative for integration; its original momentum identity is
generated below on the receipt's own full-measure H¹ face. -/
def rate (source : StressAt escape) (pointLe : point ≤ 1) (time : Icc (0 : ℝ) 1) : State := by
  classical
  exact if regular : H1 (meanInput source pointLe (.fixed time)) then
    NativeNegativeOneMomentum.momentum nu (meanInput source pointLe (.fixed time)) regular else 0

theorem rate_original_ae (source : StressAt escape) (pointLe : point ≤ 1) :
    ∀ᵐ time ∂commonTimeMeasure 1, ∀ wave : Wave, rate source pointLe time wave =
      (lowerWeight wave)⁻¹ • (NativeWholeResolventZeroAction.momentumOperator nu
        (meanInput source pointLe (.fixed time)).1 (meanInput source pointLe (.fixed time)).1 wave) := by
  filter_upwards [NativeWholeH1OriginalSource.meanInput_curl_summable_ae source pointLe] with time generated
  have regular := h1_of_curl_summable _ generated
  intro wave
  rw [rate, dif_pos regular]
  exact original_row nu _ regular wave

theorem rate_measurable (source : StressAt escape) (pointLe : point ≤ 1) :
    AEStronglyMeasurable (rate source pointLe) (commonTimeMeasure 1) := by
  have rows (wave : Wave) : AEStronglyMeasurable (fun time => rate source pointLe time wave) (commonTimeMeasure 1) := by
    have original := (original_continuous nu).comp_aestronglyMeasurable (mean_measurable source pointLe)
    have read := ((lp.evalCLM ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.comp_aestronglyMeasurable original).const_smul
      (lowerWeight wave)⁻¹
    apply read.congr
    filter_upwards [rate_original_ae source pointLe] with time same
    exact (same wave).symm
  let part (observed : Finset Wave) (time : Icc (0 : ℝ) 1) : State :=
    ∑ wave ∈ observed, lp.single 2 wave (rate source pointLe time wave)
  have measurable (observed : Finset Wave) : AEStronglyMeasurable (part observed) (commonTimeMeasure 1) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro wave _
    exact (lp.singleContinuousLinearMap ℝ (fun _ : Wave => ComplexCoordinateEuclidean) 2 wave).continuous.comp_aestronglyMeasurable (rows wave)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Wave)) measurable
  exact Eventually.of_forall fun time => lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) (rate source pointLe time)

theorem rate_bound (source : StressAt escape) (pointLe : point ≤ 1) (time : Icc (0 : ℝ) 1) :
    ‖rate source pointLe time‖ ≤ coefficient nu * (1 + gradientMass (meanInput source pointLe (.fixed time))) := by
  by_cases regular : H1 (meanInput source pointLe (.fixed time))
  · rw [rate, dif_pos regular]
    exact momentum_bound nu _ regular
  · rw [rate, dif_neg regular, norm_zero]
    exact mul_nonneg (coefficient_nonnegative nu) (add_nonneg zero_le_one (tsum_nonneg (gradient_nonnegative _)))

theorem rate_integrable (source : StressAt escape) (pointLe : point ≤ 1) :
    Integrable (rate source pointLe) (commonTimeMeasure 1) :=
  ((integrable_const (1 : ℝ)).add (gradient_integrable source pointLe)).const_mul (coefficient nu) |>.mono'
    (rate_measurable source pointLe) (Eventually.of_forall (rate_bound source pointLe))

theorem original_writer (source : StressAt escape) (pointLe : point ≤ 1) (time : Icc (0 : ℝ) 1) :
    momentumCLM nu (WithLp.toLp 2 ((meanInput source pointLe (.fixed time)).1,
      originalStress source pointLe (.fixed time))) = NativeUnifiedSourceActionFeed.actionAt source pointLe (.fixed time) := by
  apply lp.ext
  funext wave
  rw [originalStress, momentumCLM_source]
  change NativeNegativeFourMomentum.weightedRowCLM wave.1
    (NativeTimeJetCarrier.projectedDivergenceCLM wave.1 (NativeRecoveryTimeGramReadout.stressRead source pointLe (.fixed time) wave.1) -
      (nu.coeff * integerWaveViscousMultiplier wave.1) • wholeVelocity (meanInput source pointLe (.fixed time)).1 wave.1) =
    NativeNegativeFourMomentum.weightedRowCLM wave.1
      (NativeTimeJetCarrier.projectedDivergenceCLM wave.1 (NativeRecoveryTimeGramReadout.stressRead source pointLe (.fixed time) wave.1) -
        (nu.coeff * integerWaveViscousMultiplier wave.1) • NativeRecoveryTimeGramReadout.velocityRead source pointLe (.fixed time) wave.1)
  have read : NativeRecoveryTimeGramReadout.velocityRead source pointLe (.fixed time) wave.1 = receipt.wholePath time wave.1 :=
    funext (NativeRecoveryTimeGramReadout.source_velocity source pointLe (.fixed time) wave.1)
  rw [read, mean_whole source pointLe time]

theorem lower_rate_ae (source : StressAt escape) (pointLe : point ≤ 1) :
    (fun time => lowerCLM (rate source pointLe time)) =ᵐ[commonTimeMeasure 1]
      (fun time => NativeUnifiedSourceActionFeed.actionAt source pointLe (.fixed time)) := by
  filter_upwards [NativeWholeH1OriginalSource.meanInput_curl_summable_ae source pointLe,
    NativeRecoveryTimeGramMeasured.source_stress_ae source pointLe] with time generated stress
  have regular := h1_of_curl_summable _ generated
  rw [rate, dif_pos regular, NativeNegativeOneMomentum.momentum, lower_momentum, ← original_writer source pointLe time]
  have tensor : originalStress source pointLe (.fixed time) =
      mixed (wholeVelocity (meanInput source pointLe (.fixed time)).1)
        (wholeVelocity (meanInput source pointLe (.fixed time)).1) := by
    apply NativeCompleteStressCarrier.read_injective
    rw [originalStress, NativeCompleteStressCarrier.read_ofBound, stress, mixed_read, NativeHigherTimeJets.mixedFlux_diagonal,
      mean_whole source pointLe time]
  rw [tensor]
  rfl

end
end SaturationMonoid.NavierStokes.NativeOriginalNegativeOneRate
