import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryCoverage
import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryPhysical
import H0mework.Versions.X.NavierStokes.CofinalReadout.FluxPairing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeRecoveryEscapeCarrier

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFiniteObservationTimeTightness
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeRecoveryCoverage NativeRecoveryControlProducer NativeRecoveryPhysical
open NativeEndpointVelocityCarrier NativeCofinalFluxPairing

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}

def radius (escape : SourceActionEscape receipt point) (index : ℕ) : ℕ :=
  receipt.core.subsequence (escape.extraction (escape.index index))

def sampleTime (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨escape.sample index,
    ⟨escape.anchor_inside.1.le.trans ((le_max_left _ _).trans (escape.sample_inside index).1.le),
      (escape.sample_inside index).2.le.trans pointLe⟩⟩

def state (escape : SourceActionEscape receipt point) (index : ℕ) : ComplexVorticityHilbertState :=
  (ledger.family.stage (radius escape index)).trajectory (escape.sample index)

def velocity (escape : SourceActionEscape receipt point) (index : ℕ) : WholeRestartVelocityEndpointState :=
  puncturedWholeVelocityEuclideanState (state escape index)

def endpoint (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (time : Icc (0 : ℝ) 1) : WholeRestartVelocityEndpointState := puncturedEuclideanize (receipt.wholePath time)

theorem point_nonnegative (escape : SourceActionEscape receipt point) : 0 ≤ point :=
  escape.anchor_inside.1.le.trans escape.anchor_inside.2.le

theorem velocity_row_tendsto (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (wave : IntegerWavevector) :
    Tendsto (fun index => finiteStateVelocityCoefficient (state escape index) wave) atTop
      (𝓝 (receipt.wholePath ⟨point, point_nonnegative escape, pointLe⟩ wave)) := by
  let time : Icc (0 : ℝ) 1 := ⟨point, point_nonnegative escape, pointLe⟩
  have fixed := (endpoint_velocity_row_tendsto ledger receipt.core time wave).comp
    (escape.extraction_strict.tendsto_atTop.comp (tendsto_atTop_mono escape.index_ge tendsto_id))
  rw [← receipt.wholePath_apply] at fixed
  apply fixed.congr_dist
  have timeGap : Tendsto (fun index => generatedVelocityEndpointGalerkinWaveSpeedCeiling ledger wave *
      dist point (escape.sample index)) atTop (𝓝 0) := by
    simpa only [dist_self, mul_zero] using
      ((tendsto_const_nhds (x := point)).dist escape.sample_tendsto).const_mul
        (generatedVelocityEndpointGalerkinWaveSpeedCeiling ledger wave)
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ timeGap
  exact Eventually.of_forall fun index =>
    generatedVelocityEndpointGalerkinWavePath_dist_le_allRadius ledger (radius escape index) wave time
      (sampleTime escape pointLe index)

theorem velocity_norm_bound (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) :
    ‖velocity escape index‖ ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ := by
  have physical := (ledger.family.stage (radius escape index)).physical _ (sampleTime escape pointLe index).2
  have source := ledger.kinetic_energy_le (radius escape index) (sampleTime escape pointLe index)
  have exactMass := puncturedWholeVelocityEuclideanState_norm_sq (state escape index) physical.2.2.1
  rw [puncturedWholeVorticityKineticMass_eq_two_mul_finiteEnergy (wholeRestartModes (radius escape index))
    (zero_not_mem_puncturedIntegerWaveFrequencyCube _) (state escape index) physical.2.1
    (fun wave _ => physical.2.2.1 wave)] at exactMass
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖puncturedWholeVelocityEuclideanState (state escape index)‖ ^ 2 ≤ _
  rw [exactMass]
  change finiteStateVorticityKineticEnergy (wholeRestartModes (radius escape index)) (state escape index) ≤ _ at source
  linarith

theorem endpoint_norm_bound (time : Icc (0 : ℝ) 1) :
    ‖endpoint receipt time‖ ≤ ‖ledger.family.endpointReceipt.velocityEndpoint‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖puncturedEuclideanize (receipt.wholePath time)‖ ^ 2 ≤ _
  rw [receipt.wholePath_apply]
  exact velocityEndpointWholeMildState_physical_norm_sq_le_endpoint receipt.core time

theorem velocity_coefficient_tendsto (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (wave : NonzeroIntegerWavevector) :
    Tendsto (fun index => velocity escape index wave) atTop
      (𝓝 (endpoint receipt ⟨point, point_nonnegative escape, pointLe⟩ wave)) := by
  have source := (PiLp.continuous_toLp 2 (fun _ : Coordinate => ℂ)).tendsto _ |>.comp
    (velocity_row_tendsto escape pointLe wave.1)
  exact source

theorem velocity_reality (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1) (index : ℕ) :
    WholeRestartVelocityEndpointReality (velocity escape index) := by
  have physical := (ledger.family.stage (radius escape index)).physical _ (sampleTime escape pointLe index).2
  intro wave coordinate
  change biotSavartVelocityCoefficient (waveNeg wave.1) (state escape index (waveNeg wave.1)) coordinate =
    star (biotSavartVelocityCoefficient wave.1 (state escape index wave.1) coordinate)
  have reality : FiniteStateFourierReality (state escape index) := physical.2.2.2
  rw [reality wave.1, biotSavartVelocityCoefficient_waveNeg_vectorConj]
  rfl

theorem endpoint_reality (time : Icc (0 : ℝ) 1) : WholeRestartVelocityEndpointReality (endpoint receipt time) := by
  intro wave coordinate
  exact congrFun (wholeMild_reality ledger receipt time wave.1) coordinate

theorem weak_of_bounded_coordinates (sequence : ℕ → WholeRestartVelocityEndpointState)
    (limit : WholeRestartVelocityEndpointState) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (sequenceBound : ∀ index, ‖sequence index‖ ≤ bound) (limitBound : ‖limit‖ ≤ bound)
    (rows : ∀ wave, Tendsto (fun index => sequence index wave) atTop (𝓝 (limit wave)))
    (test : WholeRestartVelocityEndpointState) :
    Tendsto (fun index => inner ℂ (sequence index) test) atTop (𝓝 (inner ℂ limit test)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  have denominator : 0 < 4 * (bound + 1) := by positivity
  have approximation : ∀ᶠ observed : Finset NonzeroIntegerWavevector in atTop,
      (∑ wave ∈ observed, lp.single 2 wave (test wave)) ∈ Metric.ball test (epsilon / (4 * (bound + 1))) :=
    (lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) test)
    (Metric.ball_mem_nhds test (div_pos positive denominator))
  obtain ⟨observed, observedClose⟩ := approximation.exists
  let finiteTest : WholeRestartVelocityEndpointState := ∑ wave ∈ observed, lp.single 2 wave (test wave)
  have nearby : ‖test - finiteTest‖ < epsilon / (4 * (bound + 1)) := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev, finiteTest] using observedClose
  have finiteConverges : Tendsto (fun index => inner ℂ (sequence index) finiteTest) atTop
      (𝓝 (inner ℂ limit finiteTest)) := by
    simp only [finiteTest, inner_sum, lp.inner_single_right]
    exact tendsto_finsetSum observed (fun wave _ => (rows wave).inner tendsto_const_nhds)
  have close := finiteConverges (Metric.ball_mem_nhds (inner ℂ limit finiteTest) (half_pos positive))
  filter_upwards [close] with index nearFinite
  have center : ‖inner ℂ (sequence index) finiteTest - inner ℂ limit finiteTest‖ < epsilon / 2 := by
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using nearFinite
  have first : ‖inner ℂ (sequence index) (test - finiteTest)‖ ≤ bound * ‖test - finiteTest‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (sequenceBound index) (norm_nonneg _))
  have last : ‖inner ℂ limit (finiteTest - test)‖ ≤ bound * ‖test - finiteTest‖ := by
    calc
      _ ≤ ‖limit‖ * ‖finiteTest - test‖ := norm_inner_le_norm _ _
      _ ≤ bound * ‖finiteTest - test‖ := mul_le_mul_of_nonneg_right limitBound (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev]
  have identity : inner ℂ (sequence index) test - inner ℂ limit test =
      inner ℂ (sequence index) (test - finiteTest) +
        (inner ℂ (sequence index) finiteTest - inner ℂ limit finiteTest) +
          inner ℂ limit (finiteTest - test) := by
    rw [inner_sub_right, inner_sub_right]
    ring
  have triangle := (norm_add_le (inner ℂ (sequence index) (test - finiteTest) +
      (inner ℂ (sequence index) finiteTest - inner ℂ limit finiteTest)) (inner ℂ limit (finiteTest - test))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [← identity] at triangle
  have small := (lt_div_iff₀ denominator).mp nearby
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (test - finiteTest)]

theorem velocity_weak_tendsto (escape : SourceActionEscape receipt point) (pointLe : point ≤ 1)
    (test : WholeRestartVelocityEndpointState) :
    Tendsto (fun index => inner ℂ (velocity escape index) test) atTop
      (𝓝 (inner ℂ (endpoint receipt ⟨point, point_nonnegative escape, pointLe⟩) test)) :=
  weak_of_bounded_coordinates (velocity escape) _ ‖ledger.family.endpointReceipt.velocityEndpoint‖ (norm_nonneg _)
    (velocity_norm_bound escape pointLe) (endpoint_norm_bound _) (velocity_coefficient_tendsto escape pointLe) test

end
end SaturationMonoid.NavierStokes.NativeRecoveryEscapeCarrier
