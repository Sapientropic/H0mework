import H0mework.NavierStokes.SourceUnheated.BandGradient
import H0mework.NavierStokes.MacroAction.MacroMomentumIntegral
import H0mework.NavierStokes.StressTimeControl.UnfilteredBudget

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedMacroGradient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open NativeUnheatedBandGradient NativeMacroMomentumIntegral NativeRecoveryTimeGramRaw
open NativeOriginalGradientTime NativeOriginalNegativeOneBudget
noncomputable section
variable {nu : Viscosity} {current next : GeneratedWholeRestartCurrent nu}

theorem prefix_in_stage (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (length : ℕ) (time : ℝ) (inside : time ∈ Icc 0 (elapsedTime current length)) :
    step.physicalStageTrajectory time = puncturedWholeVelocityEuclideanState
      (wholeRestartPrefixPhysicalTrajectory current length time) := by
  have before : time < wholeRestartVelocityAccumulationTime current :=
    inside.2.trans_lt (elapsedTime_lt_wholeRestartVelocityAccumulationTime current step.elapsedBounded length)
  have stageInside : time ∈ Icc 0 step.clockAdvance :=
    ⟨inside.1, before.le.trans step.physicalStageAccumulation.2.2⟩
  rw [step.physicalStageTrajectory_eq_stage ⟨time, stageInside⟩, GeneratedWholeRestartEndpointMacroStep.physicalStage,
    sourceGeneratedWholeRestartBoundedAccumulationAbsoluteVelocitySplice_of_lt current step.elapsedBounded _ before]
  change puncturedWholeVelocityEuclideanState (wholeRestartBoundedPreAccumulationPhysicalTrajectory
    current step.elapsedBounded ⟨time, inside.1, before⟩) = _
  rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix current step.elapsedBounded _ length inside.2]

theorem stage_band_continuous (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (waves : Finset NonzeroIntegerWavevector) : Continuous (fun time => band waves (step.physicalStageTrajectory time)) :=
  band_curve_continuous step.physicalStageTrajectory_coordinate_continuous waves

theorem preaccumulation_bound (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (waves : Finset NonzeroIntegerWavevector) :
    (∫ time in 0..wholeRestartVelocityAccumulationTime current, band waves (step.physicalStageTrajectory time)) ≤
      biotSavartSerrinConstant * NativeUnheatedPrefixPayment.budget current := by
  have continuousIntegral : Continuous (fun last => ∫ time in 0..last, band waves (step.physicalStageTrajectory time)) :=
    (intervalIntegral.differentiable_integral_of_continuous (stage_band_continuous step waves)).continuous
  have elapsed : Tendsto (elapsedTime current) atTop (𝓝 (wholeRestartVelocityAccumulationTime current)) :=
    tendsto_atTop_ciSup (elapsedTime_strictMono current).monotone step.elapsedBounded
  apply le_of_tendsto (continuousIntegral.tendsto _ |>.comp elapsed)
  apply Eventually.of_forall
  intro length
  have same : (∫ time in 0..elapsedTime current length, band waves (step.physicalStageTrajectory time)) =
      ∫ time in 0..elapsedTime current length, band waves (puncturedWholeVelocityEuclideanState
        (wholeRestartPrefixPhysicalTrajectory current length time)) := by
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le (GeneratedWholeRestartCurrent.elapsedTime_nonneg current length)] at inside
    change band waves (step.physicalStageTrajectory time) = _
    rw [prefix_in_stage step length time inside]
  change (∫ time in 0..elapsedTime current length, band waves (step.physicalStageTrajectory time)) ≤ _
  rw [same]
  exact prefix_band_integral_bound current length waves


variable {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}

theorem recovery_band_continuous (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (waves : Finset NonzeroIntegerWavevector) : Continuous (fun time => band waves (recoveryCurve receipt time)) := by
  apply band_curve_continuous
  intro wave
  exact NativeCompleteStressAction.euclideanCLM.continuous.comp
    ((receipt.coordinate_continuous wave.1).comp continuous_projIcc)

theorem recovery_band_dominated (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (waves : Finset NonzeroIntegerWavevector) :
    ∀ᵐ time ∂commonTimeMeasure 1, band waves (recoveryCurve receipt time.1) ≤ 3 * carrierCost receipt time := by
  classical
  have rows := eventually_countable_forall.mpr
    (fun wave => fixedWaveSpaceTimeRestriction_coeFn 1 wave receipt.core.stateLimit)
  filter_upwards [rows, receipt.stateLimit_ae,
    wholePointwiseCarrierGradientDensity_ae_summable 1 receipt.core.stateLimit receipt.core.gradient_summable]
      with time equal same summable
  let density := wholePointwiseCarrierGradientDensity 1 receipt.core.stateLimit time
  have nonnegative (wave : IntegerWavevector) : 0 ≤ density wave := by
    exact mul_nonneg (integerWaveNormSq_nonneg _) (sq_nonneg _)
  have observed := summable.sum_le_tsum (waves.image Subtype.val) (fun wave _ => nonnegative wave)
  have image : (∑ wave ∈ waves.image Subtype.val, density wave) = ∑ wave ∈ waves, density wave.1 := by
    rw [Finset.sum_image]
    intro first _ last _ same
    exact Subtype.ext same
  rw [image] at observed
  apply (le_trans _ (mul_le_mul_of_nonneg_left observed (by norm_num : (0 : ℝ) ≤ 3)))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro wave _
  change integerWaveNormSq wave.1 * ‖euclideanCoordinateRow (NativeRecoveryRowAction.velocity receipt time.1 wave.1)‖ ^ 2 ≤ _
  rw [NativeRecoveryRowAction.velocity_on_interval, euclideanCoordinateRow_norm_sq, same, ← equal wave.1]
  have paid := mul_le_mul_of_nonneg_left
    (complexCoordinateAmplitudeSq_le_three_mul_norm_sq (fixedWaveSpaceTimeRestriction 1 wave.1 receipt.core.stateLimit time))
    (integerWaveNormSq_nonneg wave.1)
  simpa only [density, wholePointwiseCarrierGradientDensity, mul_left_comm] using paid


theorem recovery_integral_bound (receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger)
    (waves : Finset NonzeroIntegerWavevector) :
    (∫ time in 0..1, band waves (recoveryCurve receipt time)) ≤ gradientBudget receipt := by
  have integrable : Integrable (fun time : Icc (0 : ℝ) 1 => band waves (recoveryCurve receipt time.1)) (commonTimeMeasure 1) := by
    simpa only [integrableOn_univ, Function.comp_def] using! ContinuousOn.integrableOn_compact isCompact_univ
      ((recovery_band_continuous receipt waves).comp continuous_subtype_val).continuousOn
  have paid := integral_mono_ae integrable ((carrierCost_integrable (receipt := receipt)).const_mul 3)
    (recovery_band_dominated receipt waves)
  rw [integral_const_mul, carrier_integral] at paid
  have clock := commonTime_integral_eq_intervalIntegral 1 zero_le_one (fun time => band waves (recoveryCurve receipt time))
  rw [← clock]
  change _ ≤ gradientBudget receipt
  apply paid.trans
  unfold gradientBudget
  apply (le_div_iff₀ (mul_pos nu.coeff_pos (sq_pos_of_pos (by positivity)))).mpr
  have original := receipt.core.viscous_gradient_mass_le
  nlinarith

def budget (step : GeneratedWholeRestartEndpointMacroStep nu current next) : ℝ :=
  biotSavartSerrinConstant * NativeUnheatedPrefixPayment.budget current +
    gradientBudget (sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt current step.elapsedBounded)

theorem recovery_in_stage (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (time : ℝ) (inside : time ∈ Icc 0 (recoveryTime step)) :
    step.physicalStageTrajectory (wholeRestartVelocityAccumulationTime current + time) = recovery step time := by
  rw [physicalStage_reads_earlyCurve step _ (by
    rw [clock_split step]
    constructor <;> linarith [accumulation_positive step, inside.1, inside.2]), earlyCurve_after step time inside]

theorem stage_integral_bound (step : GeneratedWholeRestartEndpointMacroStep nu current next)
    (waves : Finset NonzeroIntegerWavevector) :
    (∫ time in 0..step.clockAdvance, band waves (step.physicalStageTrajectory time)) ≤ budget step := by
  have continuous := stage_band_continuous step waves
  have post : (∫ time in wholeRestartVelocityAccumulationTime current..step.clockAdvance,
      band waves (step.physicalStageTrajectory time)) =
      ∫ time in 0..recoveryTime step, band waves (recovery step time) := by
    have shifted := intervalIntegral.integral_comp_add_left (f := fun time => band waves (step.physicalStageTrajectory time))
      (a := 0) (b := recoveryTime step) (wholeRestartVelocityAccumulationTime current)
    simp only [add_zero] at shifted
    rw [clock_split, ← shifted]
    apply intervalIntegral.integral_congr
    intro time inside
    rw [uIcc_of_le (recoveryTime_mem step).1] at inside
    change band waves (step.physicalStageTrajectory (_ + time)) = _
    rw [recovery_in_stage step time inside]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous.intervalIntegrable 0 (wholeRestartVelocityAccumulationTime current))
    (continuous.intervalIntegrable (wholeRestartVelocityAccumulationTime current) step.clockAdvance), post]
  apply add_le_add (preaccumulation_bound step waves)
  have restricted := intervalIntegral.integral_mono_interval (μ := volume) (a := (0 : ℝ)) le_rfl
    (recoveryTime_mem step).1 (recoveryTime_mem step).2
    (Eventually.of_forall fun time => band_nonnegative waves (recovery step time))
    ((recovery_band_continuous _ waves).intervalIntegrable 0 1)
  exact restricted.trans (recovery_integral_bound _ waves)

end
end SaturationMonoid.NavierStokes.NativeUnheatedMacroGradient
