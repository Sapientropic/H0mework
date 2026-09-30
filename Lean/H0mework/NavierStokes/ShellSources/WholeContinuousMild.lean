import H0mework.NavierStokes.ShellSources.InfiniteMildDuhamel
import H0mework.NavierStokes.ShellSources.InfiniteMildPhysicalLimit
import H0mework.NavierStokes.WholeSpace.WholeSpaceTimeCoordinateParseval
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Whole continuous mild state from the generated negative-one forcing

The source-generated infinite mild receipt already supplies one common
initial state, one whole `L²_t H⁻¹_x` nonlinear forcing, and a continuous
mild representative of every nonzero Fourier row.  This module performs
the genuinely whole-carrier parabolic step.

For every nonzero wave `k`, the frequency growth in the unweighted
nonlinearity is paired with the viscous kernel

```text
sqrt(m_k) * exp (-ν m_k (t - s)) * 1_{s ≤ t}.
```

Its time-`L²` norm is bounded by `(2ν)⁻¹/²`, independently of `k` and `t`.
Orthogonal summation over all waves therefore yields uniform `ℓ²` tails,
which assemble the fixed-row mild laws into an actual whole continuous
state.  No cutoff, terminal frequency, tail-silence certificate, or target
continuation conclusion is accepted as input.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild

open scoped BigOperators ENNReal Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildPhysicalLimit
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval

noncomputable section

private theorem causal_exp_interval_integral
    (a time : ℝ)
    (aNe : a ≠ 0) :
    (∫ earlier : ℝ in 0..time,
        Real.exp (a * (earlier - time))) =
      a⁻¹ * (1 - Real.exp (-a * time)) := by
  rw [intervalIntegral.integral_comp_sub_right
    (fun x : ℝ => Real.exp (a * x)) time]
  simp only [zero_sub, sub_self]
  rw [intervalIntegral.integral_comp_mul_left
    (f := fun x : ℝ => Real.exp x) (a := -time) (b := 0) aNe]
  simp only [mul_zero, integral_exp, Real.exp_zero, smul_eq_mul]
  congr 1 <;> ring

/--
The weighted causal heat kernel which converts the actual negative-one
forcing coordinate into the unweighted Duhamel coordinate.
-/
def weightedCausalHeatKernelFunction
    (requestedTime ν : ℝ)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    Icc (0 : ℝ) requestedTime → ℂ :=
  (Iic time).indicator fun earlier =>
    ((Real.sqrt (integerWaveViscousMultiplier wave) *
      finiteStateVorticityHeatMultiplier
        ν (time.1 - earlier.1) wave : ℝ) : ℂ)

theorem weightedCausalHeatKernelFunction_aestronglyMeasurable
    (requestedTime ν : ℝ)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    AEStronglyMeasurable
      (weightedCausalHeatKernelFunction requestedTime ν wave time)
      (commonTimeMeasure requestedTime) := by
  apply AEStronglyMeasurable.indicator
  · apply Continuous.aestronglyMeasurable
    apply Complex.continuous_ofReal.comp
    unfold finiteStateVorticityHeatMultiplier
    fun_prop
  · exact measurableSet_Iic

private theorem weightedCausalHeatKernelFunction_norm_sq_on_interval
    (ν : ℝ)
    (wave : IntegerWavevector)
    (earlier time : ℝ) :
    ‖((Real.sqrt (integerWaveViscousMultiplier wave) *
        finiteStateVorticityHeatMultiplier
          ν (time - earlier) wave : ℝ) : ℂ)‖ ^ 2 =
      integerWaveViscousMultiplier wave *
        Real.exp
          ((2 * ν * integerWaveViscousMultiplier wave) *
            (earlier - time)) := by
  have multiplierNonneg :
      0 ≤ integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact
      mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg wave)
  unfold finiteStateVorticityHeatMultiplier
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (Real.exp_nonneg _))]
  rw [mul_pow, Real.sq_sqrt multiplierNonneg]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem weightedCausalHeatKernelFunction_integral_norm_sq
    (requestedTime ν : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (wave : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    (∫ earlier,
        ‖weightedCausalHeatKernelFunction
          requestedTime ν wave time earlier‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
      ∫ earlier in (0 : ℝ)..time.1,
        integerWaveViscousMultiplier wave *
          Real.exp
            ((2 * ν * integerWaveViscousMultiplier wave) *
              (earlier - time.1)) := by
  calc
    (∫ earlier,
        ‖weightedCausalHeatKernelFunction
          requestedTime ν wave time earlier‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
        ∫ earlier in Iic time,
          ‖((Real.sqrt (integerWaveViscousMultiplier wave) *
              finiteStateVorticityHeatMultiplier
                ν (time.1 - earlier.1) wave : ℝ) : ℂ)‖ ^ 2
          ∂(commonTimeMeasure requestedTime) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      filter_upwards with earlier
      by_cases earlierLe : earlier ≤ time
      · simp [weightedCausalHeatKernelFunction, earlierLe]
      · simp [weightedCausalHeatKernelFunction, earlierLe]
    _ =
        ∫ earlier in (0 : ℝ)..time.1,
          ‖((Real.sqrt (integerWaveViscousMultiplier wave) *
              finiteStateVorticityHeatMultiplier
                ν (time.1 - earlier) wave : ℝ) : ℂ)‖ ^ 2 := by
      exact
        commonTime_integral_Iic_eq_intervalIntegral
          requestedTime requestedTimeNonneg time
          (fun earlier =>
            ‖((Real.sqrt (integerWaveViscousMultiplier wave) *
                finiteStateVorticityHeatMultiplier
                  ν (time.1 - earlier) wave : ℝ) : ℂ)‖ ^ 2)
    _ =
        ∫ earlier in (0 : ℝ)..time.1,
          integerWaveViscousMultiplier wave *
            Real.exp
              ((2 * ν * integerWaveViscousMultiplier wave) *
                (earlier - time.1)) := by
      apply intervalIntegral.integral_congr
      intro earlier earlierMem
      exact
        weightedCausalHeatKernelFunction_norm_sq_on_interval
          ν wave earlier time.1

theorem weightedCausalHeatKernelFunction_integral_norm_sq_le
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    (∫ earlier,
        ‖weightedCausalHeatKernelFunction
          requestedTime ν wave time earlier‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) ≤
      (2 * ν)⁻¹ := by
  have requestedTimeNonneg : 0 ≤ requestedTime :=
    time.2.1.trans time.2.2
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact
      mul_pos (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
        (integerWaveNormSq_pos waveNe)
  let a : ℝ := 2 * ν * integerWaveViscousMultiplier wave
  have aPos : 0 < a := by
    dsimp [a]
    positivity
  rw [weightedCausalHeatKernelFunction_integral_norm_sq
    requestedTime ν requestedTimeNonneg wave time]
  rw [intervalIntegral.integral_const_mul]
  rw [causal_exp_interval_integral a time.1 aPos.ne']
  have exponentialNonneg :
      0 ≤ Real.exp (-a * time.1) := Real.exp_nonneg _
  have oneSubLe : 1 - Real.exp (-a * time.1) ≤ 1 := by
    linarith
  calc
    integerWaveViscousMultiplier wave *
        (a⁻¹ * (1 - Real.exp (-a * time.1))) ≤
      integerWaveViscousMultiplier wave * (a⁻¹ * 1) := by
        gcongr
    _ = (2 * ν)⁻¹ := by
      dsimp [a]
      field_simp [νPos.ne', multiplierPos.ne']

theorem weightedCausalHeatKernelFunction_memLp
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    MemLp
      (weightedCausalHeatKernelFunction requestedTime ν wave time)
      2 (commonTimeMeasure requestedTime) := by
  have measurable :=
    weightedCausalHeatKernelFunction_aestronglyMeasurable
      requestedTime ν wave time
  apply MemLp.of_bound measurable
    (Real.sqrt (integerWaveViscousMultiplier wave))
  filter_upwards with earlier
  by_cases earlierLe : earlier ≤ time
  · simp only [weightedCausalHeatKernelFunction,
      Set.indicator_apply, Set.mem_Iic, earlierLe, if_true,
      Complex.norm_real]
    rw [Real.norm_of_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (finiteStateVorticityHeatMultiplier_nonneg
          ν (time.1 - earlier.1) wave))]
    calc
      Real.sqrt (integerWaveViscousMultiplier wave) *
          finiteStateVorticityHeatMultiplier
            ν (time.1 - earlier.1) wave ≤
        Real.sqrt (integerWaveViscousMultiplier wave) * 1 := by
          gcongr
          exact
            finiteStateVorticityHeatMultiplier_le_one
              νPos.le (sub_nonneg.mpr earlierLe) wave
      _ = Real.sqrt (integerWaveViscousMultiplier wave) := by
        ring
  · simp [weightedCausalHeatKernelFunction, earlierLe,
      Real.sqrt_nonneg]

/-- The weighted causal heat kernel installed in the exact common time
`L²` carrier. -/
def weightedCausalHeatKernelL2
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    MeasureTheory.Lp ℂ 2
      (commonTimeMeasure requestedTime) :=
  (weightedCausalHeatKernelFunction_memLp
    requestedTime ν νPos wave waveNe time).toLp
      (weightedCausalHeatKernelFunction requestedTime ν wave time)

theorem weightedCausalHeatKernelL2_norm_sq_le
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖weightedCausalHeatKernelL2
        requestedTime ν νPos wave waveNe time‖ ^ 2 ≤
      (2 * ν)⁻¹ := by
  unfold weightedCausalHeatKernelL2
  rw [MeasureTheory.Lp.norm_toLp]
  rw [MeasureTheory.toReal_eLpNorm
    (weightedCausalHeatKernelFunction_aestronglyMeasurable
      requestedTime ν wave time)]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    (weightedCausalHeatKernelFunction_aestronglyMeasurable
      requestedTime ν wave time)]
  norm_num
  have powerIdentity :
      ((∫ earlier,
          ‖weightedCausalHeatKernelFunction
            requestedTime ν wave time earlier‖ ^ 2
          ∂(commonTimeMeasure requestedTime)) ^
            ((2 : ℝ)⁻¹)) ^ 2 =
        ∫ earlier,
          ‖weightedCausalHeatKernelFunction
            requestedTime ν wave time earlier‖ ^ 2
          ∂(commonTimeMeasure requestedTime) :=
    Real.rpow_inv_natCast_pow (n := 2)
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  calc
    ((∫ earlier,
        ‖weightedCausalHeatKernelFunction
          requestedTime ν wave time earlier‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) ^
          (1 / 2 : ℝ)) ^ 2 =
      ∫ earlier,
        ‖weightedCausalHeatKernelFunction
          requestedTime ν wave time earlier‖ ^ 2
        ∂(commonTimeMeasure requestedTime) := by
          convert powerIdentity using 1 <;> norm_num
    _ ≤ ν⁻¹ * (1 / 2) := by
      calc
        (∫ earlier,
            ‖weightedCausalHeatKernelFunction
              requestedTime ν wave time earlier‖ ^ 2
            ∂(commonTimeMeasure requestedTime)) ≤
            (2 * ν)⁻¹ :=
          weightedCausalHeatKernelFunction_integral_norm_sq_le
            requestedTime ν νPos wave waveNe time
        _ = ν⁻¹ * (1 / 2) := by
          field_simp [νPos.ne']

/--
The weighted heat convolution maps one negative-one forcing coordinate
into the unweighted Duhamel coordinate with a frequency-independent
parabolic bound.
-/
theorem fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_le
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime)
    (forcing : FixedWaveSpaceTimeState requestedTime) :
    ‖fixedL2ScalarL2IntegralCLM requestedTime
        (weightedCausalHeatKernelL2
          requestedTime ν νPos wave waveNe time)
        forcing‖ ^ 2 ≤
      (2 * ν)⁻¹ * ‖forcing‖ ^ 2 := by
  let kernel :=
    weightedCausalHeatKernelL2
      requestedTime ν νPos wave waveNe time
  have convolutionNormLe :
      ‖fixedL2ScalarL2IntegralCLM
          requestedTime kernel forcing‖ ≤
        ‖kernel‖ * ‖forcing‖ := by
    calc
      ‖fixedL2ScalarL2IntegralCLM
          requestedTime kernel forcing‖ ≤
          ‖(kernel • forcing :
            MeasureTheory.Lp ComplexCoordinateVector 1
              (commonTimeMeasure requestedTime))‖ := by
        change
          ‖(MeasureTheory.L1.integralCLM' ℂ)
              (kernel • forcing :
                MeasureTheory.Lp ComplexCoordinateVector 1
                  (commonTimeMeasure requestedTime))‖ ≤ _
        rw [← MeasureTheory.L1.integral_eq' ℂ]
        exact
          MeasureTheory.L1.norm_integral_le
            (kernel • forcing :
              MeasureTheory.Lp ComplexCoordinateVector 1
                (commonTimeMeasure requestedTime))
      _ ≤ ‖kernel‖ * ‖forcing‖ :=
        MeasureTheory.Lp.norm_smul_le kernel forcing
  have squared :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
        convolutionNormLe
  calc
    ‖fixedL2ScalarL2IntegralCLM
        requestedTime kernel forcing‖ ^ 2 ≤
        (‖kernel‖ * ‖forcing‖) ^ 2 := squared
    _ = ‖kernel‖ ^ 2 * ‖forcing‖ ^ 2 := by ring
    _ ≤ (2 * ν)⁻¹ * ‖forcing‖ ^ 2 := by
      exact
        mul_le_mul_of_nonneg_right
          (weightedCausalHeatKernelL2_norm_sq_le
            requestedTime ν νPos wave waveNe time)
          (sq_nonneg _)

/-- The actual negative-one forcing convolved at one wave and one time. -/
def weightedDuhamelAt
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexCoordinateVector :=
  fixedL2ScalarL2IntegralCLM requestedTime
    (weightedCausalHeatKernelL2
      requestedTime ν.coeff ν.coeff_pos wave waveNe time)
    (fixedWaveSpaceTimeRestriction requestedTime wave
      receipt.negativeOneForcing)

theorem weightedDuhamelAt_norm_sq_le
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖weightedDuhamelAt receipt wave waveNe time‖ ^ 2 ≤
      (2 * ν.coeff)⁻¹ *
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          receipt.negativeOneForcing‖ ^ 2 := by
  exact
    fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_le
      requestedTime ν.coeff ν.coeff_pos wave waveNe time
      (fixedWaveSpaceTimeRestriction requestedTime wave
        receipt.negativeOneForcing)

theorem weightedDuhamelAt_eq_actual_nonlinear_integral
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    weightedDuhamelAt receipt wave waveNe time =
      ∫ earlier in Iic time,
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier.1) wave •
          transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave earlier
        ∂(commonTimeMeasure requestedTime) := by
  let kernel :=
    weightedCausalHeatKernelL2
      requestedTime ν.coeff ν.coeff_pos wave waveNe time
  let forcingRow :=
    fixedWaveSpaceTimeRestriction requestedTime wave
      receipt.negativeOneForcing
  have kernelAE :
      ⇑kernel =ᵐ[commonTimeMeasure requestedTime]
        weightedCausalHeatKernelFunction
          requestedTime ν.coeff wave time := by
    dsimp [kernel, weightedCausalHeatKernelL2]
    exact MemLp.coeFn_toLp _
  have forcingRowAE :
      ∀ᵐ earlier ∂(commonTimeMeasure requestedTime),
        forcingRow earlier =
          (receipt.negativeOneForcing earlier) wave := by
    exact
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.negativeOneForcing
  have productAE :
      ⇑(kernel • forcingRow :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑kernel • ⇑forcingRow :=
    MeasureTheory.Lp.coeFn_lpSMul kernel forcingRow
  have nonlinearAE :=
    receipt.negativeOneForcing_unweighted_row_ae wave waveNe
  change
    (MeasureTheory.L1.integralCLM' ℂ)
        (kernel • forcingRow) = _
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  rw [← MeasureTheory.integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [productAE, kernelAE, forcingRowAE, nonlinearAE] with
    earlier productEq kernelEq forcingEq nonlinearEq
  rw [productEq]
  change
    kernel earlier • forcingRow earlier =
      (Iic time).indicator
        (fun actual =>
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - actual.1) wave •
            transverseSpaceTimeNonlinearRow
              receipt.transverseLimit wave actual)
        earlier
  rw [kernelEq, forcingEq]
  by_cases earlierLe : earlier ≤ time
  · simp only [weightedCausalHeatKernelFunction,
      Set.indicator_apply, Set.mem_Iic, earlierLe, if_true]
    have scalarActionEq :
        ((Real.sqrt (integerWaveViscousMultiplier wave) *
              finiteStateVorticityHeatMultiplier
                ν.coeff (time.1 - earlier.1) wave : ℝ) : ℂ) •
            (receipt.negativeOneForcing earlier) wave =
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier.1) wave •
            ((Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
              (receipt.negativeOneForcing earlier) wave) := by
      ext coordinate
      simp [Complex.real_smul]
      ring
    rw [scalarActionEq, nonlinearEq]
  · simp only [weightedCausalHeatKernelFunction,
      Set.indicator_apply, Set.mem_Iic, earlierLe, if_false]
    simp

theorem rowPath_eq_heat_add_weightedDuhamel
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    receipt.rowPath wave waveNe time =
      finiteStateVorticityHeatMultiplier
          ν.coeff time.1 wave • receipt.initialState wave +
        weightedDuhamelAt receipt wave waveNe time := by
  rw [receipt.mild_identity wave waveNe time]
  unfold fixedWaveHeatDuhamelValue
  rw [weightedDuhamelAt_eq_actual_nonlinear_integral
    receipt wave waveNe time]

/-! ## Whole orthogonal mild series -/

/--
The source receipt's complete mild coefficient table.  The zero row is
installed as zero; every nonzero row is the continuous representative
generated by the receipt.
-/
def mildCoefficient
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    ComplexCoordinateVector :=
  if waveNe : wave ≠ 0
  then receipt.rowPath wave waveNe time
  else 0

@[simp] theorem mildCoefficient_zero
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime) :
    mildCoefficient receipt time 0 = 0 := by
  simp [mildCoefficient]

theorem mildCoefficient_eq_rowPath
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    mildCoefficient receipt time wave =
      receipt.rowPath wave waveNe time := by
  simp only [mildCoefficient, dif_pos waveNe]

/--
One summable, time-independent squared majorant simultaneously records
initial amplitude, frequency growth, time occupancy, and viscosity.
-/
def mildCoefficientSqMajorant
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) : ℝ :=
  2 * ‖receipt.initialState wave‖ ^ 2 +
    2 * (2 * ν.coeff)⁻¹ *
      ‖fixedWaveSpaceTimeRestriction requestedTime wave
        receipt.negativeOneForcing‖ ^ 2

theorem mildCoefficientSqMajorant_nonneg
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    0 ≤ mildCoefficientSqMajorant receipt wave := by
  unfold mildCoefficientSqMajorant
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (sq_nonneg _)
  · exact
      mul_nonneg
        (mul_nonneg (by norm_num)
          (inv_nonneg.mpr
            (mul_nonneg (by norm_num) ν.coeff_pos.le)))
        (sq_nonneg _)

theorem mildCoefficient_norm_sq_le_majorant
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    ‖mildCoefficient receipt time wave‖ ^ 2 ≤
      mildCoefficientSqMajorant receipt wave := by
  by_cases waveNe : wave ≠ 0
  · rw [mildCoefficient_eq_rowPath receipt time wave waveNe,
      rowPath_eq_heat_add_weightedDuhamel receipt wave waveNe time]
    let heatRow :=
      finiteStateVorticityHeatMultiplier
        ν.coeff time.1 wave • receipt.initialState wave
    let duhamelRow :=
      weightedDuhamelAt receipt wave waveNe time
    have heatMultiplierLe :
        finiteStateVorticityHeatMultiplier
            ν.coeff time.1 wave ≤ 1 :=
      finiteStateVorticityHeatMultiplier_le_one
        ν.coeff_pos.le time.2.1 wave
    have heatRowNormLe :
        ‖heatRow‖ ≤ ‖receipt.initialState wave‖ := by
      dsimp [heatRow]
      rw [norm_smul, Real.norm_of_nonneg
        (finiteStateVorticityHeatMultiplier_nonneg
          ν.coeff time.1 wave)]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right heatMultiplierLe (norm_nonneg _)
    have rowNormLe :
        ‖heatRow + duhamelRow‖ ≤
          ‖receipt.initialState wave‖ + ‖duhamelRow‖ :=
      (norm_add_le heatRow duhamelRow).trans
        (add_le_add heatRowNormLe (le_refl _))
    have rowSqLe :
        ‖heatRow + duhamelRow‖ ^ 2 ≤
          (‖receipt.initialState wave‖ + ‖duhamelRow‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 rowNormLe
    have sumSqLe :
        (‖receipt.initialState wave‖ + ‖duhamelRow‖) ^ 2 ≤
          2 * ‖receipt.initialState wave‖ ^ 2 +
            2 * ‖duhamelRow‖ ^ 2 := by
      nlinarith [sq_nonneg
        (‖receipt.initialState wave‖ - ‖duhamelRow‖)]
    calc
      ‖heatRow + duhamelRow‖ ^ 2 ≤
          2 * ‖receipt.initialState wave‖ ^ 2 +
            2 * ‖duhamelRow‖ ^ 2 :=
        rowSqLe.trans sumSqLe
      _ ≤
          2 * ‖receipt.initialState wave‖ ^ 2 +
            2 * ((2 * ν.coeff)⁻¹ *
              ‖fixedWaveSpaceTimeRestriction requestedTime wave
                receipt.negativeOneForcing‖ ^ 2) := by
        gcongr
        exact weightedDuhamelAt_norm_sq_le
          receipt wave waveNe time
      _ = mildCoefficientSqMajorant receipt wave := by
        unfold mildCoefficientSqMajorant
        ring
  · simpa [mildCoefficient, waveNe] using
      mildCoefficientSqMajorant_nonneg receipt wave

theorem mildCoefficient_continuous
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    Continuous (fun time => mildCoefficient receipt time wave) := by
  by_cases waveNe : wave ≠ 0
  · simpa only [mildCoefficient, dif_pos waveNe] using
      (receipt.rowPath wave waveNe).continuous
  · have waveZero : wave = 0 := not_ne_iff.mp waveNe
    subst wave
    simp only [mildCoefficient_zero]
    exact continuous_const

/-- Canonical finite-frequency approximation of the complete mild table. -/
def finiteMildState
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes
    (mildCoefficient receipt time)

theorem finiteMildState_continuous
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (modes : Finset IntegerWavevector) :
    Continuous (finiteMildState receipt modes) := by
  unfold finiteMildState finiteComplexVorticityState
  apply continuous_finsetSum
  intro wave waveMem
  exact
    (lp.singleContinuousLinearMap
      ℂ (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp
        (mildCoefficient_continuous receipt wave)

theorem mildCoefficientSqMajorant_summable
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    Summable (mildCoefficientSqMajorant receipt) := by
  have initialSummable :
      Summable fun wave : IntegerWavevector =>
        ‖receipt.initialState wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (by norm_num) receipt.initialState.2
  have forcingSummable :
      Summable fun wave : IntegerWavevector =>
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          receipt.negativeOneForcing‖ ^ 2 :=
    summable_fixedWaveSpaceTimeRestriction_norm_sq
      requestedTime receipt.negativeOneForcing
  exact
    ((initialSummable.mul_left 2).add
      (forcingSummable.mul_left
        (2 * (2 * ν.coeff)⁻¹))).congr fun wave => by
          unfold mildCoefficientSqMajorant
          ring

theorem tsum_mildCoefficientSqMajorant
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    (∑' wave : IntegerWavevector,
        mildCoefficientSqMajorant receipt wave) =
      2 * ‖receipt.initialState‖ ^ 2 +
        2 * (2 * ν.coeff)⁻¹ *
          ‖receipt.negativeOneForcing‖ ^ 2 := by
  have initialSummable :
      Summable fun wave : IntegerWavevector =>
        ‖receipt.initialState wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (by norm_num) receipt.initialState.2
  have forcingSummable :
      Summable fun wave : IntegerWavevector =>
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          receipt.negativeOneForcing‖ ^ 2 :=
    summable_fixedWaveSpaceTimeRestriction_norm_sq
      requestedTime receipt.negativeOneForcing
  rw [show
    mildCoefficientSqMajorant receipt =
      fun wave =>
        2 * ‖receipt.initialState wave‖ ^ 2 +
          (2 * (2 * ν.coeff)⁻¹) *
            ‖fixedWaveSpaceTimeRestriction requestedTime wave
              receipt.negativeOneForcing‖ ^ 2 by
      funext wave
      unfold mildCoefficientSqMajorant
      ring]
  rw [(initialSummable.mul_left 2).tsum_add
    (forcingSummable.mul_left (2 * (2 * ν.coeff)⁻¹)),
    tsum_mul_left, tsum_mul_left]
  have initialTsum :
      (∑' wave : IntegerWavevector,
          ‖receipt.initialState wave‖ ^ 2) =
        ‖receipt.initialState‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num)
        receipt.initialState).symm
  rw [initialTsum,
    tsum_fixedWaveSpaceTimeRestriction_norm_sq
      requestedTime receipt.negativeOneForcing]

/-- The complete source-generated mild coefficient table installed in the
whole spatial Hilbert carrier at one time. -/
def wholeMildState
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexVorticityHilbertState :=
  ⟨mildCoefficient receipt time, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (mildCoefficientSqMajorant_summable receipt).of_nonneg_of_le
        (fun wave => sq_nonneg _)
        (fun wave =>
          mildCoefficient_norm_sq_le_majorant receipt time wave)⟩

@[simp] theorem wholeMildState_apply
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    wholeMildState receipt time wave =
      mildCoefficient receipt time wave :=
  rfl

theorem wholeMildState_norm_sq_le
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖wholeMildState receipt time‖ ^ 2 ≤
      2 * ‖receipt.initialState‖ ^ 2 +
        2 * (2 * ν.coeff)⁻¹ *
          ‖receipt.negativeOneForcing‖ ^ 2 := by
  rw [show
    ‖wholeMildState receipt time‖ ^ 2 =
      ∑' wave : IntegerWavevector,
        ‖mildCoefficient receipt time wave‖ ^ 2 by
      simpa using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (wholeMildState receipt time))]
  calc
    (∑' wave : IntegerWavevector,
        ‖mildCoefficient receipt time wave‖ ^ 2) ≤
        ∑' wave : IntegerWavevector,
          mildCoefficientSqMajorant receipt wave := by
      exact
        Summable.tsum_le_tsum
          (fun wave =>
            mildCoefficient_norm_sq_le_majorant receipt time wave)
          (by
            have stateSummable :
                Summable fun wave : IntegerWavevector =>
                  ‖wholeMildState receipt time wave‖ ^ 2 := by
              simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
                Memℓp.summable (by norm_num)
                  (wholeMildState receipt time).2
            exact stateSummable.congr fun wave => by
              rw [wholeMildState_apply])
          (mildCoefficientSqMajorant_summable receipt)
    _ =
        2 * ‖receipt.initialState‖ ^ 2 +
          2 * (2 * ν.coeff)⁻¹ *
            ‖receipt.negativeOneForcing‖ ^ 2 :=
      tsum_mildCoefficientSqMajorant receipt

theorem finiteMildState_eq_projection
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    finiteMildState receipt modes time =
      complexSharpSupportProjection modes
        (wholeMildState receipt time) := by
  apply lp.ext
  funext wave
  simp [finiteMildState, complexSharpSupportProjection_apply]

private theorem mildCoefficient_sub_norm_sq_le
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (firstTime secondTime : Icc (0 : ℝ) requestedTime)
    (wave : IntegerWavevector) :
    ‖mildCoefficient receipt firstTime wave -
        mildCoefficient receipt secondTime wave‖ ^ 2 ≤
      4 * mildCoefficientSqMajorant receipt wave := by
  have firstBound :=
    mildCoefficient_norm_sq_le_majorant
      receipt firstTime wave
  have secondBound :=
    mildCoefficient_norm_sq_le_majorant
      receipt secondTime wave
  have subBound :
      ‖mildCoefficient receipt firstTime wave -
          mildCoefficient receipt secondTime wave‖ ≤
        ‖mildCoefficient receipt firstTime wave‖ +
          ‖mildCoefficient receipt secondTime wave‖ :=
    norm_sub_le _ _
  have subSqBound :
      ‖mildCoefficient receipt firstTime wave -
          mildCoefficient receipt secondTime wave‖ ^ 2 ≤
        (‖mildCoefficient receipt firstTime wave‖ +
          ‖mildCoefficient receipt secondTime wave‖) ^ 2 :=
    (sq_le_sq₀
      (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 subBound
  have squareDifference :
      (‖mildCoefficient receipt firstTime wave‖ -
        ‖mildCoefficient receipt secondTime wave‖) ^ 2 ≥ 0 :=
    sq_nonneg _
  nlinarith

theorem wholeMildState_continuous
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    Continuous (wholeMildState receipt) := by
  rw [continuous_iff_continuousAt]
  intro time
  rw [ContinuousAt]
  apply tendsto_sub_nhds_zero_iff.1
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have squareTendsto :
      Tendsto
        (fun approachingTime : Icc (0 : ℝ) requestedTime =>
          ∑' wave : IntegerWavevector,
            ‖mildCoefficient receipt approachingTime wave -
                mildCoefficient receipt time wave‖ ^ 2)
        (𝓝 time)
        (𝓝 0) := by
    convert
      tendsto_tsum_of_dominated_convergence
        ((mildCoefficientSqMajorant_summable receipt).mul_left 4)
        (fun wave => by
          have coefficientDifferenceContinuous :
              ContinuousAt
                (fun approachingTime =>
                  ‖mildCoefficient receipt approachingTime wave -
                    mildCoefficient receipt time wave‖ ^ 2)
                time :=
            ((mildCoefficient_continuous receipt wave).continuousAt.sub
              tendsto_const_nhds).norm.pow 2
          simpa only [ContinuousAt, sub_self, norm_zero,
            ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
            coefficientDifferenceContinuous)
        (Filter.Eventually.of_forall fun approachingTime wave =>
          (by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (sq_nonneg
                ‖mildCoefficient receipt approachingTime wave -
                  mildCoefficient receipt time wave‖)]
            exact
              mildCoefficient_sub_norm_sq_le
                receipt approachingTime time wave))
      using 1 <;> simp
  have normSquareTendsto :
      Tendsto
        (fun approachingTime : Icc (0 : ℝ) requestedTime =>
          ‖wholeMildState receipt approachingTime -
              wholeMildState receipt time‖ ^ 2)
        (𝓝 time)
        (𝓝 0) := by
    convert squareTendsto using 1
    · funext approachingTime
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
        wholeMildState_apply, lp.coeFn_sub, Pi.sub_apply] using
        lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (wholeMildState receipt approachingTime -
            wholeMildState receipt time)
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    normSquareTendsto.sqrt

/--
The complete source-generated mild state as one actual bounded continuous
path in the whole spatial Hilbert carrier.
-/
def wholeMildPath
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState :=
  BoundedContinuousFunction.mkOfCompact
    ⟨wholeMildState receipt, wholeMildState_continuous receipt⟩

@[simp] theorem wholeMildPath_apply
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime) :
    wholeMildPath receipt time =
      wholeMildState receipt time :=
  rfl

/--
The new continuous path is exactly the pre-existing whole weak state in
the common time-`L²` carrier.  Thus the continuous assembly does not replace
the source state by a merely coordinatewise lookalike.
-/
theorem wholeMildPath_toLp_eq_stateLimit
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ
        (wholeMildPath receipt) =
      receipt.stateLimit := by
  have rowsRepresent :
      ∀ wave : IntegerWavevector,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          mildCoefficient receipt time wave =
            receipt.stateLimit time wave := by
    intro wave
    have restrictionAE :=
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.stateLimit
    by_cases waveNe : wave ≠ 0
    · filter_upwards [
        receipt.row_represents wave waveNe,
        restrictionAE] with time rowEq restrictionEq
      rw [mildCoefficient_eq_rowPath receipt time wave waveNe,
        rowEq, restrictionEq]
    · have waveZero : wave = 0 := not_ne_iff.mp waveNe
      subst wave
      have zeroRow :
          fixedWaveSpaceTimeRestriction
              requestedTime 0 receipt.stateLimit =
            0 :=
        InfiniteMildDuhamelForcingReceipt.stateLimit_zero_row receipt
      have zeroRowAE :
          ∀ᵐ time ∂(commonTimeMeasure requestedTime),
            fixedWaveSpaceTimeRestriction
                requestedTime 0 receipt.stateLimit time =
              0 := by
        rw [zeroRow]
        exact
          MeasureTheory.Lp.coeFn_zero
            ComplexCoordinateVector 2
            (commonTimeMeasure requestedTime)
      filter_upwards [restrictionAE, zeroRowAE] with
          time restrictionEq zeroEq
      rw [mildCoefficient_zero, ← restrictionEq, zeroEq]
  apply MeasureTheory.Lp.ext
  filter_upwards [
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ (wholeMildPath receipt),
    eventually_countable_forall.2 rowsRepresent] with
      time pathEq timeRows
  rw [pathEq]
  apply lp.ext
  funext wave
  exact timeRows wave

/--
Every nonzero coordinate of the whole path satisfies the actual heat /
negative-one-forcing Duhamel law generated on the inherited receipt.
-/
theorem wholeMildPath_mild_identity
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    wholeMildPath receipt time wave =
      finiteStateVorticityHeatMultiplier
          ν.coeff time.1 wave • receipt.initialState wave +
        weightedDuhamelAt receipt wave waveNe time := by
  rw [wholeMildPath_apply, wholeMildState_apply,
    mildCoefficient_eq_rowPath receipt time wave waveNe]
  exact rowPath_eq_heat_add_weightedDuhamel
    receipt wave waveNe time

/--
The assembled whole path starts at the same source-generated Hilbert state
that drives every row Duhamel law.
-/
theorem wholeMildPath_initial
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    wholeMildPath receipt
        ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ =
      receipt.initialState := by
  apply lp.ext
  funext wave
  by_cases waveNe : wave ≠ 0
  · rw [wholeMildPath_mild_identity
      receipt wave waveNe
      ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩]
    rw [weightedDuhamelAt_eq_actual_nonlinear_integral
      receipt wave waveNe
      ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩]
    have iicInitial :
        Iic
            (⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ :
              Icc (0 : ℝ) requestedTime) =
          {⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩} := by
      ext earlier
      simp only [Set.mem_Iic, Set.mem_singleton_iff]
      constructor
      · intro earlierLe
        apply Subtype.ext
        exact le_antisymm earlierLe earlier.property.1
      · intro earlierEq
        subst earlier
        exact le_rfl
    have singletonMeasureZero :
        commonTimeMeasure requestedTime
            {⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩} =
          0 := by
      change
        Measure.comap
            (Subtype.val :
              Icc (0 : ℝ) requestedTime → ℝ)
            (volume.restrict (Icc (0 : ℝ) requestedTime))
            {⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩} =
          0
      rw [comap_subtype_coe_apply measurableSet_Icc]
      simp
    have iicMeasureZero :
        commonTimeMeasure requestedTime
            (Iic
              (⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ :
                Icc (0 : ℝ) requestedTime)) =
          0 := by
      rw [iicInitial]
      exact singletonMeasureZero
    rw [MeasureTheory.setIntegral_measure_zero _ iicMeasureZero]
    simp [finiteStateVorticityHeatMultiplier]
  · have waveZero : wave = 0 := not_ne_iff.mp waveNe
    subst wave
    rw [wholeMildPath_apply, wholeMildState_apply,
      mildCoefficient_zero,
      InfiniteMildDuhamelForcingReceipt.initialState_zero_row receipt]

/-- Uniform whole-state bound supplied by the viscous heat kernel and the
actual source-generated negative-one forcing. -/
theorem wholeMildPath_norm_sq_le
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}
    (receipt :
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖wholeMildPath receipt time‖ ^ 2 ≤
      2 * ‖receipt.initialState‖ ^ 2 +
        2 * (2 * ν.coeff)⁻¹ *
          ‖receipt.negativeOneForcing‖ ^ 2 := by
  rw [wholeMildPath_apply]
  exact wholeMildState_norm_sq_le receipt time

/-! ## Source-owned whole continuous receipt -/

/--
One source-generated infinite mild state installed as an actual
`C([0,T]; ℓ²)` path.  The path is exactly the receipt's pre-existing weak
space-time state, starts at its generated initial state, obeys the actual
nonzero-row Duhamel laws, and carries the whole parabolic bound.
-/
structure WholeContinuousMildReceipt
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime)
    extends
      InfiniteMildDuhamelForcingReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos where
  wholePath :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState
  wholePath_toLp_eq_stateLimit :
    BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ wholePath =
      stateLimit
  wholePath_initial :
    wholePath
        ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ =
      initialState
  wholePath_mild_identity :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0)
      (time : Icc (0 : ℝ) requestedTime),
      wholePath time wave =
        finiteStateVorticityHeatMultiplier
            ν.coeff time.1 wave • initialState wave +
          weightedDuhamelAt
            toInfiniteMildDuhamelForcingReceipt
            wave waveNe time
  wholePath_norm_sq_le :
    ∀ time : Icc (0 : ℝ) requestedTime,
      ‖wholePath time‖ ^ 2 ≤
        2 * ‖initialState‖ ^ 2 +
          2 * (2 * ν.coeff)⁻¹ *
            ‖negativeOneForcing‖ ^ 2

/--
The original infinite source lineage generates the whole continuous mild
receipt.  No terminal frequency, finite cover, tail-silence witness,
continuation target, or preselected whole path appears in the mouth.
-/
noncomputable def
    GeneratedIntegerShellInfiniteLineage.generates_wholeContinuousMild
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (ν : Viscosity)
    (θ requestedTime : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ length : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2)
    (requestedTimePos : 0 < requestedTime) :
    WholeContinuousMildReceipt
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos := by
  let base :=
    GeneratedIntegerShellInfiniteLineage.generates_infiniteMildDuhamelForcing
      lineage ν θ requestedTime θLtOne criticalMargin
      requestedTimePos
  exact
    { toInfiniteMildDuhamelForcingReceipt := base
      wholePath := wholeMildPath base
      wholePath_toLp_eq_stateLimit :=
        wholeMildPath_toLp_eq_stateLimit base
      wholePath_initial :=
        wholeMildPath_initial base
      wholePath_mild_identity := by
        intro wave waveNe time
        exact
          wholeMildPath_mild_identity
            base wave waveNe time
      wholePath_norm_sq_le := by
        intro time
        exact wholeMildPath_norm_sq_le base time }

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
end NavierStokes
end SaturationMonoid
