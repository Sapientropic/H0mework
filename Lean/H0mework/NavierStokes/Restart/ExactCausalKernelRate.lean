import H0mework.NavierStokes.Restart.NonlinearRegenerationRateObstruction

/-!
# Exact causal-kernel payment of nonlinear regeneration rate

The frequency-independent parabolic estimate is too coarse for the
finite-time cascade: it forgets the source-generated contact duration.  This
module keeps the exact causal heat-kernel square

```text
(2ν)⁻¹ (1 - exp (-2ν λₖ t)).
```

After division by the same actual duration, this factor is at most `λₖ`.
Consequently every whole nonlinear regeneration rate is paid by the
frequency-weighted nonlinear `H⁻¹` rows of the same receipt.  Combining this
with the generated quadratic-rate obstruction yields a PDE exhaustion:

```text
finite physical-time accumulation
→ some actual segment has spatially nonsummable weighted nonlinear rows
  or the segmentwise weighted nonlinear square payments are nonsummable.
```

No cutoff, output family, time partition, margin, branch, forcing
certificate, or continuation witness is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartExactCausalKernelRate

open scoped BigOperators ENNReal Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationRateObstruction

noncomputable section

/-! ## Exact causal heat-kernel square -/

private theorem causalExpIntervalIntegral
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
  ring_nf

/-- Exact square integral of the weighted causal kernel. -/
theorem weightedCausalHeatKernelFunction_integral_norm_sq_exact
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    (∫ earlier,
        ‖weightedCausalHeatKernelFunction
          requestedTime ν wave time earlier‖ ^ 2
        ∂(commonTimeMeasure requestedTime)) =
      (2 * ν)⁻¹ *
        (1 - Real.exp
          (-(2 * ν * integerWaveViscousMultiplier wave) * time.1)) := by
  have requestedTimeNonneg : 0 ≤ requestedTime :=
    time.2.1.trans time.2.2
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact mul_pos
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
      (integerWaveNormSq_pos waveNonzero)
  let a : ℝ := 2 * ν * integerWaveViscousMultiplier wave
  have aPos : 0 < a := by
    dsimp [a]
    positivity
  rw [weightedCausalHeatKernelFunction_integral_norm_sq
    requestedTime ν requestedTimeNonneg wave time]
  rw [intervalIntegral.integral_const_mul]
  rw [causalExpIntervalIntegral a time.1 aPos.ne']
  dsimp [a]
  field_simp [νPos.ne', multiplierPos.ne']

/-- Exact Hilbert norm of the installed weighted causal kernel. -/
theorem weightedCausalHeatKernelL2_norm_sq_exact
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖weightedCausalHeatKernelL2
        requestedTime ν νPos wave waveNonzero time‖ ^ 2 =
      (2 * ν)⁻¹ *
        (1 - Real.exp
          (-(2 * ν * integerWaveViscousMultiplier wave) * time.1)) := by
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
          simpa only [one_div] using powerIdentity
    _ = _ := by
      rw [weightedCausalHeatKernelFunction_integral_norm_sq_exact
        requestedTime ν νPos wave waveNonzero time]
      field_simp [νPos.ne']

/-- Exact frequency--time form of the weighted `H⁻¹ → L²` Duhamel
estimate. -/
theorem fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_le_exact
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime)
    (forcing : FixedWaveSpaceTimeState requestedTime) :
    ‖fixedL2ScalarL2IntegralCLM requestedTime
        (weightedCausalHeatKernelL2
          requestedTime ν νPos wave waveNonzero time)
        forcing‖ ^ 2 ≤
      ((2 * ν)⁻¹ *
        (1 - Real.exp
          (-(2 * ν * integerWaveViscousMultiplier wave) * time.1))) *
        ‖forcing‖ ^ 2 := by
  let kernel :=
    weightedCausalHeatKernelL2
      requestedTime ν νPos wave waveNonzero time
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
    _ =
        ((2 * ν)⁻¹ *
          (1 - Real.exp
            (-(2 * ν * integerWaveViscousMultiplier wave) * time.1))) *
          ‖forcing‖ ^ 2 := by
      rw [show ‖kernel‖ ^ 2 =
          (2 * ν)⁻¹ *
            (1 - Real.exp
              (-(2 * ν * integerWaveViscousMultiplier wave) * time.1)) by
        exact weightedCausalHeatKernelL2_norm_sq_exact
          requestedTime ν νPos wave waveNonzero time]

/-- Dividing the exact causal-kernel square by its actual positive duration
costs at most one viscous frequency multiplier. -/
theorem weightedCausalHeatKernelRateFactor_le_multiplier
    (ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (time : ℝ)
    (timePos : 0 < time) :
    ((2 * ν)⁻¹ *
        (1 - Real.exp
          (-(2 * ν * integerWaveViscousMultiplier wave) * time))) /
        time ≤
      integerWaveViscousMultiplier wave := by
  let a : ℝ := 2 * ν * integerWaveViscousMultiplier wave
  have oneSubLe :
      1 - Real.exp (-a * time) ≤ a * time := by
    linarith [Real.add_one_le_exp (-a * time)]
  rw [div_le_iff₀ timePos]
  calc
    (2 * ν)⁻¹ *
        (1 - Real.exp
          (-(2 * ν * integerWaveViscousMultiplier wave) * time)) ≤
      (2 * ν)⁻¹ * (a * time) := by
        exact mul_le_mul_of_nonneg_left oneSubLe
          (inv_nonneg.mpr (mul_nonneg (by norm_num) νPos.le))
    _ = integerWaveViscousMultiplier wave * time := by
      dsimp [a]
      field_simp [νPos.ne']

/-- Duration-normalized Duhamel output at one frequency is paid by the
frequency-weighted square of the same forcing row. -/
theorem fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_div_time_le
    (requestedTime ν : ℝ)
    (νPos : 0 < ν)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime)
    (timePos : 0 < time.1)
    (forcing : FixedWaveSpaceTimeState requestedTime) :
    ‖fixedL2ScalarL2IntegralCLM requestedTime
        (weightedCausalHeatKernelL2
          requestedTime ν νPos wave waveNonzero time)
        forcing‖ ^ 2 / time.1 ≤
      integerWaveViscousMultiplier wave * ‖forcing‖ ^ 2 := by
  let factor :=
    (2 * ν)⁻¹ *
      (1 - Real.exp
        (-(2 * ν * integerWaveViscousMultiplier wave) * time.1))
  have convolutionLe :=
    fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_le_exact
      requestedTime ν νPos wave waveNonzero time forcing
  have factorRateLe :=
    weightedCausalHeatKernelRateFactor_le_multiplier
      ν νPos wave time.1 timePos
  calc
    ‖fixedL2ScalarL2IntegralCLM requestedTime
        (weightedCausalHeatKernelL2
          requestedTime ν νPos wave waveNonzero time)
        forcing‖ ^ 2 / time.1 ≤
        (factor * ‖forcing‖ ^ 2) / time.1 := by
      exact div_le_div_of_nonneg_right convolutionLe timePos.le
    _ = (factor / time.1) * ‖forcing‖ ^ 2 := by ring
    _ ≤ integerWaveViscousMultiplier wave * ‖forcing‖ ^ 2 :=
      mul_le_mul_of_nonneg_right factorRateLe (sq_nonneg _)

/-! ## Same-receipt and same-restart specialization -/

/-- The exact endpoint remainder of one whole receipt, normalized by its
actual positive time, is paid by the same nonlinear forcing row with one
frequency multiplier restored. -/
theorem wholeContinuousMildSerrinReceipt_row_sub_heat_norm_sq_div_time_le
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime)
    (timePos : 0 < time.1) :
    ‖receipt.wholePath time wave -
        finiteStateVorticityHeatMultiplier
          ν.coeff time.1 wave • initialState wave‖ ^ 2 / time.1 ≤
      integerWaveViscousMultiplier wave *
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          (receiptNonlinearNegativeOneState receipt)‖ ^ 2 := by
  rw [wholeContinuousMildSerrinReceipt_row_sub_heat_eq
    receipt wave waveNonzero time]
  unfold receiptWeightedNonlinearDuhamelAt
  exact
    fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_div_time_le
      requestedTime ν.coeff ν.coeff_pos wave waveNonzero time timePos
      (fixedWaveSpaceTimeRestriction requestedTime wave
        (receiptNonlinearNegativeOneState receipt))

/-- Same-event specialization to the actual source-generated restart edge. -/
theorem wholeRestartNonlinearRegenerationState_row_rate_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ‖wholeRestartNonlinearRegenerationState initial index wave‖ ^ 2 /
        (run initial index).nextContact.time.1 ≤
      integerWaveViscousMultiplier wave *
        ‖fixedWaveSpaceTimeRestriction
          (run initial index).nextContact.time.1 wave
          (receiptNonlinearNegativeOneState
            (run initial index).nextContact.prefixReceipt)‖ ^ 2 := by
  let contact := (run initial index).nextContact
  let terminal : Icc (0 : ℝ) contact.time.1 :=
    ⟨contact.time.1, ⟨contact.time_pos.le, le_rfl⟩⟩
  rw [wholeRestartNonlinearRegenerationState_apply_eq_actualDuhamel]
  unfold receiptWeightedNonlinearDuhamelAt
  exact
    fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_div_time_le
      contact.time.1 ν.coeff ν.coeff_pos wave waveNonzero
      terminal contact.time_pos
      (fixedWaveSpaceTimeRestriction contact.time.1 wave
        (receiptNonlinearNegativeOneState contact.prefixReceipt))

/-! ## Whole segment payment and finite-time exhaustion -/

/-- One frequency row of the actual segment's nonlinear square payment,
before any output aggregation or spatial summation. -/
def wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector) : ℝ :=
  integerWaveViscousMultiplier wave *
    ‖fixedWaveSpaceTimeRestriction
      (run initial index).nextContact.time.1 wave
      (receiptNonlinearNegativeOneState
        (run initial index).nextContact.prefixReceipt)‖ ^ 2

theorem wholeRestartSegmentFrequencyWeightedNonlinearSquareRow_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    0 ≤ wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
      initial index wave := by
  exact mul_nonneg
    (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
    (sq_nonneg _)

/-- Complete frequency-weighted nonlinear square payment on one actual
restart segment.  Its summability is not built into the definition. -/
def wholeRestartSegmentFrequencyWeightedNonlinearSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  ∑' wave : IntegerWavevector,
    wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
      initial index wave

theorem wholeRestartSegmentFrequencyWeightedNonlinearSquarePayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 ≤ wholeRestartSegmentFrequencyWeightedNonlinearSquarePayment
      initial index := by
  exact tsum_nonneg fun wave =>
    wholeRestartSegmentFrequencyWeightedNonlinearSquareRow_nonneg
      initial index wave

/-- If the same segment's weighted nonlinear rows are spatially summable,
their complete payment bounds the actual whole regeneration rate. -/
theorem wholeRestartNonlinearRegenerationRateSquare_le_segmentPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (rowSummable :
      Summable
        (wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
          initial index)) :
    wholeRestartNonlinearRegenerationRateSquare initial index ≤
      wholeRestartSegmentFrequencyWeightedNonlinearSquarePayment
        initial index := by
  let regeneration :=
    wholeRestartNonlinearRegenerationState initial index
  let duration := (run initial index).nextContact.time.1
  have regenerationRowSummable :
      Summable fun wave : IntegerWavevector =>
        ‖regeneration wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (by norm_num) regeneration.2
  have normalizedRegenerationRowSummable :
      Summable fun wave : IntegerWavevector =>
        ‖regeneration wave‖ ^ 2 / duration :=
    regenerationRowSummable.div_const duration
  have perWave :
      ∀ wave : IntegerWavevector,
        ‖regeneration wave‖ ^ 2 / duration ≤
          wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
            initial index wave := by
    intro wave
    by_cases waveNonzero : wave ≠ 0
    · exact wholeRestartNonlinearRegenerationState_row_rate_le
        initial index wave waveNonzero
    · have waveZero : wave = 0 := not_ne_iff.mp waveNonzero
      subst wave
      calc
        ‖regeneration 0‖ ^ 2 / duration = 0 := by
          simp [regeneration]
        _ ≤ wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
            initial index 0 :=
          wholeRestartSegmentFrequencyWeightedNonlinearSquareRow_nonneg
            initial index 0
  rw [wholeRestartNonlinearRegenerationRateSquare,
    wholeRestartNonlinearRegenerationNorm]
  rw [show
    ‖wholeRestartNonlinearRegenerationState initial index‖ ^ 2 =
      ∑' wave : IntegerWavevector,
        ‖regeneration wave‖ ^ 2 by
      simpa [regeneration] using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num) regeneration)]
  rw [← tsum_div_const]
  exact Summable.tsum_le_tsum perWave
    normalizedRegenerationRowSummable rowSummable

/-- Finite physical-time accumulation forces failure of the actual
frequency-weighted nonlinear square budget: either one segment already has
spatially nonsummable rows, or the complete segment payments are
nonsummable along the same restart run. -/
theorem elapsedTime_bddAbove_forces_frequencyWeightedNonlinearSquare_obstruction
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded :
      BddAbove (Set.range (elapsedTime initial))) :
    (∃ index : ℕ,
      ¬ Summable
        (wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
          initial index)) ∨
      ¬ Summable
        (wholeRestartSegmentFrequencyWeightedNonlinearSquarePayment
          initial) := by
  by_contra bothFinite
  push Not at bothFinite
  have rateSummable :
      Summable
        (wholeRestartNonlinearRegenerationRateSquare initial) :=
    bothFinite.2.of_nonneg_of_le
      (wholeRestartNonlinearRegenerationRateSquare_nonneg initial)
      (fun index =>
        wholeRestartNonlinearRegenerationRateSquare_le_segmentPayment
          initial index (bothFinite.1 index))
  exact
    (elapsedTime_bddAbove_forces_nonlinearRegenerationRateSquare_not_summable
      initial elapsedBounded) rateSummable

/-- Premise-free physical exhaustion of the actual whole restart recursion. -/
theorem elapsedTime_unbounded_or_frequencyWeightedNonlinearSquare_obstruction
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ¬ BddAbove (Set.range (elapsedTime initial)) ∨
      (∃ index : ℕ,
        ¬ Summable
          (wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
            initial index)) ∨
        ¬ Summable
          (wholeRestartSegmentFrequencyWeightedNonlinearSquarePayment
            initial) := by
  by_cases elapsedBounded :
      BddAbove (Set.range (elapsedTime initial))
  · exact Or.inr
      (elapsedTime_bddAbove_forces_frequencyWeightedNonlinearSquare_obstruction
        initial elapsedBounded)
  · exact Or.inl elapsedBounded

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartExactCausalKernelRate
end NavierStokes
end SaturationMonoid
