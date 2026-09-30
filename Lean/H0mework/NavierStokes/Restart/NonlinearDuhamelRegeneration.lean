import H0mework.NavierStokes.Restart.PositiveOutputWorkDualBudget

/-!
# Nonlinear Duhamel regeneration on an actual whole restart

The homogeneous heat part of one unforced receipt is not a new source
responsibility.  What the nonlinear dynamics actually regenerates is the
same-event endpoint remainder

```text
whole endpoint - heat(initial endpoint).
```

This module identifies that remainder exactly with the weighted Duhamel
convolution of the receipt's generated nonlinear `H⁻¹` state.  The complete
finite-frequency Euclidean mass of that regeneration is then paid by the
same successor segment's whole dual-square ledger.  No cutoff, margin,
branch, target path, or forcing certificate enters the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration

open scoped BigOperators ENNReal Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget

noncomputable section

/-- The actual nonlinear negative-one row convolved with the causal heat
kernel on one whole mild receipt. -/
def receiptWeightedNonlinearDuhamelAt
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    ComplexCoordinateVector :=
  fixedL2ScalarL2IntegralCLM requestedTime
    (weightedCausalHeatKernelL2
      requestedTime ν.coeff ν.coeff_pos wave waveNonzero time)
    (fixedWaveSpaceTimeRestriction requestedTime wave
      (receiptNonlinearNegativeOneState receipt))

/-- The convolved generated nonlinear state is exactly the Duhamel row in
the same receipt's unforced mild identity. -/
theorem receiptWeightedNonlinearDuhamelAt_eq_actual_integral
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    receiptWeightedNonlinearDuhamelAt receipt wave waveNonzero time =
      ∫ earlier in Iic time,
        finiteStateVorticityHeatMultiplier
            ν.coeff (time.1 - earlier.1) wave •
          transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave earlier
        ∂(commonTimeMeasure requestedTime) := by
  let kernel :=
    weightedCausalHeatKernelL2
      requestedTime ν.coeff ν.coeff_pos wave waveNonzero time
  let forcingRow :=
    fixedWaveSpaceTimeRestriction requestedTime wave
      (receiptNonlinearNegativeOneState receipt)
  have kernelAE :
      ⇑kernel =ᵐ[commonTimeMeasure requestedTime]
        weightedCausalHeatKernelFunction
          requestedTime ν.coeff wave time := by
    dsimp [kernel, weightedCausalHeatKernelL2]
    exact MemLp.coeFn_toLp _
  have forcingRowAE :
      ∀ᵐ earlier ∂(commonTimeMeasure requestedTime),
        forcingRow earlier =
          (receiptNonlinearNegativeOneState receipt earlier) wave :=
    fixedWaveSpaceTimeRestriction_coeFn requestedTime wave
      (receiptNonlinearNegativeOneState receipt)
  have productAE :
      ⇑(kernel • forcingRow :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑kernel • ⇑forcingRow :=
    MeasureTheory.Lp.coeFn_lpSMul kernel forcingRow
  have nonlinearAE :
      ∀ᵐ earlier ∂(commonTimeMeasure requestedTime),
        (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
            (receiptNonlinearNegativeOneState receipt earlier) wave =
          transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave earlier := by
    filter_upwards [
      receiptNonlinearNegativeOneState_row_ae
        receipt wave waveNonzero,
      transverseSpaceTimeNonlinearRow_coeFn
        receipt.transverseLimit wave] with
        earlier nonlinearEq rowEq
    calc
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
          (receiptNonlinearNegativeOneState receipt earlier) wave =
          wholeStateVorticityBilinearCoefficientAt
            (receipt.transverseLimit earlier).1
            (receipt.transverseLimit earlier).1 wave := nonlinearEq
      _ = wholeStateVorticityNonlinearCoefficientAt
            (receipt.transverseLimit earlier).1 wave :=
        wholeStateVorticityBilinearCoefficientAt_self _ _
      _ = transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave earlier := by
        simpa [transverseSpaceTimeNonlinearRowFunction] using rowEq.symm
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
            (receiptNonlinearNegativeOneState receipt earlier) wave =
          finiteStateVorticityHeatMultiplier
              ν.coeff (time.1 - earlier.1) wave •
            ((Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
              (receiptNonlinearNegativeOneState receipt earlier) wave) := by
      ext coordinate
      simp [Complex.real_smul]
      ring
    rw [scalarActionEq, nonlinearEq]
  · simp only [weightedCausalHeatKernelFunction,
      Set.indicator_apply, Set.mem_Iic, earlierLe, if_false]
    simp

/-- Exact consume-before-quotient identity: the endpoint remainder after
removing homogeneous heat propagation is the same receipt's nonlinear
Duhamel write-back. -/
theorem wholeContinuousMildSerrinReceipt_row_sub_heat_eq
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    receipt.wholePath time wave -
        finiteStateVorticityHeatMultiplier
          ν.coeff time.1 wave • initialState wave =
      receiptWeightedNonlinearDuhamelAt
        receipt wave waveNonzero time := by
  rw [receipt.row_mild_identity wave waveNonzero time]
  unfold fixedWaveHeatDuhamelValue
  rw [receiptWeightedNonlinearDuhamelAt_eq_actual_integral
    receipt wave waveNonzero time]
  abel

/-- The same-event nonlinear regeneration row has the frequency-independent
parabolic `H⁻¹ → L²` bound. -/
theorem wholeContinuousMildSerrinReceipt_row_sub_heat_norm_sq_le
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    ‖receipt.wholePath time wave -
        finiteStateVorticityHeatMultiplier
          ν.coeff time.1 wave • initialState wave‖ ^ 2 ≤
      (2 * ν.coeff)⁻¹ *
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          (receiptNonlinearNegativeOneState receipt)‖ ^ 2 := by
  rw [wholeContinuousMildSerrinReceipt_row_sub_heat_eq
    receipt wave waveNonzero time]
  exact
    fixedL2ScalarL2IntegralCLM_weightedCausalHeatKernel_norm_sq_le
      requestedTime ν.coeff ν.coeff_pos wave waveNonzero time
      (fixedWaveSpaceTimeRestriction requestedTime wave
        (receiptNonlinearNegativeOneState receipt))

/-- Every finite zero-free observation of one actual receipt's nonlinear
regeneration is paid by its complete generated nonlinear `H⁻¹` state. -/
theorem wholeContinuousMildSerrinReceipt_finiteNonlinearRegenerationMass_le
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ wave ∈ modes, wave ≠ 0)
    (time : Icc (0 : ℝ) requestedTime) :
    2 *
        (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            (receipt.wholePath time wave -
              finiteStateVorticityHeatMultiplier
                ν.coeff time.1 wave • initialState wave)) ≤
      (3 / ν.coeff) *
        ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 := by
  let forcing := receiptNonlinearNegativeOneState receipt
  let rowSquare : IntegerWavevector → ℝ := fun wave =>
    ‖fixedWaveSpaceTimeRestriction requestedTime wave forcing‖ ^ 2
  have rowSquareSummable : Summable rowSquare := by
    simpa [rowSquare, forcing] using
      summable_fixedWaveSpaceTimeRestriction_norm_sq
        requestedTime forcing
  have finiteRowsLe :
      (∑ wave ∈ modes, rowSquare wave) ≤ ∑' wave, rowSquare wave :=
    rowSquareSummable.sum_le_tsum modes
      (fun wave waveMem => sq_nonneg _)
  have perWave :
      ∀ wave ∈ modes,
        2 * complexCoordinateAmplitudeSq
            (receipt.wholePath time wave -
              finiteStateVorticityHeatMultiplier
                ν.coeff time.1 wave • initialState wave) ≤
          (3 / ν.coeff) * rowSquare wave := by
    intro wave waveMem
    have amplitudeLe :=
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity.complexCoordinateAmplitudeSq_le_three_mul_norm_sq
        (receipt.wholePath time wave -
          finiteStateVorticityHeatMultiplier
            ν.coeff time.1 wave • initialState wave)
    have rowNormLe :=
      wholeContinuousMildSerrinReceipt_row_sub_heat_norm_sq_le
        receipt wave (modesNonzero wave waveMem) time
    have viscosityPos := ν.coeff_pos
    dsimp only [rowSquare, forcing]
    calc
      2 * complexCoordinateAmplitudeSq
          (receipt.wholePath time wave -
            finiteStateVorticityHeatMultiplier
              ν.coeff time.1 wave • initialState wave) ≤
          2 * (3 *
            ‖receipt.wholePath time wave -
              finiteStateVorticityHeatMultiplier
                ν.coeff time.1 wave • initialState wave‖ ^ 2) :=
        mul_le_mul_of_nonneg_left amplitudeLe (by norm_num)
      _ ≤ 2 * (3 *
          ((2 * ν.coeff)⁻¹ *
            ‖fixedWaveSpaceTimeRestriction requestedTime wave
              (receiptNonlinearNegativeOneState receipt)‖ ^ 2)) := by
        gcongr
      _ = (3 / ν.coeff) *
          ‖fixedWaveSpaceTimeRestriction requestedTime wave
            (receiptNonlinearNegativeOneState receipt)‖ ^ 2 := by
        field_simp [ne_of_gt viscosityPos]
  calc
    2 *
        (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            (receipt.wholePath time wave -
              finiteStateVorticityHeatMultiplier
                ν.coeff time.1 wave • initialState wave)) =
        ∑ wave ∈ modes,
          2 * complexCoordinateAmplitudeSq
            (receipt.wholePath time wave -
              finiteStateVorticityHeatMultiplier
                ν.coeff time.1 wave • initialState wave) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ wave ∈ modes, (3 / ν.coeff) * rowSquare wave := by
      apply Finset.sum_le_sum
      intro wave waveMem
      exact perWave wave waveMem
    _ = (3 / ν.coeff) * ∑ wave ∈ modes, rowSquare wave := by
      rw [Finset.mul_sum]
    _ ≤ (3 / ν.coeff) * ∑' wave, rowSquare wave :=
      mul_le_mul_of_nonneg_left finiteRowsLe
        (div_nonneg (by norm_num) ν.coeff_pos.le)
    _ = (3 / ν.coeff) * ‖forcing‖ ^ 2 := by
      rw [show (∑' wave, rowSquare wave) = ‖forcing‖ ^ 2 by
        simpa [rowSquare] using
          tsum_fixedWaveSpaceTimeRestriction_norm_sq
            requestedTime forcing]
    _ = (3 / ν.coeff) *
        ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 := rfl

/-- The actual successor's regenerated finite-frequency mass is charged
exactly once to that successor segment's generated dual-square payment.
The contact time and both physical endpoints are source-owned conclusions. -/
theorem wholeRestartNextFiniteNonlinearRegenerationMass_le_segmentDualSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ wave ∈ modes, wave ≠ 0) :
    2 *
        (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            ((run initial index).nextContact.physicalState wave -
              finiteStateVorticityHeatMultiplier
                  ν.coeff
                  (run initial index).nextContact.time.1 wave •
                (run initial index).contact.physicalState wave)) ≤
      wholeRestartSegmentDualSquarePayment initial (index + 1) := by
  let current := run initial index
  let receipt := current.nextContact.prefixReceipt
  let terminal : Icc (0 : ℝ) current.nextContact.time.1 :=
    ⟨current.nextContact.time.1,
      ⟨current.nextContact.time_pos.le, le_rfl⟩⟩
  have finiteRegeneration :=
    wholeContinuousMildSerrinReceipt_finiteNonlinearRegenerationMass_le
      receipt modes modesNonzero terminal
  have endpointEq : receipt.wholePath terminal =
      current.nextContact.physicalState := by
    exact current.nextContact.prefixReceipt_terminal
  have nonlinearPaymentLe :
      (3 / ν.coeff) *
          ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 ≤
        (3 / ν.coeff) *
          (‖receiptViscousNegativeOneState receipt‖ ^ 2 +
            ‖receiptNonlinearNegativeOneState receipt‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (sq_nonneg _))
      (div_nonneg (by norm_num) ν.coeff_pos.le)
  calc
    2 *
        (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            ((run initial index).nextContact.physicalState wave -
              finiteStateVorticityHeatMultiplier
                  ν.coeff
                  (run initial index).nextContact.time.1 wave •
                (run initial index).contact.physicalState wave)) =
        2 *
          (∑ wave ∈ modes,
            complexCoordinateAmplitudeSq
              (receipt.wholePath terminal wave -
                finiteStateVorticityHeatMultiplier
                    ν.coeff terminal.1 wave •
                  current.contact.physicalState wave)) := by
      simp only [current, receipt, terminal] at endpointEq ⊢
      rw [endpointEq]
    _ ≤ (3 / ν.coeff) *
        ‖receiptNonlinearNegativeOneState receipt‖ ^ 2 :=
      finiteRegeneration
    _ ≤ (3 / ν.coeff) *
        (‖receiptViscousNegativeOneState receipt‖ ^ 2 +
          ‖receiptNonlinearNegativeOneState receipt‖ ^ 2) :=
      nonlinearPaymentLe
    _ = wholeRestartSegmentDualSquarePayment initial (index + 1) := by
      simp only [wholeRestartSegmentDualSquarePayment, run_succ,
        GeneratedWholeRestartCurrent.next, current, receipt]
      rfl

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
end NavierStokes
end SaturationMonoid
