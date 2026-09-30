import H0mework.NavierStokes.Crossing.TangentQuantumPayment

/-!
# Finite negative-one displacement on an actual restart receipt

Every nonzero Fourier row of one generated restart receipt is integrated
against the same whole `L²_t H⁻¹_x` tangent.  Before coefficient projection,
time Cauchy--Schwarz and whole-carrier Parseval therefore control any finite
zero-free family without a mode-count or cutoff factor:

```text
Σₖ |λₖ⁻¹ᐟ² (ωₖ(t) - ωₖ(0))|²
  ≤ 3 t ‖wholeTangent‖².
```

The factor three is only the fixed comparison between the physical
three-coordinate Euclidean square and the ambient coefficient-row norm.
The finite family and time are observations of the same actual prefix
receipt; no modulus, margin, continuation certificate, or target path is
accepted.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteNegativeOneDisplacement

open scoped BigOperators ENNReal Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentQuantumPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade

noncomputable section

private theorem wholeRestartCrossingRow_sub_initial_eq_intervalIntegral
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    (run initial index).nextContact.prefixReceipt.wholePath time wave -
        (run initial index).contact.physicalState wave =
      ∫ earlier in (0 : ℝ)..time.1,
        wholeRestartCrossingContinuousUnforcedTangentRowAt
          initial index ⟨wave, waveNonzero⟩ earlier := by
  let current := run initial index
  let receipt := current.nextContact.prefixReceipt
  let path := actualWholeContinuousHeatDuhamelPath receipt wave
  let tangent :=
    wholeRestartCrossingContinuousUnforcedTangentRowAt
      initial index ⟨wave, waveNonzero⟩
  have nonlinearContinuous :
      Continuous (actualWholeContinuousNonlinearRow receipt wave) :=
    actualWholeContinuousNonlinearRow_continuous receipt wave
  have pathAC :
      AbsolutelyContinuousOnInterval path 0 current.nextContact.time.1 :=
    heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
      (current.contact.physicalState wave)
      (ν.coeff * integerWaveViscousMultiplier wave)
      0
      (nonlinearContinuous.intervalIntegrable
        0 current.nextContact.time.1)
      (by simp [current.nextContact.time_pos.le])
  have tangentContinuous : Continuous tangent :=
    wholeRestartCrossingContinuousUnforcedTangentRowAt_continuous
      initial index ⟨wave, waveNonzero⟩
  have pathDerivative :
      ∀ᵐ actual : ℝ,
        actual ∈ uIcc (0 : ℝ) current.nextContact.time.1 →
          HasDerivAt path (tangent actual) actual := by
    apply Filter.Eventually.of_forall
    intro actual actualMem
    have actualMem' : actual ∈ Icc (0 : ℝ) current.nextContact.time.1 := by
      simpa [uIcc_of_le current.nextContact.time_pos.le] using actualMem
    have pathEq :
        path actual = actualWholeContinuousStateRow receipt wave actual := by
      have wholePathEq :=
        wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
          receipt wave waveNonzero ⟨actual, actualMem'⟩
      have stateEq :
          actualWholeContinuousStateRow receipt wave actual =
            receipt.wholePath ⟨actual, actualMem'⟩ wave := by
        unfold actualWholeContinuousStateRow
          actualWholeProjectedTransversePath
        simp only
        rw [projIcc_of_mem receipt.requestedTimePos.le actualMem']
      exact wholePathEq.symm.trans stateEq.symm
    have generated :=
      heatDuhamelComplexCoordinatePath_hasDerivAt_of_continuous
        (current.contact.physicalState wave)
        (actualWholeContinuousNonlinearRow receipt wave)
        (ν.coeff * integerWaveViscousMultiplier wave)
        0 actual nonlinearContinuous
    have generated' :
        HasDerivAt path
          (actualWholeContinuousNonlinearRow receipt wave actual -
            (ν.coeff * integerWaveViscousMultiplier wave) • path actual)
          actual := by
      simpa [path, actualWholeContinuousHeatDuhamelPath] using generated
    rw [pathEq] at generated'
    change
      HasDerivAt
        (actualWholeContinuousHeatDuhamelPath receipt wave)
        (wholeRestartCrossingContinuousUnforcedTangentRowAt
          initial index ⟨wave, waveNonzero⟩ actual)
        actual
    simpa [path, tangent,
      wholeRestartCrossingContinuousUnforcedTangentRowAt] using generated'
  have update :=
    path_sub_eq_intervalIntegral
      pathAC
      (tangentContinuous.intervalIntegrable
        0 current.nextContact.time.1)
      pathDerivative time.1
      (by
        rw [uIcc_of_le current.nextContact.time_pos.le]
        exact time.property)
  have pathZero : path 0 = current.contact.physicalState wave := by
    simp [path, actualWholeContinuousHeatDuhamelPath,
      heatDuhamelComplexCoordinatePath,
      intervalIntegralComplexCoordinatePath]
  have pathAtTime :
      path time.1 = receipt.wholePath time wave := by
    exact
      (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
        receipt wave waveNonzero time).symm
  simpa [current, receipt, path, tangent, pathZero, pathAtTime] using update

private theorem wholeRestartCrossingNegativeOneRowDisplacement_normSq_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ‖((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
        ((run initial index).nextContact.prefixReceipt.wholePath time wave -
          (run initial index).contact.physicalState wave)‖ ^ 2 ≤
      time.1 *
        ‖fixedWaveSpaceTimeRestriction
          (run initial index).nextContact.time.1 wave
          (run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  let current := run initial index
  let receipt := current.nextContact.prefixReceipt
  let weightedTangent : ℝ → ComplexCoordinateVector := fun actual =>
    ((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
      wholeRestartCrossingContinuousUnforcedTangentRowAt
        initial index ⟨wave, waveNonzero⟩ actual
  let tangentRow :=
    fixedWaveSpaceTimeRestriction
      current.nextContact.time.1 wave receipt.wholeTangent
  have endpointUpdate :=
    wholeRestartCrossingRow_sub_initial_eq_intervalIntegral
      initial index wave waveNonzero time
  have endpointWeighted :
      ((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
          (receipt.wholePath time wave -
            current.contact.physicalState wave) =
        ∫ earlier in (0 : ℝ)..time.1, weightedTangent earlier := by
    rw [endpointUpdate]
    exact (intervalIntegral.integral_smul
      ((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)⁻¹)
      (fun earlier =>
        wholeRestartCrossingContinuousUnforcedTangentRowAt
          initial index ⟨wave, waveNonzero⟩ earlier)).symm
  have converted :=
    commonTime_integral_Iic_eq_intervalIntegral
      current.nextContact.time.1 current.nextContact.time_pos.le time
      weightedTangent
  have tangentRestrictionAE :=
    fixedWaveSpaceTimeRestriction_coeFn
      current.nextContact.time.1 wave receipt.wholeTangent
  have weightedTangentAE :=
    wholeRestartCrossingContinuousWeightedTangentRowAt_ae_eq
      initial index ⟨wave, waveNonzero⟩
  have rowAE :
      ∀ᵐ actual ∂(commonTimeMeasure current.nextContact.time.1),
        tangentRow actual = weightedTangent actual.1 := by
    filter_upwards [tangentRestrictionAE, weightedTangentAE] with
      actual restrictionEq weightedEq
    exact restrictionEq.trans weightedEq.symm
  have setIntegralEq :
      (∫ actual in Iic time, tangentRow actual
          ∂(commonTimeMeasure current.nextContact.time.1)) =
        ∫ actual in Iic time, weightedTangent actual.1
          ∂(commonTimeMeasure current.nextContact.time.1) := by
    apply integral_congr_ae
    exact ae_restrict_le rowAE
  have endpointAsSetIntegral :
      ((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
          (receipt.wholePath time wave -
            current.contact.physicalState wave) =
        ∫ actual in Iic time, tangentRow actual
          ∂(commonTimeMeasure current.nextContact.time.1) := by
    rw [endpointWeighted, ← converted, ← setIntegralEq]
  have rowMemLp :
      MemLp
        (fun actual => tangentRow actual)
        2
        ((commonTimeMeasure current.nextContact.time.1).restrict
          (Iic time)) :=
    (Lp.memLp tangentRow).restrict (Iic time)
  have cauchy :=
    norm_integral_sq_le_measureReal_mul_integral_norm_sq
      (μ :=
        (commonTimeMeasure current.nextContact.time.1).restrict
          (Iic time))
      (fun actual => tangentRow actual)
      rowMemLp
  have rowNormSqIntegrable :
      Integrable
        (fun actual => ‖tangentRow actual‖ ^ 2)
        (commonTimeMeasure current.nextContact.time.1) :=
    (Lp.memLp tangentRow).integrable_norm_pow (by norm_num)
  have restrictedIntegralLe :
      (∫ actual in Iic time,
          ‖tangentRow actual‖ ^ 2
          ∂(commonTimeMeasure current.nextContact.time.1)) ≤
        ‖tangentRow‖ ^ 2 := by
    rw [fixedWaveSpaceTimeState_norm_sq_eq_integral]
    exact
      setIntegral_le_integral
        rowNormSqIntegrable
        (Filter.Eventually.of_forall fun actual => sq_nonneg _)
  rw [endpointAsSetIntegral]
  calc
    ‖∫ actual in Iic time, tangentRow actual
        ∂(commonTimeMeasure current.nextContact.time.1)‖ ^ 2 ≤
      ((commonTimeMeasure current.nextContact.time.1).restrict
          (Iic time)).real univ *
        ∫ actual in Iic time, ‖tangentRow actual‖ ^ 2
          ∂(commonTimeMeasure current.nextContact.time.1) :=
      cauchy
    _ = time.1 *
        ∫ actual in Iic time, ‖tangentRow actual‖ ^ 2
          ∂(commonTimeMeasure current.nextContact.time.1) := by
      rw [commonTimeMeasure_Iic_real
        current.nextContact.time.1 current.nextContact.time_pos.le time]
    _ ≤ time.1 * ‖tangentRow‖ ^ 2 :=
      mul_le_mul_of_nonneg_left restrictedIntegralLe time.2.1

/-- Any finite zero-free family on one actual prefix receipt has a common
inverse-Laplacian endpoint displacement controlled by the receipt's single
whole `L²_t H⁻¹_x` tangent.  The caller supplies no cutoff, modulus, margin,
branch, or continuation certificate. -/
theorem wholeRestartCrossingFiniteNegativeOneDisplacement_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ wave ∈ modes, wave ≠ 0)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          (((Real.sqrt
            (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
            ((run initial index).nextContact.prefixReceipt.wholePath
                time wave -
              (run initial index).contact.physicalState wave))) ≤
      3 * time.1 *
        ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let rowSquare : IntegerWavevector → ℝ := fun wave =>
    ‖fixedWaveSpaceTimeRestriction
      (run initial index).nextContact.time.1 wave
      receipt.wholeTangent‖ ^ 2
  have rowSquareSummable : Summable rowSquare := by
    simpa [rowSquare] using
      summable_fixedWaveSpaceTimeRestriction_norm_sq
        (run initial index).nextContact.time.1 receipt.wholeTangent
  have finiteRowsLe :
      (∑ wave ∈ modes, rowSquare wave) ≤ ∑' wave, rowSquare wave :=
    rowSquareSummable.sum_le_tsum modes
      (fun wave waveMem => sq_nonneg _)
  calc
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          (((Real.sqrt
            (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
            ((run initial index).nextContact.prefixReceipt.wholePath
                time wave -
              (run initial index).contact.physicalState wave))) ≤
        ∑ wave ∈ modes,
          3 *
            ‖((Real.sqrt
              (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
              ((run initial index).nextContact.prefixReceipt.wholePath
                  time wave -
                (run initial index).contact.physicalState wave)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro wave waveMem
      exact complexCoordinateAmplitudeSq_le_three_mul_norm_sq _
    _ ≤ ∑ wave ∈ modes, 3 * (time.1 * rowSquare wave) := by
      apply Finset.sum_le_sum
      intro wave waveMem
      exact mul_le_mul_of_nonneg_left
        (wholeRestartCrossingNegativeOneRowDisplacement_normSq_le
          initial index wave (modesNonzero wave waveMem) time)
        (by norm_num)
    _ = 3 * time.1 * ∑ wave ∈ modes, rowSquare wave := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave waveMem
      ring
    _ ≤ 3 * time.1 * ∑' wave, rowSquare wave :=
      mul_le_mul_of_nonneg_left finiteRowsLe
        (mul_nonneg (by norm_num) time.2.1)
    _ = 3 * time.1 * ‖receipt.wholeTangent‖ ^ 2 := by
      rw [show (∑' wave, rowSquare wave) = ‖receipt.wholeTangent‖ ^ 2 by
        simpa [rowSquare] using
          tsum_fixedWaveSpaceTimeRestriction_norm_sq
            (run initial index).nextContact.time.1 receipt.wholeTangent]

/-- The actual unforced update charges every finite zero-free endpoint
displacement in inverse-Laplacian mass to the dual-square payment written by
that exact next restart segment. -/
theorem wholeRestartCrossingFiniteNegativeOneEndpointDisplacement_le_segmentDualSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ wave ∈ modes, wave ≠ 0) :
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          (((Real.sqrt
            (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
            ((run initial index).nextContact.physicalState wave -
              (run initial index).contact.physicalState wave))) ≤
      2 * ν.coeff * (run initial index).nextContact.time.1 *
        wholeRestartSegmentDualSquarePayment initial (index + 1) := by
  let terminal :
      Icc (0 : ℝ) (run initial index).nextContact.time.1 :=
    ⟨(run initial index).nextContact.time.1,
      ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩
  have debit :
      (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            (((Real.sqrt
              (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
              ((run initial index).nextContact.prefixReceipt.wholePath
                  terminal wave -
                (run initial index).contact.physicalState wave))) ≤
        2 * ν.coeff * terminal.1 *
          wholeRestartSegmentDualSquarePayment initial (index + 1) := by
    calc
      (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            (((Real.sqrt
              (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
              ((run initial index).nextContact.prefixReceipt.wholePath
                  terminal wave -
                (run initial index).contact.physicalState wave))) ≤
          3 * terminal.1 *
            ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 :=
        wholeRestartCrossingFiniteNegativeOneDisplacement_le
          initial index modes modesNonzero terminal
      _ ≤ 3 * terminal.1 *
          ((2 * ν.coeff / 3) *
            wholeRestartSegmentDualSquarePayment initial (index + 1)) :=
        mul_le_mul_of_nonneg_left
          (nextContact_wholeTangent_norm_sq_le_segmentDualSquarePayment
            initial index)
          (mul_nonneg (by norm_num) terminal.2.1)
      _ = 2 * ν.coeff * terminal.1 *
          wholeRestartSegmentDualSquarePayment initial (index + 1) := by
        ring
  rw [nextContact_prefix_terminal (run initial index)] at debit
  exact debit

/-- Dividing by the source-generated positive segment duration exposes the
finite-mode endpoint motion as a lower debit on that segment's dual-square
payment. -/
theorem wholeRestartCrossingFiniteNegativeOneEndpointDisplacementRate_le_segmentDualSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ wave ∈ modes, wave ≠ 0) :
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          (((Real.sqrt
            (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
            ((run initial index).nextContact.physicalState wave -
              (run initial index).contact.physicalState wave))) /
        (2 * ν.coeff * (run initial index).nextContact.time.1) ≤
      wholeRestartSegmentDualSquarePayment initial (index + 1) := by
  rw [div_le_iff₀]
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (wholeRestartCrossingFiniteNegativeOneEndpointDisplacement_le_segmentDualSquarePayment
        initial index modes modesNonzero)
  · exact mul_pos
      (mul_pos (by norm_num) ν.coeff_pos)
      (run initial index).nextContact.time_pos

/-- Summing the actual edge law over one native `Ico` charges the complete
finite-mode endpoint motion to the dual-square debits of those same restart
segments. -/
theorem wholeRestartIcoFiniteNegativeOneEndpointDisplacement_le_dualSquareDebit
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (start finish : ℕ) :
    (∑ index ∈ Finset.Ico start finish,
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            (((Real.sqrt
              (integerWaveViscousMultiplier wave) : ℂ)⁻¹) •
              ((run initial index).nextContact.physicalState wave -
                (run initial index).contact.physicalState wave))) ≤
      ∑ index ∈ Finset.Ico start finish,
        2 * ν.coeff * (run initial index).nextContact.time.1 *
          wholeRestartSegmentDualSquarePayment initial (index + 1) := by
  apply Finset.sum_le_sum
  intro index _indexMem
  exact
    wholeRestartCrossingFiniteNegativeOneEndpointDisplacement_le_segmentDualSquarePayment
      initial index modes fun wave waveMem waveEqZero =>
        zeroNotMem (waveEqZero ▸ waveMem)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteNegativeOneDisplacement
end NavierStokes
end SaturationMonoid
