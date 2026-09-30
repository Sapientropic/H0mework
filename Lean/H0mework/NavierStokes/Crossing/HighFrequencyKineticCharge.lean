import H0mework.NavierStokes.Crossing.MassPersistence
import H0mework.NavierStokes.Crossing.UnforcedTangentPayment
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Same-receipt kinetic charge of a faithful-zero high-frequency escape

At one actual half-critical crossing, a Fourier output outside the generated
finite-core pair support has the exact time-zero viscous derivative whenever
the complete gluing residual is faithfully zero.  This module consumes that
derivative before quotient loss.

The derivative and continuity of the same unforced whole receipt generate a
positive physical time `t` for which

```text
q = ν t |a_k(0)|² > 0,
q ≤ the actual successor receipt's kinetic payment,
λ_k q < |a_k(0)|² - |a_k(t)|².
```

Thus the high-frequency factor is retained in the physical drop while its
unweighted amplitude--time responsibility is charged exactly once to the
existing native kinetic telescope.  No time, charge, persistence modulus,
cutoff, branch, or target path is accepted from a caller.
-/

open scoped Topology
open Set Filter

namespace SaturationMonoid.NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyKineticCharge

/-- A strictly negative time-zero derivative generates one common positive
time with both a quantitative drop and a retained half-value interval.  This
is the analytic step consumed by both the single-row and finite aggregate
same-receipt charge theorems. -/
theorem exists_positive_time_quantitative_drop_and_persistence
    {f : ℝ → ℝ}
    {rate duration : ℝ}
    (derivativeAt : HasDerivAt f (-2 * rate) 0)
    (ratePos : 0 < rate)
    (valuePos : 0 < f 0)
    (durationPos : 0 < duration) :
    ∃ actual : ℝ,
      0 < actual ∧ actual < duration ∧
        rate * actual < f 0 - f actual ∧
        ∀ earlier ∈ Icc (0 : ℝ) actual,
          f 0 / 2 ≤ f earlier := by
  have slopeLt :
      ∀ᶠ actual in 𝓝[>] (0 : ℝ),
        slope f 0 actual < -rate := by
    exact ((hasDerivAt_iff_tendsto_slope_left_right.mp derivativeAt).2)
      (Iio_mem_nhds (by linarith))
  have retained :
      ∀ᶠ actual in 𝓝 (0 : ℝ),
        f 0 / 2 < f actual := by
    exact derivativeAt.continuousAt.eventually
      (Ioi_mem_nhds (by linarith))
  have retainedRight :
      ∀ᶠ actual in 𝓝[>] (0 : ℝ),
        f 0 / 2 < f actual :=
    by
      exact Filter.Eventually.filter_mono inf_le_left retained
  have insideDuration :
      ∀ᶠ actual in 𝓝[>] (0 : ℝ),
        actual < duration := by
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds durationPos)
  have combined :
      {actual : ℝ |
        slope f 0 actual < -rate ∧
          f 0 / 2 < f actual ∧ actual < duration} ∈
        𝓝[>] (0 : ℝ) := by
    exact (slopeLt.and (retainedRight.and insideDuration))
  obtain ⟨upper, upperPos, upperSpec⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset.mp combined)
  change 0 < upper at upperPos
  let actual := upper / 2
  have actualPos : 0 < actual := by
    dsimp [actual]
    linarith
  have actualLtUpper : actual < upper := by
    dsimp [actual]
    linarith
  have actualSpec := upperSpec ⟨actualPos, actualLtUpper⟩
  change
    slope f 0 actual < -rate ∧
      f 0 / 2 < f actual ∧ actual < duration at actualSpec
  refine ⟨actual, actualPos, actualSpec.2.2, ?_, ?_⟩
  · rw [slope_def_field] at actualSpec
    have denominatorPos : 0 < actual - 0 := by simpa
    have multiplied := (div_lt_iff₀ denominatorPos).mp actualSpec.1
    simp only [sub_zero] at multiplied
    linarith
  · intro earlier earlierMem
    rcases eq_or_lt_of_le earlierMem.1 with rfl | earlierPos
    · linarith
    · have earlierLtUpper : earlier < upper :=
        earlierMem.2.trans_lt actualLtUpper
      exact (upperSpec ⟨earlierPos, earlierLtUpper⟩).2.1.le

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyKineticCharge
end SaturationMonoid.NavierStokes

namespace SaturationMonoid.NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyKineticCharge

open scoped Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence

noncomputable section

private theorem singleAmplitudeSq_le_wholeVorticityEuclideanMass
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    complexCoordinateAmplitudeSq (state output) ≤
      wholeVorticityEuclideanMass state := by
  simpa [finiteStateVorticityCoefficientEnstrophy] using
    (finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      {output} state)

/-- Vanishing of the whole `H⁻¹` nonlinear state is faithful on every
nonzero Fourier row. -/
theorem
    wholeStateVorticityNonlinearCoefficientAt_eq_zero_of_negativeOneState_eq_zero
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (stateZero :
      wholeStateVorticityNonlinearNegativeOneState
        state stateTransverse gradientSummable = 0)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    wholeStateVorticityNonlinearCoefficientAt state output = 0 := by
  have weightedZero :
      wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
        state output = 0 := by
    have applied := congrArg
      (fun value : lp
        (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 =>
          value output)
      stateZero
    simpa using applied
  rw [wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
    if_neg outputNonzero] at weightedZero
  have multiplierPos :
      0 < integerWaveViscousMultiplier output :=
    integerWaveViscousMultiplier_pos ⟨output, outputNonzero⟩
  exact (smul_eq_zero.mp weightedZero).resolve_left
    (inv_ne_zero (Real.sqrt_pos.2 multiplierPos).ne')

/-- A faithful zero of one actual nonlinear row leaves the literal negative
viscous derivative of that row's physical coefficient square. -/
theorem
    wholeRestartActualWholeRowAmplitudeSq_hasDerivAt_zero_eq_neg_viscous_of_nonlinearRow_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (nonlinearRowZero :
      wholeStateVorticityNonlinearCoefficientAt
        (run initial index).contact.physicalState output = 0) :
    HasDerivAt
      (fun actual =>
        complexCoordinateAmplitudeSq
          (actualWholeContinuousHeatDuhamelPath
            (run initial index).nextContact.prefixReceipt output actual))
      (-2 * (ν.coeff * integerWaveViscousMultiplier output) *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output))
      0 := by
  let current := run initial index
  let receipt := current.nextContact.prefixReceipt
  have rowDerivative :=
    actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      (receipt := receipt) output
  rw [nonlinearRowZero] at rowDerivative
  have rowDerivative' :
      HasDerivAt
        (actualWholeContinuousHeatDuhamelPath receipt output)
        (-((ν.coeff * integerWaveViscousMultiplier output) •
          current.contact.physicalState output))
        0 := by
    simpa [current, receipt] using rowDerivative
  have energyDerivative :=
    complexCoordinateAmplitudeSq_hasDerivAt
      (actualWholeContinuousHeatDuhamelPath receipt output)
      0
      (-((ν.coeff * integerWaveViscousMultiplier output) •
        current.contact.physicalState output))
      rowDerivative'
  have pathAtZero :
      actualWholeContinuousHeatDuhamelPath receipt output 0 =
        current.contact.physicalState output := by
    unfold receipt actualWholeContinuousHeatDuhamelPath
      heatDuhamelComplexCoordinatePath
      intervalIntegralComplexCoordinatePath
    simp
  rw [pathAtZero] at energyDerivative
  convert energyDerivative using 1
  rw [← neg_smul,
    complexCoordinateRealInner_real_smul_right,
    complexCoordinateRealInner_self,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  dsimp [current, receipt]
  ring

theorem
    wholeRestartActualWholeRowAmplitudeSq_generates_kineticCharge_of_nonlinearRow_zero
    { ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (nonlinearRowZero :
      wholeStateVorticityNonlinearCoefficientAt
        (run initial index).contact.physicalState output = 0)
    (outputNonzero : output ≠ 0)
    (stateNonzero :
      (run initial index).contact.physicalState output ≠ 0) :
    ∃ actual : Ioo (0 : ℝ) (run initial index).nextContact.time.1,
      let initialAmplitude :=
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
      let charge := ν.coeff * actual.1 * initialAmplitude
      0 < charge ∧
        charge ≤
          wholeRestartNextKineticDissipationPayment initial index ∧
        integerWaveViscousMultiplier output * charge <
          initialAmplitude -
            complexCoordinateAmplitudeSq
              ((run initial index).nextContact.prefixReceipt.wholePath
                ⟨actual.1, actual.2.1.le, actual.2.2.le⟩ output) := by
  let current := run initial index
  let receipt := current.nextContact.prefixReceipt
  let initialAmplitude :=
    complexCoordinateAmplitudeSq (current.contact.physicalState output)
  let rate := ν.coeff * integerWaveViscousMultiplier output * initialAmplitude
  let physicalAmplitude : ℝ → ℝ := fun actual =>
    complexCoordinateAmplitudeSq
      (actualWholeContinuousHeatDuhamelPath receipt output actual)
  have amplitudePos : 0 < initialAmplitude := by
    simpa [initialAmplitude,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      complexCoordinateVectorNormSq_pos_iff] using stateNonzero
  have multiplierPos : 0 < integerWaveViscousMultiplier output :=
    integerWaveViscousMultiplier_pos ⟨output, outputNonzero⟩
  have ratePos : 0 < rate := by
    exact mul_pos (mul_pos ν.coeff_pos multiplierPos) amplitudePos
  have derivativeAt : HasDerivAt physicalAmplitude (-2 * rate) 0 := by
    simpa [physicalAmplitude, rate, initialAmplitude,
      current, receipt, mul_assoc] using
      wholeRestartActualWholeRowAmplitudeSq_hasDerivAt_zero_eq_neg_viscous_of_nonlinearRow_zero
        initial index output nonlinearRowZero
  have pathAtZero : physicalAmplitude 0 = initialAmplitude := by
    dsimp [physicalAmplitude, initialAmplitude, receipt, current]
    unfold actualWholeContinuousHeatDuhamelPath
      heatDuhamelComplexCoordinatePath
      intervalIntegralComplexCoordinatePath
    simp
  obtain ⟨actual, actualPos, actualLt, quantitativeDrop, retained⟩ :=
    exists_positive_time_quantitative_drop_and_persistence
      derivativeAt ratePos (pathAtZero.symm ▸ amplitudePos)
      current.nextContact.time_pos
  let actualTime : Icc (0 : ℝ) current.nextContact.time.1 :=
    ⟨actual, actualPos.le, actualLt.le⟩
  let prefixTrajectory :=
    wholeRestartReceiptPhysicalTrajectory receipt
  let fullTrajectory :=
    wholeRestartReceiptPhysicalTrajectory current.nextReceipt
  have prefixTrajectoryEq
      (earlier : ℝ)
      (earlierMem : earlier ∈ Icc (0 : ℝ) current.nextContact.time.1) :
      prefixTrajectory earlier = fullTrajectory earlier := by
    unfold prefixTrajectory fullTrajectory
      wholeRestartReceiptPhysicalTrajectory receipt
    rw [projIcc_of_mem current.nextContact.prefixReceipt.requestedTimePos.le
      earlierMem]
    rw [projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨earlierMem.1,
        earlierMem.2.trans current.nextContact.time.2.2⟩]
    rfl
  have amplitudeEq
      (earlier : ℝ)
      (earlierMem : earlier ∈ Icc (0 : ℝ) current.nextContact.time.1) :
      physicalAmplitude earlier =
        complexCoordinateAmplitudeSq (fullTrajectory earlier output) := by
    have wholePathEq :=
      wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
        receipt output outputNonzero
          (⟨earlier, earlierMem⟩ :
            Icc (0 : ℝ) current.nextContact.time.1)
    change
      complexCoordinateAmplitudeSq
          (actualWholeContinuousHeatDuhamelPath receipt output earlier) =
        complexCoordinateAmplitudeSq (fullTrajectory earlier output)
    rw [← wholePathEq]
    have prefixEq := prefixTrajectoryEq earlier earlierMem
    unfold prefixTrajectory at prefixEq
    rw [wholeRestartReceiptPhysicalTrajectory,
      projIcc_of_mem receipt.requestedTimePos.le earlierMem] at prefixEq
    rw [prefixEq]
  have retainedFull :
      ∀ earlier ∈ Icc (0 : ℝ) actual,
        initialAmplitude / 2 ≤
          complexCoordinateAmplitudeSq (fullTrajectory earlier output) := by
    intro earlier earlierMem
    have earlierFullMem :
        earlier ∈ Icc (0 : ℝ) current.nextContact.time.1 :=
      ⟨earlierMem.1, earlierMem.2.trans actualLt.le⟩
    rw [← amplitudeEq earlier earlierFullMem, ← pathAtZero]
    exact retained earlier earlierMem
  let density : ℝ → ℝ := fun earlier =>
    complexCoordinateAmplitudeSq (fullTrajectory earlier output)
  let wholeDensity : ℝ → ℝ := fun earlier =>
    wholeVorticityEuclideanMass (fullTrajectory earlier)
  have fullTrajectoryContinuous : Continuous fullTrajectory :=
    wholeRestartReceiptPhysicalTrajectory_continuous current.nextReceipt
  have densityContinuous : Continuous density := by
    exact complexCoordinateAmplitudeSq_continuous.comp
      ((lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 output).continuous.comp fullTrajectoryContinuous)
  have wholeDensityContinuous : Continuous wholeDensity := by
    rw [continuous_iff_continuousAt]
    intro earlier
    exact tendsto_wholeVorticityEuclideanMass
      fullTrajectoryContinuous.continuousAt
  have amplitudeTimeLeDensity :
      actual * (initialAmplitude / 2) ≤
        ∫ earlier in (0 : ℝ)..actual, density earlier := by
    have integrated :=
      intervalIntegral.integral_mono_on
        (μ := volume)
        actualPos.le
        (continuous_const.intervalIntegrable 0 actual)
        (densityContinuous.intervalIntegrable 0 actual)
        (fun earlier earlierMem => retainedFull earlier earlierMem)
    calc
      actual * (initialAmplitude / 2) =
          actual * initialAmplitude / 2 := by ring
      _ ≤ ∫ earlier in (0 : ℝ)..actual, density earlier := by
        simpa [density, intervalIntegral.integral_const,
          sub_zero, smul_eq_mul] using integrated
  have densityIntegralLeWhole :
      (∫ earlier in (0 : ℝ)..actual, density earlier) ≤
        ∫ earlier in (0 : ℝ)..actual, wholeDensity earlier := by
    exact intervalIntegral.integral_mono_on
      actualPos.le
      (densityContinuous.intervalIntegrable 0 actual)
      (wholeDensityContinuous.intervalIntegrable 0 actual)
      (fun earlier earlierMem =>
        singleAmplitudeSq_le_wholeVorticityEuclideanMass
          (fullTrajectory earlier) output)
  have localIntegralLeFull :
      (∫ earlier in (0 : ℝ)..actual, wholeDensity earlier) ≤
        ∫ earlier in (0 : ℝ)..current.nextContact.time.1,
          wholeDensity earlier := by
    exact intervalIntegral.integral_mono_interval
      (c := (0 : ℝ)) (d := current.nextContact.time.1)
      le_rfl actualPos.le actualLt.le
      (Filter.Eventually.of_forall fun earlier => by
        unfold wholeDensity wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _)
      (wholeDensityContinuous.intervalIntegrable
        0 current.nextContact.time.1)
  have fullIntegralEq :
      wholePrefixVorticityMass current.nextContact.time
          current.nextReceipt.stateLimit =
        ∫ earlier in (0 : ℝ)..current.nextContact.time.1,
          wholeDensity earlier := by
    simpa [wholeDensity, fullTrajectory] using
      wholePrefixVorticityMass_receipt_eq_intervalIntegral
        current.nextReceipt current.nextContact.time
  let charge := ν.coeff * actual * initialAmplitude
  have chargePos : 0 < charge := by
    exact mul_pos (mul_pos ν.coeff_pos actualPos) amplitudePos
  have chargeLe :
      charge ≤ wholeRestartNextKineticDissipationPayment initial index := by
    calc
      charge =
          2 * ν.coeff * (actual * (initialAmplitude / 2)) := by
        dsimp [charge]
        ring
      _ ≤ 2 * ν.coeff *
          (∫ earlier in (0 : ℝ)..actual, density earlier) :=
        mul_le_mul_of_nonneg_left amplitudeTimeLeDensity
          (mul_nonneg (by norm_num) ν.coeff_pos.le)
      _ ≤ 2 * ν.coeff *
          (∫ earlier in (0 : ℝ)..actual, wholeDensity earlier) :=
        mul_le_mul_of_nonneg_left densityIntegralLeWhole
          (mul_nonneg (by norm_num) ν.coeff_pos.le)
      _ ≤ 2 * ν.coeff *
          (∫ earlier in (0 : ℝ)..current.nextContact.time.1,
            wholeDensity earlier) :=
        mul_le_mul_of_nonneg_left localIntegralLeFull
          (mul_nonneg (by norm_num) ν.coeff_pos.le)
      _ = wholeRestartNextKineticDissipationPayment initial index := by
        rw [← fullIntegralEq]
        rfl
  have actualPathEq :
      physicalAmplitude actual =
        complexCoordinateAmplitudeSq
          (current.nextContact.prefixReceipt.wholePath actualTime output) := by
    exact (amplitudeEq actual ⟨actualPos.le, actualLt.le⟩).trans
      (by
        rw [← prefixTrajectoryEq actual
          ⟨actualPos.le, actualLt.le⟩]
        unfold prefixTrajectory wholeRestartReceiptPhysicalTrajectory
        rw [projIcc_of_mem receipt.requestedTimePos.le
          ⟨actualPos.le, actualLt.le⟩])
  refine ⟨⟨actual, actualPos, actualLt⟩, ?_⟩
  dsimp only
  refine ⟨chargePos, chargeLe, ?_⟩
  change
    integerWaveViscousMultiplier output * charge <
      initialAmplitude -
        complexCoordinateAmplitudeSq
          (current.nextContact.prefixReceipt.wholePath actualTime output)
  rw [← actualPathEq]
  calc
    integerWaveViscousMultiplier output * charge = rate * actual := by
      dsimp [charge, rate]
      ring
    _ < physicalAmplitude 0 - physicalAmplitude actual := quantitativeDrop
    _ = initialAmplitude - physicalAmplitude actual := by rw [pathAtZero]

/-- The existing support-exclusion branch is the concrete crossing instance
of the row-zero kinetic consumer. -/
theorem
    wholeRestartCrossingActualWholeRowAmplitudeSq_generates_kineticCharge_of_gluing_zero
    { ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0)
    (output : IntegerWavevector)
    (outputNotMem :
      output ∉ finiteVorticityPairOutputSupport
        (wholeRestartCrossingFiniteCoreModes initial index crossed))
    (outputNonzero : output ≠ 0)
    (stateNonzero :
      (run initial index).contact.physicalState output ≠ 0) :
    ∃ actual : Ioo (0 : ℝ) (run initial index).nextContact.time.1,
      let initialAmplitude :=
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
      let charge := ν.coeff * actual.1 * initialAmplitude
      0 < charge ∧
        charge ≤
          wholeRestartNextKineticDissipationPayment initial index ∧
        integerWaveViscousMultiplier output * charge <
          initialAmplitude -
            complexCoordinateAmplitudeSq
              ((run initial index).nextContact.prefixReceipt.wholePath
                ⟨actual.1, actual.2.1.le, actual.2.2.le⟩ output) := by
  exact
    wholeRestartActualWholeRowAmplitudeSq_generates_kineticCharge_of_nonlinearRow_zero
      initial index output
      (wholeRestartCrossingWholeNonlinearCoefficientAt_eq_zero_of_gluing_zero_of_not_mem_pairOutput
        initial index crossed gluingZero output outputNotMem)
      outputNonzero stateNonzero

end
end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyKineticCharge
end SaturationMonoid.NavierStokes
