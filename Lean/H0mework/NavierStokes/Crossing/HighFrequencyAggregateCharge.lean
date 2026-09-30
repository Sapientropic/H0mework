import H0mework.NavierStokes.Crossing.HighFrequencyKineticCharge

/-!
# Same-receipt aggregate kinetic charge of a high-frequency tail

The single-row kinetic charge is strengthened before coefficient quotient:
one finite family of outputs outside the generated pair support is summed
first, then differentiated along the same actual unforced whole receipt.
This generates one common positive physical time and the exact ledger

```text
q = ν t ∑ₖ |aₖ(0)|²,
q ≤ successor kinetic payment,
ν t ∑ₖ λₖ |aₖ(0)|²
  < ∑ₖ (|aₖ(0)|² - |aₖ(t)|²).
```

The common time is generated from the derivative of the finite aggregate;
it is not assembled from unrelated single-mode persistence windows.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateCharge

open scoped BigOperators Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
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
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyKineticCharge
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence

noncomputable section

/-- Every positive finite aggregate, without a nonlinear-row branch
assumption, generates one common no-drop interval and a positive charge on
the same successor kinetic ledger. -/
theorem
    wholeRestartActualWholeFiniteAmplitudeSq_generates_aggregateKineticPersistenceCharge
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (modes : Finset IntegerWavevector)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    ∃ actual : Ioo (0 : Real) (run initial index).nextContact.time.1,
      let initialMass :=
        ∑ output ∈ modes,
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output)
      let fullTrajectory :=
        wholeRestartReceiptPhysicalTrajectory
          (run initial index).nextReceipt
      let charge := nu.coeff * actual.1 * initialMass
      0 < charge ∧
        charge ≤ wholeRestartNextKineticDissipationPayment initial index ∧
        ∀ earlier ∈ Icc (0 : Real) actual.1,
          initialMass / 2 ≤
            finiteStateVorticityCoefficientEnstrophy modes
              (fullTrajectory earlier) := by
  let current := run initial index
  let initialMass :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        (current.contact.physicalState output)
  let fullTrajectory :=
    wholeRestartReceiptPhysicalTrajectory current.nextReceipt
  let density : Real → Real := fun earlier =>
    finiteStateVorticityCoefficientEnstrophy modes
      (fullTrajectory earlier)
  have initialMassPos' : 0 < initialMass := by
    simpa only [initialMass, current] using initialMassPos
  have densityContinuous : Continuous density := by
    unfold density finiteStateVorticityCoefficientEnstrophy
    apply continuous_finsetSum
    intro output outputMem
    exact complexCoordinateAmplitudeSq_continuous.comp
      ((lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 output).continuous.comp
          (wholeRestartReceiptPhysicalTrajectory_continuous
            current.nextReceipt))
  have densityZero : density 0 = initialMass := by
    unfold density initialMass fullTrajectory
      finiteStateVorticityCoefficientEnstrophy
    rw [wholeRestartReceiptPhysicalTrajectory_zero]
  have halfMassPos : 0 < initialMass / 2 := by linarith
  have halfMassLt : initialMass / 2 < density 0 := by
    rw [densityZero]
    linarith
  have eventuallyLower :
      ∀ᶠ earlier in 𝓝 (0 : Real),
        initialMass / 2 < density earlier :=
    densityContinuous.continuousAt.eventually
      (eventually_gt_nhds halfMassLt)
  obtain ⟨liveRadius, liveRadiusPos, liveWithin⟩ :=
    Metric.eventually_nhds_iff.mp eventuallyLower
  let actual := min current.nextContact.time.1 liveRadius / 2
  have commonRadiusPos :
      0 < min current.nextContact.time.1 liveRadius :=
    lt_min current.nextContact.time_pos liveRadiusPos
  have actualPos : 0 < actual := by
    dsimp only [actual]
    linarith
  have actualLtCommon :
      actual < min current.nextContact.time.1 liveRadius := by
    dsimp only [actual]
    linarith
  have actualLtContact : actual < current.nextContact.time.1 :=
    actualLtCommon.trans_le (min_le_left _ _)
  have actualLtLive : actual < liveRadius :=
    actualLtCommon.trans_le (min_le_right _ _)
  have pointwiseLower :
      ∀ earlier ∈ Icc (0 : Real) actual,
        initialMass / 2 ≤ density earlier := by
    intro earlier earlierMem
    exact (liveWithin (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg earlierMem.1]
      exact earlierMem.2.trans_lt actualLtLive)).le
  have densityIntegrable :
      IntervalIntegrable density volume 0 actual :=
    densityContinuous.intervalIntegrable 0 actual
  have integratedLower :=
    intervalIntegral.integral_mono_on
      actualPos.le
      (continuous_const.intervalIntegrable 0 actual)
      densityIntegrable pointwiseLower
  have amplitudeTimeLeDensity :
      actual * (initialMass / 2) ≤
        ∫ earlier in (0 : Real)..actual, density earlier := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] using
      integratedLower
  let wholeDensity : Real → Real := fun earlier =>
    wholeVorticityEuclideanMass (fullTrajectory earlier)
  have wholeDensityContinuous : Continuous wholeDensity := by
    rw [continuous_iff_continuousAt]
    intro earlier
    exact tendsto_wholeVorticityEuclideanMass
      (wholeRestartReceiptPhysicalTrajectory_continuous
        current.nextReceipt).continuousAt
  have densityIntegralLeWhole :
      (∫ earlier in (0 : Real)..actual, density earlier) ≤
        ∫ earlier in (0 : Real)..actual, wholeDensity earlier := by
    exact intervalIntegral.integral_mono_on
      actualPos.le densityIntegrable
      (wholeDensityContinuous.intervalIntegrable 0 actual)
      (fun earlier _ =>
        finiteStateVorticityCoefficientEnstrophy_le_wholeMass
          modes (fullTrajectory earlier))
  have localIntegralLeFull :
      (∫ earlier in (0 : Real)..actual, wholeDensity earlier) ≤
        ∫ earlier in (0 : Real)..current.nextContact.time.1,
          wholeDensity earlier := by
    exact intervalIntegral.integral_mono_interval
      (c := (0 : Real)) (d := current.nextContact.time.1)
      le_rfl actualPos.le actualLtContact.le
      (Filter.Eventually.of_forall fun earlier => by
        unfold wholeDensity wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _)
      (wholeDensityContinuous.intervalIntegrable
        0 current.nextContact.time.1)
  have fullIntegralEq :
      wholePrefixVorticityMass current.nextContact.time
          current.nextReceipt.stateLimit =
        ∫ earlier in (0 : Real)..current.nextContact.time.1,
          wholeDensity earlier := by
    simpa only [wholeDensity, fullTrajectory] using
      wholePrefixVorticityMass_receipt_eq_intervalIntegral
        current.nextReceipt current.nextContact.time
  let charge := nu.coeff * actual * initialMass
  have chargePos : 0 < charge :=
    mul_pos (mul_pos nu.coeff_pos actualPos) initialMassPos'
  have chargeLe :
      charge ≤ wholeRestartNextKineticDissipationPayment initial index := by
    calc
      charge = 2 * nu.coeff * (actual * (initialMass / 2)) := by
        dsimp only [charge]
        ring
      _ ≤ 2 * nu.coeff *
          (∫ earlier in (0 : Real)..actual, density earlier) :=
        mul_le_mul_of_nonneg_left amplitudeTimeLeDensity
          (mul_nonneg (by norm_num) nu.coeff_pos.le)
      _ ≤ 2 * nu.coeff *
          (∫ earlier in (0 : Real)..actual, wholeDensity earlier) :=
        mul_le_mul_of_nonneg_left densityIntegralLeWhole
          (mul_nonneg (by norm_num) nu.coeff_pos.le)
      _ ≤ 2 * nu.coeff *
          (∫ earlier in (0 : Real)..current.nextContact.time.1,
            wholeDensity earlier) :=
        mul_le_mul_of_nonneg_left localIntegralLeFull
          (mul_nonneg (by norm_num) nu.coeff_pos.le)
      _ = wholeRestartNextKineticDissipationPayment initial index := by
        rw [← fullIntegralEq]
        rfl
  refine ⟨⟨actual, actualPos, actualLtContact⟩, ?_⟩
  dsimp only
  exact ⟨chargePos, chargeLe, pointwiseLower⟩

/-- A finite family of high-frequency rows is consumed before projection
loss.  The same actual receipt generates a common time, an aggregate positive
charge paid by the successor kinetic ledger, and the frequency-weighted
coefficient drop. -/
theorem
    wholeRestartActualWholeFiniteAmplitudeSq_generates_aggregateKineticCharge_of_nonlinearRows_zero
    { ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector)
    (nonlinearRowsZero :
      ∀ output ∈ modes,
        wholeStateVorticityNonlinearCoefficientAt
          (run initial index).contact.physicalState output = 0)
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    ∃ actual : Ioo (0 : ℝ) (run initial index).nextContact.time.1,
      let initialMass :=
        ∑ output ∈ modes,
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output)
      let weightedInitialMass :=
        ∑ output ∈ modes,
          integerWaveViscousMultiplier output *
            complexCoordinateAmplitudeSq
              ((run initial index).contact.physicalState output)
      let charge := ν.coeff * actual.1 * initialMass
      0 < charge ∧
        charge ≤ wholeRestartNextKineticDissipationPayment initial index ∧
        ν.coeff * actual.1 * weightedInitialMass <
          initialMass -
            finiteStateVorticityCoefficientEnstrophy modes
              ((run initial index).nextContact.prefixReceipt.wholePath
                ⟨actual.1, actual.2.1.le, actual.2.2.le⟩) := by
  let current := run initial index
  let receipt := current.nextContact.prefixReceipt
  let initialMass :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        (current.contact.physicalState output)
  let weightedInitialMass :=
    ∑ output ∈ modes,
      integerWaveViscousMultiplier output *
        complexCoordinateAmplitudeSq
          (current.contact.physicalState output)
  let rate := ν.coeff * weightedInitialMass
  let physicalMass : ℝ → ℝ := fun actual =>
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        (actualWholeContinuousHeatDuhamelPath receipt output actual)
  have initialMassPos' : 0 < initialMass := by
    simpa [initialMass, current] using initialMassPos
  have weightedInitialMassPos : 0 < weightedInitialMass := by
    have spectralPos : 0 < (2 * Real.pi) ^ 2 :=
      sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)
    have spectralInitialPos :
        0 < (2 * Real.pi) ^ 2 * initialMass :=
      mul_pos spectralPos initialMassPos'
    apply spectralInitialPos.trans_le
    dsimp [initialMass, weightedInitialMass]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro output outputMem
    exact mul_le_mul_of_nonneg_right
      (twoPiSq_le_integerWaveViscousMultiplier
        ⟨output, modesNonzero output outputMem⟩)
      (complexCoordinateAmplitudeSq_nonneg _)
  have ratePos : 0 < rate :=
    mul_pos ν.coeff_pos weightedInitialMassPos
  have waveDerivative :
      ∀ output ∈ modes,
        HasDerivAt
          (fun actual =>
            complexCoordinateAmplitudeSq
              (actualWholeContinuousHeatDuhamelPath
                receipt output actual))
          (-2 * (ν.coeff * integerWaveViscousMultiplier output) *
            complexCoordinateAmplitudeSq
              (current.contact.physicalState output))
          0 := by
    intro output outputMem
    simpa [current, receipt] using
      wholeRestartActualWholeRowAmplitudeSq_hasDerivAt_zero_eq_neg_viscous_of_nonlinearRow_zero
        initial index output (nonlinearRowsZero output outputMem)
  have summedDerivative := HasDerivAt.fun_sum waveDerivative
  have derivativeEq :
      (∑ output ∈ modes,
        -2 * (ν.coeff * integerWaveViscousMultiplier output) *
          complexCoordinateAmplitudeSq
            (current.contact.physicalState output)) =
        -2 * rate := by
    dsimp [rate, weightedInitialMass]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro output outputMem
    ring
  have derivativeAt : HasDerivAt physicalMass (-2 * rate) 0 := by
    rw [derivativeEq] at summedDerivative
    exact summedDerivative
  have pathAtZero : physicalMass 0 = initialMass := by
    dsimp [physicalMass, initialMass]
    apply Finset.sum_congr rfl
    intro output outputMem
    unfold actualWholeContinuousHeatDuhamelPath
      heatDuhamelComplexCoordinatePath
      intervalIntegralComplexCoordinatePath
    simp
  obtain ⟨actual, actualPos, actualLt, quantitativeDrop, retained⟩ :=
    exists_positive_time_quantitative_drop_and_persistence
      derivativeAt ratePos (pathAtZero.symm ▸ initialMassPos')
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
  let density : ℝ → ℝ := fun earlier =>
    finiteStateVorticityCoefficientEnstrophy modes
      (fullTrajectory earlier)
  have aggregateEq
      (earlier : ℝ)
      (earlierMem : earlier ∈ Icc (0 : ℝ) current.nextContact.time.1) :
      physicalMass earlier = density earlier := by
    unfold physicalMass density finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_congr rfl
    intro output outputMem
    have wholePathEq :=
      wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
        receipt output (modesNonzero output outputMem)
          (⟨earlier, earlierMem⟩ :
            Icc (0 : ℝ) current.nextContact.time.1)
    rw [← wholePathEq]
    have prefixEq := prefixTrajectoryEq earlier earlierMem
    unfold prefixTrajectory at prefixEq
    rw [wholeRestartReceiptPhysicalTrajectory,
      projIcc_of_mem receipt.requestedTimePos.le earlierMem] at prefixEq
    rw [prefixEq]
  have retainedFull :
      ∀ earlier ∈ Icc (0 : ℝ) actual,
        initialMass / 2 ≤ density earlier := by
    intro earlier earlierMem
    have earlierFullMem :
        earlier ∈ Icc (0 : ℝ) current.nextContact.time.1 :=
      ⟨earlierMem.1, earlierMem.2.trans actualLt.le⟩
    rw [← aggregateEq earlier earlierFullMem, ← pathAtZero]
    exact retained earlier earlierMem
  let wholeDensity : ℝ → ℝ := fun earlier =>
    wholeVorticityEuclideanMass (fullTrajectory earlier)
  have fullTrajectoryContinuous : Continuous fullTrajectory :=
    wholeRestartReceiptPhysicalTrajectory_continuous current.nextReceipt
  have densityContinuous : Continuous density := by
    unfold density finiteStateVorticityCoefficientEnstrophy
    apply continuous_finsetSum
    intro output outputMem
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
      actual * (initialMass / 2) ≤
        ∫ earlier in (0 : ℝ)..actual, density earlier := by
    have integrated :=
      intervalIntegral.integral_mono_on
        (μ := volume)
        actualPos.le
        (continuous_const.intervalIntegrable 0 actual)
        (densityContinuous.intervalIntegrable 0 actual)
        (fun earlier earlierMem => retainedFull earlier earlierMem)
    calc
      actual * (initialMass / 2) = actual * initialMass / 2 := by ring
      _ ≤ ∫ earlier in (0 : ℝ)..actual, density earlier := by
        simpa [intervalIntegral.integral_const,
          sub_zero, smul_eq_mul] using integrated
  have densityIntegralLeWhole :
      (∫ earlier in (0 : ℝ)..actual, density earlier) ≤
        ∫ earlier in (0 : ℝ)..actual, wholeDensity earlier := by
    exact intervalIntegral.integral_mono_on
      actualPos.le
      (densityContinuous.intervalIntegrable 0 actual)
      (wholeDensityContinuous.intervalIntegrable 0 actual)
      (fun earlier _ =>
        finiteStateVorticityCoefficientEnstrophy_le_wholeMass
          modes (fullTrajectory earlier))
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
  let charge := ν.coeff * actual * initialMass
  have chargePos : 0 < charge :=
    mul_pos (mul_pos ν.coeff_pos actualPos) initialMassPos'
  have chargeLe :
      charge ≤ wholeRestartNextKineticDissipationPayment initial index := by
    calc
      charge = 2 * ν.coeff * (actual * (initialMass / 2)) := by
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
      physicalMass actual =
        finiteStateVorticityCoefficientEnstrophy modes
          (current.nextContact.prefixReceipt.wholePath actualTime) := by
    rw [aggregateEq actual ⟨actualPos.le, actualLt.le⟩]
    unfold density finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_congr rfl
    intro output outputMem
    rw [← prefixTrajectoryEq actual
      ⟨actualPos.le, actualLt.le⟩]
    unfold prefixTrajectory wholeRestartReceiptPhysicalTrajectory
    rw [projIcc_of_mem receipt.requestedTimePos.le
      ⟨actualPos.le, actualLt.le⟩]
  refine ⟨⟨actual, actualPos, actualLt⟩, ?_⟩
  dsimp only
  refine ⟨chargePos, chargeLe, ?_⟩
  change
    ν.coeff * actual * weightedInitialMass <
      initialMass -
        finiteStateVorticityCoefficientEnstrophy modes
          (current.nextContact.prefixReceipt.wholePath actualTime)
  rw [← actualPathEq]
  calc
    ν.coeff * actual * weightedInitialMass = rate * actual := by
      dsimp [rate]
      ring
    _ < physicalMass 0 - physicalMass actual := quantitativeDrop
    _ = initialMass - physicalMass actual := by rw [pathAtZero]

/-- The earlier support-exclusion theorem is the crossing instance of the
finite-family nonlinear-row-zero consumer. -/
theorem
    wholeRestartCrossingActualWholeFiniteAmplitudeSq_generates_aggregateKineticCharge_of_gluing_zero
    { ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0)
    (modes : Finset IntegerWavevector)
    (modesOutside :
      ∀ output ∈ modes,
        output ∉ finiteVorticityPairOutputSupport
          (wholeRestartCrossingFiniteCoreModes initial index crossed))
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    ∃ actual : Ioo (0 : ℝ) (run initial index).nextContact.time.1,
      let initialMass :=
        ∑ output ∈ modes,
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output)
      let weightedInitialMass :=
        ∑ output ∈ modes,
          integerWaveViscousMultiplier output *
            complexCoordinateAmplitudeSq
              ((run initial index).contact.physicalState output)
      let charge := ν.coeff * actual.1 * initialMass
      0 < charge ∧
        charge ≤ wholeRestartNextKineticDissipationPayment initial index ∧
        ν.coeff * actual.1 * weightedInitialMass <
          initialMass -
            finiteStateVorticityCoefficientEnstrophy modes
              ((run initial index).nextContact.prefixReceipt.wholePath
                ⟨actual.1, actual.2.1.le, actual.2.2.le⟩) := by
  exact
    wholeRestartActualWholeFiniteAmplitudeSq_generates_aggregateKineticCharge_of_nonlinearRows_zero
      initial index modes
      (fun output outputMem =>
        wholeRestartCrossingWholeNonlinearCoefficientAt_eq_zero_of_gluing_zero_of_not_mem_pairOutput
          initial index crossed gluingZero output
          (modesOutside output outputMem))
      modesNonzero initialMassPos

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateCharge
end NavierStokes
end SaturationMonoid
