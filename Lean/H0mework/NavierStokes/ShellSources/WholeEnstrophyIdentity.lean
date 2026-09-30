import H0mework.NavierStokes.ShellSources.StrongContinuationEnergyLedger
import H0mework.NavierStokes.ShellSources.WholeReceiptEnergyWriteBack

/-!
# Whole enstrophy identity for source-generated strong continuation

The same generated strong receipt already carries an exact all-wave
nonlinear-minus-viscous energy ledger.  This module separates its viscous
part before any norm estimate is taken.

The coefficient carrier uses the sup norm on the three complex vorticity
coordinates, whereas physical coefficient enstrophy is their Euclidean
square sum.  We therefore generate a dedicated Euclidean gradient mass,
prove the exact viscous identity on that carrier, and only afterwards
compare it with the existing whole `L²_t H¹_x` carrier with the sharp
finite-coordinate factor used by the repository.

No cutoff, tail witness, endpoint state, energy identity, or nonlinear-work
summability certificate is accepted as input.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity

open scoped BigOperators ENNReal Interval

open Set
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport

noncomputable section

/-- Euclidean coordinate mass is controlled by the repository's
three-coordinate sup-norm carrier. -/
theorem complexCoordinateAmplitudeSq_le_three_mul_norm_sq
    (vector : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq vector ≤ 3 * ‖vector‖ ^ 2 := by
  unfold complexCoordinateAmplitudeSq
  calc
    (∑ coordinate : Coordinate,
        Complex.normSq (vector coordinate)) ≤
        ∑ _coordinate : Coordinate, ‖vector‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro coordinate coordinateMem
      rw [Complex.normSq_eq_norm_sq]
      exact
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
          (norm_le_pi_norm vector coordinate)
    _ = 3 * ‖vector‖ ^ 2 := by
      norm_num [Fin.sum_univ_succ]

section ActualStrongReceipt

variable
    {lineage : GeneratedIntegerShellInfiniteLineage}
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    {θLtOne : θ < 1}
    {criticalMargin :
      ∀ length : ℕ,
        criticalEnstrophyLatticeConstant *
            finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current length))
              (generatedComplexVorticityState
                (lineage.current length)
                (generatedSupport (lineage.current length))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2}
    {requestedTimePos : 0 < requestedTime}

/-- One nonzero row's exact Euclidean gradient density on the actual
continuous mild path. -/
def actualWaveEuclideanGradientDensity
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  integerWaveNormSq wave.1 *
    ∫ time in (0 : ℝ)..requestedTime,
      complexCoordinateAmplitudeSq
        (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
          receipt.toWholeContinuousMildReceipt wave.1 time)

/-- Complete Euclidean `L²_t H¹_x` mass of the same generated path. -/
def actualWholeEuclideanGradientMass
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) : ℝ :=
  ∑' wave : NonzeroIntegerWavevector,
    actualWaveEuclideanGradientDensity receipt wave

private theorem actualWaveHeatDuhamelPath_norm_sq_intervalIntegral_eq
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    (∫ time in (0 : ℝ)..requestedTime,
        ‖WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
          receipt.toWholeContinuousMildReceipt wave.1 time‖ ^ 2) =
      ‖fixedWaveSpaceTimeRestriction requestedTime wave.1
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ receipt.wholePath)‖ ^ 2 := by
  rw [fixedWaveSpaceTimeState_norm_sq_eq_integral]
  rw [← commonTime_integral_eq_intervalIntegral
    requestedTime requestedTimePos.le]
  let stateLp :=
    BoundedContinuousFunction.toLp 2
      (commonTimeMeasure requestedTime) ℂ receipt.wholePath
  have stateAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ receipt.wholePath
  have rowAE :=
    fixedWaveSpaceTimeRestriction_coeFn
      requestedTime wave.1 stateLp
  apply integral_congr_ae
  filter_upwards [stateAE, rowAE] with time stateEq rowEq
  have actualPathEq :=
    WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
      receipt.toWholeContinuousMildReceipt wave.1 wave.2 time
  change
    ‖WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
        receipt.toWholeContinuousMildReceipt wave.1 time.1‖ ^ 2 =
      ‖fixedWaveSpaceTimeRestriction requestedTime wave.1 stateLp time‖ ^ 2
  rw [rowEq]
  have statePoint : stateLp time = receipt.wholePath time := by
    simpa [stateLp] using stateEq
  rw [statePoint, actualPathEq]

private theorem actualWaveAmplitudeSq_intervalIntegral_nonneg
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    0 ≤
      ∫ time in (0 : ℝ)..requestedTime,
        complexCoordinateAmplitudeSq
          (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            receipt.toWholeContinuousMildReceipt wave.1 time) := by
  apply intervalIntegral.integral_nonneg requestedTimePos.le
  intro time timeMem
  exact complexCoordinateAmplitudeSq_nonneg _

private theorem actualWaveAmplitudeSq_intervalIntegral_le
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    (∫ time in (0 : ℝ)..requestedTime,
        complexCoordinateAmplitudeSq
          (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            receipt.toWholeContinuousMildReceipt wave.1 time)) ≤
      3 *
        ‖fixedWaveSpaceTimeRestriction requestedTime wave.1
          (BoundedContinuousFunction.toLp 2
            (commonTimeMeasure requestedTime) ℂ receipt.wholePath)‖ ^ 2 := by
  let path :=
    WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
      receipt.toWholeContinuousMildReceipt wave.1
  have pathAC :
      AbsolutelyContinuousOnInterval path 0 requestedTime :=
    heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
      (receipt.initialState wave.1)
      (ν.coeff * integerWaveViscousMultiplier wave.1)
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        receipt.toWholeContinuousMildReceipt wave.1)
      (by simp [requestedTimePos.le])
  have pathContinuous :
      ContinuousOn path (Icc (0 : ℝ) requestedTime) := by
    rw [← uIcc_of_le requestedTimePos.le]
    exact pathAC.continuousOn
  have amplitudeContinuous :
      ContinuousOn
        (fun time =>
          complexCoordinateAmplitudeSq (path time))
        (Icc (0 : ℝ) requestedTime) := by
    unfold complexCoordinateAmplitudeSq
    apply continuousOn_finsetSum
    intro coordinate coordinateMem
    exact
      Complex.continuous_normSq.comp_continuousOn
        ((ContinuousLinearMap.proj coordinate :
          ComplexCoordinateVector →L[ℝ] ℂ).continuous.comp_continuousOn
            pathContinuous)
  have normContinuous :
      ContinuousOn
        (fun time => 3 * ‖path time‖ ^ 2)
        (Icc (0 : ℝ) requestedTime) := by
    exact continuousOn_const.mul (pathContinuous.norm.pow 2)
  have integrated :=
    intervalIntegral.integral_mono_on
      requestedTimePos.le
      (amplitudeContinuous.intervalIntegrable_of_Icc (μ := volume)
        requestedTimePos.le)
      (normContinuous.intervalIntegrable_of_Icc (μ := volume)
        requestedTimePos.le)
      (fun time timeMem =>
        complexCoordinateAmplitudeSq_le_three_mul_norm_sq
          (path time))
  rw [intervalIntegral.integral_const_mul] at integrated
  rw [actualWaveHeatDuhamelPath_norm_sq_intervalIntegral_eq
    receipt wave] at integrated
  exact integrated

theorem actualWaveEuclideanGradientDensity_nonneg
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    0 ≤ actualWaveEuclideanGradientDensity receipt wave := by
  unfold actualWaveEuclideanGradientDensity
  exact mul_nonneg
    (integerWaveNormSq_nonneg wave.1)
    (actualWaveAmplitudeSq_intervalIntegral_nonneg receipt wave)

/-- The physical Euclidean gradient row is controlled by the existing
whole carrier row, without identifying the two norms. -/
theorem actualWaveEuclideanGradientDensity_le_three_carrier
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    actualWaveEuclideanGradientDensity receipt wave ≤
      3 *
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (BoundedContinuousFunction.toLp 2
            (commonTimeMeasure requestedTime) ℂ receipt.wholePath)
          wave.1 := by
  unfold actualWaveEuclideanGradientDensity
    wholeSpaceTimeVorticityGradientDensity
  have rowBound :=
    actualWaveAmplitudeSq_intervalIntegral_le receipt wave
  have frequencyNonneg := integerWaveNormSq_nonneg wave.1
  nlinarith

theorem summable_actualWaveEuclideanGradientDensity
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    Summable (actualWaveEuclideanGradientDensity receipt) := by
  have carrierSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        3 *
          wholeSpaceTimeVorticityGradientDensity requestedTime
            (BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ receipt.wholePath)
            wave.1 := by
    rw [receipt.wholePath_toLp_eq_stateLimit]
    exact
      (receipt.gradient_summable.mul_left 3).subtype
        { wave : IntegerWavevector | wave ≠ 0 }
  exact
    carrierSummable.of_nonneg_of_le
      (actualWaveEuclideanGradientDensity_nonneg receipt)
      (actualWaveEuclideanGradientDensity_le_three_carrier receipt)

/-- The generated Euclidean gradient mass is finite and bounded by the
already generated whole carrier gradient budget. -/
theorem actualWholeEuclideanGradientMass_le_three_carrier
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    actualWholeEuclideanGradientMass receipt ≤
      3 *
        wholeSpaceTimeVorticityGradientMass requestedTime
          (BoundedContinuousFunction.toLp 2
            (commonTimeMeasure requestedTime) ℂ receipt.wholePath) := by
  unfold actualWholeEuclideanGradientMass
  have carrierSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        3 *
          wholeSpaceTimeVorticityGradientDensity requestedTime
            (BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ receipt.wholePath)
            wave.1 := by
    rw [receipt.wholePath_toLp_eq_stateLimit]
    exact
      (receipt.gradient_summable.mul_left 3).subtype
        { wave : IntegerWavevector | wave ≠ 0 }
  calc
    (∑' wave : NonzeroIntegerWavevector,
        actualWaveEuclideanGradientDensity receipt wave) ≤
        ∑' wave : NonzeroIntegerWavevector,
          3 *
            wholeSpaceTimeVorticityGradientDensity requestedTime
              (BoundedContinuousFunction.toLp 2
                (commonTimeMeasure requestedTime) ℂ receipt.wholePath)
              wave.1 := by
      exact
        (summable_actualWaveEuclideanGradientDensity receipt).tsum_le_tsum
          (actualWaveEuclideanGradientDensity_le_three_carrier receipt)
          carrierSummable
    _ ≤
        ∑' wave : IntegerWavevector,
          3 *
            wholeSpaceTimeVorticityGradientDensity requestedTime
              (BoundedContinuousFunction.toLp 2
                (commonTimeMeasure requestedTime) ℂ receipt.wholePath)
              wave := by
      exact
        Summable.tsum_subtype_le
          (fun wave : IntegerWavevector =>
            3 *
              wholeSpaceTimeVorticityGradientDensity requestedTime
                (BoundedContinuousFunction.toLp 2
                  (commonTimeMeasure requestedTime) ℂ receipt.wholePath)
                wave)
          { wave : IntegerWavevector | wave ≠ 0 }
          (fun wave =>
            mul_nonneg (by norm_num)
              (wholeSpaceTimeVorticityGradientDensity_nonneg
                requestedTime _ wave))
          (by
            rw [receipt.wholePath_toLp_eq_stateLimit]
            exact receipt.gradient_summable.mul_left 3)
    _ =
        3 *
          wholeSpaceTimeVorticityGradientMass requestedTime
            (BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ receipt.wholePath) := by
      rw [tsum_mul_left]
      rfl

/-! ## Exact viscous separation before summation -/

/-- One actual nonzero row's positive viscous energy cost. -/
def actualWaveViscousEnergyCost
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  ∫ time in (0 : ℝ)..requestedTime,
    2 *
      complexCoordinateRealInner
        (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
          receipt.toWholeContinuousMildReceipt wave.1 time)
        (((ν.coeff * integerWaveViscousMultiplier wave.1 : ℝ)) •
          WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            receipt.toWholeContinuousMildReceipt wave.1 time)

/-- The actual rowwise viscous work is exactly the Euclidean gradient
density with the physical torus normalization. -/
theorem actualWaveViscousEnergyCost_eq
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    actualWaveViscousEnergyCost receipt wave =
      2 * ν.coeff * (2 * Real.pi) ^ 2 *
        actualWaveEuclideanGradientDensity receipt wave := by
  unfold actualWaveViscousEnergyCost
    actualWaveEuclideanGradientDensity
  calc
    (∫ time in (0 : ℝ)..requestedTime,
        2 *
          complexCoordinateRealInner
            (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
              receipt.toWholeContinuousMildReceipt wave.1 time)
            (((ν.coeff * integerWaveViscousMultiplier wave.1 : ℝ)) •
              WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                receipt.toWholeContinuousMildReceipt wave.1 time)) =
      ∫ time in (0 : ℝ)..requestedTime,
        (2 * ν.coeff * integerWaveViscousMultiplier wave.1) *
          complexCoordinateAmplitudeSq
            (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
              receipt.toWholeContinuousMildReceipt wave.1 time) := by
      apply intervalIntegral.integral_congr
      intro time timeMem
      let current :=
        WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
          receipt.toWholeContinuousMildReceipt wave.1 time
      change
        2 *
            complexCoordinateRealInner current
              ((ν.coeff * integerWaveViscousMultiplier wave.1 : ℝ) •
                current) =
          (2 * ν.coeff * integerWaveViscousMultiplier wave.1) *
            complexCoordinateAmplitudeSq current
      rw [
        ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.complexCoordinateRealInner_real_smul_right,
        complexCoordinateRealInner_self,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      ring
    _ =
        (2 * ν.coeff * integerWaveViscousMultiplier wave.1) *
          ∫ time in (0 : ℝ)..requestedTime,
            complexCoordinateAmplitudeSq
              (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                receipt.toWholeContinuousMildReceipt wave.1 time) := by
      rw [intervalIntegral.integral_const_mul]
    _ =
        2 * ν.coeff * (2 * Real.pi) ^ 2 *
          (integerWaveNormSq wave.1 *
            ∫ time in (0 : ℝ)..requestedTime,
              complexCoordinateAmplitudeSq
                (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                  receipt.toWholeContinuousMildReceipt wave.1 time)) := by
      unfold integerWaveViscousMultiplier
      ring

theorem actualWaveViscousEnergyCost_nonneg
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    0 ≤ actualWaveViscousEnergyCost receipt wave := by
  rw [actualWaveViscousEnergyCost_eq]
  have coefficientNonneg :
      0 ≤ 2 * ν.coeff * (2 * Real.pi) ^ 2 :=
    mul_nonneg
      (mul_nonneg (by norm_num) ν.coeff_pos.le)
      (sq_nonneg (2 * Real.pi))
  exact
    mul_nonneg
      coefficientNonneg
      (actualWaveEuclideanGradientDensity_nonneg receipt wave)

theorem summable_actualWaveViscousEnergyCost
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    Summable (actualWaveViscousEnergyCost receipt) := by
  exact
    ((summable_actualWaveEuclideanGradientDensity receipt).mul_left
      (2 * ν.coeff * (2 * Real.pi) ^ 2)).congr
        (fun wave => (actualWaveViscousEnergyCost_eq receipt wave).symm)

/-- All rowwise viscous costs assemble exactly into the generated Euclidean
gradient mass. -/
theorem tsum_actualWaveViscousEnergyCost_eq
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    (∑' wave : NonzeroIntegerWavevector,
        actualWaveViscousEnergyCost receipt wave) =
      2 * ν.coeff * (2 * Real.pi) ^ 2 *
        actualWholeEuclideanGradientMass receipt := by
  rw [show
      (fun wave : NonzeroIntegerWavevector =>
        actualWaveViscousEnergyCost receipt wave) =
        (fun wave =>
          (2 * ν.coeff * (2 * Real.pi) ^ 2) *
            actualWaveEuclideanGradientDensity receipt wave) by
        funext wave
        exact actualWaveViscousEnergyCost_eq receipt wave]
  rw [(summable_actualWaveEuclideanGradientDensity receipt).tsum_mul_left]
  rfl

/-! ## Whole nonlinear work and exact enstrophy identity -/

/-- The actual nonlinear work obtained by restoring the separately
generated viscous cost to the nonlinear-minus-viscous tangent ledger.  The
addition occurs rowwise before the infinite sum. -/
def actualWaveNonlinearEnergyWork
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  actualWaveEnergyWork receipt wave +
    actualWaveViscousEnergyCost receipt wave

/-- A continuous coefficient row paired with an interval-integrable row is
interval-integrable.  This general lemma is shared by whole-flow work
transports; it is independent of any source certificate. -/
theorem complexCoordinateRealInner_intervalIntegrable
    {left right : ℝ → ComplexCoordinateVector}
    {a b : ℝ}
    (leftContinuous : ContinuousOn left [[a, b]])
    (rightIntegrable : IntervalIntegrable right volume a b) :
    IntervalIntegrable
      (fun time =>
        complexCoordinateRealInner (left time) (right time))
      volume a b := by
  have coordinateIntegrable :
      ∀ coordinate : Coordinate,
        IntervalIntegrable
          (fun time =>
            (left time coordinate).re *
                (right time coordinate).re +
              (left time coordinate).im *
                (right time coordinate).im)
          volume a b := by
    intro coordinate
    let realCoordinate :
        ComplexCoordinateVector →L[ℝ] ℝ :=
      Complex.reCLM.comp
        (ContinuousLinearMap.proj coordinate)
    let imaginaryCoordinate :
        ComplexCoordinateVector →L[ℝ] ℝ :=
      Complex.imCLM.comp
        (ContinuousLinearMap.proj coordinate)
    have leftRealContinuous :
        ContinuousOn
          (fun time => (left time coordinate).re)
          [[a, b]] := by
      have mapped :=
        realCoordinate.continuous.comp_continuousOn
          leftContinuous
      change
        ContinuousOn
          (fun time => realCoordinate (left time))
          [[a, b]] at mapped
      simpa only [realCoordinate,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply,
        Complex.reCLM_apply] using mapped
    have leftImaginaryContinuous :
        ContinuousOn
          (fun time => (left time coordinate).im)
          [[a, b]] := by
      have mapped :=
        imaginaryCoordinate.continuous.comp_continuousOn
          leftContinuous
      change
        ContinuousOn
          (fun time => imaginaryCoordinate (left time))
          [[a, b]] at mapped
      simpa only [imaginaryCoordinate,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply,
        Complex.imCLM_apply] using mapped
    have rightRealIntegrable :
        IntervalIntegrable
          (fun time => (right time coordinate).re)
          volume a b := by
      constructor
      · have mapped :=
          realCoordinate.integrableOn_comp rightIntegrable.1
        change
          IntegrableOn
            (fun time => realCoordinate (right time))
            (Ioc a b) volume at mapped
        simpa only [realCoordinate,
          ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply,
          Complex.reCLM_apply] using mapped
      · have mapped :=
          realCoordinate.integrableOn_comp rightIntegrable.2
        change
          IntegrableOn
            (fun time => realCoordinate (right time))
            (Ioc b a) volume at mapped
        simpa only [realCoordinate,
          ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply,
          Complex.reCLM_apply] using mapped
    have rightImaginaryIntegrable :
        IntervalIntegrable
          (fun time => (right time coordinate).im)
          volume a b := by
      constructor
      · have mapped :=
          imaginaryCoordinate.integrableOn_comp
            rightIntegrable.1
        change
          IntegrableOn
            (fun time => imaginaryCoordinate (right time))
            (Ioc a b) volume at mapped
        simpa only [imaginaryCoordinate,
          ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply,
          Complex.imCLM_apply] using mapped
      · have mapped :=
          imaginaryCoordinate.integrableOn_comp
            rightIntegrable.2
        change
          IntegrableOn
            (fun time => imaginaryCoordinate (right time))
            (Ioc b a) volume at mapped
        simpa only [imaginaryCoordinate,
          ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.proj_apply,
          Complex.imCLM_apply] using mapped
    exact
      (rightRealIntegrable.continuousOn_mul
          leftRealContinuous).add
        (rightImaginaryIntegrable.continuousOn_mul
          leftImaginaryContinuous)
  unfold complexCoordinateRealInner
  exact
    IntervalIntegrable.sum Finset.univ
      (fun coordinate _coordinateMem =>
        coordinateIntegrable coordinate)

/--
The restored rowwise nonlinear work is literally the interval integral of
the actual nonlinear Fourier coefficient paired with the same actual mild
path.  The viscous row is removed only by the exact update-law split; no
norm estimate enters this identification.
-/
theorem actualWaveNonlinearEnergyWork_eq_intervalIntegral
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : NonzeroIntegerWavevector) :
    actualWaveNonlinearEnergyWork receipt wave =
      ∫ time in (0 : ℝ)..requestedTime,
        2 *
          complexCoordinateRealInner
            (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
              receipt.toWholeContinuousMildReceipt wave.1 time)
            (WholeContinuousMildReceipt.actualWaveNonlinearExtension
              receipt.toWholeContinuousMildReceipt wave.1 time) := by
  let path :=
    WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
      receipt.toWholeContinuousMildReceipt wave.1
  let nonlinear :=
    WholeContinuousMildReceipt.actualWaveNonlinearExtension
      receipt.toWholeContinuousMildReceipt wave.1
  let viscousCoefficient :=
    ν.coeff * integerWaveViscousMultiplier wave.1
  have pathAC :
      AbsolutelyContinuousOnInterval path 0 requestedTime :=
    heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
      (receipt.initialState wave.1)
      viscousCoefficient
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        receipt.toWholeContinuousMildReceipt wave.1)
      (by simp [requestedTimePos.le])
  have pathContinuous :
      ContinuousOn path [[(0 : ℝ), requestedTime]] :=
    pathAC.continuousOn
  have nonlinearIntegrable :
      IntervalIntegrable nonlinear volume 0 requestedTime :=
    WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
      receipt.toWholeContinuousMildReceipt wave.1
  have viscousIntegrable :
      IntervalIntegrable
        (fun time => viscousCoefficient • path time)
        volume 0 requestedTime := by
    have pathContinuousIcc :
        ContinuousOn path (Icc (0 : ℝ) requestedTime) := by
      simpa only [uIcc_of_le requestedTimePos.le] using
        pathContinuous
    exact
      (pathContinuousIcc.const_smul
        viscousCoefficient).intervalIntegrable_of_Icc
        requestedTimePos.le
  have nonlinearPairingIntegrable :
      IntervalIntegrable
        (fun time =>
          2 * complexCoordinateRealInner
            (path time) (nonlinear time))
        volume 0 requestedTime :=
    (complexCoordinateRealInner_intervalIntegrable
      pathContinuous nonlinearIntegrable).const_mul 2
  have viscousPairingIntegrable :
      IntervalIntegrable
        (fun time =>
          2 * complexCoordinateRealInner
            (path time) (viscousCoefficient • path time))
        volume 0 requestedTime :=
    (complexCoordinateRealInner_intervalIntegrable
      pathContinuous viscousIntegrable).const_mul 2
  have netIntegral :
      (∫ time in (0 : ℝ)..requestedTime,
          2 * complexCoordinateRealInner
            (path time)
            (nonlinear time -
              viscousCoefficient • path time)) =
        (∫ time in (0 : ℝ)..requestedTime,
            2 * complexCoordinateRealInner
              (path time) (nonlinear time)) -
          ∫ time in (0 : ℝ)..requestedTime,
            2 * complexCoordinateRealInner
              (path time)
              (viscousCoefficient • path time) := by
    rw [← intervalIntegral.integral_sub
      nonlinearPairingIntegrable viscousPairingIntegrable]
    apply intervalIntegral.integral_congr
    intro time timeMem
    change
      2 * complexCoordinateRealInner
          (path time)
          (nonlinear time -
            viscousCoefficient • path time) =
        2 * complexCoordinateRealInner
            (path time) (nonlinear time) -
          2 * complexCoordinateRealInner
            (path time)
            (viscousCoefficient • path time)
    rw [complexCoordinateRealInner_sub_right]
    ring
  unfold actualWaveNonlinearEnergyWork actualWaveEnergyWork
    actualWaveViscousEnergyCost
  change
    (∫ time in (0 : ℝ)..requestedTime,
        2 * complexCoordinateRealInner
          (path time)
          (nonlinear time -
            viscousCoefficient • path time)) +
        (∫ time in (0 : ℝ)..requestedTime,
          2 * complexCoordinateRealInner
            (path time)
            (viscousCoefficient • path time)) =
      ∫ time in (0 : ℝ)..requestedTime,
        2 * complexCoordinateRealInner
          (path time) (nonlinear time)
  rw [netIntegral]
  ring

theorem summable_actualWaveNonlinearEnergyWork
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    Summable (actualWaveNonlinearEnergyWork receipt) := by
  unfold actualWaveNonlinearEnergyWork
  exact
    (summable_actualWaveEnergyWork receipt).add
      (summable_actualWaveViscousEnergyCost receipt)

/-- Exact whole-carrier coefficient enstrophy identity on the same actual
source-generated mild path.

The nonlinear work is summed only after the viscous row has been restored,
so no triangle inequality or nonlinear tail estimate is used in the
identity. -/
theorem whole_enstrophy_identity
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    puncturedWholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime,
              ⟨requestedTimePos.le, le_rfl⟩⟩) +
        2 * ν.coeff * (2 * Real.pi) ^ 2 *
          actualWholeEuclideanGradientMass receipt =
      puncturedWholeVorticityEuclideanMass receipt.initialState +
        ∑' wave : NonzeroIntegerWavevector,
          actualWaveNonlinearEnergyWork receipt wave := by
  have energyIdentity :=
    tsum_actualWaveEnergyWork_eq receipt
  have viscousIdentity :=
    tsum_actualWaveViscousEnergyCost_eq receipt
  have nonlinearSplit :
      (∑' wave : NonzeroIntegerWavevector,
          actualWaveNonlinearEnergyWork receipt wave) =
        (∑' wave : NonzeroIntegerWavevector,
          actualWaveEnergyWork receipt wave) +
        ∑' wave : NonzeroIntegerWavevector,
          actualWaveViscousEnergyCost receipt wave := by
    unfold actualWaveNonlinearEnergyWork
    exact
      (Summable.tsum_add
        (summable_actualWaveEnergyWork receipt)
        (summable_actualWaveViscousEnergyCost receipt))
  rw [nonlinearSplit, energyIdentity, viscousIdentity]
  ring

/--
Exact source/PDE enstrophy write-back on one carrier.

The source-generated receipt series is the actual initial mass term, the
viscous term is the whole Euclidean gradient mass of the same mild path,
and every nonlinear row is the literal interval pairing with that path.
No cutoff, frequency cover, tail-silence witness, or energy identity is
supplied by the caller.
-/
theorem whole_enstrophy_identity_source_receipt_writeback
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    puncturedWholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime,
              ⟨requestedTimePos.le, le_rfl⟩⟩) +
        2 * ν.coeff * (2 * Real.pi) ^ 2 *
          actualWholeEuclideanGradientMass receipt =
      (coefficientCarrierNormSq
          (generatedCoefficientCarrier
            (lineage.current 0)) +
        ∑' index : ℕ, lineage.receiptQuantum index) +
      ∑' wave : NonzeroIntegerWavevector,
        ∫ time in (0 : ℝ)..requestedTime,
          2 *
            complexCoordinateRealInner
              (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                receipt.toWholeContinuousMildReceipt wave.1 time)
              (WholeContinuousMildReceipt.actualWaveNonlinearExtension
                receipt.toWholeContinuousMildReceipt wave.1 time) := by
  calc
    puncturedWholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime,
              ⟨requestedTimePos.le, le_rfl⟩⟩) +
        2 * ν.coeff * (2 * Real.pi) ^ 2 *
          actualWholeEuclideanGradientMass receipt =
      puncturedWholeVorticityEuclideanMass receipt.initialState +
        ∑' wave : NonzeroIntegerWavevector,
          actualWaveNonlinearEnergyWork receipt wave :=
      whole_enstrophy_identity receipt
    _ =
      (coefficientCarrierNormSq
          (generatedCoefficientCarrier
            (lineage.current 0)) +
        ∑' index : ℕ, lineage.receiptQuantum index) +
      ∑' wave : NonzeroIntegerWavevector,
        ∫ time in (0 : ℝ)..requestedTime,
          2 *
            complexCoordinateRealInner
              (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                receipt.toWholeContinuousMildReceipt wave.1 time)
              (WholeContinuousMildReceipt.actualWaveNonlinearExtension
                receipt.toWholeContinuousMildReceipt wave.1 time) := by
      rw [
        initialState_puncturedEuclideanMass_eq_seed_add_receiptQuantum_tsum
          receipt.toInfiniteMildDuhamelForcingReceipt]
      congr 1
      exact
        tsum_congr fun wave =>
          actualWaveNonlinearEnergyWork_eq_intervalIntegral
            receipt wave

/-- The exact Euclidean dissipation in the whole identity is bounded by
the already generated cutoff-free critical gradient budget. -/
theorem actualWholeEuclideanGradientMass_le_generated
    (receipt :
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    actualWholeEuclideanGradientMass receipt ≤
      3 *
        (((1 / 2 : ℝ) *
            criticalCoefficientEnstrophyCeiling ν θ) /
          criticalEnstrophyAbsorptionCoefficient θ ν) := by
  calc
    actualWholeEuclideanGradientMass receipt ≤
        3 *
          wholeSpaceTimeVorticityGradientMass requestedTime
            (BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ receipt.wholePath) :=
      actualWholeEuclideanGradientMass_le_three_carrier receipt
    _ ≤
        3 *
          (((1 / 2 : ℝ) *
              criticalCoefficientEnstrophyCeiling ν θ) /
            criticalEnstrophyAbsorptionCoefficient θ ν) := by
      gcongr
      exact receipt.wholePath_gradient_mass_le

end ActualStrongReceipt

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity
end NavierStokes
end SaturationMonoid
