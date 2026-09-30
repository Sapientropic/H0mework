import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.AddCircleMulti
import H0mework.NavierStokes.Fourier.NonlinearOutputCompiler
import H0mework.NavierStokes.WholeSpace.WholeContinuousMildSerrinUniqueness

/-!
# Weak action of an actual whole mild/Serrin receipt

The rowwise absolute-continuity and unforced tangent laws carried by an
actual `WholeContinuousMildSerrinReceipt` already imply its fixed-wave weak
equation.  This file performs that conversion on the receipt's existing
whole space-time carrier.  It introduces no weak-solution certificate,
source lineage, cutoff, or auxiliary trajectory.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinWeakAction

open scoped ContDiff ENNReal FourierTransform SchwartzMap

open Complex Filter Function LineDeriv MeasureTheory Real Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientPhysicalFourierCoordinateObserver
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

private theorem commonTimeZeroExtension_intervalIntegrable_of_integrable
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (requestedTime : ℝ) (requestedTimeNonneg : 0 ≤ requestedTime)
    (value : Icc (0 : ℝ) requestedTime → E)
    (valueIntegrable :
      Integrable value (commonTimeMeasure requestedTime)) :
    IntervalIntegrable
      (commonTimeZeroExtension requestedTime value)
      volume 0 requestedTime := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le requestedTimeNonneg,
    integrableOn_iff_comap_subtypeVal measurableSet_Icc]
  have measureEq :
      commonTimeMeasure requestedTime =
        Measure.comap
          (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
          volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  rw [← measureEq]
  apply valueIntegrable.congr
  filter_upwards with time
  simp only [Function.comp_apply]
  rw [commonTimeZeroExtension_of_mem
    requestedTime value time.1 time.property]

private theorem fixedL2ScalarL2IntegralCLM_eq_intervalIntegral_of_ae
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (scalar : ℝ → ℂ)
    (scalarContinuous :
      ContinuousOn scalar (Icc (0 : ℝ) requestedTime))
    (row :
      MeasureTheory.Lp ComplexCoordinateVector 2
        (commonTimeMeasure requestedTime))
    (representative : ℝ → ComplexCoordinateVector)
    (rowAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        row time = representative time.1) :
    fixedL2ScalarL2IntegralCLM requestedTime
        (restrictedScalarL2
          requestedTime scalar scalarContinuous)
        row =
      ∫ time in (0 : ℝ)..requestedTime,
        scalar time • representative time := by
  let scalarLp :=
    restrictedScalarL2 requestedTime scalar scalarContinuous
  have scalarAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (restrictedScalarBoundedPath
        requestedTime scalar scalarContinuous)
  have productAE :
      ⇑(scalarLp • row :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑scalarLp • ⇑row :=
    MeasureTheory.Lp.coeFn_lpSMul scalarLp row
  change
    (MeasureTheory.L1.integralCLM' ℂ)
        (scalarLp • row) =
      _
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  calc
    (∫ time,
        (scalarLp • row) time
      ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          scalar time.1 • representative time.1
        ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards
        [productAE, scalarAE, rowAE] with
        time productEq scalarEq rowEq
      rw [productEq]
      change scalarLp time • row time = _
      have scalarPoint : scalarLp time = scalar time.1 := by
        have scalarPoint' :
            scalarLp time =
              restrictedScalarBoundedPath
                requestedTime scalar scalarContinuous time := by
          simpa [scalarLp, restrictedScalarL2] using scalarEq
        exact scalarPoint'.trans rfl
      rw [scalarPoint, rowEq]
    _ =
        ∫ time in (0 : ℝ)..requestedTime,
          scalar time • representative time :=
      commonTime_integral_eq_intervalIntegral_vector
        requestedTime requestedTimeNonneg
        (fun time => scalar time • representative time)

private theorem fixedLInfScalarL1IntegralCLM_eq_intervalIntegral_of_ae
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (scalar : ℝ → ℂ)
    (scalarContinuous :
      ContinuousOn scalar (Icc (0 : ℝ) requestedTime))
    (row :
      MeasureTheory.Lp ComplexCoordinateVector 1
        (commonTimeMeasure requestedTime))
    (representative : ℝ → ComplexCoordinateVector)
    (rowAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        row time = representative time.1) :
    fixedLInfScalarL1IntegralCLM requestedTime
        (restrictedScalarLInf
          requestedTime scalar scalarContinuous)
        row =
      ∫ time in (0 : ℝ)..requestedTime,
        scalar time • representative time := by
  let scalarLp :=
    restrictedScalarLInf requestedTime scalar scalarContinuous
  have scalarAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (∞ : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ
      (restrictedScalarBoundedPath
        requestedTime scalar scalarContinuous)
  have productAE :
      ⇑(scalarLp • row :
          MeasureTheory.Lp ComplexCoordinateVector 1
            (commonTimeMeasure requestedTime)) =ᵐ[
          commonTimeMeasure requestedTime]
        ⇑scalarLp • ⇑row :=
    MeasureTheory.Lp.coeFn_lpSMul scalarLp row
  change
    (MeasureTheory.L1.integralCLM' ℂ)
        (scalarLp • row) =
      _
  rw [← MeasureTheory.L1.integral_eq' ℂ,
    MeasureTheory.L1.integral_eq_integral]
  calc
    (∫ time,
        (scalarLp • row) time
      ∂(commonTimeMeasure requestedTime)) =
        ∫ time : Icc (0 : ℝ) requestedTime,
          scalar time.1 • representative time.1
        ∂(commonTimeMeasure requestedTime) := by
      apply integral_congr_ae
      filter_upwards
        [productAE, scalarAE, rowAE] with
        time productEq scalarEq rowEq
      rw [productEq]
      change scalarLp time • row time = _
      have scalarPoint : scalarLp time = scalar time.1 := by
        have scalarPoint' :
            scalarLp time =
              restrictedScalarBoundedPath
                requestedTime scalar scalarContinuous time := by
          simpa [scalarLp, restrictedScalarLInf] using scalarEq
        exact scalarPoint'.trans rfl
      rw [scalarPoint, rowEq]
    _ =
        ∫ time in (0 : ℝ)..requestedTime,
          scalar time • representative time :=
      commonTime_integral_eq_intervalIntegral_vector
        requestedTime requestedTimeNonneg
        (fun time => scalar time • representative time)

/--
The fixed-wave weak action of an actual whole mild/Serrin receipt is the
endpoint difference of the tested Fourier row.

The identity is generated from the receipt's actual row absolute continuity,
almost-everywhere derivative, and unforced tangent law.
-/
theorem WholeContinuousMildSerrinReceipt.fixedWaveWeakAction_eq_boundary
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test) :
    fixedWaveWeakAction
        requestedTime ν.coeff wave
        (restrictedScalarL2 requestedTime test
          testSmooth.continuous.continuousOn)
        (restrictedScalarL2 requestedTime (deriv test)
          (testSmooth.continuous_deriv (by simp)).continuousOn)
        (restrictedScalarLInf requestedTime test
          testSmooth.continuous.continuousOn)
        receipt.stateLimit
        (transverseSpaceTimeNonlinearRow
          receipt.transverseLimit wave) =
      test requestedTime • receipt.rowExtension wave waveNe requestedTime -
        test 0 • receipt.rowExtension wave waveNe 0 := by
  let stateRow :=
    fixedWaveSpaceTimeRestriction
      requestedTime wave receipt.stateLimit
  let rowPath := receipt.rowExtension wave waveNe
  let rowTangentExtension :=
    commonTimeZeroExtension requestedTime
      (receipt.rowTangent wave waveNe)
  let nonlinearFunction :=
    transverseSpaceTimeNonlinearRowFunction
      receipt.transverseLimit wave
  let nonlinearExtension :=
    commonTimeZeroExtension requestedTime nonlinearFunction
  let nonlinearRow :=
    transverseSpaceTimeNonlinearRow receipt.transverseLimit wave
  let viscousCoefficient : ℝ :=
    ν.coeff * integerWaveViscousMultiplier wave
  have stateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        receipt.stateLimit time = receipt.wholePath time := by
    rw [← receipt.wholePath_toLp_eq_stateLimit]
    exact
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure requestedTime)
        ℂ receipt.wholePath
  have rowAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        stateRow time = rowPath time.1 := by
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.stateLimit,
      stateAE] with time rowEq stateEq
    calc
      stateRow time = receipt.stateLimit time wave := by
        simpa [stateRow] using rowEq
      _ = receipt.wholePath time wave := by rw [stateEq]
      _ = rowPath time.1 := by
        simpa [rowPath] using
          (receipt.rowExtension_on_interval wave waveNe time).symm
  have nonlinearAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        nonlinearRow time = nonlinearExtension time.1 := by
    filter_upwards [
      transverseSpaceTimeNonlinearRow_coeFn
        receipt.transverseLimit wave] with time nonlinearEq
    rw [nonlinearEq]
    simp [nonlinearExtension,
      nonlinearFunction, commonTimeZeroExtension_of_mem]
  have rowTangentIntegrable :
      Integrable
        (receipt.rowTangent wave waveNe)
        (commonTimeMeasure requestedTime) := by
    let wholeTangentRow :=
      fixedWaveSpaceTimeRestriction
        requestedTime wave receipt.wholeTangent
    have wholeTangentRowIntegrable :
        Integrable
          (fun time : Icc (0 : ℝ) requestedTime =>
            wholeTangentRow time)
          (commonTimeMeasure requestedTime) := by
      have onUniv :=
        integrableOn_Lp_of_measure_ne_top
          wholeTangentRow fact_one_le_two_ennreal.elim
          (measure_ne_top
            (commonTimeMeasure requestedTime) Set.univ)
      simpa only [integrableOn_univ] using onUniv
    have scaledIntegrable :=
      Integrable.smul
        (Real.sqrt
          (integerWaveViscousMultiplier wave) : ℂ)
        wholeTangentRowIntegrable
    apply scaledIntegrable.congr
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.wholeTangent,
      receipt.rowTangent_eq_wholeTangent_ae
        wave waveNe] with time wholeTangentRowEq tangentEq
    change
      (Real.sqrt
        (integerWaveViscousMultiplier wave) : ℂ) •
          wholeTangentRow time =
        receipt.rowTangent wave waveNe time
    rw [wholeTangentRowEq]
    exact tangentEq
  have rowTangentExtensionIntegrable :
      IntervalIntegrable rowTangentExtension
        volume 0 requestedTime := by
    exact
      commonTimeZeroExtension_intervalIntegrable_of_integrable
        requestedTime receipt.requestedTimePos.le
        (receipt.rowTangent wave waveNe)
        rowTangentIntegrable
  have rowPathIntegrable :
      IntervalIntegrable rowPath volume 0 requestedTime := by
    apply ContinuousOn.intervalIntegrable_of_Icc
      receipt.requestedTimePos.le
    simpa [rowPath, uIcc_of_le receipt.requestedTimePos.le] using
      (receipt.rowExtension_absolutelyContinuous
        wave waveNe).continuousOn
  have testContinuousU :
      ContinuousOn test (uIcc (0 : ℝ) requestedTime) := by
    simpa [uIcc_of_le receipt.requestedTimePos.le] using
      testSmooth.continuous.continuousOn
  have testDerivativeContinuousU :
      ContinuousOn (deriv test)
        (uIcc (0 : ℝ) requestedTime) := by
    simpa [uIcc_of_le receipt.requestedTimePos.le] using
      (testSmooth.continuous_deriv (by simp)).continuousOn
  have testTangentIntegrable :
      IntervalIntegrable
        (fun time => test time • rowTangentExtension time)
        volume 0 requestedTime :=
    rowTangentExtensionIntegrable.continuousOn_smul testContinuousU
  have derivativeRowIntegrable :
      IntervalIntegrable
        (fun time => deriv test time • rowPath time)
        volume 0 requestedTime :=
    rowPathIntegrable.continuousOn_smul testDerivativeContinuousU
  have productPathAC :
      AbsolutelyContinuousOnInterval
        (fun time => test time • rowPath time)
        0 requestedTime := by
    exact
      ((testSmooth.of_le (by simp)).contDiffOn
        |>.absolutelyContinuousOnInterval).smul
          (receipt.rowExtension_absolutelyContinuous
            wave waveNe)
  have productPathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc (0 : ℝ) requestedTime →
          HasDerivAt
            (fun actual => test actual • rowPath actual)
            (test time • rowTangentExtension time +
              deriv test time • rowPath time)
            time := by
    filter_upwards [
      receipt.rowExtension_ae_hasDerivAt
        wave waveNe] with time rowDerivative
    intro timeMem
    change
      HasDerivAt
        (test • receipt.rowExtension wave waveNe)
        (test time •
            commonTimeZeroExtension requestedTime
              (receipt.rowTangent wave waveNe) time +
          deriv test time • receipt.rowExtension wave waveNe time)
        time
    exact
      ((testSmooth.differentiable (by simp)) time).hasDerivAt.smul
        (rowDerivative timeMem)
  have productIntegralBoundary :
      (∫ time in (0 : ℝ)..requestedTime,
          test time • rowTangentExtension time +
            deriv test time • rowPath time) =
        test requestedTime • rowPath requestedTime -
          test 0 • rowPath 0 := by
    have update :=
      path_sub_eq_intervalIntegral
        productPathAC
        (testTangentIntegrable.add derivativeRowIntegrable)
        productPathDerivative
        requestedTime
        (by simp)
    exact update.symm
  have integrationByParts :
      (∫ time in (0 : ℝ)..requestedTime,
          test time • rowTangentExtension time) +
      (∫ time in (0 : ℝ)..requestedTime,
          deriv test time • rowPath time) =
        test requestedTime • rowPath requestedTime -
          test 0 • rowPath 0 := by
    simpa only [
      intervalIntegral.integral_add
        testTangentIntegrable derivativeRowIntegrable] using
      productIntegralBoundary
  have tangentIntegralSplit :
      (∫ time in (0 : ℝ)..requestedTime,
          test time • rowTangentExtension time) =
        (∫ time in (0 : ℝ)..requestedTime,
          test time • nonlinearExtension time) -
        ∫ time in (0 : ℝ)..requestedTime,
          test time •
            (viscousCoefficient • rowPath time) := by
    have nonlinearExtensionIntegrable :
        IntervalIntegrable nonlinearExtension
          volume 0 requestedTime := by
      apply
        commonTimeZeroExtension_intervalIntegrable_of_integrable
          requestedTime receipt.requestedTimePos.le
          nonlinearFunction
      simpa only [nonlinearFunction] using
        transverseSpaceTimeNonlinearRowFunction_integrable
          receipt.transverseLimit wave
    have rowPathContinuous :
        ContinuousOn rowPath
          (Icc (0 : ℝ) requestedTime) := by
      simpa [rowPath, uIcc_of_le receipt.requestedTimePos.le] using
        (receipt.rowExtension_absolutelyContinuous
          wave waveNe).continuousOn
    have viscousPathIntegrable :
        IntervalIntegrable
          (fun time =>
            viscousCoefficient • rowPath time)
          volume 0 requestedTime := by
      exact ContinuousOn.intervalIntegrable_of_Icc
        receipt.requestedTimePos.le
        (rowPathContinuous.const_smul viscousCoefficient)
    have testNonlinearIntegrable :
        IntervalIntegrable
          (fun time =>
            test time • nonlinearExtension time)
          volume 0 requestedTime :=
      nonlinearExtensionIntegrable.continuousOn_smul
        testContinuousU
    have testViscousIntegrable :
        IntervalIntegrable
          (fun time =>
            test time •
              (viscousCoefficient • rowPath time))
          volume 0 requestedTime :=
      viscousPathIntegrable.continuousOn_smul
        testContinuousU
    have tangentIntegralEqCombined :
        (∫ time in (0 : ℝ)..requestedTime,
            test time • rowTangentExtension time) =
          ∫ time in (0 : ℝ)..requestedTime,
            test time •
              (nonlinearExtension time -
                viscousCoefficient • rowPath time) := by
      rw [
        ← commonTime_integral_eq_intervalIntegral_vector
          requestedTime receipt.requestedTimePos.le
          (fun time =>
            test time • rowTangentExtension time),
        ← commonTime_integral_eq_intervalIntegral_vector
          requestedTime receipt.requestedTimePos.le
          (fun time =>
            test time •
              (nonlinearExtension time -
                viscousCoefficient • rowPath time))]
      apply integral_congr_ae
      filter_upwards [
        receipt.rowTangent_eq_unforced_ae
          wave waveNe] with time tangentEq
      rw [show
        rowTangentExtension time.1 =
          receipt.rowTangent wave waveNe time by
            change
              commonTimeZeroExtension requestedTime
                  (receipt.rowTangent wave waveNe) time.1 =
                receipt.rowTangent wave waveNe time
            exact commonTimeZeroExtension_of_mem
              requestedTime (receipt.rowTangent wave waveNe)
              time.1 time.property]
      rw [show
        nonlinearExtension time.1 =
          nonlinearFunction time by
            change
              commonTimeZeroExtension requestedTime
                  nonlinearFunction time.1 =
                nonlinearFunction time
            exact commonTimeZeroExtension_of_mem
              requestedTime nonlinearFunction
              time.1 time.property]
      rw [show
        rowPath time.1 = receipt.wholePath time wave by
          simpa only [rowPath] using
            receipt.rowExtension_on_interval wave waveNe time]
      change
        test time.1 • receipt.rowTangent wave waveNe time =
          test time.1 •
            (wholeStateVorticityNonlinearCoefficientAt
                (receipt.transverseLimit time).1 wave -
              viscousCoefficient • receipt.wholePath time wave)
      rw [tangentEq,
        ← wholeStateVorticityBilinearCoefficientAt_self]
    rw [tangentIntegralEqCombined,
      ← intervalIntegral.integral_sub
        testNonlinearIntegrable testViscousIntegrable]
    apply intervalIntegral.integral_congr
    intro time _
    change
      test time •
          (nonlinearExtension time -
            viscousCoefficient • rowPath time) =
        test time • nonlinearExtension time -
          test time • (viscousCoefficient • rowPath time)
    exact smul_sub _ _ _
  have derivativeAction :
      fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn)
          stateRow =
        ∫ time in (0 : ℝ)..requestedTime,
          deriv test time • rowPath time :=
    fixedL2ScalarL2IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le
      (deriv test)
      (testSmooth.continuous_deriv (by simp)).continuousOn
      stateRow rowPath rowAE
  have nonlinearAction :
      fixedLInfScalarL1IntegralCLM requestedTime
          (restrictedScalarLInf requestedTime test
            testSmooth.continuous.continuousOn)
          nonlinearRow =
        ∫ time in (0 : ℝ)..requestedTime,
          test time • nonlinearExtension time :=
    fixedLInfScalarL1IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le
      test testSmooth.continuous.continuousOn
      nonlinearRow nonlinearExtension nonlinearAE
  have stateAction :
      fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          stateRow =
        ∫ time in (0 : ℝ)..requestedTime,
          test time • rowPath time :=
    fixedL2ScalarL2IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le
      test testSmooth.continuous.continuousOn
      stateRow rowPath rowAE
  have viscousAction :
      fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          (((viscousCoefficient : ℝ) : ℂ) • stateRow) =
        ∫ time in (0 : ℝ)..requestedTime,
          test time •
            (viscousCoefficient • rowPath time) := by
    rw [map_smul, stateAction,
      ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro time _
    ext coordinate
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    ring
  change
    fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn)
          stateRow +
        fixedLInfScalarL1IntegralCLM requestedTime
          (restrictedScalarLInf requestedTime test
            testSmooth.continuous.continuousOn)
          nonlinearRow -
        fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          (((viscousCoefficient : ℝ) : ℂ) • stateRow) =
      test requestedTime • receipt.rowExtension wave waveNe requestedTime -
        test 0 • receipt.rowExtension wave waveNe 0
  rw [derivativeAction, nonlinearAction, viscousAction]
  rw [tangentIntegralSplit] at integrationByParts
  abel_nf at integrationByParts ⊢
  exact integrationByParts

/--
Every fixed nonzero Fourier row of an actual whole mild/Serrin receipt has
zero weak action against an endpoint-zero smooth scalar test.
-/
theorem WholeContinuousMildSerrinReceipt.fixedWaveWeakAction_eq_zero
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test)
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
    fixedWaveWeakAction
        requestedTime ν.coeff wave
        (restrictedScalarL2 requestedTime test
          testSmooth.continuous.continuousOn)
        (restrictedScalarL2 requestedTime (deriv test)
          (testSmooth.continuous_deriv (by simp)).continuousOn)
        (restrictedScalarLInf requestedTime test
          testSmooth.continuous.continuousOn)
        receipt.stateLimit
        (transverseSpaceTimeNonlinearRow
          receipt.transverseLimit wave) =
      0 := by
  rw [WholeContinuousMildSerrinReceipt.fixedWaveWeakAction_eq_boundary
    receipt wave waveNe test testSmooth, testZero, testRequestedTimeZero]
  simp

/--
The finite trigonometric weak action of an actual whole mild/Serrin receipt is
the corresponding finite sum of tested endpoint differences.
-/
theorem WholeContinuousMildSerrinReceipt.finiteTrigonometricWeakAction_eq_boundary
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (testModes : Finset IntegerWavevector)
    (testModesZeroFree : ∀ wave ∈ testModes, wave ≠ 0)
    (testCoefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test) :
    (∑ wave ∈ testModes,
      complexCoordinateRealInner (testCoefficient wave)
        (fixedWaveWeakAction
          requestedTime nu.coeff wave
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          (restrictedScalarL2 requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn)
          (restrictedScalarLInf requestedTime test
            testSmooth.continuous.continuousOn)
          receipt.stateLimit
          (transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave))) =
      ∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (test requestedTime •
              receipt.wholePath
                ⟨requestedTime, receipt.requestedTimePos.le, le_rfl⟩ wave -
            test 0 •
              receipt.wholePath
                ⟨0, le_rfl, receipt.requestedTimePos.le⟩ wave) := by
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [WholeContinuousMildSerrinReceipt.fixedWaveWeakAction_eq_boundary
    receipt wave (testModesZeroFree wave waveMem) test testSmooth]
  rw [receipt.rowExtension_on_interval wave
      (testModesZeroFree wave waveMem)
      ⟨requestedTime, receipt.requestedTimePos.le, le_rfl⟩,
    receipt.rowExtension_on_interval wave
      (testModesZeroFree wave waveMem)
      ⟨0, le_rfl, receipt.requestedTimePos.le⟩]

/--
An actual whole mild/Serrin receipt satisfies the weak equation against every
finite trigonometric spatial test and one endpoint-zero smooth time test.
-/
theorem WholeContinuousMildSerrinReceipt.finiteTrigonometricWeakAction_eq_zero
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        nu initialState requestedTime)
    (testModes : Finset IntegerWavevector)
    (testModesZeroFree : ∀ wave ∈ testModes, wave ≠ 0)
    (testCoefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test)
    (testZero : test 0 = 0)
    (testRequestedTimeZero : test requestedTime = 0) :
    (∑ wave ∈ testModes,
      complexCoordinateRealInner (testCoefficient wave)
        (fixedWaveWeakAction
          requestedTime nu.coeff wave
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          (restrictedScalarL2 requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn)
          (restrictedScalarLInf requestedTime test
            testSmooth.continuous.continuousOn)
          receipt.stateLimit
          (transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave))) = 0 := by
  rw [WholeContinuousMildSerrinReceipt.finiteTrigonometricWeakAction_eq_boundary
    receipt testModes testModesZeroFree testCoefficient test testSmooth]
  apply Finset.sum_eq_zero
  intro wave waveMem
  rw [testZero, testRequestedTimeZero]
  simp [complexCoordinateRealInner]

/--
The weak action of one actual receipt, written on its literal continuous
whole path, is exactly its endpoint write.  This is the physical-path form
used when adjacent generated receipts are telescoped in absolute time.
-/
theorem WholeContinuousMildSerrinReceipt.fixedWavePhysicalPathWeakAction_eq_boundary
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (test : Real → Complex)
    (testSmooth : ContDiff Real ∞ test) :
    (∫ time in 0..requestedTime,
        deriv test time •
          receipt.wholePath
            (projIcc 0 requestedTime receipt.requestedTimePos.le time) wave) +
      (∫ time in 0..requestedTime,
        test time •
          wholeStateVorticityNonlinearCoefficientAt
            (receipt.wholePath
              (projIcc 0 requestedTime receipt.requestedTimePos.le time))
            wave) -
      (∫ time in 0..requestedTime,
        test time •
          ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
            receipt.wholePath
              (projIcc 0 requestedTime receipt.requestedTimePos.le time) wave) =
      test requestedTime •
          receipt.wholePath
            ⟨requestedTime, receipt.requestedTimePos.le, le_rfl⟩ wave -
        test 0 •
          receipt.wholePath
            ⟨0, le_rfl, receipt.requestedTimePos.le⟩ wave := by
  have boundary :=
    WholeContinuousMildSerrinReceipt.fixedWaveWeakAction_eq_boundary
      receipt wave waveNe test testSmooth
  unfold fixedWaveWeakAction at boundary
  have stateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        fixedWaveSpaceTimeRestriction requestedTime wave receipt.stateLimit time =
          receipt.rowExtension wave waveNe time.1 := by
    have fullStateAE :
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          receipt.stateLimit time = receipt.wholePath time := by
      rw [← receipt.wholePath_toLp_eq_stateLimit]
      exact
        BoundedContinuousFunction.coeFn_toLp
          (p := (2 : ℝ≥0∞))
          (μ := commonTimeMeasure requestedTime)
          Complex receipt.wholePath
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.stateLimit,
      fullStateAE] with time rowEq stateEq
    rw [rowEq, stateEq]
    exact (receipt.rowExtension_on_interval wave waveNe time).symm
  have nonlinearAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        transverseSpaceTimeNonlinearRow receipt.transverseLimit wave time =
          wholeStateVorticityNonlinearCoefficientAt
            (receipt.wholePath
              (projIcc 0 requestedTime receipt.requestedTimePos.le time.1))
            wave := by
    filter_upwards [
      transverseSpaceTimeNonlinearRow_coeFn
        receipt.transverseLimit wave,
      receipt.wholePath_eq_transverse_ae] with time nonlinearEq pathEq
    rw [nonlinearEq]
    unfold transverseSpaceTimeNonlinearRowFunction
    rw [← pathEq]
    rw [projIcc_of_mem receipt.requestedTimePos.le time.property]
  have viscousAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        (((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
          fixedWaveSpaceTimeRestriction requestedTime wave
            receipt.stateLimit) time =
          ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
            receipt.rowExtension wave waveNe time.1 := by
    filter_upwards [stateAE,
      MeasureTheory.Lp.coeFn_smul
        ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex)
        (fixedWaveSpaceTimeRestriction requestedTime wave receipt.stateLimit)]
      with time rowEq smulEq
    rw [smulEq]
    change
      ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
          fixedWaveSpaceTimeRestriction requestedTime wave
            receipt.stateLimit time = _
    rw [rowEq]
  rw [fixedL2ScalarL2IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le (deriv test)
      (testSmooth.continuous_deriv (by simp)).continuousOn
      _ _ stateAE,
    fixedLInfScalarL1IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le test
      testSmooth.continuous.continuousOn _
      (fun time =>
        wholeStateVorticityNonlinearCoefficientAt
          (receipt.wholePath
            (projIcc 0 requestedTime receipt.requestedTimePos.le time))
          wave)
      nonlinearAE,
    fixedL2ScalarL2IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le test
      testSmooth.continuous.continuousOn _
      (fun time =>
        ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
          receipt.rowExtension wave waveNe time)
      viscousAE] at boundary
  have stateIntegralEq :
      (∫ time in 0..requestedTime,
          deriv test time •
            receipt.wholePath
              (projIcc 0 requestedTime receipt.requestedTimePos.le time) wave) =
        ∫ time in 0..requestedTime,
          deriv test time • receipt.rowExtension wave waveNe time := by
    apply intervalIntegral.integral_congr
    intro time timeMem
    have timeIcc : time ∈ Icc (0 : Real) requestedTime := by
      simpa [uIcc_of_le receipt.requestedTimePos.le] using timeMem
    have projEq :
        projIcc 0 requestedTime receipt.requestedTimePos.le time =
          ⟨time, timeIcc⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val
        (projIcc_of_mem receipt.requestedTimePos.le timeIcc)
    have pathEq :
        receipt.wholePath
            (projIcc 0 requestedTime receipt.requestedTimePos.le time) wave =
          receipt.rowExtension wave waveNe time := by
      rw [projEq]
      exact (receipt.rowExtension_on_interval wave waveNe ⟨time, timeIcc⟩).symm
    exact congrArg (fun value => deriv test time • value) pathEq
  have viscousIntegralEq :
      (∫ time in 0..requestedTime,
          test time •
            ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
              receipt.wholePath
                (projIcc 0 requestedTime receipt.requestedTimePos.le time) wave) =
        ∫ time in 0..requestedTime,
          test time •
            ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) •
              receipt.rowExtension wave waveNe time := by
    apply intervalIntegral.integral_congr
    intro time timeMem
    have timeIcc : time ∈ Icc (0 : Real) requestedTime := by
      simpa [uIcc_of_le receipt.requestedTimePos.le] using timeMem
    have projEq :
        projIcc 0 requestedTime receipt.requestedTimePos.le time =
          ⟨time, timeIcc⟩ := by
      apply Subtype.ext
      exact congrArg Subtype.val
        (projIcc_of_mem receipt.requestedTimePos.le timeIcc)
    have pathEq :
        receipt.wholePath
            (projIcc 0 requestedTime receipt.requestedTimePos.le time) wave =
          receipt.rowExtension wave waveNe time := by
      rw [projEq]
      exact (receipt.rowExtension_on_interval wave waveNe ⟨time, timeIcc⟩).symm
    exact congrArg
      (fun value =>
        test time •
          ((nu.coeff * integerWaveViscousMultiplier wave : Real) : Complex) • value)
      pathEq
  have terminalEq :
      receipt.wholePath
          ⟨requestedTime, receipt.requestedTimePos.le, le_rfl⟩ wave =
        receipt.rowExtension wave waveNe requestedTime :=
    (receipt.rowExtension_on_interval wave waveNe
      ⟨requestedTime, receipt.requestedTimePos.le, le_rfl⟩).symm
  have zeroEq :
      receipt.wholePath ⟨0, le_rfl, receipt.requestedTimePos.le⟩ wave =
        receipt.rowExtension wave waveNe 0 :=
    (receipt.rowExtension_on_interval wave waveNe
      ⟨0, le_rfl, receipt.requestedTimePos.le⟩).symm
  rw [stateIntegralEq, viscousIntegralEq, terminalEq, zeroEq]
  exact boundary

private def scaledSchwartzTest
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 period periodNe)) test

private theorem scaledSchwartzTest_apply
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) (x : ℝ) :
    scaledSchwartzTest test period periodNe x = test (period * x) := by
  rfl

private theorem scaledSchwartzTest_fourier_apply
    (test : 𝓢(ℝ, ℂ))
    (period frequency : ℝ)
    (periodPos : 0 < period) :
    𝓕 (scaledSchwartzTest test period periodPos.ne') frequency =
      (period⁻¹ : ℝ) • 𝓕 test (frequency / period) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  let integrand : ℝ → ℂ := fun y =>
    𝐞 (-(y * (frequency / period))) • test y
  have changeVariables :=
    Measure.integral_comp_smul (volume : Measure ℝ) integrand period
  have changeVariables' :
      (∫ x : ℝ, integrand (period • x)) =
        (period⁻¹ : ℝ) • ∫ y : ℝ, integrand y := by
    simpa only [Module.finrank_self, pow_one,
      abs_of_pos (inv_pos.mpr periodPos)] using changeVariables
  rw [← changeVariables']
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [integrand]
  rw [scaledSchwartzTest_apply]
  congr 2
  simp only [smul_eq_mul]
  field_simp [periodPos.ne']

private theorem schwartzTest_fourier_samples_summable
    (test : 𝓢(ℝ, ℂ)) :
    Summable fun frequency : ℤ => 𝓕 test frequency := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (((𝓕 test).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

private theorem scaledSchwartzTest_fourier_samples_summable
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) :
    Summable fun frequency : ℤ =>
      𝓕 (scaledSchwartzTest test period periodNe) frequency :=
  schwartzTest_fourier_samples_summable _

private theorem schwartzTest_fourier_frequency_sq_mul_samples_summable
    (test : 𝓢(ℝ, ℂ)) :
    Summable fun frequency : ℤ =>
      ((2 * Real.pi * Complex.I * (frequency : ℝ)) ^ 2) *
        𝓕 test frequency := by
  have secondDerivativeSummable :=
    schwartzTest_fourier_samples_summable
      (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test))
  convert secondDerivativeSummable using 1
  funext frequency
  have firstDerivativeFourier := congrArg
    (fun transformed : 𝓢(ℝ, ℂ) => transformed (frequency : ℝ))
    (SchwartzMap.fourier_lineDerivOp_eq test (1 : ℝ))
  have secondDerivativeFourier := congrArg
    (fun transformed : 𝓢(ℝ, ℂ) => transformed (frequency : ℝ))
    (SchwartzMap.fourier_lineDerivOp_eq (∂_{(1 : ℝ)} test) (1 : ℝ))
  change (𝓕 (∂_{(1 : ℝ)} test)) (frequency : ℝ) =
    (2 * Real.pi * Complex.I) *
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x 1)
        (𝓕 test)) (frequency : ℝ) at firstDerivativeFourier
  change (𝓕 (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test))) (frequency : ℝ) =
    (2 * Real.pi * Complex.I) *
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x 1)
        (𝓕 (∂_{(1 : ℝ)} test))) (frequency : ℝ) at secondDerivativeFourier
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)] at firstDerivativeFourier
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)] at secondDerivativeFourier
  rw [secondDerivativeFourier, firstDerivativeFourier]
  simp
  ring

private theorem schwartzTest_fourier_frequency_sq_norm_summable
    (test : 𝓢(ℝ, ℂ)) :
    Summable fun frequency : ℤ =>
      (frequency : ℝ) ^ 2 * ‖𝓕 test frequency‖ := by
  have weighted :=
    (schwartzTest_fourier_frequency_sq_mul_samples_summable test).norm
  have rescaled := weighted.mul_left ((2 * Real.pi) ^ (-2 : ℤ))
  apply rescaled.congr
  intro frequency
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, norm_real,
    Complex.norm_I, mul_one, norm_eq_abs]
  rw [abs_of_pos Real.pi_pos]
  have piNe : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  field_simp [piNe]
  rw [sq_abs (frequency : ℝ)]
  ring

private theorem scaledSchwartzTest_periodization_eq
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) (x : ℝ) :
    (∑' shift : ℤ, test (x + period * shift)) =
      ∑' frequency : ℤ,
        𝓕 (scaledSchwartzTest test period periodNe) frequency *
          fourier frequency ((x / period : ℝ) : UnitAddCircle) := by
  convert SchwartzMap.tsum_eq_tsum_fourier
      (scaledSchwartzTest test period periodNe) (x / period) using 1
  · congr 1
    funext shift
    rw [scaledSchwartzTest_apply]
    field_simp [periodNe]

private theorem scaledSchwartzTest_periodization_eq_self_of_compactSupport
    (test : 𝓢(ℝ, ℂ))
    (supportRadius observationRadius period x : ℝ)
    (periodPos : 0 < period)
    (periodLarge : supportRadius + observationRadius < period)
    (xBound : |x| ≤ observationRadius)
    (support : ∀ y : ℝ, supportRadius < |y| → test y = 0) :
    (∑' shift : ℤ, test (x + period * shift)) = test x := by
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro shift shiftNe
    have shiftAbsInt : (1 : ℤ) ≤ |shift| := Int.one_le_abs shiftNe
    have shiftAbs : (1 : ℝ) ≤ |(shift : ℝ)| := by
      exact_mod_cast shiftAbsInt
    have periodLe : period ≤ |period * (shift : ℝ)| := by
      rw [abs_mul, abs_of_pos periodPos]
      exact le_mul_of_one_le_right periodPos.le shiftAbs
    have triangle :
        |period * (shift : ℝ)| ≤
          |x + period * (shift : ℝ)| + |x| := by
      calc
        |period * (shift : ℝ)| =
            |(x + period * (shift : ℝ)) + (-x)| := by
          congr 1
          ring
        _ ≤ |x + period * (shift : ℝ)| + |-x| := abs_add_le _ _
        _ = |x + period * (shift : ℝ)| + |x| := by rw [abs_neg]
    apply support
    linarith

private theorem schwartzLineDeriv_eq_zero_of_compactSupport
    (test : 𝓢(ℝ, ℂ))
    (supportRadius y : ℝ)
    (support : ∀ z : ℝ, supportRadius < |z| → test z = 0)
    (outside : supportRadius < |y|) :
    (∂_{(1 : ℝ)} test) y = 0 := by
  have outsideOpen : IsOpen {z : ℝ | supportRadius < |z|} :=
    isOpen_lt continuous_const continuous_abs
  have outsideMem : {z : ℝ | supportRadius < |z|} ∈ nhds y :=
    outsideOpen.mem_nhds outside
  have eventuallyZero :
      test =ᶠ[nhds y] (fun _z : ℝ => (0 : ℂ)) := by
    filter_upwards [outsideMem] with z zOutside
    exact support z zOutside
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [eventuallyZero.fderiv_eq]
  simp

private theorem schwartzSecondLineDeriv_eq_zero_of_compactSupport
    (test : 𝓢(ℝ, ℂ))
    (supportRadius y : ℝ)
    (support : ∀ z : ℝ, supportRadius < |z| → test z = 0)
    (outside : supportRadius < |y|) :
    (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test)) y = 0 := by
  apply schwartzLineDeriv_eq_zero_of_compactSupport
    (∂_{(1 : ℝ)} test) supportRadius y
  · intro z zOutside
    exact schwartzLineDeriv_eq_zero_of_compactSupport
      test supportRadius z support zOutside
  · exact outside

private theorem scaledSchwartzTest_periodization_eq_self_C2_of_compactSupport
    (test : 𝓢(ℝ, ℂ))
    (supportRadius observationRadius period x : ℝ)
    (periodPos : 0 < period)
    (periodLarge : supportRadius + observationRadius < period)
    (xBound : |x| ≤ observationRadius)
    (support : ∀ y : ℝ, supportRadius < |y| → test y = 0) :
    (∑' shift : ℤ, test (x + period * shift)) = test x ∧
      (∑' shift : ℤ,
        (∂_{(1 : ℝ)} test) (x + period * shift)) =
          (∂_{(1 : ℝ)} test) x ∧
      (∑' shift : ℤ,
        (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test))
          (x + period * shift)) =
          (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test)) x := by
  refine ⟨scaledSchwartzTest_periodization_eq_self_of_compactSupport
      test supportRadius observationRadius period x periodPos periodLarge xBound support,
    ?_, ?_⟩
  · apply scaledSchwartzTest_periodization_eq_self_of_compactSupport
      (∂_{(1 : ℝ)} test) supportRadius observationRadius period x
      periodPos periodLarge xBound
    intro y yOutside
    exact schwartzLineDeriv_eq_zero_of_compactSupport
      test supportRadius y support yOutside
  · apply scaledSchwartzTest_periodization_eq_self_of_compactSupport
      (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} test)) supportRadius observationRadius period x
      periodPos periodLarge xBound
    intro y yOutside
    exact schwartzSecondLineDeriv_eq_zero_of_compactSupport
      test supportRadius y support yOutside

private def scaledSchwartzPeriodicTest
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) :
    C(UnitAddCircle, ℂ) :=
  ∑' frequency : ℤ,
    𝓕 (scaledSchwartzTest test period periodNe) frequency • fourier frequency

private theorem scaledSchwartzPeriodicTest_hasSum
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) :
    HasSum
      (fun frequency : ℤ =>
        𝓕 (scaledSchwartzTest test period periodNe) frequency • fourier frequency)
      (scaledSchwartzPeriodicTest test period periodNe) := by
  apply Summable.hasSum
  apply Summable.of_norm
  convert (scaledSchwartzTest_fourier_samples_summable test period periodNe).norm using 1
  funext frequency
  rw [norm_smul, fourier_norm, mul_one]

private theorem scaledSchwartzPeriodicTest_apply
    (test : 𝓢(ℝ, ℂ)) (period : ℝ) (periodNe : period ≠ 0) (x : ℝ) :
    scaledSchwartzPeriodicTest test period periodNe
        ((x / period : ℝ) : UnitAddCircle) =
      ∑' shift : ℤ, test (x + period * shift) := by
  rw [scaledSchwartzPeriodicTest]
  rw [← ContinuousMap.tsum_apply
    (scaledSchwartzPeriodicTest_hasSum test period periodNe).summable]
  simpa only [ContinuousMap.smul_apply, smul_eq_mul] using
    (scaledSchwartzTest_periodization_eq test period periodNe x).symm

private def tensorSchwartzFourierCoefficient
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0)
    (wave : IntegerWavevector) : ℂ :=
  𝓕 (scaledSchwartzTest (test 0) period periodNe) (wave 0) *
    𝓕 (scaledSchwartzTest (test 1) period periodNe) (wave 1) *
      𝓕 (scaledSchwartzTest (test 2) period periodNe) (wave 2)

private def integerWavevectorEquivTriple :
    IntegerWavevector ≃ (ℤ × ℤ) × ℤ :=
  (Fin.succFunEquiv ℤ 2).trans
    (Equiv.prodCongr (finTwoArrowEquiv ℤ) (Equiv.refl ℤ))

private theorem tensorSchwartzFourierCoefficient_norm_summable
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0) :
    Summable fun wave : IntegerWavevector =>
      ‖tensorSchwartzFourierCoefficient test period periodNe wave‖ := by
  let coefficient : Coordinate → ℤ → ℂ := fun coordinate frequency =>
    𝓕 (scaledSchwartzTest (test coordinate) period periodNe) frequency
  have h₀ : Summable fun frequency : ℤ => ‖coefficient 0 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 0) period periodNe).norm
  have h₁ : Summable fun frequency : ℤ => ‖coefficient 1 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 1) period periodNe).norm
  have h₂ : Summable fun frequency : ℤ => ‖coefficient 2 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 2) period periodNe).norm
  have h₀₁₂ : Summable fun frequencies : (ℤ × ℤ) × ℤ =>
      ‖(coefficient 0 frequencies.1.1 * coefficient 1 frequencies.1.2) *
        coefficient 2 frequencies.2‖ :=
    (h₀.mul_norm h₁).mul_norm h₂
  let tripleDensity : (ℤ × ℤ) × ℤ → ℝ := fun frequencies =>
    ‖(coefficient 0 frequencies.1.1 * coefficient 1 frequencies.1.2) *
      coefficient 2 frequencies.2‖
  have transported : Summable (tripleDensity ∘ integerWavevectorEquivTriple) :=
    integerWavevectorEquivTriple.summable_iff.mpr h₀₁₂
  apply transported.congr
  intro wave
  simp [integerWavevectorEquivTriple, tensorSchwartzFourierCoefficient,
    tripleDensity, coefficient, mul_assoc]

set_option maxHeartbeats 800000 in
private theorem tensorSchwartzFourierCoefficient_normSq_mul_norm_summable
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0) :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        ‖tensorSchwartzFourierCoefficient test period periodNe wave‖ := by
  let coefficient : Coordinate → ℤ → ℂ := fun coordinate frequency =>
    𝓕 (scaledSchwartzTest (test coordinate) period periodNe) frequency
  have h₀ : Summable fun frequency : ℤ => ‖coefficient 0 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 0) period periodNe).norm
  have h₁ : Summable fun frequency : ℤ => ‖coefficient 1 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 1) period periodNe).norm
  have h₂ : Summable fun frequency : ℤ => ‖coefficient 2 frequency‖ :=
    (scaledSchwartzTest_fourier_samples_summable
      (test 2) period periodNe).norm
  have h₀Sq : Summable fun frequency : ℤ =>
      (frequency : ℝ) ^ 2 * ‖coefficient 0 frequency‖ :=
    schwartzTest_fourier_frequency_sq_norm_summable
      (scaledSchwartzTest (test 0) period periodNe)
  have h₁Sq : Summable fun frequency : ℤ =>
      (frequency : ℝ) ^ 2 * ‖coefficient 1 frequency‖ :=
    schwartzTest_fourier_frequency_sq_norm_summable
      (scaledSchwartzTest (test 1) period periodNe)
  have h₂Sq : Summable fun frequency : ℤ =>
      (frequency : ℝ) ^ 2 * ‖coefficient 2 frequency‖ :=
    schwartzTest_fourier_frequency_sq_norm_summable
      (scaledSchwartzTest (test 2) period periodNe)
  have firstPair : Summable fun frequencies : ℤ × ℤ =>
      ((frequencies.1 : ℝ) ^ 2 * ‖coefficient 0 frequencies.1‖) *
        ‖coefficient 1 frequencies.2‖ :=
    h₀Sq.mul_of_nonneg h₁
      (fun frequency => mul_nonneg (sq_nonneg _) (norm_nonneg _))
      (fun frequency => norm_nonneg _)
  have firstWeighted : Summable fun frequencies : (ℤ × ℤ) × ℤ =>
      ((frequencies.1.1 : ℝ) ^ 2 * ‖coefficient 0 frequencies.1.1‖) *
        ‖coefficient 1 frequencies.1.2‖ *
          ‖coefficient 2 frequencies.2‖ :=
    firstPair.mul_of_nonneg h₂
      (fun frequencies =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))
          (norm_nonneg _))
      (fun frequency => norm_nonneg _)
  have secondPair : Summable fun frequencies : ℤ × ℤ =>
      ‖coefficient 0 frequencies.1‖ *
        ((frequencies.2 : ℝ) ^ 2 * ‖coefficient 1 frequencies.2‖) :=
    h₀.mul_of_nonneg h₁Sq
      (fun frequency => norm_nonneg _)
      (fun frequency => mul_nonneg (sq_nonneg _) (norm_nonneg _))
  have secondWeighted : Summable fun frequencies : (ℤ × ℤ) × ℤ =>
      ‖coefficient 0 frequencies.1.1‖ *
        ((frequencies.1.2 : ℝ) ^ 2 * ‖coefficient 1 frequencies.1.2‖) *
          ‖coefficient 2 frequencies.2‖ :=
    secondPair.mul_of_nonneg h₂
      (fun frequencies =>
        mul_nonneg (norm_nonneg _)
          (mul_nonneg (sq_nonneg _) (norm_nonneg _)))
      (fun frequency => norm_nonneg _)
  have thirdPair : Summable fun frequencies : ℤ × ℤ =>
      ‖coefficient 0 frequencies.1‖ *
        ‖coefficient 1 frequencies.2‖ :=
    h₀.mul_of_nonneg h₁
      (fun frequency => norm_nonneg _)
      (fun frequency => norm_nonneg _)
  have thirdWeighted : Summable fun frequencies : (ℤ × ℤ) × ℤ =>
      ‖coefficient 0 frequencies.1.1‖ *
        ‖coefficient 1 frequencies.1.2‖ *
          ((frequencies.2 : ℝ) ^ 2 * ‖coefficient 2 frequencies.2‖) :=
    thirdPair.mul_of_nonneg h₂Sq
      (fun frequencies => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun frequency => mul_nonneg (sq_nonneg _) (norm_nonneg _))
  let tripleDensity : (ℤ × ℤ) × ℤ → ℝ := fun frequencies =>
    (((frequencies.1.1 : ℝ) ^ 2 +
          (frequencies.1.2 : ℝ) ^ 2 +
          (frequencies.2 : ℝ) ^ 2) *
      ‖(coefficient 0 frequencies.1.1 * coefficient 1 frequencies.1.2) *
        coefficient 2 frequencies.2‖)
  have tripleSummable : Summable tripleDensity := by
    apply ((firstWeighted.add secondWeighted).add thirdWeighted).congr
    intro frequencies
    simp only [tripleDensity, norm_mul]
    ring
  have transported : Summable (tripleDensity ∘ integerWavevectorEquivTriple) :=
    integerWavevectorEquivTriple.summable_iff.mpr tripleSummable
  apply transported.congr
  intro wave
  simp [integerWavevectorEquivTriple, tensorSchwartzFourierCoefficient,
    tripleDensity, coefficient, integerWaveNormSq, Fin.sum_univ_three,
    mul_assoc]

private def tensorSchwartzPeriodicTest
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0) :
    C(UnitAddTorus Coordinate, ℂ) :=
  ∑' wave : IntegerWavevector,
    tensorSchwartzFourierCoefficient test period periodNe wave •
      UnitAddTorus.mFourier wave

private theorem tensorSchwartzPeriodicTest_hasSum
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0) :
    HasSum
      (fun wave : IntegerWavevector =>
        tensorSchwartzFourierCoefficient test period periodNe wave •
          UnitAddTorus.mFourier wave)
      (tensorSchwartzPeriodicTest test period periodNe) := by
  apply Summable.hasSum
  apply Summable.of_norm
  convert tensorSchwartzFourierCoefficient_norm_summable test period periodNe using 1
  funext wave
  rw [norm_smul, UnitAddTorus.mFourier_norm, mul_one]

private theorem tensorSchwartzPeriodicTest_apply_eq_mul
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0)
    (z : UnitAddTorus Coordinate) :
    tensorSchwartzPeriodicTest test period periodNe z =
      scaledSchwartzPeriodicTest (test 0) period periodNe (z 0) *
        scaledSchwartzPeriodicTest (test 1) period periodNe (z 1) *
          scaledSchwartzPeriodicTest (test 2) period periodNe (z 2) := by
  let coefficient : Coordinate → ℤ → ℂ := fun coordinate frequency =>
    𝓕 (scaledSchwartzTest (test coordinate) period periodNe) frequency
  let term : Coordinate → ℤ → ℂ := fun coordinate frequency =>
    coefficient coordinate frequency * fourier frequency (z coordinate)
  have termNormSummable (coordinate : Coordinate) :
      Summable fun frequency : ℤ => ‖term coordinate frequency‖ := by
    convert (scaledSchwartzTest_fourier_samples_summable
      (test coordinate) period periodNe).norm using 1
    funext frequency
    simp only [term, coefficient, norm_mul]
    rw [fourier_apply, Circle.norm_coe, mul_one]
  have termTsum (coordinate : Coordinate) :
      (∑' frequency : ℤ, term coordinate frequency) =
        scaledSchwartzPeriodicTest (test coordinate) period periodNe
          (z coordinate) := by
    rw [scaledSchwartzPeriodicTest]
    rw [← ContinuousMap.tsum_apply
      (scaledSchwartzPeriodicTest_hasSum
        (test coordinate) period periodNe).summable]
    apply tsum_congr
    intro frequency
    simp [term, coefficient]
  have productTsum :
      ((∑' frequency : ℤ, term 0 frequency) *
          ∑' frequency : ℤ, term 1 frequency) *
          ∑' frequency : ℤ, term 2 frequency =
        ∑' frequencies : (ℤ × ℤ) × ℤ,
          (term 0 frequencies.1.1 * term 1 frequencies.1.2) *
            term 2 frequencies.2 := by
    rw [tsum_mul_tsum_of_summable_norm
      (termNormSummable 0) (termNormSummable 1)]
    rw [tsum_mul_tsum_of_summable_norm
      ((termNormSummable 0).mul_norm (termNormSummable 1))
      (termNormSummable 2)]
  rw [tensorSchwartzPeriodicTest]
  rw [← ContinuousMap.tsum_apply
    (tensorSchwartzPeriodicTest_hasSum test period periodNe).summable]
  rw [← termTsum 0, ← termTsum 1, ← termTsum 2, productTsum]
  rw [← integerWavevectorEquivTriple.tsum_eq]
  congr 1
  funext wave
  change
    ((𝓕 (scaledSchwartzTest (test 0) period periodNe)) (wave 0) *
        (𝓕 (scaledSchwartzTest (test 1) period periodNe)) (wave 1) *
        (𝓕 (scaledSchwartzTest (test 2) period periodNe)) (wave 2)) *
        (∏ coordinate : Coordinate,
          fourier (wave coordinate) (z coordinate)) =
      (((𝓕 (scaledSchwartzTest (test 0) period periodNe)) (wave 0) *
          fourier (wave 0) (z 0)) *
        ((𝓕 (scaledSchwartzTest (test 1) period periodNe)) (wave 1) *
          fourier (wave 1) (z 1))) *
        ((𝓕 (scaledSchwartzTest (test 2) period periodNe)) (wave 2) *
          fourier (wave 2) (z 2))
  rw [Fin.prod_univ_three]
  ring

private theorem tensorSchwartzPeriodicTest_apply
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (period : ℝ) (periodNe : period ≠ 0)
    (x : Coordinate → ℝ) :
    tensorSchwartzPeriodicTest test period periodNe
        (fun coordinate =>
          ((x coordinate / period : ℝ) : UnitAddCircle)) =
      ∏ coordinate : Coordinate,
        ∑' shift : ℤ,
          test coordinate (x coordinate + period * shift) := by
  rw [tensorSchwartzPeriodicTest_apply_eq_mul]
  rw [Fin.prod_univ_three]
  rw [scaledSchwartzPeriodicTest_apply,
    scaledSchwartzPeriodicTest_apply,
    scaledSchwartzPeriodicTest_apply]

private theorem unitAddTorus_mFourier_physicalSpace
    (wave : IntegerWavevector) (x : PhysicalSpace) :
    UnitAddTorus.mFourier wave
        (fun coordinate => ((x coordinate : ℝ) : UnitAddCircle)) =
      Complex.exp (Complex.I * integerWavePhase wave x) := by
  rw [show UnitAddTorus.mFourier wave
        (fun coordinate => ((x coordinate : ℝ) : UnitAddCircle)) =
      ∏ coordinate : Coordinate,
        fourier (wave coordinate)
          ((x coordinate : ℝ) : UnitAddCircle) by rfl]
  rw [Fin.prod_univ_three]
  simp only [fourier_coe_apply]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp [integerWavePhase, Fin.sum_univ_three]
  ring

private noncomputable def realFrequencyPlateauBump
    (inner outer : Real)
    (innerNonneg : 0 ≤ inner)
    (innerLtOuter : inner < outer) :
    ContDiffBump (0 : Real) where
  rIn := (inner + outer) / 2
  rOut := outer
  rIn_pos := by nlinarith
  rIn_lt_rOut := by linarith

/-- The canonical real-valued Schwartz frequency cutoff with an inner
plateau and a strictly larger compact outer support. -/
noncomputable def realFrequencyPlateauSchwartz
    (inner outer : Real)
    (innerNonneg : 0 ≤ inner)
    (innerLtOuter : inner < outer) : 𝓢(Real, Complex) := by
  let bump :=
    realFrequencyPlateauBump inner outer innerNonneg innerLtOuter
  let value : Real → Complex := fun frequency => (bump frequency : Complex)
  have valueCompact : HasCompactSupport value := by
    apply bump.hasCompactSupport.mono
    intro frequency valueNe bumpZero
    apply valueNe
    dsimp only [value]
    rw [bumpZero]
    simp
  have valueSmooth : ContDiff Real ∞ value := by
    exact Complex.ofRealCLM.contDiff.comp bump.contDiff
  exact valueCompact.toSchwartzMap valueSmooth

/-- The canonical frequency cutoff is exactly one throughout its requested
inner interval. -/
theorem realFrequencyPlateauSchwartz_eq_one
    (inner outer : Real)
    (innerNonneg : 0 ≤ inner)
    (innerLtOuter : inner < outer)
    (frequency : Real)
    (frequencyMem : |frequency| ≤ inner) :
    realFrequencyPlateauSchwartz inner outer innerNonneg innerLtOuter
        frequency = 1 := by
  let bump :=
    realFrequencyPlateauBump inner outer innerNonneg innerLtOuter
  have frequencyClosedBall : frequency ∈ Metric.closedBall (0 : Real) bump.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    dsimp only [bump, realFrequencyPlateauBump]
    linarith
  change (bump frequency : Complex) = 1
  rw [bump.one_of_mem_closedBall frequencyClosedBall]
  simp

/-- The canonical frequency cutoff vanishes outside its requested outer
interval. -/
theorem realFrequencyPlateauSchwartz_eq_zero
    (inner outer : Real)
    (innerNonneg : 0 ≤ inner)
    (innerLtOuter : inner < outer)
    (frequency : Real)
    (frequencyOutside : outer ≤ |frequency|) :
    realFrequencyPlateauSchwartz inner outer innerNonneg innerLtOuter
        frequency = 0 := by
  let bump :=
    realFrequencyPlateauBump inner outer innerNonneg innerLtOuter
  have outside : bump.rOut ≤ dist frequency 0 := by
    dsimp only [bump, realFrequencyPlateauBump]
    simpa [Real.dist_eq] using frequencyOutside
  change (bump frequency : Complex) = 0
  rw [bump.zero_of_le_dist outside]
  simp

/-- Every value of the canonical frequency cutoff is a real scalar in the
closed unit interval. -/
theorem realFrequencyPlateauSchwartz_real_unit
    (inner outer : Real)
    (innerNonneg : 0 ≤ inner)
    (innerLtOuter : inner < outer)
    (frequency : Real) :
    ∃ value : Real, value ∈ Icc 0 1 ∧
      realFrequencyPlateauSchwartz inner outer innerNonneg innerLtOuter
          frequency = (value : Complex) := by
  let bump :=
    realFrequencyPlateauBump inner outer innerNonneg innerLtOuter
  refine ⟨bump frequency, ⟨bump.nonneg, bump.le_one⟩, ?_⟩
  rfl

/-- Fourier coefficient of the tensor-Schwartz test at one physical scale
and center.  Prefix weak-action telescopes use this exact coefficient family
to preserve the compiler's endpoint pairing definitionally. -/
def recenteredTensorSchwartzFourierCoefficient
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (wave : IntegerWavevector) : ℂ :=
  tensorSchwartzFourierCoefficient test scale⁻¹ (inv_ne_zero scaleNe) wave *
    Complex.exp (-Complex.I * integerWavePhase wave center)

/-- An inverse-Fourier tensor test whose frequency factors vanish outside
`[-supportRadius, supportRadius]` has no recentered lattice coefficient
outside the corresponding physical-frequency box. -/
theorem recenteredInverseFourierTensorSchwartzCoefficient_supported
    (frequencyTest : Coordinate → 𝓢(ℝ, ℂ))
    (supportRadius scale : ℝ)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (frequencySupport : ∀ coordinate frequency,
      supportRadius ≤ |frequency| → frequencyTest coordinate frequency = 0)
    (wave : IntegerWavevector)
    (coefficientNonzero :
      recenteredTensorSchwartzFourierCoefficient
          (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
          scale scalePos.ne' center wave ≠ 0) :
    ∀ coordinate : Coordinate,
      |scale * (wave coordinate : ℝ)| < supportRadius := by
  have scaledZero (coordinate : Coordinate) (outside :
      supportRadius ≤ |scale * (wave coordinate : ℝ)|) :
      𝓕
          (scaledSchwartzTest (𝓕⁻ (frequencyTest coordinate))
            scale⁻¹ (inv_ne_zero scalePos.ne'))
          (wave coordinate) = 0 := by
    rw [scaledSchwartzTest_fourier_apply _ _ _ (inv_pos.mpr scalePos)]
    rw [FourierTransform.fourier_fourierInv_eq]
    rw [frequencySupport coordinate]
    simp
    convert outside using 1
    field_simp [scalePos.ne']
  intro coordinate
  apply lt_of_not_ge
  intro outside
  apply coefficientNonzero
  unfold recenteredTensorSchwartzFourierCoefficient
  unfold tensorSchwartzFourierCoefficient
  fin_cases coordinate
  · rw [scaledZero 0 outside]
    simp
  · rw [scaledZero 1 outside]
    simp
  · rw [scaledZero 2 outside]
    simp

/-- Exact sampled-frequency formula for a recentered inverse-Fourier tensor
test.  It exposes the physical scale, the three frequency multipliers, and
the recentering phase separately. -/
theorem recenteredInverseFourierTensorSchwartzCoefficient_eq_scaleCube_samples_phase
    (frequencyTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (wave : IntegerWavevector) :
    recenteredTensorSchwartzFourierCoefficient
        (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
        scale scalePos.ne' center wave =
      ((scale ^ 3 : ℝ) : ℂ) *
        (∏ coordinate : Coordinate,
          frequencyTest coordinate (scale * (wave coordinate : ℝ))) *
        Complex.exp (-Complex.I * integerWavePhase wave center) := by
  have scaledSample (coordinate : Coordinate) :
      𝓕
          (scaledSchwartzTest (𝓕⁻ (frequencyTest coordinate))
            scale⁻¹ (inv_ne_zero scalePos.ne'))
          (wave coordinate) =
        (scale : ℝ) •
          frequencyTest coordinate (scale * (wave coordinate : ℝ)) := by
    rw [scaledSchwartzTest_fourier_apply _ _ _ (inv_pos.mpr scalePos)]
    rw [FourierTransform.fourier_fourierInv_eq]
    rw [show (wave coordinate : ℝ) / scale⁻¹ =
        scale * (wave coordinate : ℝ) by
      field_simp [scalePos.ne']]
    rw [inv_inv]
  unfold recenteredTensorSchwartzFourierCoefficient
  unfold tensorSchwartzFourierCoefficient
  rw [scaledSample 0, scaledSample 1, scaledSample 2]
  rw [Fin.prod_univ_three]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- On a frequency plateau, the inverse-Fourier tensor test has exactly the
parabolic volume coefficient and the recentering phase. -/
theorem recenteredInverseFourierTensorSchwartzCoefficient_eq_scaleCube_phase
    (frequencyTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (wave : IntegerWavevector)
    (frequencyPlateau : ∀ coordinate : Coordinate,
      frequencyTest coordinate (scale * (wave coordinate : ℝ)) = 1) :
    recenteredTensorSchwartzFourierCoefficient
        (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
        scale scalePos.ne' center wave =
      ((scale ^ 3 : ℝ) : ℂ) *
        Complex.exp (-Complex.I * integerWavePhase wave center) := by
  rw [recenteredInverseFourierTensorSchwartzCoefficient_eq_scaleCube_samples_phase
    frequencyTest scale scalePos center wave]
  simp_rw [frequencyPlateau]
  simp

/-- A real frequency multiplier in the recentered phase pairing is exactly
the same multiplier on the actual finite physical Fourier state. -/
theorem finiteRecenteredPhaseWeightPairing_eq_field
    (scale : ℝ)
    (_scalePos : 0 < scale)
    (center : PhysicalSpace)
    (modes : Finset IntegerWavevector)
    (state : IntegerWavevector → ComplexCoordinateVector)
    (weight : IntegerWavevector → ℝ)
    (testCoordinate : Coordinate) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner
        (Pi.single testCoordinate
          ((((scale ^ 3 * weight wave : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * integerWavePhase wave center)))
        (state wave)) =
      scale ^ 3 *
        finiteRealComplexFourierField modes
          (fun wave => ((weight wave : ℝ) : ℂ) • state wave)
          center testCoordinate := by
  unfold finiteRealComplexFourierField
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  unfold complexCoordinateRealInner
  rw [Finset.sum_eq_single testCoordinate]
  · simp [realComplexFourierMode, coefficientReal, coefficientImag,
      integerCosine, integerSine, Complex.exp_re, Complex.exp_im]
    have scaleCubeRe : ((scale : ℂ) ^ 3).re = scale ^ 3 := by
      calc
        ((scale : ℂ) ^ 3).re = (((scale ^ 3 : ℝ) : ℂ)).re :=
          congrArg Complex.re (Complex.ofReal_pow scale 3).symm
        _ = scale ^ 3 := Complex.ofReal_re _
    have scaleCubeIm : ((scale : ℂ) ^ 3).im = 0 := by
      calc
        ((scale : ℂ) ^ 3).im = (((scale ^ 3 : ℝ) : ℂ)).im :=
          congrArg Complex.im (Complex.ofReal_pow scale 3).symm
        _ = 0 := Complex.ofReal_im _
    rw [scaleCubeRe, scaleCubeIm]
    ring
  · intro coordinate _ coordinateNe
    simp [coordinateNe]
  · simp

/-- Real-valued tensor frequency samples compile directly into the
correspondingly weighted actual finite physical field. -/
theorem finiteRecenteredInverseFourierRealTensorPairing_eq_weightedField
    (frequencyTest : Coordinate → SchwartzMap ℝ ℂ)
    (frequencyValue : IntegerWavevector → Coordinate → ℝ)
    (scale : ℝ)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (modes : Finset IntegerWavevector)
    (state : IntegerWavevector → ComplexCoordinateVector)
    (testCoordinate : Coordinate)
    (frequencyReal : ∀ wave ∈ modes, ∀ coordinate : Coordinate,
      frequencyTest coordinate (scale * (wave coordinate : ℝ)) =
        ((frequencyValue wave coordinate : ℝ) : ℂ)) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner
        (Pi.single testCoordinate
          (recenteredTensorSchwartzFourierCoefficient
            (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
            scale scalePos.ne' center wave))
        (state wave)) =
      scale ^ 3 *
        finiteRealComplexFourierField modes
          (fun wave =>
            (((∏ coordinate : Coordinate,
              frequencyValue wave coordinate) : ℝ) : ℂ) • state wave)
          center testCoordinate := by
  rw [← finiteRecenteredPhaseWeightPairing_eq_field
    scale scalePos center modes state
    (fun wave => ∏ coordinate : Coordinate, frequencyValue wave coordinate)
    testCoordinate]
  apply Finset.sum_congr rfl
  intro wave waveMem
  apply congrArg (fun scalar : ℂ =>
    complexCoordinateRealInner (Pi.single testCoordinate scalar) (state wave))
  rw [recenteredInverseFourierTensorSchwartzCoefficient_eq_scaleCube_samples_phase
    frequencyTest scale scalePos center wave]
  simp_rw [frequencyReal wave waveMem]
  push_cast
  ring

/-- A finite plateau pairing is the actual physical Fourier field at the
recentered point, with precisely the parabolic spatial-volume factor. -/
theorem finiteRecenteredInverseFourierTensorPlateauPairing_eq_field
    (frequencyTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (modes : Finset IntegerWavevector)
    (state : IntegerWavevector → ComplexCoordinateVector)
    (testCoordinate : Coordinate)
    (frequencyPlateau : ∀ wave ∈ modes, ∀ coordinate : Coordinate,
      frequencyTest coordinate (scale * (wave coordinate : ℝ)) = 1) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner
        (Pi.single testCoordinate
          (recenteredTensorSchwartzFourierCoefficient
            (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
            scale scalePos.ne' center wave))
        (state wave)) =
      scale ^ 3 *
        finiteRealComplexFourierField modes state center testCoordinate := by
  unfold finiteRealComplexFourierField
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [recenteredInverseFourierTensorSchwartzCoefficient_eq_scaleCube_phase
    frequencyTest scale scalePos center wave
    (frequencyPlateau wave waveMem)]
  unfold complexCoordinateRealInner
  rw [Finset.sum_eq_single testCoordinate]
  · simp [realComplexFourierMode, coefficientReal, coefficientImag,
      integerCosine, integerSine, Complex.exp_re, Complex.exp_im]
    have scaleCubeRe : ((scale : ℂ) ^ 3).re = scale ^ 3 := by
      calc
        ((scale : ℂ) ^ 3).re = (((scale ^ 3 : ℝ) : ℂ)).re :=
          congrArg Complex.re (Complex.ofReal_pow scale 3).symm
        _ = scale ^ 3 := Complex.ofReal_re _
    have scaleCubeIm : ((scale : ℂ) ^ 3).im = 0 := by
      calc
        ((scale : ℂ) ^ 3).im = (((scale ^ 3 : ℝ) : ℂ)).im :=
          congrArg Complex.im (Complex.ofReal_pow scale 3).symm
        _ = 0 := Complex.ofReal_im _
    rw [scaleCubeRe, scaleCubeIm]
    ring
  · intro coordinate _ coordinateNe
    simp [coordinateNe]
  · simp

/-- A strict physical-frequency box contained in one integer source cube
contains every lattice row carried by that test. -/
theorem scaledCoordinateSupport_mem_integerWaveFrequencyCube
    (scale supportRadius : ℝ)
    (radius : ℕ)
    (scalePos : 0 < scale)
    (supportInside : supportRadius < scale * (radius : ℝ))
    (wave : IntegerWavevector)
    (waveSupported : ∀ coordinate : Coordinate,
      |scale * (wave coordinate : ℝ)| ≤ supportRadius) :
    wave ∈ integerWaveFrequencyCube radius := by
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset]
  intro coordinate
  rw [Finset.mem_Icc]
  have scaledBound := waveSupported coordinate
  rw [abs_mul, abs_of_pos scalePos] at scaledBound
  have coordinateAbsLt :
      |(wave coordinate : ℝ)| < (radius : ℝ) := by
    nlinarith
  have lowerReal :
      -(radius : ℝ) ≤ (wave coordinate : ℝ) :=
    neg_le_of_abs_le (le_of_lt coordinateAbsLt)
  have upperReal :
      (wave coordinate : ℝ) ≤ (radius : ℝ) :=
    le_of_abs_le (le_of_lt coordinateAbsLt)
  constructor
  · exact_mod_cast lowerReal
  · exact_mod_cast upperReal

/-- Once a test's physical-frequency support lies strictly inside the
source cube, its whole-lattice pairing reads exactly the source rows. -/
theorem wholePairing_eq_sourceCubePairing_of_scaledSupport
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector)
    (state : IntegerWavevector → ComplexCoordinateVector)
    (scale supportRadius : ℝ)
    (radius : ℕ)
    (scalePos : 0 < scale)
    (supportInside : supportRadius < scale * (radius : ℝ))
    (coefficientSupported : ∀ wave,
      testCoefficient wave ≠ 0 →
        ∀ coordinate : Coordinate,
          |scale * (wave coordinate : ℝ)| ≤ supportRadius) :
    (∑' wave : IntegerWavevector,
      complexCoordinateRealInner (testCoefficient wave) (state wave)) =
      ∑ wave ∈ integerWaveFrequencyCube radius,
        complexCoordinateRealInner (testCoefficient wave) (state wave) := by
  rw [tsum_eq_sum (s := integerWaveFrequencyCube radius)]
  intro wave waveNotMem
  by_cases coefficientZero : testCoefficient wave = 0
  · rw [coefficientZero]
    simp [complexCoordinateRealInner]
  · exact (waveNotMem
      (scaledCoordinateSupport_mem_integerWaveFrequencyCube
        scale supportRadius radius scalePos supportInside wave
        (coefficientSupported wave coefficientZero))).elim

private theorem recenteredTensorSchwartzFourierCoefficient_norm
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace)
    (wave : IntegerWavevector) :
    ‖recenteredTensorSchwartzFourierCoefficient
        test scale scaleNe center wave‖ =
      ‖tensorSchwartzFourierCoefficient
        test scale⁻¹ (inv_ne_zero scaleNe) wave‖ := by
  rw [recenteredTensorSchwartzFourierCoefficient, norm_mul,
    Complex.norm_exp]
  simp

private theorem recenteredTensorSchwartzFourierCoefficient_c2_summable
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace) :
    Summable fun wave : IntegerWavevector =>
      (1 + integerWaveNormSq wave) *
        ‖recenteredTensorSchwartzFourierCoefficient
          test scale scaleNe center wave‖ := by
  have unweighted := tensorSchwartzFourierCoefficient_norm_summable
    test scale⁻¹ (inv_ne_zero scaleNe)
  have secondWeighted :=
    tensorSchwartzFourierCoefficient_normSq_mul_norm_summable
      test scale⁻¹ (inv_ne_zero scaleNe)
  apply (unweighted.add secondWeighted).congr
  intro wave
  rw [recenteredTensorSchwartzFourierCoefficient_norm]
  ring

private theorem recenteredTensorSchwartzFourierSeries_summable
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center : PhysicalSpace) :
    Summable fun wave : IntegerWavevector =>
      recenteredTensorSchwartzFourierCoefficient
          test scale scaleNe center wave •
        UnitAddTorus.mFourier wave := by
  apply Summable.of_norm
  convert (tensorSchwartzFourierCoefficient_norm_summable
    test scale⁻¹ (inv_ne_zero scaleNe)) using 1
  funext wave
  rw [norm_smul, UnitAddTorus.mFourier_norm, mul_one,
    recenteredTensorSchwartzFourierCoefficient_norm]

private theorem recenteredTensorSchwartzFourierSeries_physical_eq
    (test : Coordinate → 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (center x : PhysicalSpace) :
    (∑' wave : IntegerWavevector,
      recenteredTensorSchwartzFourierCoefficient
          test scale scaleNe center wave *
        UnitAddTorus.mFourier wave
          (fun coordinate => ((x coordinate : ℝ) : UnitAddCircle))) =
      ∏ coordinate : Coordinate,
        ∑' shift : ℤ,
          test coordinate
            (scale⁻¹ * (x coordinate - center coordinate + shift)) := by
  let shiftedPoint : PhysicalSpace := x - center
  have seriesEq :
      (∑' wave : IntegerWavevector,
        recenteredTensorSchwartzFourierCoefficient
            test scale scaleNe center wave *
          UnitAddTorus.mFourier wave
            (fun coordinate => ((x coordinate : ℝ) : UnitAddCircle))) =
        tensorSchwartzPeriodicTest test scale⁻¹ (inv_ne_zero scaleNe)
          (fun coordinate =>
            ((shiftedPoint coordinate : ℝ) : UnitAddCircle)) := by
    rw [tensorSchwartzPeriodicTest]
    rw [← ContinuousMap.tsum_apply
      (tensorSchwartzPeriodicTest_hasSum
        test scale⁻¹ (inv_ne_zero scaleNe)).summable]
    apply tsum_congr
    intro wave
    rw [unitAddTorus_mFourier_physicalSpace]
    change
      tensorSchwartzFourierCoefficient
            test scale⁻¹ (inv_ne_zero scaleNe) wave *
          Complex.exp (-Complex.I * integerWavePhase wave center) *
          Complex.exp (Complex.I * integerWavePhase wave x) =
        tensorSchwartzFourierCoefficient
            test scale⁻¹ (inv_ne_zero scaleNe) wave *
          UnitAddTorus.mFourier wave
            (fun coordinate =>
              ((shiftedPoint coordinate : ℝ) : UnitAddCircle))
    rw [unitAddTorus_mFourier_physicalSpace]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    dsimp only [shiftedPoint]
    rw [integerWavePhase_sub]
    push_cast
    ring_nf
  rw [seriesEq]
  have periodized := tensorSchwartzPeriodicTest_apply
    test scale⁻¹ (inv_ne_zero scaleNe)
    (fun coordinate => scale⁻¹ * shiftedPoint coordinate)
  have pointEq :
      (fun coordinate =>
        ((scale⁻¹ * shiftedPoint coordinate / scale⁻¹ : ℝ) :
          UnitAddCircle)) =
        (fun coordinate =>
          ((shiftedPoint coordinate : ℝ) : UnitAddCircle)) := by
    funext coordinate
    congr 1
    field_simp [scaleNe]
  rw [pointEq] at periodized
  rw [periodized]
  congr 1
  funext coordinate
  congr 1
  funext shift
  simp [shiftedPoint, mul_add]

private theorem physicalUnitCell_finiteTest_pairing_eq_coefficients
    (modes : Finset IntegerWavevector)
    (modesNegClosed :
      ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (testCoefficient state :
      IntegerWavevector → ComplexCoordinateVector)
    (stateReality : ∀ wave,
      state (waveNeg wave) = vectorConj (state wave)) :
    (∫ x in physicalUnitCell,
      velocityDot
        (finiteRealComplexFourierField modes testCoefficient)
        (finiteRealComplexFourierField modes state) x) =
      ∑ wave ∈ modes,
        complexCoordinateRealInner
          (testCoefficient wave) (state wave) := by
  rw [physicalUnitCell_finiteRealComplexFourierField_pairing
    modes testCoefficient
    (finiteRealComplexFourierField modes state)
    (finiteRealComplexFourierField_contDiff modes state).continuous]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField]
  have negMem : waveNeg wave ∈ modes := modesNegClosed waveMem
  simp only [if_pos waveMem, if_pos negMem]
  have reality := stateReality wave
  simp [complexCoordinateRealInner, reality, vectorConj_apply]

private theorem complexCoordinateRealInner_conj_smul_left
    (scalar : ℂ) (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (star scalar • left) right =
      complexCoordinateRealInner left (scalar • right) := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, smul_eq_mul, Complex.star_def,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

private def complexCoordinateRealInnerRightCLM
    (left : ComplexCoordinateVector) :
    ComplexCoordinateVector →L[ℝ] ℝ :=
  ∑ coordinate : Coordinate,
    ((left coordinate).re •
        (Complex.reCLM.comp
          (ContinuousLinearMap.proj coordinate :
            ComplexCoordinateVector →L[ℝ] ℂ)) +
      (left coordinate).im •
        (Complex.imCLM.comp
          (ContinuousLinearMap.proj coordinate :
            ComplexCoordinateVector →L[ℝ] ℂ)))

@[simp] private theorem complexCoordinateRealInnerRightCLM_apply
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInnerRightCLM left right =
      complexCoordinateRealInner left right := by
  simp [complexCoordinateRealInnerRightCLM,
    complexCoordinateRealInner]

private theorem complexCoordinateRealInner_integral_right
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (left : ComplexCoordinateVector)
    (right : α → ComplexCoordinateVector)
    (rightIntegrable : Integrable right μ) :
    complexCoordinateRealInner left
        (∫ point, right point ∂μ) =
      ∫ point, complexCoordinateRealInner left (right point) ∂μ := by
  simpa only [complexCoordinateRealInnerRightCLM_apply] using
    ((complexCoordinateRealInnerRightCLM left).integral_comp_comm
      rightIntegrable).symm

private theorem receipt_fixedWaveWeakAction_eq_intervalIntegral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test) :
    fixedWaveWeakAction
        requestedTime nu.coeff wave
        (restrictedScalarL2 requestedTime test
          testSmooth.continuous.continuousOn)
        (restrictedScalarL2 requestedTime (deriv test)
          (testSmooth.continuous_deriv (by simp)).continuousOn)
        (restrictedScalarLInf requestedTime test
          testSmooth.continuous.continuousOn)
        receipt.stateLimit
        (transverseSpaceTimeNonlinearRow
          receipt.transverseLimit wave) =
      (∫ time in (0 : ℝ)..requestedTime,
        deriv test time •
            commonTimeZeroExtension requestedTime
              (fun localTime => receipt.wholePath localTime wave) time) +
        (∫ time in (0 : ℝ)..requestedTime,
          test time •
            commonTimeZeroExtension requestedTime
              (fun localTime =>
                transverseSpaceTimeNonlinearRowFunction
                  receipt.transverseLimit wave localTime) time) -
        (∫ time in (0 : ℝ)..requestedTime,
          test time •
            ((nu.coeff * integerWaveViscousMultiplier wave) •
              commonTimeZeroExtension requestedTime
                (fun localTime => receipt.wholePath localTime wave) time)) := by
  let stateRow :=
    fixedWaveSpaceTimeRestriction requestedTime wave receipt.stateLimit
  let stateExtension : ℝ → ComplexCoordinateVector := fun time =>
    commonTimeZeroExtension requestedTime
      (fun localTime => receipt.wholePath localTime wave) time
  let nonlinearRow :=
    transverseSpaceTimeNonlinearRow receipt.transverseLimit wave
  let nonlinearExtension : ℝ → ComplexCoordinateVector := fun time =>
    commonTimeZeroExtension requestedTime
      (fun localTime =>
        transverseSpaceTimeNonlinearRowFunction
          receipt.transverseLimit wave localTime) time
  have stateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        receipt.stateLimit time = receipt.wholePath time := by
    rw [← receipt.wholePath_toLp_eq_stateLimit]
    exact
      BoundedContinuousFunction.coeFn_toLp
        (p := (2 : ℝ≥0∞))
        (μ := commonTimeMeasure requestedTime)
        ℂ receipt.wholePath
  have rowAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        stateRow time = stateExtension time.1 := by
    filter_upwards [
      fixedWaveSpaceTimeRestriction_coeFn
        requestedTime wave receipt.stateLimit,
      stateAE] with time rowEq stateEq
    calc
      stateRow time = receipt.stateLimit time wave := by
        simpa [stateRow] using rowEq
      _ = receipt.wholePath time wave := by rw [stateEq]
      _ = stateExtension time.1 := by
        simp [stateExtension, commonTimeZeroExtension_of_mem,
          time.property]
  have nonlinearAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        nonlinearRow time = nonlinearExtension time.1 := by
    filter_upwards [
      transverseSpaceTimeNonlinearRow_coeFn
        receipt.transverseLimit wave] with time nonlinearEq
    rw [nonlinearEq]
    simp [nonlinearExtension, commonTimeZeroExtension_of_mem,
      time.property]
  have derivativeAction :=
    fixedL2ScalarL2IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le
      (deriv test)
      (testSmooth.continuous_deriv (by simp)).continuousOn
      stateRow stateExtension rowAE
  have nonlinearAction :=
    fixedLInfScalarL1IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le
      test testSmooth.continuous.continuousOn
      nonlinearRow nonlinearExtension nonlinearAE
  have stateAction :=
    fixedL2ScalarL2IntegralCLM_eq_intervalIntegral_of_ae
      requestedTime receipt.requestedTimePos.le
      test testSmooth.continuous.continuousOn
      stateRow stateExtension rowAE
  have viscousAction :
      fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          ((((nu.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ)) •
            stateRow) =
        ∫ time in (0 : ℝ)..requestedTime,
          test time •
            ((nu.coeff * integerWaveViscousMultiplier wave) •
              stateExtension time) := by
    rw [map_smul, stateAction, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro time _
    ext coordinate
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    ring
  change
    fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn)
          stateRow +
        fixedLInfScalarL1IntegralCLM requestedTime
          (restrictedScalarLInf requestedTime test
            testSmooth.continuous.continuousOn)
          nonlinearRow -
        fixedL2ScalarL2IntegralCLM requestedTime
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          ((((nu.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ)) •
            stateRow) = _
  rw [derivativeAction, nonlinearAction, viscousAction]

private theorem receipt_fixedWaveWeakAction_eq_commonTimeIntegral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test) :
    fixedWaveWeakAction
        requestedTime nu.coeff wave
        (restrictedScalarL2 requestedTime test
          testSmooth.continuous.continuousOn)
        (restrictedScalarL2 requestedTime (deriv test)
          (testSmooth.continuous_deriv (by simp)).continuousOn)
        (restrictedScalarLInf requestedTime test
          testSmooth.continuous.continuousOn)
        receipt.stateLimit
        (transverseSpaceTimeNonlinearRow
          receipt.transverseLimit wave) =
      (∫ time : Icc (0 : ℝ) requestedTime,
        deriv test time.1 • receipt.wholePath time wave
        ∂(commonTimeMeasure requestedTime)) +
        (∫ time : Icc (0 : ℝ) requestedTime,
          test time.1 •
            transverseSpaceTimeNonlinearRowFunction
              receipt.transverseLimit wave time
          ∂(commonTimeMeasure requestedTime)) -
        (∫ time : Icc (0 : ℝ) requestedTime,
          test time.1 •
            ((nu.coeff * integerWaveViscousMultiplier wave) •
              receipt.wholePath time wave)
          ∂(commonTimeMeasure requestedTime)) := by
  rw [receipt_fixedWaveWeakAction_eq_intervalIntegral
    receipt wave test testSmooth]
  have derivativeEq := commonTime_integral_eq_intervalIntegral_vector
    requestedTime receipt.requestedTimePos.le
    (fun time : ℝ =>
      deriv test time •
        commonTimeZeroExtension requestedTime
          (fun localTime => receipt.wholePath localTime wave) time)
  have nonlinearEq := commonTime_integral_eq_intervalIntegral_vector
    requestedTime receipt.requestedTimePos.le
    (fun time : ℝ =>
      test time •
        commonTimeZeroExtension requestedTime
          (fun localTime =>
            transverseSpaceTimeNonlinearRowFunction
              receipt.transverseLimit wave localTime) time)
  have viscousEq := commonTime_integral_eq_intervalIntegral_vector
    requestedTime receipt.requestedTimePos.le
    (fun time : ℝ =>
      test time •
        ((nu.coeff * integerWaveViscousMultiplier wave) •
          commonTimeZeroExtension requestedTime
            (fun localTime => receipt.wholePath localTime wave) time))
  rw [← derivativeEq, ← nonlinearEq, ← viscousEq]
  apply congrArg₂ (fun left right => left - right)
  · apply congrArg₂ (fun left right => left + right)
    · apply integral_congr_ae
      filter_upwards with time
      rw [commonTimeZeroExtension_of_mem _ _ time.1 time.property]
    · apply integral_congr_ae
      filter_upwards with time
      rw [commonTimeZeroExtension_of_mem _ _ time.1 time.property]
  · apply integral_congr_ae
    filter_upwards with time
    rw [commonTimeZeroExtension_of_mem _ _ time.1 time.property]

private theorem receipt_fixedWaveWeakIntegrands_commonTimeIntegrable
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test) :
    Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          deriv test time.1 • receipt.wholePath time wave)
        (commonTimeMeasure requestedTime) ∧
      Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          test time.1 •
            transverseSpaceTimeNonlinearRowFunction
              receipt.transverseLimit wave time)
        (commonTimeMeasure requestedTime) ∧
      Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          test time.1 •
            ((nu.coeff * integerWaveViscousMultiplier wave) •
              receipt.wholePath time wave))
        (commonTimeMeasure requestedTime) := by
  let testLp := restrictedScalarLInf requestedTime test
    testSmooth.continuous.continuousOn
  let derivativeLp := restrictedScalarLInf requestedTime (deriv test)
    (testSmooth.continuous_deriv (by simp)).continuousOn
  have testAE :
      ⇑testLp =ᵐ[commonTimeMeasure requestedTime]
        (fun time : Icc (0 : ℝ) requestedTime => test time.1) := by
    have generated := BoundedContinuousFunction.coeFn_toLp
        (p := (∞ : ℝ≥0∞))
        (μ := commonTimeMeasure requestedTime) ℂ
        (restrictedScalarBoundedPath requestedTime test
          testSmooth.continuous.continuousOn)
    filter_upwards [generated] with time equality
    have testPoint :
        testLp time =
          restrictedScalarBoundedPath requestedTime test
            testSmooth.continuous.continuousOn time := by
      simpa [testLp, restrictedScalarLInf] using equality
    exact testPoint.trans rfl
  have derivativeAE :
      ⇑derivativeLp =ᵐ[commonTimeMeasure requestedTime]
        (fun time : Icc (0 : ℝ) requestedTime => deriv test time.1) := by
    have generated := BoundedContinuousFunction.coeFn_toLp
        (p := (∞ : ℝ≥0∞))
        (μ := commonTimeMeasure requestedTime) ℂ
        (restrictedScalarBoundedPath requestedTime (deriv test)
          (testSmooth.continuous_deriv (by simp)).continuousOn)
    filter_upwards [generated] with time equality
    have derivativePoint :
        derivativeLp time =
          restrictedScalarBoundedPath requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn time := by
      simpa [derivativeLp, restrictedScalarLInf] using equality
    exact derivativePoint.trans rfl
  have testMemLp : MemLp
      (fun time : Icc (0 : ℝ) requestedTime => test time.1)
      ∞ (commonTimeMeasure requestedTime) := by
    rw [← memLp_congr_ae testAE]
    exact MeasureTheory.Lp.memLp testLp
  have derivativeMemLp : MemLp
      (fun time : Icc (0 : ℝ) requestedTime => deriv test time.1)
      ∞ (commonTimeMeasure requestedTime) := by
    rw [← memLp_congr_ae derivativeAE]
    exact MeasureTheory.Lp.memLp derivativeLp
  have stateRowContinuous : Continuous
      (fun time : Icc (0 : ℝ) requestedTime =>
        receipt.wholePath time wave) :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp receipt.wholePath.continuous
  have stateRowIntegrable : Integrable
      (fun time : Icc (0 : ℝ) requestedTime =>
        receipt.wholePath time wave)
      (commonTimeMeasure requestedTime) := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        stateRowContinuous.continuousOn)
  have nonlinearIntegrable :=
    transverseSpaceTimeNonlinearRowFunction_integrable
      receipt.transverseLimit wave
  refine ⟨?_, ?_, ?_⟩
  · apply (stateRowIntegrable.smul_of_top_right derivativeMemLp).congr
    filter_upwards with time
    rfl
  · apply (nonlinearIntegrable.smul_of_top_right testMemLp).congr
    filter_upwards with time
    rfl
  · have viscousContinuous : Continuous
        (fun time : Icc (0 : ℝ) requestedTime =>
          test time.1 •
            ((nu.coeff * integerWaveViscousMultiplier wave) •
              receipt.wholePath time wave)) := by
      fun_prop
    simpa only [MeasureTheory.integrableOn_univ] using
      (ContinuousOn.integrableOn_compact isCompact_univ
        viscousContinuous.continuousOn)

private theorem receipt_finiteTrigonometricWeakAction_eq_physicalIntegral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (modesNegClosed :
      ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (testCoefficient :
      IntegerWavevector → ComplexCoordinateVector)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner (testCoefficient wave)
        (fixedWaveWeakAction
          requestedTime nu.coeff wave
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          (restrictedScalarL2 requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn)
          (restrictedScalarLInf requestedTime test
            testSmooth.continuous.continuousOn)
          receipt.stateLimit
          (transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave))) =
      ∫ time : Icc (0 : ℝ) requestedTime,
        ((∫ x in physicalUnitCell,
          velocityDot
            (finiteRealComplexFourierField modes (fun wave =>
              star (deriv test time.1) • testCoefficient wave))
            (finiteRealComplexFourierField modes
              (receipt.transverseLimit time).1) x) +
        (∫ x in physicalUnitCell,
          velocityDot
            (finiteRealComplexFourierField modes (fun wave =>
              star (test time.1) • testCoefficient wave))
            (finiteRealComplexFourierField modes (fun wave =>
              wholeStateVorticityNonlinearCoefficientAt
                (receipt.transverseLimit time).1 wave)) x) -
        (∫ x in physicalUnitCell,
          velocityDot
            (finiteRealComplexFourierField modes (fun wave =>
              star (test time.1 *
                ((nu.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ)) •
                  testCoefficient wave))
            (finiteRealComplexFourierField modes
              (receipt.transverseLimit time).1) x))
        ∂(commonTimeMeasure requestedTime) := by
  have waveActionEq (wave : IntegerWavevector) :
      complexCoordinateRealInner (testCoefficient wave)
          (fixedWaveWeakAction
            requestedTime nu.coeff wave
            (restrictedScalarL2 requestedTime test
              testSmooth.continuous.continuousOn)
            (restrictedScalarL2 requestedTime (deriv test)
              (testSmooth.continuous_deriv (by simp)).continuousOn)
            (restrictedScalarLInf requestedTime test
              testSmooth.continuous.continuousOn)
            receipt.stateLimit
            (transverseSpaceTimeNonlinearRow
              receipt.transverseLimit wave)) =
        (∫ time : Icc (0 : ℝ) requestedTime,
          complexCoordinateRealInner (testCoefficient wave)
            (deriv test time.1 • receipt.wholePath time wave)
          ∂(commonTimeMeasure requestedTime)) +
        (∫ time : Icc (0 : ℝ) requestedTime,
          complexCoordinateRealInner (testCoefficient wave)
            (test time.1 •
              transverseSpaceTimeNonlinearRowFunction
                receipt.transverseLimit wave time)
          ∂(commonTimeMeasure requestedTime)) -
        (∫ time : Icc (0 : ℝ) requestedTime,
          complexCoordinateRealInner (testCoefficient wave)
            (test time.1 •
              ((nu.coeff * integerWaveViscousMultiplier wave) •
                receipt.wholePath time wave))
          ∂(commonTimeMeasure requestedTime)) := by
    have integrable := receipt_fixedWaveWeakIntegrands_commonTimeIntegrable
      receipt wave test testSmooth
    rw [receipt_fixedWaveWeakAction_eq_commonTimeIntegral
      receipt wave test testSmooth]
    change
      complexCoordinateRealInnerRightCLM (testCoefficient wave)
          (_ + _ - _) = _
    rw [map_sub, map_add]
    simp only [complexCoordinateRealInnerRightCLM_apply]
    rw [complexCoordinateRealInner_integral_right
        (commonTimeMeasure requestedTime) _ _ integrable.1,
      complexCoordinateRealInner_integral_right
        (commonTimeMeasure requestedTime) _ _ integrable.2.1,
      complexCoordinateRealInner_integral_right
        (commonTimeMeasure requestedTime) _ _ integrable.2.2]
  have derivativeIntegrable : ∀ wave ∈ modes,
      Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          complexCoordinateRealInner (testCoefficient wave)
            (deriv test time.1 • receipt.wholePath time wave))
        (commonTimeMeasure requestedTime) := by
    intro wave _waveMem
    exact (complexCoordinateRealInnerRightCLM
      (testCoefficient wave)).integrable_comp
        (receipt_fixedWaveWeakIntegrands_commonTimeIntegrable
          receipt wave test testSmooth).1
  have nonlinearIntegrable : ∀ wave ∈ modes,
      Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          complexCoordinateRealInner (testCoefficient wave)
            (test time.1 •
              transverseSpaceTimeNonlinearRowFunction
                receipt.transverseLimit wave time))
        (commonTimeMeasure requestedTime) := by
    intro wave _waveMem
    exact (complexCoordinateRealInnerRightCLM
      (testCoefficient wave)).integrable_comp
        (receipt_fixedWaveWeakIntegrands_commonTimeIntegrable
          receipt wave test testSmooth).2.1
  have viscousIntegrable : ∀ wave ∈ modes,
      Integrable
        (fun time : Icc (0 : ℝ) requestedTime =>
          complexCoordinateRealInner (testCoefficient wave)
            (test time.1 •
              ((nu.coeff * integerWaveViscousMultiplier wave) •
                receipt.wholePath time wave)))
        (commonTimeMeasure requestedTime) := by
    intro wave _waveMem
    exact (complexCoordinateRealInnerRightCLM
      (testCoefficient wave)).integrable_comp
        (receipt_fixedWaveWeakIntegrands_commonTimeIntegrable
          receipt wave test testSmooth).2.2
  calc
    (∑ wave ∈ modes,
      complexCoordinateRealInner (testCoefficient wave)
        (fixedWaveWeakAction
          requestedTime nu.coeff wave
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          (restrictedScalarL2 requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn)
          (restrictedScalarLInf requestedTime test
            testSmooth.continuous.continuousOn)
          receipt.stateLimit
          (transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave))) =
        ∑ wave ∈ modes,
          ((∫ time : Icc (0 : ℝ) requestedTime,
              complexCoordinateRealInner (testCoefficient wave)
                (deriv test time.1 • receipt.wholePath time wave)
              ∂(commonTimeMeasure requestedTime)) +
            (∫ time : Icc (0 : ℝ) requestedTime,
              complexCoordinateRealInner (testCoefficient wave)
                (test time.1 •
                  transverseSpaceTimeNonlinearRowFunction
                    receipt.transverseLimit wave time)
              ∂(commonTimeMeasure requestedTime)) -
            (∫ time : Icc (0 : ℝ) requestedTime,
              complexCoordinateRealInner (testCoefficient wave)
                (test time.1 •
                  ((nu.coeff * integerWaveViscousMultiplier wave) •
                    receipt.wholePath time wave))
              ∂(commonTimeMeasure requestedTime))) := by
      apply Finset.sum_congr rfl
      intro wave _waveMem
      exact waveActionEq wave
    _ =
        (∫ time : Icc (0 : ℝ) requestedTime,
          ∑ wave ∈ modes,
            complexCoordinateRealInner (testCoefficient wave)
              (deriv test time.1 • receipt.wholePath time wave)
          ∂(commonTimeMeasure requestedTime)) +
        (∫ time : Icc (0 : ℝ) requestedTime,
          ∑ wave ∈ modes,
            complexCoordinateRealInner (testCoefficient wave)
              (test time.1 •
                transverseSpaceTimeNonlinearRowFunction
                  receipt.transverseLimit wave time)
          ∂(commonTimeMeasure requestedTime)) -
        (∫ time : Icc (0 : ℝ) requestedTime,
          ∑ wave ∈ modes,
            complexCoordinateRealInner (testCoefficient wave)
              (test time.1 •
                ((nu.coeff * integerWaveViscousMultiplier wave) •
                  receipt.wholePath time wave))
          ∂(commonTimeMeasure requestedTime)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [integral_finsetSum modes derivativeIntegrable,
        integral_finsetSum modes nonlinearIntegrable,
        integral_finsetSum modes viscousIntegrable]
    _ = _ := by
      let derivativeDensity : Icc (0 : ℝ) requestedTime → ℝ := fun time =>
        ∑ wave ∈ modes,
          complexCoordinateRealInner (testCoefficient wave)
            (deriv test time.1 • receipt.wholePath time wave)
      let nonlinearDensity : Icc (0 : ℝ) requestedTime → ℝ := fun time =>
        ∑ wave ∈ modes,
          complexCoordinateRealInner (testCoefficient wave)
            (test time.1 •
              transverseSpaceTimeNonlinearRowFunction
                receipt.transverseLimit wave time)
      let viscousDensity : Icc (0 : ℝ) requestedTime → ℝ := fun time =>
        ∑ wave ∈ modes,
          complexCoordinateRealInner (testCoefficient wave)
            (test time.1 •
              ((nu.coeff * integerWaveViscousMultiplier wave) •
                receipt.wholePath time wave))
      have derivativeSumIntegrable : Integrable derivativeDensity
          (commonTimeMeasure requestedTime) := by
        simpa only [derivativeDensity] using
          integrable_finsetSum modes derivativeIntegrable
      have nonlinearSumIntegrable : Integrable nonlinearDensity
          (commonTimeMeasure requestedTime) := by
        simpa only [nonlinearDensity] using
          integrable_finsetSum modes nonlinearIntegrable
      have viscousSumIntegrable : Integrable viscousDensity
          (commonTimeMeasure requestedTime) := by
        simpa only [viscousDensity] using
          integrable_finsetSum modes viscousIntegrable
      have combineAll :
          (∫ time, derivativeDensity time
              ∂(commonTimeMeasure requestedTime)) +
            (∫ time, nonlinearDensity time
              ∂(commonTimeMeasure requestedTime)) -
            (∫ time, viscousDensity time
              ∂(commonTimeMeasure requestedTime)) =
            ∫ time,
              (derivativeDensity + nonlinearDensity - viscousDensity) time
              ∂(commonTimeMeasure requestedTime) := by
        calc
          _ = (∫ time,
                  derivativeDensity time + nonlinearDensity time
                  ∂(commonTimeMeasure requestedTime)) -
                ∫ time, viscousDensity time
                  ∂(commonTimeMeasure requestedTime) := by
              rw [integral_add derivativeSumIntegrable
                nonlinearSumIntegrable]
          _ = _ := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_sub
                (μ := commonTimeMeasure requestedTime)
                (derivativeSumIntegrable.add nonlinearSumIntegrable)
                viscousSumIntegrable).symm
      change
        (∫ time, derivativeDensity time
            ∂(commonTimeMeasure requestedTime)) +
          (∫ time, nonlinearDensity time
            ∂(commonTimeMeasure requestedTime)) -
          (∫ time, viscousDensity time
            ∂(commonTimeMeasure requestedTime)) = _
      rw [combineAll]
      apply integral_congr_ae
      filter_upwards [receipt.transverse_fourierReality_ae,
        receipt.wholePath_eq_transverse_ae] with time reality pathEq
      have statePairing (coefficient :
          IntegerWavevector → ComplexCoordinateVector) :=
        physicalUnitCell_finiteTest_pairing_eq_coefficients
          modes modesNegClosed coefficient
          (receipt.transverseLimit time).1 reality
      have nonlinearReality : ∀ wave,
          wholeStateVorticityNonlinearCoefficientAt
              (receipt.transverseLimit time).1 (waveNeg wave) =
            vectorConj
              (wholeStateVorticityNonlinearCoefficientAt
                (receipt.transverseLimit time).1 wave) := by
        intro wave
        have generated :=
          wholeStateVorticityNonlinearCoefficientAt_waveNeg
            (receipt.transverseLimit time).1
            (receipt.transverseLimit time).2 reality (waveNeg wave)
        simpa using generated
      have nonlinearPairing (coefficient :
          IntegerWavevector → ComplexCoordinateVector) :=
        physicalUnitCell_finiteTest_pairing_eq_coefficients
          modes modesNegClosed coefficient
          (fun wave => wholeStateVorticityNonlinearCoefficientAt
            (receipt.transverseLimit time).1 wave) nonlinearReality
      change derivativeDensity time + nonlinearDensity time -
        viscousDensity time = _
      dsimp only [derivativeDensity, nonlinearDensity, viscousDensity]
      rw [statePairing, nonlinearPairing, statePairing]
      have derivativeSumEq :
          (∑ wave ∈ modes,
            complexCoordinateRealInner (testCoefficient wave)
              (deriv test time.1 • receipt.wholePath time wave)) =
            ∑ wave ∈ modes,
              complexCoordinateRealInner
                (star (deriv test time.1) • testCoefficient wave)
                ((receipt.transverseLimit time).1 wave) := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        rw [pathEq]
        exact (complexCoordinateRealInner_conj_smul_left
          (deriv test time.1) (testCoefficient wave)
          ((receipt.transverseLimit time).1 wave)).symm
      have nonlinearSumEq :
          (∑ wave ∈ modes,
            complexCoordinateRealInner (testCoefficient wave)
              (test time.1 •
                transverseSpaceTimeNonlinearRowFunction
                  receipt.transverseLimit wave time)) =
            ∑ wave ∈ modes,
              complexCoordinateRealInner
                (star (test time.1) • testCoefficient wave)
                (wholeStateVorticityNonlinearCoefficientAt
                  (receipt.transverseLimit time).1 wave) := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        exact (complexCoordinateRealInner_conj_smul_left
          (test time.1) (testCoefficient wave)
          (wholeStateVorticityNonlinearCoefficientAt
            (receipt.transverseLimit time).1 wave)).symm
      have viscousSumEq :
          (∑ wave ∈ modes,
            complexCoordinateRealInner (testCoefficient wave)
              (test time.1 •
                ((nu.coeff * integerWaveViscousMultiplier wave) •
                  receipt.wholePath time wave))) =
            ∑ wave ∈ modes,
              complexCoordinateRealInner
                (star (test time.1 *
                  ((nu.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ)) •
                    testCoefficient wave)
                ((receipt.transverseLimit time).1 wave) := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        rw [pathEq]
        rw [complexCoordinateRealInner_conj_smul_left]
        congr 1
        ext coordinate
        simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
        push_cast
        ring
      rw [derivativeSumEq, nonlinearSumEq, viscousSumEq]

private theorem parabolic_intervalIntegral_change
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (value : ℝ → E)
    (scale requestedTime : ℝ)
    (scaleNe : scale ≠ 0) :
    (∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
      (scale ^ 4 : ℝ) • value (scale ^ 2 * scaledTime)) =
      (scale ^ 2 : ℝ) •
        ∫ time in (0 : ℝ)..requestedTime, value time := by
  have changeVariables :=
    intervalIntegral.smul_integral_comp_add_mul
      (f := value) (a := (0 : ℝ))
      (b := requestedTime / scale ^ 2)
      (c := scale ^ 2) (0 : ℝ)
  have terminalEq :
      scale ^ 2 * (requestedTime / scale ^ 2) = requestedTime := by
    field_simp [scaleNe]
  simp only [zero_add, mul_zero, terminalEq] at changeVariables
  rw [intervalIntegral.integral_smul]
  calc
    (scale ^ 4 : ℝ) •
        ∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
          value (scale ^ 2 * scaledTime) =
      (scale ^ 2 : ℝ) •
        ((scale ^ 2 : ℝ) •
          ∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
            value (scale ^ 2 * scaledTime)) := by
        rw [smul_smul]
        congr 1
        ring
    _ = (scale ^ 2 : ℝ) •
        ∫ time in (0 : ℝ)..requestedTime, value time := by
      rw [changeVariables]

private theorem receipt_fixedWaveWeakAction_parabolic_change
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (test : ℝ → ℂ)
    (testSmooth : ContDiff ℝ ∞ test)
    (scale : ℝ) (scaleNe : scale ≠ 0) :
    let stateExtension : ℝ → ComplexCoordinateVector := fun time =>
      commonTimeZeroExtension requestedTime
        (fun localTime => receipt.wholePath localTime wave) time
    let nonlinearExtension : ℝ → ComplexCoordinateVector := fun time =>
      commonTimeZeroExtension requestedTime
        (fun localTime =>
          transverseSpaceTimeNonlinearRowFunction
            receipt.transverseLimit wave localTime) time
    (∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
      (scale ^ 4 : ℝ) •
        (deriv test (scale ^ 2 * scaledTime) •
          stateExtension (scale ^ 2 * scaledTime))) +
      (∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
        (scale ^ 4 : ℝ) •
          (test (scale ^ 2 * scaledTime) •
            nonlinearExtension (scale ^ 2 * scaledTime))) -
      (∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
        (scale ^ 4 : ℝ) •
          (test (scale ^ 2 * scaledTime) •
            ((nu.coeff * integerWaveViscousMultiplier wave) •
              stateExtension (scale ^ 2 * scaledTime)))) =
      (scale ^ 2 : ℝ) •
        fixedWaveWeakAction
          requestedTime nu.coeff wave
          (restrictedScalarL2 requestedTime test
            testSmooth.continuous.continuousOn)
          (restrictedScalarL2 requestedTime (deriv test)
            (testSmooth.continuous_deriv (by simp)).continuousOn)
          (restrictedScalarLInf requestedTime test
            testSmooth.continuous.continuousOn)
          receipt.stateLimit
          (transverseSpaceTimeNonlinearRow
            receipt.transverseLimit wave) := by
  dsimp only
  have derivativeChange := parabolic_intervalIntegral_change
    (fun time =>
      deriv test time •
        commonTimeZeroExtension requestedTime
          (fun localTime => receipt.wholePath localTime wave) time)
    scale requestedTime scaleNe
  have nonlinearChange := parabolic_intervalIntegral_change
    (fun time =>
      test time •
        commonTimeZeroExtension requestedTime
          (fun localTime =>
            transverseSpaceTimeNonlinearRowFunction
              receipt.transverseLimit wave localTime) time)
    scale requestedTime scaleNe
  have viscousChange := parabolic_intervalIntegral_change
    (fun time =>
      test time •
        ((nu.coeff * integerWaveViscousMultiplier wave) •
          commonTimeZeroExtension requestedTime
            (fun localTime => receipt.wholePath localTime wave) time))
    scale requestedTime scaleNe
  rw [derivativeChange, nonlinearChange, viscousChange]
  rw [receipt_fixedWaveWeakAction_eq_intervalIntegral
    receipt wave test testSmooth]
  module

private theorem c2MultiplierSeries_tendsto
    (coefficient multiplier : IntegerWavevector → ℂ)
    (multiplierConstant : ℝ)
    (c2Summable : Summable fun wave : IntegerWavevector =>
      (1 + integerWaveNormSq wave) * ‖coefficient wave‖)
    (multiplierBound : ∀ wave,
      ‖multiplier wave‖ ≤ multiplierConstant *
        (1 + integerWaveNormSq wave)) :
    Tendsto
      (fun radius : ℕ =>
        ∑ wave ∈ integerWaveFrequencyCube radius,
          (multiplier wave * coefficient wave) •
            UnitAddTorus.mFourier wave)
      atTop
      (nhds (∑' wave : IntegerWavevector,
        (multiplier wave * coefficient wave) •
          UnitAddTorus.mFourier wave)) := by
  have dominated : Summable fun wave : IntegerWavevector =>
      multiplierConstant *
        ((1 + integerWaveNormSq wave) * ‖coefficient wave‖) :=
    c2Summable.mul_left multiplierConstant
  have seriesSummable : Summable fun wave : IntegerWavevector =>
      (multiplier wave * coefficient wave) •
        UnitAddTorus.mFourier wave := by
    apply dominated.of_norm_bounded
    intro wave
    rw [norm_smul, norm_mul, UnitAddTorus.mFourier_norm, mul_one]
    calc
      ‖multiplier wave‖ * ‖coefficient wave‖ ≤
          (multiplierConstant * (1 + integerWaveNormSq wave)) *
            ‖coefficient wave‖ :=
        mul_le_mul_of_nonneg_right (multiplierBound wave) (norm_nonneg _)
      _ = multiplierConstant *
          ((1 + integerWaveNormSq wave) * ‖coefficient wave‖) := by ring
  exact seriesSummable.hasSum.comp integerWaveFrequencyCube_tendsto_atTop

/--
Compiles a scaled and recentered tensor-Schwartz test into canonical finite
trigonometric tests of one actual whole mild/Serrin receipt.  Every finite
action commutes with its unit-cell physical integral, endpoint write, and
parabolic time scaling.  The same coefficient family converges in its
second-order Fourier weight to the periodized test and recovers compactly
supported value, first-derivative, and second-derivative observations.
-/
theorem WholeContinuousMildSerrinReceipt.scaledRecenteredTensorSchwartzPhysicalWeakActionCompiler
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (spatialTest : Coordinate → 𝓢(ℝ, ℂ))
    (temporalTest : 𝓢(ℝ, ℂ))
    (scale : ℝ) (scaleNe : scale ≠ 0)
    (spaceCenter : PhysicalSpace)
    (timeCenter : ℝ)
    (testCoordinate : Coordinate) :
    let scaledTimeTest : ℝ → ℂ := fun time =>
      temporalTest ((time - timeCenter) / scale ^ 2)
    let scaledTimeSmooth : ContDiff ℝ ∞ scaledTimeTest := by
      dsimp only [scaledTimeTest]
      fun_prop
    let testCoefficient :
        IntegerWavevector → ComplexCoordinateVector := fun wave =>
      Pi.single testCoordinate
        (recenteredTensorSchwartzFourierCoefficient
          spatialTest scale scaleNe spaceCenter wave)
    let finiteAction : ℕ → ℝ := fun radius =>
      ∑ wave ∈ puncturedIntegerWaveFrequencyCube radius,
        complexCoordinateRealInner
          (testCoefficient wave)
          (fixedWaveWeakAction
            requestedTime nu.coeff wave
            (restrictedScalarL2 requestedTime scaledTimeTest
              scaledTimeSmooth.continuous.continuousOn)
            (restrictedScalarL2 requestedTime (deriv scaledTimeTest)
              (scaledTimeSmooth.continuous_deriv
                (by simp)).continuousOn)
            (restrictedScalarLInf requestedTime scaledTimeTest
              scaledTimeSmooth.continuous.continuousOn)
            receipt.stateLimit
            (transverseSpaceTimeNonlinearRow
              receipt.transverseLimit wave))
    let parabolicAction : ℕ → ℝ := fun radius =>
      ∑ wave ∈ puncturedIntegerWaveFrequencyCube radius,
        complexCoordinateRealInner (testCoefficient wave)
          ((∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
              (scale ^ 4 : ℝ) •
                (deriv scaledTimeTest (scale ^ 2 * scaledTime) •
                  commonTimeZeroExtension requestedTime
                    (fun localTime => receipt.wholePath localTime wave)
                    (scale ^ 2 * scaledTime))) +
            (∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
              (scale ^ 4 : ℝ) •
                (scaledTimeTest (scale ^ 2 * scaledTime) •
                  commonTimeZeroExtension requestedTime
                    (fun localTime =>
                      transverseSpaceTimeNonlinearRowFunction
                        receipt.transverseLimit wave localTime)
                    (scale ^ 2 * scaledTime))) -
            (∫ scaledTime in (0 : ℝ)..requestedTime / scale ^ 2,
              (scale ^ 4 : ℝ) •
                (scaledTimeTest (scale ^ 2 * scaledTime) •
                  ((nu.coeff * integerWaveViscousMultiplier wave) •
                    commonTimeZeroExtension requestedTime
                      (fun localTime => receipt.wholePath localTime wave)
                      (scale ^ 2 * scaledTime)))))
    let physicalAction : ℕ → ℝ := fun radius =>
      let modes := puncturedIntegerWaveFrequencyCube radius
      ∫ time : Icc (0 : ℝ) requestedTime,
        ((∫ x in physicalUnitCell,
          velocityDot
            (finiteRealComplexFourierField modes (fun wave =>
              star (deriv scaledTimeTest time.1) • testCoefficient wave))
            (finiteRealComplexFourierField modes
              (receipt.transverseLimit time).1) x) +
        (∫ x in physicalUnitCell,
          velocityDot
            (finiteRealComplexFourierField modes (fun wave =>
              star (scaledTimeTest time.1) • testCoefficient wave))
            (finiteRealComplexFourierField modes (fun wave =>
              wholeStateVorticityNonlinearCoefficientAt
                (receipt.transverseLimit time).1 wave)) x) -
        (∫ x in physicalUnitCell,
          velocityDot
            (finiteRealComplexFourierField modes (fun wave =>
              star (scaledTimeTest time.1 *
                ((nu.coeff * integerWaveViscousMultiplier wave : ℝ) : ℂ)) •
                  testCoefficient wave))
            (finiteRealComplexFourierField modes
              (receipt.transverseLimit time).1) x))
        ∂(commonTimeMeasure requestedTime)
    let endpointAction : ℕ → ℝ := fun radius =>
      ∑ wave ∈ puncturedIntegerWaveFrequencyCube radius,
        complexCoordinateRealInner (testCoefficient wave)
          (scaledTimeTest requestedTime •
              receipt.wholePath
                ⟨requestedTime, receipt.requestedTimePos.le, le_rfl⟩ wave -
            scaledTimeTest 0 •
              receipt.wholePath
                ⟨0, le_rfl, receipt.requestedTimePos.le⟩ wave)
    let c2Weight : IntegerWavevector → ℝ := fun wave =>
      (1 + integerWaveNormSq wave) *
        ‖recenteredTensorSchwartzFourierCoefficient
          spatialTest scale scaleNe spaceCenter wave‖
    let spatialPolynomial := fun radius : ℕ =>
      ∑ wave ∈ integerWaveFrequencyCube radius,
        recenteredTensorSchwartzFourierCoefficient
            spatialTest scale scaleNe spaceCenter wave •
          UnitAddTorus.mFourier wave
    let spatialLimit :=
      ∑' wave : IntegerWavevector,
        recenteredTensorSchwartzFourierCoefficient
            spatialTest scale scaleNe spaceCenter wave •
          UnitAddTorus.mFourier wave
    let spatialMultiplierPolynomial :=
      fun (multiplier : IntegerWavevector → ℂ) (radius : ℕ) =>
        ∑ wave ∈ integerWaveFrequencyCube radius,
          (multiplier wave *
              recenteredTensorSchwartzFourierCoefficient
                spatialTest scale scaleNe spaceCenter wave) •
            UnitAddTorus.mFourier wave
    let spatialMultiplierLimit :=
      fun multiplier : IntegerWavevector → ℂ =>
        ∑' wave : IntegerWavevector,
          (multiplier wave *
              recenteredTensorSchwartzFourierCoefficient
                spatialTest scale scaleNe spaceCenter wave) •
            UnitAddTorus.mFourier wave
    (∀ radius : ℕ,
        finiteAction radius = physicalAction radius ∧
          finiteAction radius = endpointAction radius ∧
          parabolicAction radius = scale ^ 2 * finiteAction radius) ∧
      Summable c2Weight ∧
      Tendsto
        (fun radius =>
          ∑ wave ∈ integerWaveFrequencyCube radius, c2Weight wave)
        atTop (nhds (∑' wave, c2Weight wave)) ∧
      Tendsto spatialPolynomial atTop (nhds spatialLimit) ∧
      (∀ (multiplier : IntegerWavevector → ℂ)
          (multiplierConstant : ℝ),
        (∀ wave, ‖multiplier wave‖ ≤
          multiplierConstant * (1 + integerWaveNormSq wave)) →
        Tendsto (spatialMultiplierPolynomial multiplier) atTop
          (nhds (spatialMultiplierLimit multiplier))) ∧
      (∀ x : PhysicalSpace,
        spatialLimit
            (fun coordinate =>
              ((x coordinate : ℝ) : UnitAddCircle)) =
          ∏ coordinate : Coordinate,
            ∑' shift : ℤ,
              spatialTest coordinate
                (scale⁻¹ *
                  (x coordinate - spaceCenter coordinate + shift))) ∧
      ∀ coordinate : Coordinate,
        ∀ supportRadius observationRadius x : ℝ,
          0 < scale⁻¹ →
          supportRadius + observationRadius < scale⁻¹ →
          |x| ≤ observationRadius →
          (∀ y : ℝ,
            supportRadius < |y| → spatialTest coordinate y = 0) →
          (∑' shift : ℤ,
              spatialTest coordinate (x + scale⁻¹ * shift)) =
              spatialTest coordinate x ∧
            (∑' shift : ℤ,
              (∂_{(1 : ℝ)} (spatialTest coordinate))
                (x + scale⁻¹ * shift)) =
              (∂_{(1 : ℝ)} (spatialTest coordinate)) x ∧
            (∑' shift : ℤ,
              (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (spatialTest coordinate)))
                (x + scale⁻¹ * shift)) =
              (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (spatialTest coordinate))) x := by
  dsimp only
  have scaledTimeSmooth : ContDiff ℝ ∞
      (fun time => temporalTest ((time - timeCenter) / scale ^ 2)) := by
    fun_prop
  have modesZeroFree (radius : ℕ) :
      ∀ wave ∈ puncturedIntegerWaveFrequencyCube radius, wave ≠ 0 := by
    intro wave waveMem waveZero
    subst wave
    exact zero_not_mem_puncturedIntegerWaveFrequencyCube radius waveMem
  have modesNegClosed (radius : ℕ) :
      ∀ {wave}, wave ∈ puncturedIntegerWaveFrequencyCube radius →
        waveNeg wave ∈ puncturedIntegerWaveFrequencyCube radius := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
  have c2Summable :=
    recenteredTensorSchwartzFourierCoefficient_c2_summable
      spatialTest scale scaleNe spaceCenter
  have seriesSummable :=
    recenteredTensorSchwartzFourierSeries_summable
      spatialTest scale scaleNe spaceCenter
  refine ⟨?_, c2Summable,
    c2Summable.hasSum.comp integerWaveFrequencyCube_tendsto_atTop,
    seriesSummable.hasSum.comp integerWaveFrequencyCube_tendsto_atTop,
    ?_, ?_, ?_⟩
  · intro radius
    refine ⟨?_, ?_, ?_⟩
    · exact receipt_finiteTrigonometricWeakAction_eq_physicalIntegral
        receipt (puncturedIntegerWaveFrequencyCube radius)
        (modesNegClosed radius)
        (fun wave => Pi.single testCoordinate
          (recenteredTensorSchwartzFourierCoefficient
            spatialTest scale scaleNe spaceCenter wave))
        (fun time => temporalTest ((time - timeCenter) / scale ^ 2))
        scaledTimeSmooth
    · exact
        WholeContinuousMildSerrinReceipt.finiteTrigonometricWeakAction_eq_boundary
          receipt (puncturedIntegerWaveFrequencyCube radius)
          (modesZeroFree radius)
          (fun wave => Pi.single testCoordinate
            (recenteredTensorSchwartzFourierCoefficient
              spatialTest scale scaleNe spaceCenter wave))
          (fun time => temporalTest ((time - timeCenter) / scale ^ 2))
          scaledTimeSmooth
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [receipt_fixedWaveWeakAction_parabolic_change
        receipt wave
        (fun time => temporalTest ((time - timeCenter) / scale ^ 2))
        scaledTimeSmooth scale scaleNe]
      rw [ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.complexCoordinateRealInner_real_smul_right]
  · intro multiplier multiplierConstant multiplierBound
    exact c2MultiplierSeries_tendsto
      (fun wave => recenteredTensorSchwartzFourierCoefficient
        spatialTest scale scaleNe spaceCenter wave)
      multiplier multiplierConstant c2Summable multiplierBound
  · intro x
    rw [← ContinuousMap.tsum_apply seriesSummable]
    exact recenteredTensorSchwartzFourierSeries_physical_eq
      spatialTest scale scaleNe spaceCenter x
  · intro coordinate supportRadius observationRadius x
      periodPos periodLarge xBound support
    exact scaledSchwartzTest_periodization_eq_self_C2_of_compactSupport
      (spatialTest coordinate) supportRadius observationRadius scale⁻¹ x
      periodPos periodLarge xBound support


end

end ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinWeakAction
end NavierStokes
end SaturationMonoid
