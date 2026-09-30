import H0mework.NavierStokes.ShellSources.WholeEnstrophyIdentity
import H0mework.NavierStokes.GeneratedPaths.WholeReceiptPersistence
import H0mework.NavierStokes.GeneratedPaths.ViscousEnstrophyCost

/-!
# Whole-path receipt-square continuation cost

An arbitrary finite prefix of one source-generated integer-shell lineage
writes pairwise-disjoint receipt supports into the same actual whole mild
solution.  For the `i`-th receipt, its source quantum `qᵢ`, selected shell
frequency `sᵢ`, and the generated whole `L²_t H⁻¹_x` tangent ceiling determine
the positive persistence time

```text
τᵢ = qᵢ / (12 (2π)² sᵢ max(1, B)).
```

On `[0, τᵢ]` at least `qᵢ / 4` remains on that exact support.  Multiplying by
the enstrophy weight `sᵢ` cancels the generated frequency and forces the
actual whole solution to pay

```text
qᵢ² / (48 (2π)² max(1, B)).
```

Disjoint source receipts then sum this cost without a shell-cardinality
loss.  The terminal theorem generates one common whole solution and bounds
the complete receipt-square prefix by its actual Euclidean gradient mass,
then by the existing cutoff-free strict-critical gradient ceiling.

The source producer remains unchanged.  In particular, no path, cutoff,
persistence window, amplitude lower bound, or target continuation receipt is
accepted by the source mouth.  The strict critical margin is consumed only
by the independent whole-solution continuation theorem.
-/

open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation

open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion.GeneratedIntegerShellInfiniteLineage
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPathTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellNonlinearNegativeOneForcing
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalEnvelope
open ThreeDimensionalVorticityCoefficientGeneratedPathWholeReceiptPersistence
open ThreeDimensionalVorticityCoefficientGeneratedPathViscousEnstrophyCost
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne

noncomputable section

theorem path_sub_eq_intervalIntegral
    {path tangent : ℝ → ComplexCoordinateVector}
    {a b : ℝ}
    (pathAC : AbsolutelyContinuousOnInterval path a b)
    (tangentIntegrable :
      IntervalIntegrable tangent MeasureTheory.volume a b)
    (pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ Set.uIcc a b →
          HasDerivAt path (tangent time) time)
    (time : ℝ)
    (timeMem : time ∈ Set.uIcc a b) :
    path time - path a =
      ∫ earlier in a..time, tangent earlier := by
  let integratedPath :=
    intervalIntegralComplexCoordinatePath
      (path a) tangent a
  have integratedPathAC :
      AbsolutelyContinuousOnInterval integratedPath a b :=
    intervalIntegralComplexCoordinatePath_absolutelyContinuousOnInterval
      (path a) tangentIntegrable
  have integratedPathDerivative :
      ∀ᵐ actual : ℝ,
        actual ∈ Set.uIcc a b →
          HasDerivAt integratedPath (tangent actual) actual := by
    filter_upwards [
      tangentIntegrable.ae_hasDerivAt_integral] with
        actual integralDerivative
    intro actualMem
    have actualIntegralDerivative :=
      integralDerivative actualMem a (by simp)
    change
      HasDerivAt
        ((fun _ : ℝ => path a) +
          fun terminal =>
            ∫ earlier in a..terminal, tangent earlier)
        (tangent actual)
        actual
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const actual (path a)).add
        actualIntegralDerivative
  have differenceAC :
      AbsolutelyContinuousOnInterval
        (fun actual => path actual - integratedPath actual)
        a b :=
    pathAC.sub integratedPathAC
  have differenceDerivative :
      ∀ᵐ actual : ℝ,
        actual ∈ Set.uIcc a b →
          HasDerivAt
            (fun terminal =>
              path terminal - integratedPath terminal)
            0 actual := by
    filter_upwards [
      pathDerivative, integratedPathDerivative] with
        actual pathDeriv integratedDeriv
    intro actualMem
    change
      HasDerivAt (path - integratedPath) 0 actual
    simpa only [sub_self] using
      (pathDeriv actualMem).sub (integratedDeriv actualMem)
  obtain ⟨constant, constantEq⟩ :=
    differenceAC.const_of_ae_hasDerivAt_zero
      differenceDerivative
  have atStart := constantEq a (by simp)
  have atTime := constantEq time timeMem
  have integratedAtStart :
      integratedPath a = path a := by
    simp [integratedPath, intervalIntegralComplexCoordinatePath]
  have integratedAtTime :
      integratedPath time =
        path a + ∫ earlier in a..time, tangent earlier := by
    rfl
  rw [integratedAtStart, sub_self] at atStart
  rw [← atStart] at atTime
  have pathEq : path time = integratedPath time :=
    sub_eq_zero.mp atTime
  rw [integratedAtTime] at pathEq
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using pathEq)

theorem norm_integral_sq_le_measureReal_mul_integral_norm_sq
    {α E : Type*}
    [MeasurableSpace α]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    (f : α → E)
    (fMemLp : MeasureTheory.MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤
      μ.real Set.univ * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have normMemLp :
      MeasureTheory.MemLp
        (fun x => ‖f x‖)
        (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using fMemLp.norm
  have oneMemLp :
      MeasureTheory.MemLp
        (fun _ : α => (1 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) μ :=
    MeasureTheory.memLp_const 1
  have cauchy :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (μ := μ)
      (f := fun _ : α => (1 : ℝ))
      (g := fun x => ‖f x‖)
      (Filter.Eventually.of_forall fun _ => zero_le_one)
      (Filter.Eventually.of_forall fun x => norm_nonneg (f x))
      oneMemLp normMemLp
  have cauchySqrt :
      ∫ x, ‖f x‖ ∂μ ≤
        Real.sqrt (μ.real Set.univ) *
          Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    norm_num [Real.sqrt_eq_rpow] at cauchy ⊢
    exact cauchy
  have normIntegralLe :
      ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
    MeasureTheory.norm_integral_le_integral_norm _
  have rhsSqrtNonneg :
      0 ≤
        Real.sqrt (μ.real Set.univ) *
          Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have chained :
      ‖∫ x, f x ∂μ‖ ≤
        Real.sqrt (μ.real Set.univ) *
          Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) :=
    normIntegralLe.trans cauchySqrt
  have squared :=
    (sq_le_sq₀ (norm_nonneg _) rhsSqrtNonneg).mpr chained
  rw [
    mul_pow,
    Real.sq_sqrt (MeasureTheory.measureReal_def _ _ ▸ ENNReal.toReal_nonneg),
    Real.sq_sqrt
      (MeasureTheory.integral_nonneg fun x => sq_nonneg ‖f x‖)] at squared
  exact squared

def actualWaveTangent
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    ℝ → ComplexCoordinateVector :=
  fun time =>
    WholeContinuousMildReceipt.actualWaveNonlinearExtension
        receipt.toWholeContinuousMildReceipt wave time -
      (ν.coeff * integerWaveViscousMultiplier wave) •
        WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
          receipt.toWholeContinuousMildReceipt wave time

theorem fixedWaveNegativeOneTangentL2_ae_actual
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
        receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
        wave) time =
      actualWaveTangent receipt wave time.1 := by
  let negativeReceipt :=
    receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
  let tangentRow :=
    fixedWaveSpaceTimeRestriction requestedTime wave
      (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
        negativeReceipt)
  let stateLp :=
    BoundedContinuousFunction.toLp 2
      (commonTimeMeasure requestedTime) ℂ receipt.wholePath
  have tangentSmulAE :=
    MeasureTheory.Lp.coeFn_smul
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)
      tangentRow
  have tangentRestrictionAE :=
    fixedWaveSpaceTimeRestriction_coeFn
      requestedTime wave
      (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
        negativeReceipt)
  have tangentRowAE :=
    NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent_unweighted_row_ae
      negativeReceipt wave waveNe
  have stateAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime)
      ℂ receipt.wholePath
  rw [receipt.wholePath_toLp_eq_stateLimit] at stateAE
  filter_upwards [
    tangentSmulAE, tangentRestrictionAE, tangentRowAE, stateAE] with
      time tangentSmulEq tangentRestrictionEq tangentEq stateEq
  change
    (((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
      tangentRow) time) =
      actualWaveTangent receipt wave time.1
  rw [tangentSmulEq]
  simp only [Pi.smul_apply]
  rw [tangentRestrictionEq]
  have scalarEq :
      (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
          (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            negativeReceipt time) wave =
        (Real.sqrt (integerWaveViscousMultiplier wave) : ℝ) •
          (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            negativeReceipt time) wave := by
    ext coordinate
    simp [Complex.real_smul]
  rw [scalarEq, tangentEq]
  unfold actualWaveTangent
  rw [WholeContinuousMildReceipt.actualWaveNonlinearExtension,
    commonTimeZeroExtension_of_mem
      requestedTime
      (ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow.transverseSpaceTimeNonlinearRow
        receipt.transverseLimit wave)
      time.1 time.property]
  have pathEq :=
    WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
      receipt.toWholeContinuousMildReceipt wave waveNe time
  rw [← pathEq, ← stateEq]

theorem actualWaveTangent_intervalIntegrable
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (actualWaveTangent receipt wave)
      MeasureTheory.volume 0 requestedTime := by
  let path :=
    WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
      receipt.toWholeContinuousMildReceipt wave
  have pathAC :
      AbsolutelyContinuousOnInterval path 0 requestedTime :=
    heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
      (receipt.initialState wave)
      (ν.coeff * integerWaveViscousMultiplier wave)
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        receipt.toWholeContinuousMildReceipt wave)
      (by simp [requestedTimePos.le])
  have pathContinuous :
      ContinuousOn path (Set.Icc (0 : ℝ) requestedTime) := by
    rw [← Set.uIcc_of_le requestedTimePos.le]
    exact pathAC.continuousOn
  have viscousIntegrable :
      IntervalIntegrable
        (fun time =>
          (ν.coeff * integerWaveViscousMultiplier wave) •
            path time)
        MeasureTheory.volume 0 requestedTime :=
    by
      have scalarContinuous :
          ContinuousOn
            (fun _ : ℝ =>
              ν.coeff * integerWaveViscousMultiplier wave)
            (Set.Icc (0 : ℝ) requestedTime) :=
        continuousOn_const
      exact
        (scalarContinuous.smul pathContinuous).intervalIntegrable_of_Icc
          requestedTimePos.le
  exact
    (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
      receipt.toWholeContinuousMildReceipt wave).sub
        viscousIntegrable

theorem actualWavePath_sub_initial_eq_intervalIntegral
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (time : ℝ)
    (timeMem : time ∈ Set.Icc (0 : ℝ) requestedTime) :
    WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
          receipt.toWholeContinuousMildReceipt wave time -
        receipt.initialState wave =
      ∫ earlier in (0 : ℝ)..time,
        actualWaveTangent receipt wave earlier := by
  let path :=
    WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
      receipt.toWholeContinuousMildReceipt wave
  have pathAC :
      AbsolutelyContinuousOnInterval path 0 requestedTime :=
    heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
      (receipt.initialState wave)
      (ν.coeff * integerWaveViscousMultiplier wave)
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        receipt.toWholeContinuousMildReceipt wave)
      (by simp [requestedTimePos.le])
  have pathDerivative :
      ∀ᵐ actual : ℝ,
        actual ∈ Set.uIcc (0 : ℝ) requestedTime →
          HasDerivAt path
            (actualWaveTangent receipt wave actual)
            actual := by
    change
      ∀ᵐ actual : ℝ,
        actual ∈ Set.uIcc (0 : ℝ) requestedTime →
          HasDerivAt
            (heatDuhamelComplexCoordinatePath
              (receipt.initialState wave)
              (WholeContinuousMildReceipt.actualWaveNonlinearExtension
                receipt.toWholeContinuousMildReceipt wave)
              (ν.coeff * integerWaveViscousMultiplier wave)
              0)
            (WholeContinuousMildReceipt.actualWaveNonlinearExtension
                receipt.toWholeContinuousMildReceipt wave actual -
              (ν.coeff * integerWaveViscousMultiplier wave) •
                heatDuhamelComplexCoordinatePath
                  (receipt.initialState wave)
                  (WholeContinuousMildReceipt.actualWaveNonlinearExtension
                    receipt.toWholeContinuousMildReceipt wave)
                  (ν.coeff * integerWaveViscousMultiplier wave)
                  0 actual)
            actual
    exact
      heatDuhamelComplexCoordinatePath_ae_hasDerivAt
        (receipt.initialState wave)
        (ν.coeff * integerWaveViscousMultiplier wave)
        0
        (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
          receipt.toWholeContinuousMildReceipt wave)
        (by simp [requestedTimePos.le])
  have update :=
    path_sub_eq_intervalIntegral
      pathAC
      (actualWaveTangent_intervalIntegrable receipt wave)
      pathDerivative time
      (by simpa [Set.uIcc_of_le requestedTimePos.le] using timeMem)
  have pathZero : path 0 = receipt.initialState wave := by
    simp [path, WholeContinuousMildReceipt.actualWaveHeatDuhamelPath,
      heatDuhamelComplexCoordinatePath,
      intervalIntegralComplexCoordinatePath]
  simpa [path, pathZero] using update

theorem commonTimeMeasure_Iic_real
    (requestedTime : ℝ)
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    ((commonTimeMeasure requestedTime).restrict
        (Set.Iic time)).real Set.univ =
      time.1 := by
  have converted :=
    commonTime_integral_Iic_eq_intervalIntegral
      requestedTime requestedTimeNonneg time
      (fun _ : ℝ => (1 : ℝ))
  simpa [
    MeasureTheory.integral_const,
    MeasureTheory.Measure.restrict_apply_univ,
    intervalIntegral.integral_const,
    smul_eq_mul] using converted

theorem actualWave_timeIncrement_normSq_le
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    ‖WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
          receipt.toWholeContinuousMildReceipt wave time.1 -
        receipt.initialState wave‖ ^ 2 ≤
      time.1 *
        ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
          receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
          wave‖ ^ 2 := by
  let tangentRow :=
    NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
      receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
      wave
  have endpointUpdate :=
    actualWavePath_sub_initial_eq_intervalIntegral
      receipt wave time.1 time.property
  have converted :=
    commonTime_integral_Iic_eq_intervalIntegral
      requestedTime requestedTimePos.le time
      (actualWaveTangent receipt wave)
  have rowAE :=
    fixedWaveNegativeOneTangentL2_ae_actual
      receipt wave waveNe
  have setIntegralEq :
      (∫ actual in Set.Iic time,
          tangentRow actual
          ∂(commonTimeMeasure requestedTime)) =
        ∫ actual in Set.Iic time,
          actualWaveTangent receipt wave actual.1
          ∂(commonTimeMeasure requestedTime) := by
    apply MeasureTheory.integral_congr_ae
    have rowAERestricted :
        ∀ᵐ actual ∂
            (commonTimeMeasure requestedTime).restrict
              (Set.Iic time),
          tangentRow actual =
            actualWaveTangent receipt wave actual.1 :=
      MeasureTheory.ae_restrict_le rowAE
    filter_upwards [rowAERestricted] with actual equality
    exact equality
  have endpointAsSetIntegral :
      WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            receipt.toWholeContinuousMildReceipt wave time.1 -
          receipt.initialState wave =
        ∫ actual in Set.Iic time,
          tangentRow actual
          ∂(commonTimeMeasure requestedTime) := by
    rw [endpointUpdate, ← converted, ← setIntegralEq]
  have rowMemLp :
      MeasureTheory.MemLp
        (fun actual => tangentRow actual)
        2
        ((commonTimeMeasure requestedTime).restrict
          (Set.Iic time)) :=
    (MeasureTheory.Lp.memLp tangentRow).restrict (Set.Iic time)
  have cauchy :=
    norm_integral_sq_le_measureReal_mul_integral_norm_sq
      (μ :=
        (commonTimeMeasure requestedTime).restrict
          (Set.Iic time))
      (fun actual => tangentRow actual)
      rowMemLp
  have rowNormSqIntegrable :
      MeasureTheory.Integrable
        (fun actual => ‖tangentRow actual‖ ^ 2)
        (commonTimeMeasure requestedTime) :=
    (MeasureTheory.Lp.memLp tangentRow).integrable_norm_pow
      (by norm_num)
  have restrictedIntegralLe :
      (∫ actual in Set.Iic time,
          ‖tangentRow actual‖ ^ 2
          ∂(commonTimeMeasure requestedTime)) ≤
        ‖tangentRow‖ ^ 2 := by
    rw [fixedWaveSpaceTimeState_norm_sq_eq_integral]
    exact
      MeasureTheory.setIntegral_le_integral
        rowNormSqIntegrable
        (Filter.Eventually.of_forall fun actual =>
          sq_nonneg ‖tangentRow actual‖)
  rw [endpointAsSetIntegral]
  calc
    ‖∫ actual in Set.Iic time,
        tangentRow actual
        ∂(commonTimeMeasure requestedTime)‖ ^ 2 ≤
      ((commonTimeMeasure requestedTime).restrict
          (Set.Iic time)).real Set.univ *
        ∫ actual in Set.Iic time,
          ‖tangentRow actual‖ ^ 2
          ∂(commonTimeMeasure requestedTime) :=
      cauchy
    _ =
      time.1 *
        ∫ actual in Set.Iic time,
          ‖tangentRow actual‖ ^ 2
          ∂(commonTimeMeasure requestedTime) := by
      rw [commonTimeMeasure_Iic_real
        requestedTime requestedTimePos.le time]
    _ ≤ time.1 * ‖tangentRow‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        restrictedIntegralLe time.2.1

theorem receiptWave_ne_zero
    (sourceReceipt : GeneratedIntegerShellReceipt)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ sourceReceipt.wholeShellModes) :
    wave ≠ 0 := by
  intro waveZero
  have waveShell :
      integerWaveShellSq wave =
        sourceReceipt.selectedShellSq :=
    ((mem_generatedOuterNonlinearShellModes_iff
      sourceReceipt.current sourceReceipt.selectedShellSq wave).mp
        waveMem).2
  rw [waveZero, integerWaveShellSq_zero] at waveShell
  have shellPos :=
    generatedIntegerShellReceipt_selectedShellSq_pos sourceReceipt
  omega

theorem receiptWave_multiplier
    (sourceReceipt : GeneratedIntegerShellReceipt)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ sourceReceipt.wholeShellModes) :
    integerWaveViscousMultiplier wave =
      (2 * Real.pi) ^ 2 *
        (sourceReceipt.selectedShellSq : ℝ) := by
  unfold integerWaveViscousMultiplier
  rw [integerWaveNormSq_eq_integerWaveShellSq]
  have waveShell :
      integerWaveShellSq wave =
        sourceReceipt.selectedShellSq :=
    ((mem_generatedOuterNonlinearShellModes_iff
      sourceReceipt.current sourceReceipt.selectedShellSq wave).mp
        waveMem).2
  rw [waveShell]

theorem fixedWaveNegativeOneTangentL2_norm_sq_eq
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
        receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
        wave‖ ^ 2 =
      integerWaveViscousMultiplier wave *
        ‖fixedWaveSpaceTimeRestriction requestedTime wave
          (NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt)‖ ^ 2 := by
  have multiplierNonneg :
      0 ≤ integerWaveViscousMultiplier wave := by
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)
  unfold
    NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
  rw [norm_smul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt multiplierNonneg]

theorem receiptShell_fixedWaveTangent_norm_sq_le
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (sourceReceipt : GeneratedIntegerShellReceipt) :
    (∑ wave ∈ sourceReceipt.wholeShellModes,
        ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
          receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
          wave‖ ^ 2) ≤
      (2 * Real.pi) ^ 2 *
          (sourceReceipt.selectedShellSq : ℝ) *
        ‖NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
          receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt‖ ^ 2 := by
  let wholeTangent :=
    NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
      receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
  let multiplier :=
    (2 * Real.pi) ^ 2 *
      (sourceReceipt.selectedShellSq : ℝ)
  have multiplierNonneg : 0 ≤ multiplier := by
    exact mul_nonneg (sq_nonneg _)
      (generatedIntegerShellReceipt_selectedShellSq_cast_pos
        sourceReceipt).le
  have restrictionSummable :
      Summable fun wave : IntegerWavevector =>
        ‖fixedWaveSpaceTimeRestriction
          requestedTime wave wholeTangent‖ ^ 2 :=
    summable_fixedWaveSpaceTimeRestriction_norm_sq
      requestedTime wholeTangent
  have finiteRestrictionLe :
      (∑ wave ∈ sourceReceipt.wholeShellModes,
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave wholeTangent‖ ^ 2) ≤
        ∑' wave : IntegerWavevector,
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave wholeTangent‖ ^ 2 :=
    restrictionSummable.sum_le_tsum
      sourceReceipt.wholeShellModes
      (fun wave waveMem => sq_nonneg _)
  calc
    (∑ wave ∈ sourceReceipt.wholeShellModes,
        ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
          receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
          wave‖ ^ 2) =
      ∑ wave ∈ sourceReceipt.wholeShellModes,
        multiplier *
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave wholeTangent‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [
        fixedWaveNegativeOneTangentL2_norm_sq_eq
          receipt wave,
        receiptWave_multiplier sourceReceipt waveMem]
    _ =
      multiplier *
        ∑ wave ∈ sourceReceipt.wholeShellModes,
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave wholeTangent‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤
      multiplier *
        ∑' wave : IntegerWavevector,
          ‖fixedWaveSpaceTimeRestriction
            requestedTime wave wholeTangent‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        finiteRestrictionLe multiplierNonneg
    _ =
      multiplier * ‖wholeTangent‖ ^ 2 := by
      rw [tsum_fixedWaveSpaceTimeRestriction_norm_sq]
    _ =
      (2 * Real.pi) ^ 2 *
          (sourceReceipt.selectedShellSq : ℝ) *
        ‖NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
          receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt‖ ^ 2 := by
      rfl

theorem receiptSupportDifferenceEnergy_wholePath_le
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (sourceReceipt : GeneratedIntegerShellReceipt)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    receiptSupportDifferenceEnergy sourceReceipt
        receipt.initialState (receipt.wholePath time) ≤
      3 * time.1 * (2 * Real.pi) ^ 2 *
          (sourceReceipt.selectedShellSq : ℝ) *
        ‖NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
          receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt‖ ^ 2 := by
  let differenceState : ComplexVorticityHilbertState :=
    receipt.initialState - receipt.wholePath time
  have supportDifferenceEq :
      receiptSupportDifferenceEnergy sourceReceipt
          receipt.initialState (receipt.wholePath time) =
        receiptSupportEnergy sourceReceipt differenceState := by
    unfold receiptSupportDifferenceEnergy receiptSupportEnergy
    apply Finset.sum_congr rfl
    intro index indexMem
    rfl
  have eachWave :
      ∀ wave ∈ sourceReceipt.wholeShellModes,
        complexCoordinateAmplitudeSq (differenceState wave) ≤
          3 * time.1 *
            ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
              receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
              wave‖ ^ 2 := by
    intro wave waveMem
    have waveNe :=
      receiptWave_ne_zero sourceReceipt waveMem
    have pathEq :=
      WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
        receipt.toWholeContinuousMildReceipt wave waveNe time
    have increment :=
      actualWave_timeIncrement_normSq_le
        receipt wave waveNe time
    calc
      complexCoordinateAmplitudeSq (differenceState wave) ≤
          3 * ‖differenceState wave‖ ^ 2 :=
        complexCoordinateAmplitudeSq_le_three_mul_norm_sq _
      _ =
          3 *
            ‖WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                  receipt.toWholeContinuousMildReceipt wave time.1 -
                receipt.initialState wave‖ ^ 2 := by
        change
          3 *
              ‖receipt.initialState wave -
                receipt.wholePath time wave‖ ^ 2 =
            3 *
              ‖WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
                  receipt.toWholeContinuousMildReceipt wave time.1 -
                receipt.initialState wave‖ ^ 2
        rw [pathEq, norm_sub_rev]
      _ ≤
          3 *
            (time.1 *
              ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
                receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
                wave‖ ^ 2) :=
        mul_le_mul_of_nonneg_left increment (by norm_num)
      _ =
          3 * time.1 *
            ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
              receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
              wave‖ ^ 2 := by
        ring
  have shellTangentBound :=
    receiptShell_fixedWaveTangent_norm_sq_le
      receipt sourceReceipt
  rw [supportDifferenceEq]
  calc
    receiptSupportEnergy sourceReceipt differenceState ≤
        generatedIntegerShellReceiptWholeShellVorticityMass
          sourceReceipt differenceState :=
      receiptSupportEnergy_le_wholeShellVorticityMass
        sourceReceipt differenceState
    _ ≤
        ∑ wave ∈ sourceReceipt.wholeShellModes,
          3 * time.1 *
            ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
              receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
              wave‖ ^ 2 := by
      unfold generatedIntegerShellReceiptWholeShellVorticityMass
      apply Finset.sum_le_sum
      intro wave waveMem
      exact eachWave wave waveMem
    _ =
        3 * time.1 *
          ∑ wave ∈ sourceReceipt.wholeShellModes,
            ‖NonlinearNegativeOneForcingReceipt.fixedWaveNegativeOneTangentL2
              receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt
              wave‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤
        3 * time.1 *
          ((2 * Real.pi) ^ 2 *
              (sourceReceipt.selectedShellSq : ℝ) *
            ‖NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
              receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt‖ ^ 2) :=
      mul_le_mul_of_nonneg_left shellTangentBound
        (mul_nonneg (by norm_num) time.2.1)
    _ =
      3 * time.1 * (2 * Real.pi) ^ 2 *
          (sourceReceipt.selectedShellSq : ℝ) *
        ‖NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
          receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt‖ ^ 2 := by
      ring

theorem receiptSupportDifferenceEnergy_wholePath_le_generated
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (sourceReceipt : GeneratedIntegerShellReceipt)
    (time : Set.Icc (0 : ℝ) requestedTime) :
    receiptSupportDifferenceEnergy sourceReceipt
        receipt.initialState (receipt.wholePath time) ≤
      3 * time.1 * (2 * Real.pi) ^ 2 *
          (sourceReceipt.selectedShellSq : ℝ) *
        generatedWholeNegativeOneTangentCeiling ν θ := by
  have dynamicBound :=
    receiptSupportDifferenceEnergy_wholePath_le
      receipt sourceReceipt time
  have coefficientNonneg :
      0 ≤
        3 * time.1 * (2 * Real.pi) ^ 2 *
          (sourceReceipt.selectedShellSq : ℝ) := by
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) time.2.1)
          (sq_nonneg _))
        (generatedIntegerShellReceipt_selectedShellSq_cast_pos
          sourceReceipt).le
  exact
    dynamicBound.trans
      (mul_le_mul_of_nonneg_left
        receipt.wholeNegativeOneTangent_norm_sq_le_generated
        coefficientNonneg)

theorem continuous_receiptSupportEnergy
    (sourceReceipt : GeneratedIntegerShellReceipt) :
    Continuous (receiptSupportEnergy sourceReceipt) := by
  unfold receiptSupportEnergy
  apply continuous_finsetSum
  intro index indexMem
  exact
    Complex.continuous_normSq.comp
      ((continuous_apply index.2).comp
        (lp.evalCLM ℂ
          (fun _ : IntegerWavevector =>
            ComplexCoordinateVector)
          2 index.1).continuous)

theorem receipt_initial_energy
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
    (index : ℕ) :
    receiptSupportEnergy (lineage.receipt index)
        receipt.initialState =
      lineage.receiptQuantum index := by
  have endpointTendsto :
      Tendsto
        (fun length =>
          receiptSupportEnergy (lineage.receipt index)
            (endpointHilbertState lineage length))
        atTop
        (𝓝
          (receiptSupportEnergy (lineage.receipt index)
            receipt.initialState)) :=
    (continuous_receiptSupportEnergy
      (lineage.receipt index)).continuousAt.tendsto.comp
        (endpointHilbertState_tendsto_initialState receipt)
  have eventuallyExact :
      ∀ᶠ length in atTop,
        receiptSupportEnergy (lineage.receipt index)
            (endpointHilbertState lineage length) =
          lineage.receiptQuantum index := by
    filter_upwards [eventually_ge_atTop (index + 1)] with
      length lengthGe
    have indexLt : index < length := by omega
    have sourceReceiptMem :
        lineage.receipt index ∈
          generatedIntegerShellReachableReceipts
            (lineage.prefixReachable length) := by
      rw [lineage.prefixReachable_receipts length]
      exact
        List.mem_map.mpr
          ⟨index, List.mem_range.mpr indexLt, rfl⟩
    exact
      receiptSupportEnergy_generatedEndpoint
        (lineage.prefixReachable length)
        sourceReceiptMem
  have exactTendsto :
      Tendsto
        (fun length =>
          receiptSupportEnergy (lineage.receipt index)
            (endpointHilbertState lineage length))
        atTop
        (𝓝 (lineage.receiptQuantum index)) := by
    exact tendsto_const_nhds.congr'
      (eventuallyExact.mono fun length equality => equality.symm)
  exact tendsto_nhds_unique endpointTendsto exactTendsto

def generatedWholeReceiptPersistenceTime
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ)
    (ν : Viscosity)
    (θ : ℝ) : ℝ :=
  lineage.receiptQuantum index /
    (12 * (2 * Real.pi) ^ 2 *
      ((lineage.receipt index).selectedShellSq : ℝ) *
      max 1 (generatedWholeNegativeOneTangentCeiling ν θ))

theorem generatedWholeReceiptPersistenceTime_pos
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ)
    (ν : Viscosity)
    (θ : ℝ) :
    0 <
      generatedWholeReceiptPersistenceTime
        lineage index ν θ := by
  have frequencyPos : 0 < (2 * Real.pi) ^ 2 :=
    sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)
  have shellPos :
      0 <
        ((lineage.receipt index).selectedShellSq : ℝ) :=
    generatedIntegerShellReceipt_selectedShellSq_cast_pos
      (lineage.receipt index)
  have ceilingPos :
      0 <
        max 1 (generatedWholeNegativeOneTangentCeiling ν θ) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  unfold generatedWholeReceiptPersistenceTime
  exact
    div_pos (lineage.receiptQuantum_pos index)
      (mul_pos
        (mul_pos
          (mul_pos (by norm_num) frequencyPos)
          shellPos)
        ceilingPos)

theorem generatedWholeReceiptPersistenceTime_frequency_cancel
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ)
    (ν : Viscosity)
    (θ : ℝ) :
    3 * (2 * Real.pi) ^ 2 *
          ((lineage.receipt index).selectedShellSq : ℝ) *
          (generatedWholeReceiptPersistenceTime
              lineage index ν θ *
            max 1
              (generatedWholeNegativeOneTangentCeiling ν θ)) =
        lineage.receiptQuantum index / 4 := by
  have frequencyNe :
      (2 * Real.pi) ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have shellNe :
      ((lineage.receipt index).selectedShellSq : ℝ) ≠ 0 :=
    ne_of_gt
      (generatedIntegerShellReceipt_selectedShellSq_cast_pos
        (lineage.receipt index))
  have ceilingNe :
      max 1
          (generatedWholeNegativeOneTangentCeiling ν θ) ≠ 0 :=
    ne_of_gt
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  unfold generatedWholeReceiptPersistenceTime
  field_simp [frequencyNe, shellNe, ceilingNe]
  ring

theorem generatedWholeReceiptPersistenceTime_weighted_trace_eq
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (index : ℕ)
    (ν : Viscosity)
    (θ : ℝ) :
    generatedWholeReceiptPersistenceTime
          lineage index ν θ *
          (((lineage.receipt index).selectedShellSq : ℝ) *
            lineage.receiptQuantum index / 4) =
      lineage.receiptQuantum index ^ 2 /
        (48 * (2 * Real.pi) ^ 2 *
          max 1
            (generatedWholeNegativeOneTangentCeiling ν θ)) := by
  have frequencyNe :
      (2 * Real.pi) ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have shellNe :
      ((lineage.receipt index).selectedShellSq : ℝ) ≠ 0 :=
    ne_of_gt
      (generatedIntegerShellReceipt_selectedShellSq_cast_pos
        (lineage.receipt index))
  have ceilingNe :
      max 1
          (generatedWholeNegativeOneTangentCeiling ν θ) ≠ 0 :=
    ne_of_gt
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  unfold generatedWholeReceiptPersistenceTime
  field_simp [frequencyNe, shellNe, ceilingNe]
  ring

theorem lineageReceipt_persists_on_wholePath
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (index : ℕ)
    (persistenceTimeLe :
      generatedWholeReceiptPersistenceTime
          lineage index ν θ ≤
        requestedTime) :
    ∀ time :
        Set.Icc (0 : ℝ)
          (generatedWholeReceiptPersistenceTime
            lineage index ν θ),
      lineage.receiptQuantum index / 4 ≤
        receiptSupportEnergy
          (lineage.receipt index)
          (receipt.wholePath
            ⟨time.1,
              ⟨time.2.1,
                time.2.2.trans persistenceTimeLe⟩⟩) := by
  intro time
  let actualTime : Set.Icc (0 : ℝ) requestedTime :=
    ⟨time.1, ⟨time.2.1, time.2.2.trans persistenceTimeLe⟩⟩
  have dynamicBound :=
    receiptSupportDifferenceEnergy_wholePath_le_generated
      receipt (lineage.receipt index) actualTime
  have timeCeilingBound :
      time.1 *
          generatedWholeNegativeOneTangentCeiling ν θ ≤
        generatedWholeReceiptPersistenceTime
            lineage index ν θ *
          max 1
            (generatedWholeNegativeOneTangentCeiling ν θ) := by
    have tangentCeilingLe :
        generatedWholeNegativeOneTangentCeiling ν θ ≤
          max 1
            (generatedWholeNegativeOneTangentCeiling ν θ) :=
      le_max_right _ _
    have tangentCeilingNonneg :
        0 ≤ generatedWholeNegativeOneTangentCeiling ν θ := by
      exact
        le_trans (sq_nonneg
          ‖NonlinearNegativeOneForcingReceipt.wholeNegativeOneTangent
            receipt.toInfiniteMildDuhamelForcingReceipt.toNonlinearNegativeOneForcingReceipt‖)
          receipt.wholeNegativeOneTangent_norm_sq_le_generated
    exact
      mul_le_mul time.2.2 tangentCeilingLe
        tangentCeilingNonneg
        (generatedWholeReceiptPersistenceTime_pos
          lineage index ν θ).le
  have scaleNonneg :
      0 ≤
        3 * (2 * Real.pi) ^ 2 *
          ((lineage.receipt index).selectedShellSq : ℝ) := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (generatedIntegerShellReceipt_selectedShellSq_cast_pos
          (lineage.receipt index)).le
  have differenceSmall :
      receiptSupportDifferenceEnergy
            (lineage.receipt index)
            receipt.initialState
            (receipt.wholePath actualTime) ≤
        lineage.receiptQuantum index / 4 := by
    calc
      receiptSupportDifferenceEnergy
            (lineage.receipt index)
            receipt.initialState
            (receipt.wholePath actualTime) ≤
        3 * time.1 * (2 * Real.pi) ^ 2 *
            ((lineage.receipt index).selectedShellSq : ℝ) *
          generatedWholeNegativeOneTangentCeiling ν θ := by
        simpa [actualTime] using dynamicBound
      _ =
        (3 * (2 * Real.pi) ^ 2 *
          ((lineage.receipt index).selectedShellSq : ℝ)) *
          (time.1 *
            generatedWholeNegativeOneTangentCeiling ν θ) := by
        ring
      _ ≤
        (3 * (2 * Real.pi) ^ 2 *
          ((lineage.receipt index).selectedShellSq : ℝ)) *
          (generatedWholeReceiptPersistenceTime
              lineage index ν θ *
            max 1
              (generatedWholeNegativeOneTangentCeiling ν θ)) :=
        mul_le_mul_of_nonneg_left
          timeCeilingBound scaleNonneg
      _ = lineage.receiptQuantum index / 4 := by
        simpa using
          generatedWholeReceiptPersistenceTime_frequency_cancel
            lineage index ν θ
  have referenceBound :=
    receiptSupportEnergy_le_two_current_add_difference
      (lineage.receipt index)
      receipt.initialState
      (receipt.wholePath actualTime)
  rw [receipt_initial_energy
    receipt.toInfiniteMildDuhamelForcingReceipt index] at referenceBound
  change
    lineage.receiptQuantum index / 4 ≤
      receiptSupportEnergy
        (lineage.receipt index)
        (receipt.wholePath actualTime)
  linarith

def generatedWholePrefixPersistenceHorizon
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ)
    (ν : Viscosity)
    (θ : ℝ) : ℝ :=
  1 +
    ∑ index ∈ Finset.range length,
      generatedWholeReceiptPersistenceTime
        lineage index ν θ

theorem generatedWholePrefixPersistenceHorizon_pos
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ)
    (ν : Viscosity)
    (θ : ℝ) :
    0 <
      generatedWholePrefixPersistenceHorizon
        lineage length ν θ := by
  unfold generatedWholePrefixPersistenceHorizon
  have sumNonneg :
      0 ≤
        ∑ index ∈ Finset.range length,
          generatedWholeReceiptPersistenceTime
            lineage index ν θ :=
    Finset.sum_nonneg fun index indexMem =>
      (generatedWholeReceiptPersistenceTime_pos
        lineage index ν θ).le
  linarith

theorem generatedWholeReceiptPersistenceTime_le_prefixHorizon
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length index : ℕ)
    (indexLt : index < length)
    (ν : Viscosity)
    (θ : ℝ) :
    generatedWholeReceiptPersistenceTime
        lineage index ν θ ≤
      generatedWholePrefixPersistenceHorizon
        lineage length ν θ := by
  have ownLe :
      generatedWholeReceiptPersistenceTime
          lineage index ν θ ≤
        ∑ actual ∈ Finset.range length,
          generatedWholeReceiptPersistenceTime
            lineage actual ν θ :=
    Finset.single_le_sum
      (fun actual actualMem =>
        (generatedWholeReceiptPersistenceTime_pos
          lineage actual ν θ).le)
      (Finset.mem_range.mpr indexLt)
  unfold generatedWholePrefixPersistenceHorizon
  linarith

theorem lineagePrefix_persists_on_one_wholePath
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ actualLength : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current actualLength))
              (generatedComplexVorticityState
                (lineage.current actualLength)
                (generatedSupport (lineage.current actualLength))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ receipt :
        StrongContinuationReceipt
          lineage ν θ
          (generatedWholePrefixPersistenceHorizon
            lineage length ν θ)
          θLtOne criticalMargin
          (generatedWholePrefixPersistenceHorizon_pos
            lineage length ν θ),
      ∀ (index : ℕ) (indexLt : index < length),
        ∀ time :
          Set.Icc (0 : ℝ)
            (generatedWholeReceiptPersistenceTime
              lineage index ν θ),
          lineage.receiptQuantum index / 4 ≤
            receiptSupportEnergy
              (lineage.receipt index)
              (receipt.wholePath
                ⟨time.1,
                  ⟨time.2.1,
                    time.2.2.trans
                      (generatedWholeReceiptPersistenceTime_le_prefixHorizon
                        lineage length index indexLt ν θ)⟩⟩) := by
  let horizon :=
    generatedWholePrefixPersistenceHorizon
      lineage length ν θ
  let horizonPos :=
    generatedWholePrefixPersistenceHorizon_pos
      lineage length ν θ
  let receipt :
      StrongContinuationReceipt
        lineage ν θ horizon θLtOne criticalMargin horizonPos :=
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation.GeneratedIntegerShellInfiniteLineage.generates_strongContinuation
      lineage ν θ horizon θLtOne criticalMargin horizonPos
  refine ⟨receipt, ?_⟩
  intro index indexLt
  have persistenceTimeLe :
      generatedWholeReceiptPersistenceTime
          lineage index ν θ ≤
        horizon := by
    simpa [horizon] using
      generatedWholeReceiptPersistenceTime_le_prefixHorizon
        lineage length index indexLt ν θ
  have persists :=
    lineageReceipt_persists_on_wholePath
      receipt index persistenceTimeLe
  intro time
  simpa [receipt, horizon, horizonPos] using persists time

def wholePathExtension
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos) :
    ℝ → ComplexVorticityHilbertState :=
  commonTimeZeroExtension requestedTime receipt.wholePath

theorem lineageReceipt_wholePersistenceIntegral_lower
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (index : ℕ)
    (persistenceTimeLe :
      generatedWholeReceiptPersistenceTime
          lineage index ν θ ≤
        requestedTime) :
    lineage.receiptQuantum index ^ 2 /
          (48 * (2 * Real.pi) ^ 2 *
            max 1
              (generatedWholeNegativeOneTangentCeiling ν θ)) ≤
      ∫ time in (0 : ℝ)..
          generatedWholeReceiptPersistenceTime
            lineage index ν θ,
        receiptSupportEnstrophyMass
          (lineage.receipt index)
          (wholePathExtension receipt time) := by
  let persistenceTime :=
    generatedWholeReceiptPersistenceTime
      lineage index ν θ
  have persistenceTimePos :
      0 < persistenceTime :=
    generatedWholeReceiptPersistenceTime_pos
      lineage index ν θ
  have pathInclusionContinuous :
      Continuous
        (fun time : Set.Icc (0 : ℝ) persistenceTime =>
          (⟨time.1,
            ⟨time.2.1,
              time.2.2.trans persistenceTimeLe⟩⟩ :
            Set.Icc (0 : ℝ) requestedTime)) := by
    exact
      continuous_subtype_val.subtype_mk
        (fun time =>
          ⟨time.2.1,
            time.2.2.trans persistenceTimeLe⟩)
  have supportContinuous :
      ContinuousOn
        (fun time =>
          receiptSupportEnstrophyMass
            (lineage.receipt index)
            (wholePathExtension receipt time))
        (Set.Icc (0 : ℝ) persistenceTime) := by
    rw [continuousOn_iff_continuous_restrict]
    have pathContinuous :
        Continuous
          (fun time : Set.Icc (0 : ℝ) persistenceTime =>
            receipt.wholePath
              ⟨time.1,
                ⟨time.2.1,
                  time.2.2.trans persistenceTimeLe⟩⟩) :=
      receipt.wholePath.continuous.comp pathInclusionContinuous
    have energyContinuous :
        Continuous
          (fun time : Set.Icc (0 : ℝ) persistenceTime =>
            receiptSupportEnergy
              (lineage.receipt index)
              (receipt.wholePath
                ⟨time.1,
                  ⟨time.2.1,
                    time.2.2.trans persistenceTimeLe⟩⟩)) :=
      (continuous_receiptSupportEnergy
        (lineage.receipt index)).comp pathContinuous
    have weightedContinuous :
        Continuous
          (fun time : Set.Icc (0 : ℝ) persistenceTime =>
            ((lineage.receipt index).selectedShellSq : ℝ) *
              receiptSupportEnergy
                (lineage.receipt index)
                (receipt.wholePath
                  ⟨time.1,
                    ⟨time.2.1,
                      time.2.2.trans persistenceTimeLe⟩⟩)) :=
      continuous_const.mul energyContinuous
    apply weightedContinuous.congr
    intro time
    have horizonMem :
        time.1 ∈ Set.Icc (0 : ℝ) requestedTime :=
      ⟨time.property.1,
        time.property.2.trans persistenceTimeLe⟩
    change
      ((lineage.receipt index).selectedShellSq : ℝ) *
          receiptSupportEnergy
            (lineage.receipt index)
            (receipt.wholePath ⟨time.1, horizonMem⟩) =
        ((lineage.receipt index).selectedShellSq : ℝ) *
          receiptSupportEnergy
            (lineage.receipt index)
            (commonTimeZeroExtension
              requestedTime receipt.wholePath time.1)
    rw [commonTimeZeroExtension_of_mem
      requestedTime receipt.wholePath time.1 horizonMem]
  have supportIntegrable :
      IntervalIntegrable
        (fun time =>
          receiptSupportEnstrophyMass
            (lineage.receipt index)
            (wholePathExtension receipt time))
        MeasureTheory.volume 0 persistenceTime :=
    supportContinuous.intervalIntegrable_of_Icc
      persistenceTimePos.le
  have constantIntegrable :
      IntervalIntegrable
        (fun _ : ℝ =>
          ((lineage.receipt index).selectedShellSq : ℝ) *
              lineage.receiptQuantum index /
            4)
        MeasureTheory.volume 0 persistenceTime :=
    continuous_const.intervalIntegrable 0 persistenceTime
  have pointwiseLower :
      ∀ time ∈ Set.Icc (0 : ℝ) persistenceTime,
        ((lineage.receipt index).selectedShellSq : ℝ) *
              lineage.receiptQuantum index /
            4 ≤
          receiptSupportEnstrophyMass
            (lineage.receipt index)
            (wholePathExtension receipt time) := by
    intro time timeMem
    let actualTime : Set.Icc (0 : ℝ) persistenceTime :=
      ⟨time, timeMem⟩
    have persists :=
      lineageReceipt_persists_on_wholePath
        receipt index persistenceTimeLe actualTime
    have extensionEq :
        wholePathExtension receipt time =
          receipt.wholePath
            ⟨time,
              ⟨timeMem.1,
                timeMem.2.trans persistenceTimeLe⟩⟩ := by
      unfold wholePathExtension
      rw [commonTimeZeroExtension_of_mem
        requestedTime receipt.wholePath time
        ⟨timeMem.1,
          timeMem.2.trans persistenceTimeLe⟩]
    unfold receiptSupportEnstrophyMass
    rw [extensionEq]
    have weighted :=
      mul_le_mul_of_nonneg_left
        persists
        (generatedIntegerShellReceipt_selectedShellSq_cast_pos
          (lineage.receipt index)).le
    simpa only [mul_div_assoc] using weighted
  have integratedLower :=
    intervalIntegral.integral_mono_on
      persistenceTimePos.le
      constantIntegrable supportIntegrable pointwiseLower
  have normalizedLower :
      persistenceTime *
            (((lineage.receipt index).selectedShellSq : ℝ) *
              lineage.receiptQuantum index /
              4) ≤
        ∫ time in (0 : ℝ)..persistenceTime,
          receiptSupportEnstrophyMass
            (lineage.receipt index)
            (wholePathExtension receipt time) := by
    have integratedLower' :
        ((lineage.receipt index).selectedShellSq : ℝ) *
              (persistenceTime *
                lineage.receiptQuantum index) /
            4 ≤
          ∫ time in (0 : ℝ)..persistenceTime,
            receiptSupportEnstrophyMass
              (lineage.receipt index)
              (wholePathExtension receipt time) := by
      simpa [
        intervalIntegral.integral_const,
        sub_zero,
        smul_eq_mul] using integratedLower
    calc
      persistenceTime *
            (((lineage.receipt index).selectedShellSq : ℝ) *
              lineage.receiptQuantum index /
              4) =
          ((lineage.receipt index).selectedShellSq : ℝ) *
              (persistenceTime *
                lineage.receiptQuantum index) /
            4 := by
        ring
      _ ≤ _ := integratedLower'
  rw [
    generatedWholeReceiptPersistenceTime_weighted_trace_eq
      lineage index ν θ] at normalizedLower
  exact normalizedLower

theorem receiptSupportEnstrophyMass_wholePathExtension_intervalIntegrable
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (sourceReceipt : GeneratedIntegerShellReceipt) :
    IntervalIntegrable
      (fun time =>
        receiptSupportEnstrophyMass sourceReceipt
          (wholePathExtension receipt time))
      MeasureTheory.volume 0 requestedTime := by
  have supportContinuous :
      ContinuousOn
        (fun time =>
          receiptSupportEnstrophyMass sourceReceipt
            (wholePathExtension receipt time))
        (Set.Icc (0 : ℝ) requestedTime) := by
    rw [continuousOn_iff_continuous_restrict]
    have energyContinuous :
        Continuous
          (fun time : Set.Icc (0 : ℝ) requestedTime =>
            receiptSupportEnergy sourceReceipt
              (receipt.wholePath time)) :=
      (continuous_receiptSupportEnergy sourceReceipt).comp
        receipt.wholePath.continuous
    have weightedContinuous :
        Continuous
          (fun time : Set.Icc (0 : ℝ) requestedTime =>
            (sourceReceipt.selectedShellSq : ℝ) *
              receiptSupportEnergy sourceReceipt
                (receipt.wholePath time)) :=
      continuous_const.mul energyContinuous
    apply weightedContinuous.congr
    intro time
    change
      (sourceReceipt.selectedShellSq : ℝ) *
          receiptSupportEnergy sourceReceipt
            (receipt.wholePath time) =
        (sourceReceipt.selectedShellSq : ℝ) *
          receiptSupportEnergy sourceReceipt
            (commonTimeZeroExtension
              requestedTime receipt.wholePath time.1)
    rw [commonTimeZeroExtension_of_mem
      requestedTime receipt.wholePath time.1 time.property]
  exact
    supportContinuous.intervalIntegrable_of_Icc
      requestedTimePos.le

theorem prefixReceiptSupportEnstrophyMass_eq_sum_range
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ)
    (state : ComplexVorticityHilbertState) :
    pathReceiptSupportEnstrophyMass
        (lineage.prefixReachable length) state =
      ∑ index ∈ Finset.range length,
        receiptSupportEnstrophyMass
          (lineage.receipt index) state := by
  unfold pathReceiptSupportEnstrophyMass
  rw [lineage.prefixReachable_receipts length]
  simp only [List.map_map]
  change
    ((List.range length).map fun index =>
      receiptSupportEnstrophyMass
        (lineage.receipt index) state).sum =
      ∑ index ∈ Finset.range length,
        receiptSupportEnstrophyMass
          (lineage.receipt index) state
  simpa only [List.toFinset_range] using
    (List.sum_toFinset
      (fun index =>
        receiptSupportEnstrophyMass
          (lineage.receipt index) state)
      (List.nodup_range (n := length))).symm

theorem continuous_complexCoordinateAmplitudeSq :
    Continuous complexCoordinateAmplitudeSq := by
  unfold complexCoordinateAmplitudeSq
  apply continuous_finsetSum
  intro coordinate coordinateMem
  exact Complex.continuous_normSq.comp
    (continuous_apply coordinate)

theorem prefixWholeShellWave_ne_zero
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ)
    {wave : IntegerWavevector}
    (waveMem :
      wave ∈ generatedIntegerShellReachableWholeShellModes
        (lineage.prefixReachable length)) :
    wave ≠ 0 := by
  intro waveZero
  subst wave
  exact
    zero_not_mem_generatedSupport
      (lineage.current length)
      (generatedIntegerShellReachableWholeShellModes_subset_endpointSupport
        (lineage.prefixReachable length) waveMem)

theorem actualWaveEuclideanGradientDensityFunction_intervalIntegrable
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (fun time =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
              receipt.toWholeContinuousMildReceipt wave time))
      MeasureTheory.volume 0 requestedTime := by
  let path :=
    WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
      receipt.toWholeContinuousMildReceipt wave
  have pathAC :
      AbsolutelyContinuousOnInterval path 0 requestedTime :=
    heatDuhamelComplexCoordinatePath_absolutelyContinuousOnInterval
      (receipt.initialState wave)
      (ν.coeff * integerWaveViscousMultiplier wave)
      0
      (WholeContinuousMildReceipt.actualWaveNonlinearExtension_intervalIntegrable
        receipt.toWholeContinuousMildReceipt wave)
      (by simp [requestedTimePos.le])
  have pathContinuous :
      ContinuousOn path (Set.Icc (0 : ℝ) requestedTime) := by
    rw [← Set.uIcc_of_le requestedTimePos.le]
    exact pathAC.continuousOn
  exact
    (continuousOn_const.mul
      (continuous_complexCoordinateAmplitudeSq.comp_continuousOn
        pathContinuous)).intervalIntegrable_of_Icc
          requestedTimePos.le

theorem prefixReceiptSupportIntegral_le_actualWholeGradient
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (length : ℕ) :
    (∫ time in (0 : ℝ)..requestedTime,
        pathReceiptSupportEnstrophyMass
          (lineage.prefixReachable length)
          (wholePathExtension receipt time)) ≤
      actualWholeEuclideanGradientMass receipt := by
  let modes :=
    generatedIntegerShellReachableWholeShellModes
      (lineage.prefixReachable length)
  let modeDensity : IntegerWavevector → ℝ → ℝ :=
    fun wave time =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          (WholeContinuousMildReceipt.actualWaveHeatDuhamelPath
            receipt.toWholeContinuousMildReceipt wave time)
  have leftIntegrable :
      IntervalIntegrable
        (fun time =>
          pathReceiptSupportEnstrophyMass
            (lineage.prefixReachable length)
            (wholePathExtension receipt time))
        MeasureTheory.volume 0 requestedTime := by
    rw [show
      (fun time =>
        pathReceiptSupportEnstrophyMass
          (lineage.prefixReachable length)
          (wholePathExtension receipt time)) =
        (fun time =>
          ∑ index ∈ Finset.range length,
            receiptSupportEnstrophyMass
              (lineage.receipt index)
              (wholePathExtension receipt time)) by
      funext time
      exact
        prefixReceiptSupportEnstrophyMass_eq_sum_range
          lineage length
          (wholePathExtension receipt time)]
    have summed :=
      IntervalIntegrable.sum (Finset.range length)
        (fun index indexMem =>
          receiptSupportEnstrophyMass_wholePathExtension_intervalIntegrable
            receipt (lineage.receipt index))
    exact summed.congr fun time timeMem => by
      simp only [Finset.sum_apply]
  have rightIntegrable :
      IntervalIntegrable
        (fun time =>
          ∑ wave ∈ modes, modeDensity wave time)
        MeasureTheory.volume 0 requestedTime :=
    by
      have summed :=
        IntervalIntegrable.sum modes
          (fun wave waveMem =>
            actualWaveEuclideanGradientDensityFunction_intervalIntegrable
              receipt wave)
      exact summed.congr fun time timeMem => by
        simp only [Finset.sum_apply]
        rfl
  have pointwise :
      ∀ time ∈ Set.Icc (0 : ℝ) requestedTime,
        pathReceiptSupportEnstrophyMass
            (lineage.prefixReachable length)
            (wholePathExtension receipt time) ≤
          ∑ wave ∈ modes, modeDensity wave time := by
    intro time timeMem
    calc
      pathReceiptSupportEnstrophyMass
            (lineage.prefixReachable length)
            (wholePathExtension receipt time) ≤
        pathWholeShellEnstrophyMass
          (lineage.prefixReachable length)
          (wholePathExtension receipt time) :=
        pathReceiptSupportEnstrophyMass_le_pathWholeShell
          (lineage.prefixReachable length)
          (wholePathExtension receipt time)
      _ =
        ∑ wave ∈ modes,
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (wholePathExtension receipt time wave) := by
        simpa [modes] using
          pathWholeShellEnstrophyMass_eq_finiteSum
            (lineage.prefixReachable length)
            (wholePathExtension receipt time)
      _ =
        ∑ wave ∈ modes, modeDensity wave time := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        have waveNe :
            wave ≠ 0 :=
          prefixWholeShellWave_ne_zero
            lineage length (by simpa [modes] using waveMem)
        have pathEq :=
          WholeContinuousMildReceipt.wholePath_wave_eq_actualWaveHeatDuhamelPath
            receipt.toWholeContinuousMildReceipt
            wave waveNe ⟨time, timeMem⟩
        unfold wholePathExtension
        rw [commonTimeZeroExtension_of_mem
          requestedTime receipt.wholePath time timeMem]
        rw [pathEq]
  have integrated :=
    intervalIntegral.integral_mono_on
      requestedTimePos.le
      leftIntegrable rightIntegrable pointwise
  have eachModeIntegrable :
      ∀ wave ∈ modes,
        IntervalIntegrable
          (modeDensity wave)
          MeasureTheory.volume 0 requestedTime := by
    intro wave waveMem
    exact
      actualWaveEuclideanGradientDensityFunction_intervalIntegrable
        receipt wave
  have rightIntegralEq :
      (∫ time in (0 : ℝ)..requestedTime,
        ∑ wave ∈ modes, modeDensity wave time) =
      ∑ wave ∈ modes,
        ∫ time in (0 : ℝ)..requestedTime,
          modeDensity wave time := by
    rw [intervalIntegral.integral_finsetSum eachModeIntegrable]
  rw [rightIntegralEq] at integrated
  have finiteLeWhole :
      (∑ wave ∈ modes,
        ∫ time in (0 : ℝ)..requestedTime,
          modeDensity wave time) ≤
        actualWholeEuclideanGradientMass receipt := by
    let inclusion :
        ↥modes ↪ NonzeroIntegerWavevector :=
      { toFun := fun wave =>
          ⟨wave.1,
            prefixWholeShellWave_ne_zero
              lineage length
              wave.2⟩
        inj' := fun left right equality =>
          Subtype.ext
            (congrArg
              (fun value : NonzeroIntegerWavevector => value.1)
              equality) }
    have mappedLe :=
      (summable_actualWaveEuclideanGradientDensity receipt).sum_le_tsum
        (Finset.univ.map inclusion)
        (fun wave waveMem =>
          actualWaveEuclideanGradientDensity_nonneg receipt wave)
    rw [← Finset.sum_attach]
    calc
      (∑ wave : ↥modes,
          ∫ time in (0 : ℝ)..requestedTime,
            modeDensity wave.1 time) =
        ∑ wave : ↥modes,
          actualWaveEuclideanGradientDensity receipt
            (inclusion wave) := by
        apply Finset.sum_congr rfl
        intro wave waveMem
        unfold modeDensity actualWaveEuclideanGradientDensity
        rw [intervalIntegral.integral_const_mul]
        have inclusionVal :
            (inclusion wave).1 = wave.1 := by
          rfl
        rw [inclusionVal]
      _ =
        ∑ wave ∈ Finset.univ.map inclusion,
          actualWaveEuclideanGradientDensity receipt wave := by
        rw [Finset.sum_map]
      _ ≤
        ∑' wave : NonzeroIntegerWavevector,
          actualWaveEuclideanGradientDensity receipt wave :=
        mappedLe
      _ = actualWholeEuclideanGradientMass receipt := rfl
  exact integrated.trans finiteLeWhole

theorem lineageReceipt_wholePersistenceIntegral_le_horizon
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (index : ℕ)
    (persistenceTimeLe :
      generatedWholeReceiptPersistenceTime
          lineage index ν θ ≤
        requestedTime) :
    (∫ time in (0 : ℝ)..
        generatedWholeReceiptPersistenceTime
          lineage index ν θ,
      receiptSupportEnstrophyMass
        (lineage.receipt index)
        (wholePathExtension receipt time)) ≤
      ∫ time in (0 : ℝ)..requestedTime,
        receiptSupportEnstrophyMass
          (lineage.receipt index)
          (wholePathExtension receipt time) := by
  exact
    intervalIntegral.integral_mono_interval
      (μ := MeasureTheory.volume)
      (c := (0 : ℝ))
      (d := requestedTime)
      le_rfl
      (generatedWholeReceiptPersistenceTime_pos
        lineage index ν θ).le
      persistenceTimeLe
      (Filter.Eventually.of_forall fun time =>
        receiptSupportEnstrophyMass_nonneg
          (lineage.receipt index)
          (wholePathExtension receipt time))
      (receiptSupportEnstrophyMass_wholePathExtension_intervalIntegrable
        receipt (lineage.receipt index))

theorem prefixReceiptTraceSquareMass_div_le_actualWholeGradient
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
      StrongContinuationReceipt
        lineage ν θ requestedTime θLtOne criticalMargin
        requestedTimePos)
    (length : ℕ)
    (prefixPersistence :
      ∀ index < length,
        generatedWholeReceiptPersistenceTime
            lineage index ν θ ≤
          requestedTime) :
    lineage.prefixReceiptTraceSquareMass length /
          (48 * (2 * Real.pi) ^ 2 *
            max 1
              (generatedWholeNegativeOneTangentCeiling ν θ)) ≤
      actualWholeEuclideanGradientMass receipt := by
  let denominator :=
    48 * (2 * Real.pi) ^ 2 *
      max 1
        (generatedWholeNegativeOneTangentCeiling ν θ)
  let horizonIntegral : ℕ → ℝ :=
    fun index =>
      ∫ time in (0 : ℝ)..requestedTime,
        receiptSupportEnstrophyMass
          (lineage.receipt index)
          (wholePathExtension receipt time)
  have eachLower :
      ∀ index < length,
        lineage.receiptQuantum index ^ 2 / denominator ≤
          horizonIntegral index := by
    intro index indexLt
    exact
      (lineageReceipt_wholePersistenceIntegral_lower
        receipt index (prefixPersistence index indexLt)).trans
        (lineageReceipt_wholePersistenceIntegral_le_horizon
          receipt index (prefixPersistence index indexLt))
  have summedLower :
      (∑ index ∈ Finset.range length,
        lineage.receiptQuantum index ^ 2 / denominator) ≤
        ∑ index ∈ Finset.range length,
          horizonIntegral index := by
    apply Finset.sum_le_sum
    intro index indexMem
    exact eachLower index (Finset.mem_range.mp indexMem)
  have eachIntegrable :
      ∀ index ∈ Finset.range length,
        IntervalIntegrable
          (fun time =>
            receiptSupportEnstrophyMass
              (lineage.receipt index)
              (wholePathExtension receipt time))
          MeasureTheory.volume 0 requestedTime := by
    intro index indexMem
    exact
      receiptSupportEnstrophyMass_wholePathExtension_intervalIntegrable
        receipt (lineage.receipt index)
  have horizonSumEq :
      (∑ index ∈ Finset.range length,
        horizonIntegral index) =
        ∫ time in (0 : ℝ)..requestedTime,
          pathReceiptSupportEnstrophyMass
            (lineage.prefixReachable length)
            (wholePathExtension receipt time) := by
    unfold horizonIntegral
    rw [← intervalIntegral.integral_finsetSum eachIntegrable]
    apply intervalIntegral.integral_congr
    intro time timeMem
    exact
      (prefixReceiptSupportEnstrophyMass_eq_sum_range
        lineage length
        (wholePathExtension receipt time)).symm
  calc
    lineage.prefixReceiptTraceSquareMass length / denominator =
        ∑ index ∈ Finset.range length,
          lineage.receiptQuantum index ^ 2 / denominator := by
      rw [
        lineage.prefixReceiptTraceSquareMass_eq_sum_range length,
        Finset.sum_div]
    _ ≤ ∑ index ∈ Finset.range length,
          horizonIntegral index :=
      summedLower
    _ =
        ∫ time in (0 : ℝ)..requestedTime,
          pathReceiptSupportEnstrophyMass
            (lineage.prefixReachable length)
            (wholePathExtension receipt time) :=
      horizonSumEq
    _ ≤ actualWholeEuclideanGradientMass receipt :=
      prefixReceiptSupportIntegral_le_actualWholeGradient
        receipt length

theorem
    generates_prefixReceiptTraceSquareMass_actualWholeGradient_bound
    (lineage : GeneratedIntegerShellInfiniteLineage)
    (length : ℕ)
    (ν : Viscosity)
    (θ : ℝ)
    (θLtOne : θ < 1)
    (criticalMargin :
      ∀ actualLength : ℕ,
        ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier.criticalEnstrophyLatticeConstant *
            ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance.finiteStateVorticityCoefficientEnstrophy
              (generatedSupport (lineage.current actualLength))
              (generatedComplexVorticityState
                (lineage.current actualLength)
                (generatedSupport (lineage.current actualLength))) ≤
          θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ receipt :
        StrongContinuationReceipt
          lineage ν θ
          (generatedWholePrefixPersistenceHorizon
            lineage length ν θ)
          θLtOne criticalMargin
          (generatedWholePrefixPersistenceHorizon_pos
            lineage length ν θ),
      lineage.prefixReceiptTraceSquareMass length /
            (48 * (2 * Real.pi) ^ 2 *
              max 1
                (generatedWholeNegativeOneTangentCeiling ν θ)) ≤
        actualWholeEuclideanGradientMass receipt ∧
      actualWholeEuclideanGradientMass receipt ≤
        3 *
          (((1 / 2 : ℝ) *
              ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness.criticalCoefficientEnstrophyCeiling
                ν θ) /
            ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption.criticalEnstrophyAbsorptionCoefficient
              θ ν) := by
  let horizon :=
    generatedWholePrefixPersistenceHorizon
      lineage length ν θ
  let horizonPos :=
    generatedWholePrefixPersistenceHorizon_pos
      lineage length ν θ
  let receipt :
      StrongContinuationReceipt
        lineage ν θ horizon θLtOne criticalMargin horizonPos :=
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuation.GeneratedIntegerShellInfiniteLineage.generates_strongContinuation
      lineage ν θ horizon θLtOne criticalMargin horizonPos
  refine ⟨receipt, ?_, ?_⟩
  · apply
      prefixReceiptTraceSquareMass_div_le_actualWholeGradient
        receipt length
    intro index indexLt
    simpa [horizon] using
      generatedWholeReceiptPersistenceTime_le_prefixHorizon
        lineage length index indexLt ν θ
  · exact
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity.actualWholeEuclideanGradientMass_le_generated
        receipt

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
end SaturationMonoid.NavierStokes
