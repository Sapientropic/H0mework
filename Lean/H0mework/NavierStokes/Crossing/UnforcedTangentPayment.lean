import H0mework.NavierStokes.Crossing.SelfForcingReduction
import H0mework.NavierStokes.Restart.PositiveOutputWorkDualBudget
import H0mework.NavierStokes.PairRestart.SourcePairOccurrence
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Actual unforced payment of a whole-crossing gluing obstruction

The complete component-gluing row is not charged as an independent metric.
At the same actual crossing it first recombines with the generated primitive
self row and the literal viscous row to form the genuine unforced tangent:

```text
unforced tangent = self + gluing - viscous.
```

The source-owned exhaustion is then physical.  A zero gluing row gives the
existing reciprocal-count forcing reduction.  A nonzero gluing row with zero
unforced tangent is an exact relation `gluing = viscous - self`.  Otherwise
the actual tangent internally selects a nonzero Fourier output; continuity on
the same positive-time prefix receipt produces a quantitative interval
payment bounded by that receipt's existing `L²_t H⁻¹_x` whole-tangent norm.

No output, interval, branch, nonzero witness, cutoff, persistence certificate,
target path, or continuation is accepted by the final theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment

open scoped Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteComponentSources
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingWholeSourceGluingLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open AffineRelaxation

noncomputable section

/-! ## Same-crossing unforced tangent relation -/

/-- The literal coefficient row driving the actual unforced whole receipt at
one crossing contact. -/
def wholeRestartCrossingUnforcedTangentRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    IntegerWavevector → ComplexCoordinateVector :=
  fun output =>
    wholeStateVorticityNonlinearCoefficientAt
          (run initial index).contact.physicalState output -
      (ν.coeff * integerWaveViscousMultiplier output) •
        (run initial index).contact.physicalState output

/-- The generated self/gluing ledger and the actual viscous row recombine
exactly into the genuine unforced tangent of the same crossing contact. -/
theorem wholeRestartCrossingUnforcedTangentRow_eq_self_add_gluing_sub_viscous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    wholeRestartCrossingUnforcedTangentRow initial index output =
      wholeRestartCrossingFiniteComponentSelfRow
          initial index crossed output +
        wholeRestartCrossingCompleteSourceGluingResidual
          initial index crossed output -
        (ν.coeff * integerWaveViscousMultiplier output) •
          (run initial index).contact.physicalState output := by
  unfold wholeRestartCrossingUnforcedTangentRow
  rw [wholeRestartCrossingWholeNonlinear_eq_sourceSelf_add_gluing
    initial index crossed output]

/-- Outside the source-selected core pair-output support, faithful gluing
zero makes the actual whole unforced tangent exactly the physical viscous
decay row.  The excluded support is generated by the crossing itself. -/
theorem wholeRestartCrossingUnforcedTangentRow_eq_neg_viscous_of_gluing_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0)
    (output : IntegerWavevector)
    (outputNotMem :
      output ∉ finiteVorticityPairOutputSupport
        (wholeRestartCrossingFiniteCoreModes initial index crossed)) :
    wholeRestartCrossingUnforcedTangentRow initial index output =
      -((ν.coeff * integerWaveViscousMultiplier output) •
        (run initial index).contact.physicalState output) := by
  unfold wholeRestartCrossingUnforcedTangentRow
  rw [
    wholeRestartCrossingWholeNonlinearCoefficientAt_eq_zero_of_gluing_zero_of_not_mem_pairOutput
      initial index crossed gluingZero output outputNotMem]
  exact zero_sub _

/-- When the actual unforced tangent is faithfully zero, a nonzero gluing
row is not silent: it is exactly the relation balancing the viscous and
primitive-self rows. -/
theorem wholeRestartCrossingGluingResidual_eq_viscous_sub_self_of_tangent_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (tangentZero :
      wholeRestartCrossingUnforcedTangentRow initial index = 0)
    (output : IntegerWavevector) :
    wholeRestartCrossingCompleteSourceGluingResidual
        initial index crossed output =
      (ν.coeff * integerWaveViscousMultiplier output) •
          (run initial index).contact.physicalState output -
        wholeRestartCrossingFiniteComponentSelfRow
          initial index crossed output := by
  have rowZero := congrFun tangentZero output
  rw [wholeRestartCrossingUnforcedTangentRow_eq_self_add_gluing_sub_viscous
    initial index crossed output] at rowZero
  have sumEq := sub_eq_zero.mp rowZero
  calc
    wholeRestartCrossingCompleteSourceGluingResidual
          initial index crossed output =
        (wholeRestartCrossingFiniteComponentSelfRow
            initial index crossed output +
          wholeRestartCrossingCompleteSourceGluingResidual
            initial index crossed output) -
          wholeRestartCrossingFiniteComponentSelfRow
            initial index crossed output := by abel
    _ =
        (ν.coeff * integerWaveViscousMultiplier output) •
            (run initial index).contact.physicalState output -
          wholeRestartCrossingFiniteComponentSelfRow
            initial index crossed output := by rw [sumEq]

private theorem exists_unforcedTangent_output_nonzero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    ∃ output : IntegerWavevector,
      wholeRestartCrossingUnforcedTangentRow initial index output ≠ 0 := by
  by_contra noOutput
  push Not at noOutput
  apply tangentNonzero
  funext output
  exact noOutput output

/-- Output selected internally from the actual nonzero unforced tangent. -/
noncomputable def wholeRestartCrossingUnforcedTangentOutput
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    IntegerWavevector :=
  Classical.choose
    (exists_unforcedTangent_output_nonzero
      initial index tangentNonzero)

theorem wholeRestartCrossingUnforcedTangentOutput_spec
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    wholeRestartCrossingUnforcedTangentRow initial index
        (wholeRestartCrossingUnforcedTangentOutput
          initial index tangentNonzero) ≠ 0 :=
  Classical.choose_spec
    (exists_unforcedTangent_output_nonzero
      initial index tangentNonzero)

theorem wholeRestartCrossingUnforcedTangentOutput_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    wholeRestartCrossingUnforcedTangentOutput
        initial index tangentNonzero ≠ 0 := by
  intro outputZero
  have selectedNonzero :=
    wholeRestartCrossingUnforcedTangentOutput_spec
      initial index tangentNonzero
  apply selectedNonzero
  rw [outputZero]
  unfold wholeRestartCrossingUnforcedTangentRow
  rw [wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse
    (run initial index).contact.physicalState
    (run initial index).contact.transverse]
  simp [integerWaveViscousMultiplier,
    (run initial index).contact.physicalState_zero]

/-! ## Continuous same-receipt tangent row -/

/-- Continuous real-line state row of the actual prefix receipt.  The
projection outside the physical interval is proof-only; on the interval this
is literally the whole path. -/
def actualWholeContinuousStateRow
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector)
    (actual : ℝ) : ComplexCoordinateVector :=
  (actualWholeProjectedTransversePath receipt actual).1 output

theorem actualWholeContinuousStateRow_continuous
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (output : IntegerWavevector) :
    Continuous (actualWholeContinuousStateRow receipt output) := by
  exact
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 output).continuous.comp
      (continuous_subtype_val.comp
        (actualWholeProjectedTransversePath_continuous receipt))

/-- The actual unforced coefficient row along the same prefix receipt. -/
def wholeRestartCrossingContinuousUnforcedTangentRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0)
    (actual : ℝ) : ComplexCoordinateVector :=
  let receipt := (run initial index).nextContact.prefixReceipt
  let output :=
    wholeRestartCrossingUnforcedTangentOutput
      initial index tangentNonzero
  actualWholeContinuousNonlinearRow receipt output actual -
    (ν.coeff * integerWaveViscousMultiplier output) •
      actualWholeContinuousStateRow receipt output actual

theorem wholeRestartCrossingContinuousUnforcedTangentRow_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    Continuous
      (wholeRestartCrossingContinuousUnforcedTangentRow
        initial index tangentNonzero) := by
  unfold wholeRestartCrossingContinuousUnforcedTangentRow
  exact
    (actualWholeContinuousNonlinearRow_continuous
      (run initial index).nextContact.prefixReceipt
      (wholeRestartCrossingUnforcedTangentOutput
        initial index tangentNonzero)).sub
      ((actualWholeContinuousStateRow_continuous
        (run initial index).nextContact.prefixReceipt
        (wholeRestartCrossingUnforcedTangentOutput
          initial index tangentNonzero)).const_smul
        (ν.coeff * integerWaveViscousMultiplier
          (wholeRestartCrossingUnforcedTangentOutput
            initial index tangentNonzero)))

theorem wholeRestartCrossingContinuousUnforcedTangentRow_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    wholeRestartCrossingContinuousUnforcedTangentRow
        initial index tangentNonzero 0 =
      wholeRestartCrossingUnforcedTangentRow initial index
        (wholeRestartCrossingUnforcedTangentOutput
          initial index tangentNonzero) := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let output :=
    wholeRestartCrossingUnforcedTangentOutput
      initial index tangentNonzero
  have stateAtZero :
      actualWholeContinuousStateRow receipt output 0 =
        (run initial index).contact.physicalState output := by
    change
      receipt.wholePath
          (Set.projIcc (0 : ℝ)
            (run initial index).nextContact.time.1
            receipt.requestedTimePos.le 0) output =
        (run initial index).contact.physicalState output
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le
      ⟨le_rfl, receipt.requestedTimePos.le⟩]
    exact congrArg
      (fun state : ComplexVorticityHilbertState => state output)
      receipt.wholePath_initial
  change
    actualWholeContinuousNonlinearRow receipt output 0 -
        (ν.coeff * integerWaveViscousMultiplier output) •
          actualWholeContinuousStateRow receipt output 0 =
      wholeRestartCrossingUnforcedTangentRow initial index output
  rw [actualWholeContinuousNonlinearRow_zero, stateAtZero]
  rfl

/-- The same support exclusion is an actual PDE statement: on the identical
positive-time unforced receipt, every output outside the generated core-pair
support starts with the literal viscous derivative. -/
theorem
    wholeRestartCrossingActualWholeRow_hasDerivAt_zero_eq_neg_viscous_of_gluing_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0)
    (output : IntegerWavevector)
    (outputNotMem :
      output ∉ finiteVorticityPairOutputSupport
        (wholeRestartCrossingFiniteCoreModes initial index crossed)) :
    HasDerivAt
      (actualWholeContinuousHeatDuhamelPath
        (run initial index).nextContact.prefixReceipt output)
      (-((ν.coeff * integerWaveViscousMultiplier output) •
        (run initial index).contact.physicalState output))
      0 := by
  have generated :=
    actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      (receipt := (run initial index).nextContact.prefixReceipt)
      output
  rw [
    wholeRestartCrossingWholeNonlinearCoefficientAt_eq_zero_of_gluing_zero_of_not_mem_pairOutput
      initial index crossed gluingZero output outputNotMem] at generated
  simpa using generated

/-- The same actual row identity differentiates its physical Euclidean
coefficient energy.  Outside the source-generated pair-output support, the
faithful-zero branch has the exact negative viscous energy derivative; no
local-time or persistence witness is supplied by a caller. -/
theorem
    wholeRestartCrossingActualWholeRowAmplitudeSq_hasDerivAt_zero_eq_neg_viscous_of_gluing_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0)
    (output : IntegerWavevector)
    (outputNotMem :
      output ∉ finiteVorticityPairOutputSupport
        (wholeRestartCrossingFiniteCoreModes initial index crossed)) :
    HasDerivAt
      (fun actual =>
        complexCoordinateAmplitudeSq
          (actualWholeContinuousHeatDuhamelPath
            (run initial index).nextContact.prefixReceipt output actual))
      (-2 * (ν.coeff * integerWaveViscousMultiplier output) *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output))
      0 := by
  have rowDerivative :=
    wholeRestartCrossingActualWholeRow_hasDerivAt_zero_eq_neg_viscous_of_gluing_zero
      initial index crossed gluingZero output outputNotMem
  have energyDerivative :=
    complexCoordinateAmplitudeSq_hasDerivAt
      (actualWholeContinuousHeatDuhamelPath
        (run initial index).nextContact.prefixReceipt output)
      0
      (-((ν.coeff * integerWaveViscousMultiplier output) •
        (run initial index).contact.physicalState output))
      rowDerivative
  have pathAtZero :
      actualWholeContinuousHeatDuhamelPath
          (run initial index).nextContact.prefixReceipt output 0 =
        (run initial index).contact.physicalState output := by
    unfold actualWholeContinuousHeatDuhamelPath
      heatDuhamelComplexCoordinatePath
      intervalIntegralComplexCoordinatePath
    simp
  rw [pathAtZero] at energyDerivative
  convert energyDerivative using 1
  rw [← neg_smul,
    complexCoordinateRealInner_real_smul_right,
    complexCoordinateRealInner_self,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  ring

/-- If the same generated high-frequency responsibility is physically
nonzero, its exact faithful-zero energy derivative is strictly negative.
This turns support escape into a genuine unforced viscous consumer. -/
theorem
    wholeRestartCrossingActualWholeRowAmplitudeSq_neg_viscous_derivative_lt_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0)
    (stateNonzero :
      (run initial index).contact.physicalState output ≠ 0) :
    -2 * (ν.coeff * integerWaveViscousMultiplier output) *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output) < 0 := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier output :=
    integerWaveViscousMultiplier_pos ⟨output, outputNonzero⟩
  have amplitudePos :
      0 < complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState output) := by
    rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      complexCoordinateVectorNormSq_pos_iff]
    exact stateNonzero
  have productPos :
      0 < 2 * (ν.coeff * integerWaveViscousMultiplier output) *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output) :=
    mul_pos
      (mul_pos (by norm_num) (mul_pos ν.coeff_pos multiplierPos))
      amplitudePos
  nlinarith

private theorem exists_positive_time_strict_drop_of_hasDerivAt_neg
    {f : ℝ → ℝ}
    {derivative duration : ℝ}
    (derivativeAt : HasDerivAt f derivative 0)
    (derivativeNeg : derivative < 0)
    (durationPos : 0 < duration) :
    ∃ actual : ℝ,
      0 < actual ∧ actual < duration ∧ f actual < f 0 := by
  have slopeNeg :
      ∀ᶠ actual in 𝓝[>] (0 : ℝ),
        slope f 0 actual < 0 := by
    exact ((hasDerivAt_iff_tendsto_slope_left_right.mp derivativeAt).2)
      (Iio_mem_nhds derivativeNeg)
  have insideDuration :
      ∀ᶠ actual in 𝓝[>] (0 : ℝ),
        actual ∈ Ioo (0 : ℝ) duration :=
    Ioo_mem_nhdsGT durationPos
  obtain ⟨actual, actualMem, actualSlopeNeg⟩ :
      ∃ actual, actual ∈ Ioo (0 : ℝ) duration ∧ slope f 0 actual < 0 :=
    (insideDuration.and slopeNeg).exists
  exact
    ⟨actual, actualMem.1, actualMem.2,
      (slope_neg_iff_of_le actualMem.1.le).mp actualSlopeNeg⟩

/-- Faithful-zero support escape writes back on the actual outgoing unforced
receipt: the source-generated negative derivative itself selects a strictly
positive physical time before the receipt endpoint where the escaped Fourier
coefficient has lost Euclidean energy.  No local time or persistence witness
is accepted from the caller. -/
theorem
    wholeRestartCrossingActualWholeRowAmplitudeSq_generates_positive_time_drop_of_gluing_zero
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
      complexCoordinateAmplitudeSq
          ((run initial index).nextContact.prefixReceipt.wholePath
            ⟨actual.1, actual.2.1.le, actual.2.2.le⟩ output) <
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output) := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let physicalAmplitude : ℝ → ℝ := fun actual =>
    complexCoordinateAmplitudeSq
      (actualWholeContinuousHeatDuhamelPath receipt output actual)
  have derivativeAt :
      HasDerivAt physicalAmplitude
        (-2 * (ν.coeff * integerWaveViscousMultiplier output) *
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output)) 0 := by
    exact
      wholeRestartCrossingActualWholeRowAmplitudeSq_hasDerivAt_zero_eq_neg_viscous_of_gluing_zero
        initial index crossed gluingZero output outputNotMem
  have derivativeNeg :
      -2 * (ν.coeff * integerWaveViscousMultiplier output) *
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output) < 0 :=
    wholeRestartCrossingActualWholeRowAmplitudeSq_neg_viscous_derivative_lt_zero
      initial index output outputNonzero stateNonzero
  obtain ⟨actual, actualPos, actualLt, actualDrop⟩ :=
    exists_positive_time_strict_drop_of_hasDerivAt_neg
      derivativeAt derivativeNeg
      (run initial index).nextContact.time_pos
  have pathAtZero :
      actualWholeContinuousHeatDuhamelPath receipt output 0 =
        (run initial index).contact.physicalState output := by
    unfold receipt actualWholeContinuousHeatDuhamelPath
      heatDuhamelComplexCoordinatePath
      intervalIntegralComplexCoordinatePath
    simp
  have actualDrop' :
      complexCoordinateAmplitudeSq
          (actualWholeContinuousHeatDuhamelPath receipt output actual) <
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output) := by
    simpa [physicalAmplitude, pathAtZero] using actualDrop
  let physicalTime :
      Icc (0 : ℝ) (run initial index).nextContact.time.1 :=
    ⟨actual, actualPos.le, actualLt.le⟩
  refine ⟨⟨actual, actualPos, actualLt⟩, ?_⟩
  rw [wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
    receipt output outputNonzero physicalTime]
  exact actualDrop'

/-- Inverse-square-root weighted physical tangent density at the selected
actual output. -/
def wholeRestartCrossingContinuousUnforcedTangentDensity
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0)
    (actual : ℝ) : ℝ :=
  let output :=
    wholeRestartCrossingUnforcedTangentOutput
      initial index tangentNonzero
  ‖((Real.sqrt (integerWaveViscousMultiplier output) : ℂ)⁻¹) •
      wholeRestartCrossingContinuousUnforcedTangentRow
        initial index tangentNonzero actual‖ ^ 2

theorem wholeRestartCrossingContinuousUnforcedTangentDensity_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    Continuous
      (wholeRestartCrossingContinuousUnforcedTangentDensity
        initial index tangentNonzero) := by
  unfold wholeRestartCrossingContinuousUnforcedTangentDensity
  exact
    (((wholeRestartCrossingContinuousUnforcedTangentRow_continuous
      initial index tangentNonzero).const_smul
        ((Real.sqrt
          (integerWaveViscousMultiplier
            (wholeRestartCrossingUnforcedTangentOutput
              initial index tangentNonzero)) : ℂ)⁻¹)).norm.pow 2)

theorem wholeRestartCrossingContinuousUnforcedTangentDensity_zero_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    0 < wholeRestartCrossingContinuousUnforcedTangentDensity
      initial index tangentNonzero 0 := by
  let output :=
    wholeRestartCrossingUnforcedTangentOutput
      initial index tangentNonzero
  have outputNe : output ≠ 0 :=
    wholeRestartCrossingUnforcedTangentOutput_ne_zero
      initial index tangentNonzero
  have multiplierPos :
      0 < integerWaveViscousMultiplier output :=
    integerWaveViscousMultiplier_pos ⟨output, outputNe⟩
  have sqrtNe :
      (Real.sqrt (integerWaveViscousMultiplier output) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 multiplierPos).ne'
  have rowNe :
      wholeRestartCrossingContinuousUnforcedTangentRow
          initial index tangentNonzero 0 ≠ 0 := by
    rw [wholeRestartCrossingContinuousUnforcedTangentRow_zero]
    exact wholeRestartCrossingUnforcedTangentOutput_spec
      initial index tangentNonzero
  unfold wholeRestartCrossingContinuousUnforcedTangentDensity
  exact sq_pos_of_pos
    (norm_pos_iff.mpr (smul_ne_zero (inv_ne_zero sqrtNe) rowNe))

/-- On the physical prefix interval, the continuously selected weighted row
is the selected coordinate of the receipt's existing whole `H⁻¹` tangent.
This is the same-event bridge that makes the later interval payment physical. -/
theorem wholeRestartCrossingContinuousWeightedTangentRow_ae_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    let receipt := (run initial index).nextContact.prefixReceipt
    let output :=
      wholeRestartCrossingUnforcedTangentOutput
        initial index tangentNonzero
    (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
      ((Real.sqrt (integerWaveViscousMultiplier output) : ℂ)⁻¹) •
        wholeRestartCrossingContinuousUnforcedTangentRow
          initial index tangentNonzero time.1) =ᵐ[
      commonTimeMeasure (run initial index).nextContact.time.1]
      fun time => receipt.wholeTangent time output := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let output :=
    wholeRestartCrossingUnforcedTangentOutput
      initial index tangentNonzero
  have outputNe : output ≠ 0 :=
    wholeRestartCrossingUnforcedTangentOutput_ne_zero
      initial index tangentNonzero
  have multiplierPos :
      0 < integerWaveViscousMultiplier output :=
    integerWaveViscousMultiplier_pos ⟨output, outputNe⟩
  have sqrtNe :
      (Real.sqrt (integerWaveViscousMultiplier output) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 multiplierPos).ne'
  filter_upwards [
    actualWholeContinuousNonlinearRow_ae_eq receipt output,
    transverseSpaceTimeNonlinearRow_coeFn
      receipt.transverseLimit output,
    receipt.rowTangent_eq_unforced_ae output outputNe,
    receipt.rowTangent_eq_wholeTangent_ae output outputNe] with
      time nonlinearEq representativeEq rowEq tangentEq
  have stateEq :
      actualWholeContinuousStateRow receipt output time.1 =
        receipt.wholePath time output := by
    change
      receipt.wholePath
          (Set.projIcc (0 : ℝ)
            (run initial index).nextContact.time.1
            receipt.requestedTimePos.le time.1) output =
        receipt.wholePath time output
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le time.property]
  change
    ((Real.sqrt (integerWaveViscousMultiplier output) : ℂ)⁻¹) •
        (actualWholeContinuousNonlinearRow receipt output time.1 -
          (ν.coeff * integerWaveViscousMultiplier output) •
            actualWholeContinuousStateRow receipt output time.1) =
      receipt.wholeTangent time output
  rw [nonlinearEq, representativeEq,
    transverseSpaceTimeNonlinearRowFunction,
    ← wholeStateVorticityBilinearCoefficientAt_self,
    stateEq, ← rowEq, ← tangentEq, smul_smul]
  simp [sqrtNe]

theorem wholeRestartCrossingContinuousUnforcedTangentDensity_ae_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    let receipt := (run initial index).nextContact.prefixReceipt
    let output :=
      wholeRestartCrossingUnforcedTangentOutput
        initial index tangentNonzero
    (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
      wholeRestartCrossingContinuousUnforcedTangentDensity
        initial index tangentNonzero time.1) =ᵐ[
      commonTimeMeasure (run initial index).nextContact.time.1]
      fun time => ‖receipt.wholeTangent time output‖ ^ 2 := by
  filter_upwards [
    wholeRestartCrossingContinuousWeightedTangentRow_ae_eq
      initial index tangentNonzero] with time rowEq
  change
    ‖((Real.sqrt (integerWaveViscousMultiplier
          (wholeRestartCrossingUnforcedTangentOutput
            initial index tangentNonzero)) : ℂ)⁻¹) •
        wholeRestartCrossingContinuousUnforcedTangentRow
          initial index tangentNonzero time.1‖ ^ 2 =
      ‖(run initial index).nextContact.prefixReceipt.wholeTangent time
        (wholeRestartCrossingUnforcedTangentOutput
          initial index tangentNonzero)‖ ^ 2
  rw [rowEq]

/-! ## Source-generated positive-time payment -/

/-- A nonzero actual unforced tangent generates its own output and positive
time window on the same prefix receipt.  The quantitative initial density is
paid directly by the receipt's existing `L²_t H⁻¹_x` whole tangent. -/
theorem wholeRestartCrossingUnforcedTangent_positiveTimePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    ∃ localTime : ℝ,
      0 < localTime ∧
        localTime < (run initial index).nextContact.time.1 ∧
        localTime *
              (wholeRestartCrossingContinuousUnforcedTangentDensity
                initial index tangentNonzero 0 / 2) ≤
          ∫ time in (0 : ℝ)..localTime,
            wholeRestartCrossingContinuousUnforcedTangentDensity
              initial index tangentNonzero time ∧
        0 <
          ∫ time in (0 : ℝ)..localTime,
            wholeRestartCrossingContinuousUnforcedTangentDensity
              initial index tangentNonzero time ∧
        (∫ time in (0 : ℝ)..localTime,
            wholeRestartCrossingContinuousUnforcedTangentDensity
              initial index tangentNonzero time) ≤
          ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let output :=
    wholeRestartCrossingUnforcedTangentOutput
      initial index tangentNonzero
  let density :=
    wholeRestartCrossingContinuousUnforcedTangentDensity
      initial index tangentNonzero
  have densityContinuous : Continuous density :=
    wholeRestartCrossingContinuousUnforcedTangentDensity_continuous
      initial index tangentNonzero
  have densityZeroPos : 0 < density 0 :=
    wholeRestartCrossingContinuousUnforcedTangentDensity_zero_pos
      initial index tangentNonzero
  have halfPos : 0 < density 0 / 2 := by linarith
  have halfLt : density 0 / 2 < density 0 := by linarith
  have eventuallyLower :
      ∀ᶠ time in 𝓝 (0 : ℝ), density 0 / 2 < density time :=
    densityContinuous.continuousAt.eventually
      (eventually_gt_nhds halfLt)
  obtain ⟨liveRadius, liveRadiusPos, liveWithin⟩ :=
    Metric.eventually_nhds_iff.mp eventuallyLower
  let localTime :=
    min (run initial index).nextContact.time.1 liveRadius / 2
  have receiptTimePos :
      0 < (run initial index).nextContact.time.1 :=
    receipt.requestedTimePos
  have commonRadiusPos :
      0 < min (run initial index).nextContact.time.1 liveRadius :=
    lt_min receiptTimePos liveRadiusPos
  have localTimePos : 0 < localTime := by
    dsimp [localTime]
    linarith
  have localTimeLtCommon :
      localTime <
        min (run initial index).nextContact.time.1 liveRadius := by
    dsimp [localTime]
    linarith
  have localTimeLtReceipt :
      localTime < (run initial index).nextContact.time.1 :=
    lt_of_lt_of_le localTimeLtCommon (min_le_left _ _)
  have localTimeLtLive : localTime < liveRadius :=
    lt_of_lt_of_le localTimeLtCommon (min_le_right _ _)
  have pointwiseLower :
      ∀ time ∈ Icc (0 : ℝ) localTime,
        density 0 / 2 ≤ density time := by
    intro time timeMem
    exact (liveWithin (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg timeMem.1]
      exact timeMem.2.trans_lt localTimeLtLive)).le
  have densityIntegrableLocal :
      IntervalIntegrable density volume 0 localTime :=
    densityContinuous.intervalIntegrable 0 localTime
  have constantIntegrable :
      IntervalIntegrable
        (fun _ : ℝ => density 0 / 2) volume 0 localTime :=
    continuous_const.intervalIntegrable 0 localTime
  have integratedLower :=
    intervalIntegral.integral_mono_on
      localTimePos.le constantIntegrable densityIntegrableLocal
      pointwiseLower
  have normalizedLower :
      localTime * (density 0 / 2) ≤
        ∫ time in (0 : ℝ)..localTime, density time := by
    calc
      localTime * (density 0 / 2) = localTime * density 0 / 2 := by
        ring
      _ ≤ ∫ time in (0 : ℝ)..localTime, density time := by
        simpa [intervalIntegral.integral_const, smul_eq_mul] using
          integratedLower
  have integralPositive :
      0 < ∫ time in (0 : ℝ)..localTime, density time :=
    (mul_pos localTimePos halfPos).trans_le normalizedLower
  have densityNonneg : ∀ time : ℝ, 0 ≤ density time := by
    intro time
    exact sq_nonneg _
  have densityIntegrableFull :
      IntervalIntegrable density volume 0
        (run initial index).nextContact.time.1 :=
    densityContinuous.intervalIntegrable
      0 (run initial index).nextContact.time.1
  have localIntegralLeFull :
      (∫ time in (0 : ℝ)..localTime, density time) ≤
        ∫ time in (0 : ℝ)..(run initial index).nextContact.time.1,
          density time :=
    intervalIntegral.integral_mono_interval
      (μ := volume)
      (c := (0 : ℝ))
      (d := (run initial index).nextContact.time.1)
      le_rfl localTimePos.le localTimeLtReceipt.le
      (Filter.Eventually.of_forall densityNonneg)
      densityIntegrableFull
  have fullDensityIntegralEq :
      (∫ time in (0 : ℝ)..(run initial index).nextContact.time.1,
          density time) =
        ∫ time,
          ‖receipt.wholeTangent time output‖ ^ 2
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1) := by
    rw [← commonTime_integral_eq_intervalIntegral
      (run initial index).nextContact.time.1 receiptTimePos.le]
    exact integral_congr_ae
      (wholeRestartCrossingContinuousUnforcedTangentDensity_ae_eq
        initial index tangentNonzero)
  have tangentSqIntegrable :
      Integrable
        (fun time => ‖receipt.wholeTangent time‖ ^ 2)
        (commonTimeMeasure
          (run initial index).nextContact.time.1) :=
    (MeasureTheory.Lp.memLp receipt.wholeTangent).integrable_norm_pow
      (by norm_num)
  have rowSqMeasurable :
      AEStronglyMeasurable
        (fun time => ‖receipt.wholeTangent time output‖ ^ 2)
        (commonTimeMeasure
          (run initial index).nextContact.time.1) :=
    ((lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 output).continuous.comp_aestronglyMeasurable
        (MeasureTheory.Lp.aestronglyMeasurable
          receipt.wholeTangent)).norm.pow 2
  have rowSqLe :
      ∀ᵐ time ∂(commonTimeMeasure
          (run initial index).nextContact.time.1),
        ‖receipt.wholeTangent time output‖ ^ 2 ≤
          ‖receipt.wholeTangent time‖ ^ 2 := by
    filter_upwards with time
    exact
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (lp.norm_apply_le_norm
          (by norm_num)
          (receipt.wholeTangent time) output)
  have rowSqIntegrable :
      Integrable
        (fun time => ‖receipt.wholeTangent time output‖ ^ 2)
        (commonTimeMeasure
          (run initial index).nextContact.time.1) := by
    apply tangentSqIntegrable.mono' rowSqMeasurable
    filter_upwards [rowSqLe] with time bound
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact bound
  have rowIntegralLeTangent :
      (∫ time,
          ‖receipt.wholeTangent time output‖ ^ 2
            ∂(commonTimeMeasure
              (run initial index).nextContact.time.1)) ≤
        ‖receipt.wholeTangent‖ ^ 2 := by
    rw [spaceTime_norm_sq_eq_integral]
    exact integral_mono_ae
      rowSqIntegrable tangentSqIntegrable rowSqLe
  refine ⟨localTime, localTimePos, localTimeLtReceipt,
    ?_, integralPositive, ?_⟩
  · simpa only [density] using normalizedLower
  · exact localIntegralLeFull.trans
      (fullDensityIntegralEq.trans_le rowIntegralLeTangent)

/-! ## Source-owned crossing exhaustion -/

/-- An actual half-critical crossing now generates its complete physical
alternative without any caller-selected branch, output, time window, or
smallness parameter.

If the complete gluing row vanishes faithfully in `H⁻¹`, the nonlinear
forcing is the reciprocal-count finite-core forcing.  Otherwise the same
generated obstruction is written into the next residual keep or trace, and
the actual unforced tangent either closes as the exact viscous/self relation
or produces a strictly positive payment on its own positive-time prefix
receipt. -/
theorem wholeRestartCrossing_reduced_forcing_or_native_relation_or_tangent_payment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (wholeStateVorticityNonlinearNegativeOneState
          (run initial index).contact.physicalState
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable =
        ((canonicalHalfCriticalComponentCount ν
            (wholeRestartCrossingFiniteCoreState
              initial index crossed) : ℝ)⁻¹ : ℂ) •
          wholeRestartCrossingFiniteCoreNegativeOneState
            initial index crossed) ∨
      (wholeRestartCrossingCompleteSourceGluingNegativeOneState
            initial index crossed ≠ 0 ∧
        (wholeRestartComponentGluingResidualRow initial (index + 1) ≠ 0 ∨
          linearResidualTrace wholeRestartComponentGluingResidualTailKeep
              (wholeRestartComponentGluingResidualTail initial index) 0 ≠
            0) ∧
        ((wholeRestartCrossingUnforcedTangentRow initial index = 0 ∧
            ∀ output : IntegerWavevector,
              wholeRestartCrossingCompleteSourceGluingResidual
                    initial index crossed output =
                (ν.coeff * integerWaveViscousMultiplier output) •
                    (run initial index).contact.physicalState output -
                  wholeRestartCrossingFiniteComponentSelfRow
                    initial index crossed output) ∨
          ∃ tangentNonzero :
              wholeRestartCrossingUnforcedTangentRow initial index ≠ 0,
            ∃ localTime : ℝ,
              0 < localTime ∧
                localTime < (run initial index).nextContact.time.1 ∧
                localTime *
                      (wholeRestartCrossingContinuousUnforcedTangentDensity
                        initial index tangentNonzero 0 / 2) ≤
                  ∫ time in (0 : ℝ)..localTime,
                    wholeRestartCrossingContinuousUnforcedTangentDensity
                      initial index tangentNonzero time ∧
                0 <
                  ∫ time in (0 : ℝ)..localTime,
                    wholeRestartCrossingContinuousUnforcedTangentDensity
                      initial index tangentNonzero time ∧
                (∫ time in (0 : ℝ)..localTime,
                    wholeRestartCrossingContinuousUnforcedTangentDensity
                      initial index tangentNonzero time) ≤
                  ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2)) := by
  by_cases gluingZero :
      wholeRestartCrossingCompleteSourceGluingNegativeOneState
        initial index crossed = 0
  · exact Or.inl
      (wholeRestartCrossingWholeNegativeOneState_eq_core_smul_of_gluing_zero
        initial index crossed gluingZero)
  · right
    have nativeNonzero :
        wholeRestartComponentGluingResidualRow initial index ≠ 0 :=
      (wholeRestartComponentGluingResidualRow_nonzero_iff_negativeOne
        initial index crossed).2 gluingZero
    refine ⟨gluingZero,
      wholeRestartComponentGluingResidual_nonzero_next_or_trace
        initial index nativeNonzero, ?_⟩
    by_cases tangentZero :
        wholeRestartCrossingUnforcedTangentRow initial index = 0
    · exact Or.inl ⟨tangentZero, fun output =>
        wholeRestartCrossingGluingResidual_eq_viscous_sub_self_of_tangent_zero
          initial index crossed tangentZero output⟩
    · exact Or.inr ⟨tangentZero,
        wholeRestartCrossingUnforcedTangent_positiveTimePayment
          initial index tangentZero⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
end NavierStokes
end SaturationMonoid
