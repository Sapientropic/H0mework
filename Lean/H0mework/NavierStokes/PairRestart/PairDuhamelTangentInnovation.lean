import H0mework.NavierStokes.PairRestart.PairDuhamelExactHeadroom
import H0mework.NavierStokes.Crossing.UnforcedTangentPayment
import H0mework.NavierStokes.Crossing.TangentPaymentCascade
import H0mework.NavierStokes.Crossing.PairOccurrenceGluing
import H0mework.NavierStokes.PairRestart.PairDuhamelTerminalTraceRedirect

/-!
# Causal tangent / pair-innovation split of one actual restart endpoint

The nonlinear Duhamel row is not replaced by its time-zero source tangent.
Instead, the same actual receipt generates an exact causal gain and a typed
dynamic innovation for every input-pair occurrence:

```text
endpoint - current
  = causalGain · (time-zero unforced tangent)
    + tsum pairInnovation.
```

The frozen tangent term combines the homogeneous heat displacement with the
time-zero nonlinear row.  The innovation is the remainder of the actual
positive-time Duhamel occurrence after that frozen contribution is removed.
Thus any cancellation of the source tangent remains on the complete
`output × input-pair` carrier before aggregation.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation

open scoped BigOperators ENNReal Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelExactHeadroom
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTerminalTraceRedirect

noncomputable section

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

/-! ## Source-owned frozen gain and pair innovation -/

/-- Exact integral of the frozen nonlinear row under the actual causal heat
kernel.  The denominator is nonzero on every output where this gain is
consumed. -/
def wholeRestartCausalTangentGain
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) : ℝ :=
  (1 - finiteStateVorticityHeatMultiplier
      ν.coeff (run initial index).nextContact.time.1 output) /
    (ν.coeff * integerWaveViscousMultiplier output)

/-- One actual causal Duhamel occurrence after removing the frozen contact
pair transported by the same source-generated gain. -/
def wholeRestartPairDuhamelInnovationOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  wholeRestartPairDuhamelOccurrence initial index output first -
    wholeRestartCausalTangentGain initial index output •
      wholeRestartContactPairOccurrenceTable
        initial index output first

theorem summable_wholeRestartContactPairOccurrenceTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    Summable fun first : IntegerWavevector =>
      wholeRestartContactPairOccurrenceTable
        initial index output first := by
  have zeroSummable :=
    summable_actualWholeContinuousPairVector
      (run initial index).nextContact.prefixReceipt output
        ⟨0, ⟨le_rfl,
          (run initial index).nextContact.time_pos.le⟩⟩
  exact zeroSummable.congr fun first =>
    actualWholeContinuousPairVector_zero_eq_contact
      initial index output first

theorem tsum_wholeRestartContactPairOccurrenceTable_eq_nonlinearOutput
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    (∑' first : IntegerWavevector,
      wholeRestartContactPairOccurrenceTable
        initial index output first) =
      wholeStateVorticityNonlinearCoefficientAt
        (run initial index).contact.physicalState output := by
  unfold wholeRestartContactPairOccurrenceTable
    wholeStateVorticityNonlinearCoefficientAt
  rfl

theorem summable_wholeRestartPairDuhamelInnovationOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    Summable fun first : IntegerWavevector =>
      wholeRestartPairDuhamelInnovationOccurrence
        initial index output first := by
  apply Summable.sub
    (summable_wholeRestartPairDuhamelOccurrence
      initial index output)
  exact
    ((summable_wholeRestartContactPairOccurrenceTable
      initial index output).hasSum.const_smul
        (wholeRestartCausalTangentGain initial index output)).summable

/-- Pair aggregation is postponed until after the dynamic innovation has
been formed. -/
theorem tsum_wholeRestartPairDuhamelInnovationOccurrence_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    (∑' first : IntegerWavevector,
      wholeRestartPairDuhamelInnovationOccurrence
        initial index output first) =
      wholeRestartNonlinearRegenerationState initial index output -
        wholeRestartCausalTangentGain initial index output •
          wholeStateVorticityNonlinearCoefficientAt
            (run initial index).contact.physicalState output := by
  unfold wholeRestartPairDuhamelInnovationOccurrence
  rw [Summable.tsum_sub
    (summable_wholeRestartPairDuhamelOccurrence
      initial index output)
    (((summable_wholeRestartContactPairOccurrenceTable
      initial index output).hasSum.const_smul
        (wholeRestartCausalTangentGain initial index output)).summable)]
  rw [tsum_wholeRestartPairDuhamelOccurrence_eq_regeneration
    initial index output outputNonzero]
  rw [show
      (∑' first : IntegerWavevector,
        wholeRestartCausalTangentGain initial index output •
          wholeRestartContactPairOccurrenceTable
            initial index output first) =
        wholeRestartCausalTangentGain initial index output •
          wholeStateVorticityNonlinearCoefficientAt
            (run initial index).contact.physicalState output by
    exact
      ((summable_wholeRestartContactPairOccurrenceTable
        initial index output).hasSum.const_smul
          (wholeRestartCausalTangentGain initial index output)).tsum_eq.trans
        (congrArg
          (fun row : ComplexCoordinateVector =>
            wholeRestartCausalTangentGain initial index output • row)
          (tsum_wholeRestartContactPairOccurrenceTable_eq_nonlinearOutput
            initial index output))]

/-! ## Actual endpoint write-back -/

theorem viscousMultiplier_mul_causalTangentGain
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    (ν.coeff * integerWaveViscousMultiplier output) *
        wholeRestartCausalTangentGain initial index output =
      1 - finiteStateVorticityHeatMultiplier
        ν.coeff (run initial index).nextContact.time.1 output := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier output := by
    unfold integerWaveViscousMultiplier
    exact mul_pos
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
      (integerWaveNormSq_pos outputNonzero)
  unfold wholeRestartCausalTangentGain
  field_simp [ν.coeff_pos.ne', multiplierPos.ne']

theorem wholeRestartCausalTangentGain_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    0 < wholeRestartCausalTangentGain initial index output := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier output := by
    unfold integerWaveViscousMultiplier
    exact mul_pos
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
      (integerWaveNormSq_pos outputNonzero)
  have exponentNeg :
      -(ν.coeff * integerWaveViscousMultiplier output) *
          (run initial index).nextContact.time.1 < 0 := by
    calc
      -(ν.coeff * integerWaveViscousMultiplier output) *
          (run initial index).nextContact.time.1 =
          -((ν.coeff * integerWaveViscousMultiplier output) *
            (run initial index).nextContact.time.1) := by ring
      _ < 0 := neg_neg_of_pos
        (mul_pos
          (mul_pos ν.coeff_pos multiplierPos)
          (run initial index).nextContact.time_pos)
  have heatLtOne :
      finiteStateVorticityHeatMultiplier
          ν.coeff (run initial index).nextContact.time.1 output < 1 := by
    unfold finiteStateVorticityHeatMultiplier
    exact Real.exp_lt_one_iff.mpr exponentNeg
  unfold wholeRestartCausalTangentGain
  exact div_pos (sub_pos.mpr heatLtOne)
    (mul_pos ν.coeff_pos multiplierPos)

/-- The frozen gain is not an algebraic replacement for the receipt: it is
the exact integral of the same causal heat kernel on the actual physical
time interval. -/
theorem wholeRestartCausalTangentGain_eq_heatIntegral
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    wholeRestartCausalTangentGain initial index output =
      ∫ earlier in
          Iic
            (⟨(run initial index).nextContact.time.1,
              ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
              Icc (0 : ℝ) (run initial index).nextContact.time.1),
        finiteStateVorticityHeatMultiplier ν.coeff
          ((run initial index).nextContact.time.1 - earlier.1) output
        ∂(commonTimeMeasure
          (run initial index).nextContact.time.1) := by
  let terminal :
      Icc (0 : ℝ) (run initial index).nextContact.time.1 :=
    ⟨(run initial index).nextContact.time.1,
      ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩
  have multiplierPos : 0 < integerWaveViscousMultiplier output := by
    unfold integerWaveViscousMultiplier
    exact mul_pos
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
      (integerWaveNormSq_pos outputNonzero)
  change
    wholeRestartCausalTangentGain initial index output =
      ∫ earlier in Iic terminal,
        finiteStateVorticityHeatMultiplier ν.coeff
          (terminal.1 - earlier.1) output
        ∂(commonTimeMeasure
          (run initial index).nextContact.time.1)
  rw [commonTime_integral_Iic_eq_intervalIntegral
    (run initial index).nextContact.time.1
    (run initial index).nextContact.time_pos.le terminal
    (fun earlier : ℝ =>
      finiteStateVorticityHeatMultiplier ν.coeff
        (terminal.1 - earlier) output)]
  unfold wholeRestartCausalTangentGain
    finiteStateVorticityHeatMultiplier
  dsimp only [terminal]
  have coefficientNe :
      ν.coeff * integerWaveViscousMultiplier output ≠ 0 :=
    mul_ne_zero ν.coeff_pos.ne' multiplierPos.ne'
  have integralEq :
      (∫ earlier : ℝ in 0..(run initial index).nextContact.time.1,
          Real.exp
            (-(ν.coeff * integerWaveViscousMultiplier output) *
              ((run initial index).nextContact.time.1 - earlier))) =
        ∫ earlier : ℝ in 0..(run initial index).nextContact.time.1,
          Real.exp
            ((ν.coeff * integerWaveViscousMultiplier output) *
              (earlier - (run initial index).nextContact.time.1)) := by
    apply intervalIntegral.integral_congr
    intro earlier _earlierMem
    ring_nf
  rw [integralEq]
  rw [causalExpIntervalIntegral
    (ν.coeff * integerWaveViscousMultiplier output)
    (run initial index).nextContact.time.1 coefficientNe]
  field_simp [coefficientNe]

/-- After the frozen contact row is removed, every typed Duhamel innovation
is exactly the causal integral of the dynamic gluing role on the same actual
unforced receipt.  This is the occurrence-level write-back; no pair sum,
norm, target path, or persistence parameter intervenes. -/
theorem
    wholeRestartPairDuhamelInnovationOccurrence_eq_dynamicGluingIntegral
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    wholeRestartPairDuhamelInnovationOccurrence
        initial index output first =
      ∫ earlier in
          Iic
            (⟨(run initial index).nextContact.time.1,
              ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ :
              Icc (0 : ℝ) (run initial index).nextContact.time.1),
        finiteStateVorticityHeatMultiplier ν.coeff
            ((run initial index).nextContact.time.1 - earlier.1) output •
          wholeRestartCrossingDynamicPairGluingOccurrence
            initial index output first earlier
        ∂(commonTimeMeasure
          (run initial index).nextContact.time.1) := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let requestedTime := (run initial index).nextContact.time.1
  let terminal : Icc (0 : ℝ) requestedTime :=
    ⟨(run initial index).nextContact.time.1,
      ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩
  let contactPair :=
    wholeRestartContactPairOccurrenceTable
      initial index output first
  have actualIntegrable :
      Integrable
        (fun earlier : Icc (0 : ℝ) requestedTime =>
          actualWholeCausalPairVector
            receipt output first terminal earlier)
        ((commonTimeMeasure requestedTime).restrict
          (Iic terminal)) := by
    have wholeIntegrable :
        Integrable
          (fun earlier : Icc (0 : ℝ) requestedTime =>
            actualWholeCausalPairVector
              receipt output first terminal earlier)
          (commonTimeMeasure requestedTime) := by
      simpa using
        (ContinuousOn.integrableOn_compact isCompact_univ
          (actualWholeCausalPairVector_continuous
            receipt output first terminal).continuousOn)
    exact wholeIntegrable.integrableOn
  have frozenContinuous :
      Continuous
        (fun earlier : Icc (0 : ℝ) requestedTime =>
          finiteStateVorticityHeatMultiplier ν.coeff
              (terminal.1 - earlier.1) output •
            contactPair) := by
    unfold finiteStateVorticityHeatMultiplier
    fun_prop
  have frozenIntegrable :
      Integrable
        (fun earlier : Icc (0 : ℝ) requestedTime =>
          finiteStateVorticityHeatMultiplier ν.coeff
              (terminal.1 - earlier.1) output •
            contactPair)
        ((commonTimeMeasure requestedTime).restrict
          (Iic terminal)) := by
    have wholeIntegrable :
        Integrable
          (fun earlier : Icc (0 : ℝ) requestedTime =>
            finiteStateVorticityHeatMultiplier ν.coeff
                (terminal.1 - earlier.1) output •
              contactPair)
          (commonTimeMeasure requestedTime) := by
      simpa using
        (ContinuousOn.integrableOn_compact isCompact_univ
          frozenContinuous.continuousOn)
    exact wholeIntegrable.integrableOn
  have frozenIntegral :
      (∫ earlier in Iic terminal,
          finiteStateVorticityHeatMultiplier ν.coeff
              (terminal.1 - earlier.1) output •
            contactPair
          ∂(commonTimeMeasure requestedTime)) =
        wholeRestartCausalTangentGain initial index output •
          contactPair := by
    rw [integral_smul_const]
    rw [← wholeRestartCausalTangentGain_eq_heatIntegral
      initial index output outputNonzero]
  unfold wholeRestartPairDuhamelInnovationOccurrence
    wholeRestartPairDuhamelOccurrence
    actualWholePairDuhamelOccurrence
  change
    (∫ earlier in Iic terminal,
        actualWholeCausalPairVector
          receipt output first terminal earlier
        ∂(commonTimeMeasure requestedTime)) -
        wholeRestartCausalTangentGain initial index output • contactPair =
      ∫ earlier in Iic terminal,
        finiteStateVorticityHeatMultiplier ν.coeff
            (terminal.1 - earlier.1) output •
          wholeRestartCrossingDynamicPairGluingOccurrence
            initial index output first earlier
        ∂(commonTimeMeasure requestedTime)
  rw [← frozenIntegral]
  rw [← integral_sub actualIntegrable frozenIntegrable]
  apply integral_congr_ae
  filter_upwards with earlier
  unfold actualWholeCausalPairVector
  rw [← smul_sub]
  rw [wholeRestartCrossingDynamicPairGluingOccurrence_eq_nonlinearPair_sub]

/-! ## Native disposition before pair aggregation -/

/-- A nonzero causal trace contains a nonzero pointwise trace on the same
actual receipt and the same pair occurrence.  This is deliberately proved
before taking any norm or output/pair aggregate. -/
private theorem exists_pairOccurrenceTrace_ne_zero_of_causalTrace_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (traceNonzero :
      wholeRestartPairDuhamelCausalTrace
        initial index output first ≠ 0) :
    ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
      wholeRestartPairOccurrenceTrace
        initial index output first time ≠ 0 := by
  by_contra noPointwiseTrace
  push Not at noPointwiseTrace
  apply traceNonzero
  unfold wholeRestartPairDuhamelCausalTrace
  simp [noPointwiseTrace]

/-- Native consume-before-quotient disposition of one nonzero dynamic
innovation.  The innovation is not sent to a normed auxiliary carrier:
either its actual causal pair occurrence survives in the next physical
current, or the same unforced receipt writes a nonzero pointwise trace on
that exact occurrence. -/
theorem
    wholeRestartPairDuhamelInnovationOccurrence_ne_zero_next_or_trace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (innovationNonzero :
      wholeRestartPairDuhamelInnovationOccurrence
        initial index output first ≠ 0) :
    wholeRestartNextPairOccurrence initial index output first ≠ 0 ∨
      ∃ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
        wholeRestartPairOccurrenceTrace
          initial index output first time ≠ 0 := by
  by_cases occurrenceNonzero :
      wholeRestartPairDuhamelOccurrence
        initial index output first ≠ 0
  · rcases
        wholeRestartPairDuhamelOccurrence_ne_zero_next_or_causalTrace
          initial index output first occurrenceNonzero with
      nextNonzero | causalTraceNonzero
    · exact Or.inl nextNonzero
    · exact Or.inr
        (exists_pairOccurrenceTrace_ne_zero_of_causalTrace_ne_zero
          initial index output first causalTraceNonzero)
  · have occurrenceZero :
        wholeRestartPairDuhamelOccurrence
          initial index output first = 0 :=
      not_ne_iff.mp occurrenceNonzero
    have contactPairNonzero :
        wholeRestartContactPairOccurrenceTable
          initial index output first ≠ 0 := by
      intro contactPairZero
      apply innovationNonzero
      simp [wholeRestartPairDuhamelInnovationOccurrence,
        occurrenceZero, contactPairZero]
    have zeroReadNonzero :
        actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first
            ⟨0, ⟨le_rfl,
              (run initial index).nextContact.time_pos.le⟩⟩ ≠ 0 := by
      rw [actualWholeContinuousPairVector_zero_eq_contact]
      exact contactPairNonzero
    rcases
        actualWholeContinuousPairVector_ne_zero_next_or_trace
          initial index output first
            ⟨0, ⟨le_rfl,
              (run initial index).nextContact.time_pos.le⟩⟩
          zeroReadNonzero with nextNonzero | traceNonzero
    · exact Or.inl nextNonzero
    · exact Or.inr
        ⟨⟨0, ⟨le_rfl,
            (run initial index).nextContact.time_pos.le⟩⟩,
          traceNonzero⟩

/-- The strongest same-event compiler equation: the actual unforced endpoint
increment is the frozen source tangent transported by its exact causal gain,
plus the complete pre-quotient pair innovation. -/
theorem nextContact_sub_contact_eq_causalTangent_add_pairInnovation
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    (run initial index).nextContact.physicalState output -
        (run initial index).contact.physicalState output =
      wholeRestartCausalTangentGain initial index output •
          wholeRestartCrossingUnforcedTangentRow
            initial index output +
        ∑' first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
            initial index output first := by
  rw [tsum_wholeRestartPairDuhamelInnovationOccurrence_eq
    initial index output outputNonzero]
  rw [wholeRestartNonlinearRegenerationState_apply]
  unfold wholeRestartCrossingUnforcedTangentRow
  have gainIdentity :=
    viscousMultiplier_mul_causalTangentGain
      initial index output outputNonzero
  have scalarCommute :
      wholeRestartCausalTangentGain initial index output *
          (ν.coeff * integerWaveViscousMultiplier output) =
        1 - finiteStateVorticityHeatMultiplier
          ν.coeff (run initial index).nextContact.time.1 output := by
    rw [mul_comm]
    exact gainIdentity
  rw [smul_sub, smul_smul]
  have scalarSmulEq :
      (wholeRestartCausalTangentGain initial index output *
          (ν.coeff * integerWaveViscousMultiplier output)) •
          (run initial index).contact.physicalState output =
        (1 - finiteStateVorticityHeatMultiplier
          ν.coeff (run initial index).nextContact.time.1 output) •
          (run initial index).contact.physicalState output := by
    rw [scalarCommute]
  rw [scalarSmulEq]
  module

/-! ## Source-generated endpoint or pre-quotient responsibility -/

/-- The output selected internally from the nonzero actual tangent of one
half-critical crossing. -/
noncomputable def wholeRestartCrossingGeneratedTangentOutput
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    IntegerWavevector :=
  wholeRestartCrossingUnforcedTangentOutput initial index
    (wholeRestartCrossingUnforcedTangentRow_ne_zero_of_crossed
      initial index crossed)

theorem wholeRestartCrossingGeneratedTangentOutput_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingGeneratedTangentOutput initial index crossed ≠ 0 := by
  exact wholeRestartCrossingUnforcedTangentOutput_ne_zero initial index
    (wholeRestartCrossingUnforcedTangentRow_ne_zero_of_crossed
      initial index crossed)

theorem wholeRestartCrossingGeneratedTangentOutput_spec
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingUnforcedTangentRow initial index
        (wholeRestartCrossingGeneratedTangentOutput
          initial index crossed) ≠ 0 := by
  exact wholeRestartCrossingUnforcedTangentOutput_spec initial index
    (wholeRestartCrossingUnforcedTangentRow_ne_zero_of_crossed
      initial index crossed)

/-- A half-critical crossing settles its generated nonzero frozen tangent in
one of two same-event places.  Either the actual positive-time endpoint has
changed at the generated output, or a concrete input-pair occurrence carries
nonzero dynamic innovation before pair aggregation. -/
structure WholeRestartCrossingTangentInnovationResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) where
  output : IntegerWavevector
  output_ne_zero : output ≠ 0
  tangent_ne_zero :
    wholeRestartCrossingUnforcedTangentRow initial index output ≠ 0
  settlement :
    (Subtype fun _ : Unit =>
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0) ⊕
      {first : IntegerWavevector //
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first ≠ 0}

private theorem exists_pairInnovationOccurrence_ne_zero_of_tsum_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (aggregateNonzero :
      (∑' first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first) ≠ 0) :
    ∃ first : IntegerWavevector,
      wholeRestartPairDuhamelInnovationOccurrence
        initial index output first ≠ 0 := by
  by_contra noOccurrence
  push Not at noOccurrence
  apply aggregateNonzero
  have tableZero :
      (fun first : IntegerWavevector =>
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first) = 0 := by
    funext first
    exact noOccurrence first
  rw [tableZero]
  exact tsum_zero

/-- A concrete nonzero source tangent at one actual output has no silent
fixed-output branch.  The zero mode is excluded by the source equations.
The exact same-edge causal split then writes either a changed literal
unforced endpoint or a concrete pair innovation, and that innovation enters
its already generated next-pair or same-receipt trace disposition.

Unlike the crossing-facing producer below, this theorem consumes an
already-generated fixed-output tangent responsibility and requires no
half-critical crossing certificate. -/
theorem
    wholeRestartCrossingUnforcedTangentRow_ne_zero_endpoint_or_pairNativeResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow
        initial index output ≠ 0) :
    (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0 ∨
      ∃ first : IntegerWavevector,
        wholeRestartPairDuhamelInnovationOccurrence
              initial index output first ≠ 0 ∧
          (wholeRestartNextPairOccurrence
                initial index output first ≠ 0 ∨
            ∃ time :
                Icc (0 : ℝ) (run initial index).nextContact.time.1,
              wholeRestartPairOccurrenceTrace
                initial index output first time ≠ 0) := by
  have outputNonzero : output ≠ 0 := by
    intro outputZero
    subst output
    apply tangentNonzero
    unfold wholeRestartCrossingUnforcedTangentRow
    rw [wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse
      (run initial index).contact.physicalState
      (run initial index).contact.transverse]
    simp [integerWaveViscousMultiplier,
      (run initial index).contact.physicalState_zero]
  have tangentContributionNonzero :
      wholeRestartCausalTangentGain initial index output •
          wholeRestartCrossingUnforcedTangentRow
            initial index output ≠ 0 :=
    smul_ne_zero
      (wholeRestartCausalTangentGain_pos
        initial index output outputNonzero).ne'
      tangentNonzero
  have endpointSplit :
      (run initial index).nextContact.physicalState output -
            (run initial index).contact.physicalState output =
        wholeRestartCausalTangentGain initial index output •
            wholeRestartCrossingUnforcedTangentRow
              initial index output +
          ∑' first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
              initial index output first :=
    nextContact_sub_contact_eq_causalTangent_add_pairInnovation
      initial index output outputNonzero
  by_cases endpointNonzero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0
  · exact Or.inl endpointNonzero
  · right
    have endpointZero :
        (run initial index).nextContact.physicalState output -
            (run initial index).contact.physicalState output = 0 :=
      not_ne_iff.mp endpointNonzero
    have aggregateNonzero :
        (∑' first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
            initial index output first) ≠ 0 := by
      intro aggregateZero
      rw [endpointZero, aggregateZero, add_zero] at endpointSplit
      exact tangentContributionNonzero endpointSplit.symm
    obtain ⟨first, innovationNonzero⟩ :=
      exists_pairInnovationOccurrence_ne_zero_of_tsum_ne_zero
        initial index output aggregateNonzero
    exact
      ⟨first, innovationNonzero,
        wholeRestartPairDuhamelInnovationOccurrence_ne_zero_next_or_trace
          initial index output first innovationNonzero⟩

/-- Source-owned settlement producer.  The crossing itself selects the
output; no output, pair occurrence, branch, gain, cutoff, target, or
faithfulness certificate is supplied by the caller. -/
noncomputable def wholeRestartCrossing_generates_tangentInnovationResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    WholeRestartCrossingTangentInnovationResponsibility initial index := by
  let output :=
    wholeRestartCrossingGeneratedTangentOutput initial index crossed
  have outputNonzero : output ≠ 0 :=
    wholeRestartCrossingGeneratedTangentOutput_ne_zero
      initial index crossed
  have tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index output ≠ 0 :=
    wholeRestartCrossingGeneratedTangentOutput_spec
      initial index crossed
  have tangentContributionNonzero :
      wholeRestartCausalTangentGain initial index output •
          wholeRestartCrossingUnforcedTangentRow
            initial index output ≠ 0 :=
    smul_ne_zero
      (wholeRestartCausalTangentGain_pos
        initial index output outputNonzero).ne'
      tangentNonzero
  have endpointSplit :=
    nextContact_sub_contact_eq_causalTangent_add_pairInnovation
      initial index output outputNonzero
  refine
    { output := output
      output_ne_zero := outputNonzero
      tangent_ne_zero := tangentNonzero
      settlement := ?_ }
  by_cases endpointNonzero :
      (run initial index).nextContact.physicalState output -
          (run initial index).contact.physicalState output ≠ 0
  · exact Sum.inl ⟨(), endpointNonzero⟩
  · have endpointZero :
        (run initial index).nextContact.physicalState output -
            (run initial index).contact.physicalState output = 0 :=
      not_ne_iff.mp endpointNonzero
    have aggregateNonzero :
        (∑' first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
            initial index output first) ≠ 0 := by
      intro aggregateZero
      rw [endpointZero, aggregateZero, add_zero] at endpointSplit
      exact tangentContributionNonzero endpointSplit.symm
    let first := Classical.choose
      (exists_pairInnovationOccurrence_ne_zero_of_tsum_ne_zero
        initial index output aggregateNonzero)
    have firstNonzero :
        wholeRestartPairDuhamelInnovationOccurrence
          initial index output first ≠ 0 :=
      Classical.choose_spec
        (exists_pairInnovationOccurrence_ne_zero_of_tsum_ne_zero
          initial index output aggregateNonzero)
    exact Sum.inr ⟨first, firstNonzero⟩

/-- A crossing now writes its nonlinear obstruction into the actual dynamic
gluing role itself.  The source selects a nonzero output and then either its
unforced endpoint has changed there, or one concrete input-pair occurrence
has a nonzero causal dynamic-gluing integral on that same receipt. -/
theorem wholeRestartCrossing_generates_endpoint_or_dynamicGluingIntegral
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    ∃ output : IntegerWavevector,
      output ≠ 0 ∧
        wholeRestartCrossingUnforcedTangentRow
            initial index output ≠ 0 ∧
          ((run initial index).nextContact.physicalState output -
                (run initial index).contact.physicalState output ≠ 0 ∨
            ∃ first : IntegerWavevector,
              (∫ earlier in
                  Iic
                    (⟨(run initial index).nextContact.time.1,
                      ⟨(run initial index).nextContact.time_pos.le,
                        le_rfl⟩⟩ :
                      Icc (0 : ℝ)
                        (run initial index).nextContact.time.1),
                finiteStateVorticityHeatMultiplier ν.coeff
                    ((run initial index).nextContact.time.1 - earlier.1)
                    output •
                  wholeRestartCrossingDynamicPairGluingOccurrence
                    initial index output first earlier
                ∂(commonTimeMeasure
                  (run initial index).nextContact.time.1)) ≠ 0) := by
  let responsibility :=
    wholeRestartCrossing_generates_tangentInnovationResponsibility
      initial index crossed
  refine
    ⟨responsibility.output,
      responsibility.output_ne_zero,
      responsibility.tangent_ne_zero, ?_⟩
  rcases responsibility.settlement with endpoint | innovation
  · exact Or.inl endpoint.property
  · right
    refine ⟨innovation.1, ?_⟩
    rw [←
      wholeRestartPairDuhamelInnovationOccurrence_eq_dynamicGluingIntegral
        initial index responsibility.output innovation.1
        responsibility.output_ne_zero]
    exact innovation.2

/-- Full native settlement of the source-generated tangent obstruction.
The crossing chooses its output and the causal algebra chooses the responsible
pair occurrence.  The responsibility then lands either in the actual endpoint,
the next physical pair table, or a nonzero trace written by the same receipt.
No norm, time slice, branch, target state, persistence parameter, or external
continuation witness occurs in the theorem mouth. -/
theorem wholeRestartCrossing_generates_endpoint_or_nextPair_or_trace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    ∃ output : IntegerWavevector,
      output ≠ 0 ∧
        wholeRestartCrossingUnforcedTangentRow
            initial index output ≠ 0 ∧
          ((run initial index).nextContact.physicalState output -
                (run initial index).contact.physicalState output ≠ 0 ∨
            ∃ first : IntegerWavevector,
              wholeRestartNextPairOccurrence
                    initial index output first ≠ 0 ∨
                ∃ time : Icc (0 : ℝ)
                    (run initial index).nextContact.time.1,
                  wholeRestartPairOccurrenceTrace
                    initial index output first time ≠ 0) := by
  let responsibility :=
    wholeRestartCrossing_generates_tangentInnovationResponsibility
      initial index crossed
  refine
    ⟨responsibility.output,
      responsibility.output_ne_zero,
      responsibility.tangent_ne_zero, ?_⟩
  rcases responsibility.settlement with endpoint | innovation
  · exact Or.inl endpoint.property
  · exact Or.inr
      ⟨innovation.1,
        wholeRestartPairDuhamelInnovationOccurrence_ne_zero_next_or_trace
          initial index responsibility.output innovation.1 innovation.2⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
end NavierStokes
end SaturationMonoid
