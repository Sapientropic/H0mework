import H0mework.NavierStokes.Restart.ExactCausalKernelRate
import H0mework.NavierStokes.PairRestart.SourcePairOccurrence
import H0mework.Realization.Residual.TraceWriteback

/-!
# Pair-occurrence settlement of the nonlinear restart rate

The exact causal-kernel estimate pays one restart regeneration rate by the
time-`L²` square of its actual nonlinear output.  This module identifies that
visible output, on the same outgoing receipt, with the complete typed input-pair
table before coefficient aggregation.

No occurrence norm is introduced.  The pair table is aggregated by its actual
Fourier `tsum`; its visible image is the existing physical nonlinear output,
whose square is exactly the frequency-weighted segment row already forced by
the restart recurrence.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement

open scoped BigOperators ENNReal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartExactCausalKernelRate
open AffineRelaxation
open ResidualProjection

noncomputable section

/-! ## Same-receipt pair aggregation -/

/-- On every physical time slice, the complete typed input-pair table
aggregates to the actual nonlinear Fourier output of the same whole receipt. -/
theorem tsum_actualWholeContinuousPairVector_eq_nonlinearOutput
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    (∑' first : IntegerWavevector,
      actualWholeContinuousPairVector receipt output first time) =
        wholeStateVorticityNonlinearCoefficientAt
          (receipt.wholePath time) output := by
  unfold actualWholeContinuousPairVector
    wholeStateVorticityNonlinearCoefficientAt
  rfl

/-- The same aggregation is exactly the continuous nonlinear-row readout,
not merely an endpoint or time-zero calibration. -/
theorem tsum_actualWholeContinuousPairVector_eq_continuousNonlinearRow
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    (∑' first : IntegerWavevector,
      actualWholeContinuousPairVector receipt output first time) =
        actualWholeContinuousNonlinearRow receipt output time.1 := by
  rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput]
  unfold actualWholeContinuousNonlinearRow
  have projectedEq :
      (actualWholeProjectedTransversePath receipt time.1).1 =
        receipt.wholePath time := by
    change
      receipt.wholePath
          (Set.projIcc (0 : ℝ) requestedTime
            receipt.requestedTimePos.le time.1) =
        receipt.wholePath time
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le time.property]
  exact congrArg
    (fun state : ComplexVorticityHilbertState =>
      wholeStateVorticityNonlinearCoefficientAt state output)
    projectedEq.symm

/-! ## Visible output square on one generated restart edge -/

/-- The actual nonlinear output row of one outgoing restart receipt, retained
in time `L²` before the spatial output sum. -/
def wholeRestartSegmentVisibleNonlinearOutputRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    FixedWaveSpaceTimeState (run initial index).nextContact.time.1 :=
  (Real.sqrt (integerWaveViscousMultiplier output) : ℂ) •
    fixedWaveSpaceTimeRestriction
      (run initial index).nextContact.time.1 output
      (receiptNonlinearNegativeOneState
        (run initial index).nextContact.prefixReceipt)

/-- The visible output norm square is exactly the segment row used by the
causal-kernel payment.  There is no comparison constant or caller-supplied
coercivity parameter. -/
theorem wholeRestartSegmentVisibleNonlinearOutputRow_norm_sq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector) :
    ‖wholeRestartSegmentVisibleNonlinearOutputRow initial index output‖ ^ 2 =
      wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
        initial index output := by
  have multiplierNonneg :
      0 ≤ integerWaveViscousMultiplier output := by
    unfold integerWaveViscousMultiplier
    exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output)
  unfold wholeRestartSegmentVisibleNonlinearOutputRow
    wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
  rw [norm_smul, mul_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt multiplierNonneg]

/-- On the same outgoing receipt, the visible `L²` row is almost everywhere
the aggregation of the complete typed pair table.  This is the commuting
formation/aggregation/readout square needed before any quotient can erase
pair provenance. -/
theorem wholeRestartSegmentVisibleNonlinearOutputRow_ae_eq_pairTsum
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure
        (run initial index).nextContact.time.1),
      wholeRestartSegmentVisibleNonlinearOutputRow
          initial index output time =
        ∑' first : IntegerWavevector,
          actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first time := by
  let receipt := (run initial index).nextContact.prefixReceipt
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul
      (Real.sqrt (integerWaveViscousMultiplier output) : ℂ)
      (fixedWaveSpaceTimeRestriction
        (run initial index).nextContact.time.1 output
        (receiptNonlinearNegativeOneState receipt)),
    fixedWaveSpaceTimeRestriction_coeFn
      (run initial index).nextContact.time.1 output
      (receiptNonlinearNegativeOneState receipt),
    receiptNonlinearNegativeOneState_row_ae
      receipt output outputNonzero,
    receipt.wholePath_eq_transverse_ae] with
      time smulEq restrictionEq unweightedEq pathEq
  rw [wholeRestartSegmentVisibleNonlinearOutputRow, smulEq]
  change
    (Real.sqrt (integerWaveViscousMultiplier output) : ℂ) •
        fixedWaveSpaceTimeRestriction
          (run initial index).nextContact.time.1 output
          (receiptNonlinearNegativeOneState receipt) time = _
  rw [restrictionEq]
  have scalarActionEq :
      (Real.sqrt (integerWaveViscousMultiplier output) : ℂ) •
          (receiptNonlinearNegativeOneState receipt time) output =
        (Real.sqrt (integerWaveViscousMultiplier output) : ℝ) •
          (receiptNonlinearNegativeOneState receipt time) output := by
    ext coordinate
    simp [Complex.real_smul]
  rw [scalarActionEq, unweightedEq,
    wholeStateVorticityBilinearCoefficientAt_self]
  rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput]
  exact congrArg
    (fun state : ComplexVorticityHilbertState =>
      wholeStateVorticityNonlinearCoefficientAt state output)
    pathEq.symm

/-- The causal-kernel segment row is literally the physical-time integral of
the squared visible aggregation of the complete pair table. -/
theorem wholeRestartSegmentFrequencyWeightedNonlinearSquareRow_eq_pairTsum_integral
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (outputNonzero : output ≠ 0) :
    wholeRestartSegmentFrequencyWeightedNonlinearSquareRow
        initial index output =
      ∫ time,
        ‖∑' first : IntegerWavevector,
          actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first time‖ ^ 2
        ∂(commonTimeMeasure
          (run initial index).nextContact.time.1) := by
  rw [← wholeRestartSegmentVisibleNonlinearOutputRow_norm_sq,
    fixedWaveSpaceTimeState_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [
    wholeRestartSegmentVisibleNonlinearOutputRow_ae_eq_pairTsum
      initial index output outputNonzero] with time visibleEq
  rw [visibleEq]

/-! ## Componentwise native transport inside the aggregation kernel -/

/-- The same pair occurrence, evaluated after the actual source-owned restart
write.  This is a component of the next physical current, not an auxiliary
memory state. -/
def wholeRestartNextPairOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  finiteStateVorticityNonlinearPairContribution
    (run initial (index + 1)).contact.physicalState
    (first, output - first)

/-- Forced component trace from an arbitrary time slice of the outgoing
receipt to the next actual physical current. -/
def wholeRestartPairOccurrenceTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ComplexCoordinateVector :=
  actualWholeContinuousPairVector
      (run initial index).nextContact.prefixReceipt
      output first time -
    wholeRestartNextPairOccurrence initial index output first

/-- The terminal read of the outgoing receipt is literally the corresponding
pair component of the next actual restart current. -/
theorem actualWholeContinuousPairVector_terminal_eq_next
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first
        ⟨(run initial index).nextContact.time.1,
          ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ =
      wholeRestartNextPairOccurrence initial index output first := by
  unfold actualWholeContinuousPairVector wholeRestartNextPairOccurrence
  rw [(run initial index).nextContact_prefix_terminal]
  rfl

/-- Exact read/write split on every pair occurrence of the same actual
positive-time event. -/
theorem actualWholeContinuousPairVector_eq_next_add_trace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first time =
      wholeRestartNextPairOccurrence initial index output first +
        wholeRestartPairOccurrenceTrace
          initial index output first time := by
  unfold wholeRestartPairOccurrenceTrace
  abel

/-- A nonzero pair occurrence cannot disappear through the actual write: it
either remains nonzero in the next physical current or writes a nonzero forced
trace on that very component. -/
theorem actualWholeContinuousPairVector_ne_zero_next_or_trace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (currentNonzero :
      actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time ≠ 0) :
    wholeRestartNextPairOccurrence initial index output first ≠ 0 ∨
      wholeRestartPairOccurrenceTrace
        initial index output first time ≠ 0 := by
  by_cases nextNonzero :
      wholeRestartNextPairOccurrence initial index output first ≠ 0
  · exact Or.inl nextNonzero
  · right
    intro traceZero
    apply currentNonzero
    rw [actualWholeContinuousPairVector_eq_next_add_trace,
      not_ne_iff.mp nextNonzero, traceZero, zero_add]

/-- The actual pair table is summable before aggregation at every time of the
same whole receipt. -/
theorem summable_actualWholeContinuousPairVector
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) requestedTime) :
    Summable fun first : IntegerWavevector =>
      actualWholeContinuousPairVector receipt output first time := by
  unfold actualWholeContinuousPairVector
  exact summable_wholeStateVorticityNonlinearPair
    (receipt.wholePath time) (wholePath_transverse receipt time) output

/-! ## Source-owned pair-occurrence residual process -/

/-- Complete output-by-input-pair table before Fourier aggregation. -/
abbrev WholeRestartPairOccurrenceTable :=
  IntegerWavevector → IntegerWavevector → ComplexCoordinateVector

/-- Pair table of one actual whole restart contact. -/
def wholeRestartContactPairOccurrenceTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : WholeRestartPairOccurrenceTable :=
  fun output first =>
    finiteStateVorticityNonlinearPairContribution
      (run initial index).contact.physicalState
      (first, output - first)

/-- The source end of an outgoing receipt is the current contact's complete
pair table. -/
theorem actualWholeContinuousPairVector_zero_eq_contact
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first
        ⟨0, ⟨le_rfl,
          (run initial index).nextContact.prefixReceipt.requestedTimePos.le⟩⟩ =
      wholeRestartContactPairOccurrenceTable
        initial index output first := by
  unfold actualWholeContinuousPairVector
    wholeRestartContactPairOccurrenceTable
  rw [(run initial index).nextContact.prefixReceipt.wholePath_initial]

/-- Same-event dynamic innovation before pair aggregation.  The current
contact table is the time-zero baseline; every later difference is exactly
the difference of the already generated read/write traces at those two
slices.  No auxiliary provenance state is introduced. -/
theorem actualWholeContinuousPairVector_eq_contact_add_traceInnovation
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first time =
      wholeRestartContactPairOccurrenceTable
          initial index output first +
        (wholeRestartPairOccurrenceTrace
            initial index output first time -
          wholeRestartPairOccurrenceTrace
            initial index output first
              ⟨0, ⟨le_rfl,
                (run initial index).nextContact.time_pos.le⟩⟩) := by
  have timeSplit :=
    actualWholeContinuousPairVector_eq_next_add_trace
      initial index output first time
  have zeroSplit :=
    actualWholeContinuousPairVector_eq_next_add_trace
      initial index output first
        ⟨0, ⟨le_rfl,
          (run initial index).nextContact.time_pos.le⟩⟩
  rw [actualWholeContinuousPairVector_zero_eq_contact
    initial index output first] at zeroSplit
  rw [timeSplit, zeroSplit]
  abel

/-- Aggregating the occurrence-level innovation gives exactly the change of
the physical nonlinear output along the same actual receipt.  This is the
consume-before-quotient baseline split used by the causal headroom payment. -/
theorem tsum_actualWholeContinuousPairInnovation_eq_nonlinearOutput_sub_contact
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    (∑' first : IntegerWavevector,
      (actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time -
        wholeRestartContactPairOccurrenceTable
          initial index output first)) =
      wholeStateVorticityNonlinearCoefficientAt
          ((run initial index).nextContact.prefixReceipt.wholePath time)
          output -
        wholeStateVorticityNonlinearCoefficientAt
          (run initial index).contact.physicalState output := by
  have timeSummable :=
    summable_actualWholeContinuousPairVector
      (run initial index).nextContact.prefixReceipt output time
  have zeroSummable :=
    summable_actualWholeContinuousPairVector
      (run initial index).nextContact.prefixReceipt output
        ⟨0, ⟨le_rfl,
          (run initial index).nextContact.time_pos.le⟩⟩
  rw [Summable.tsum_sub timeSummable
    (zeroSummable.congr fun first =>
      actualWholeContinuousPairVector_zero_eq_contact
        initial index output first)]
  rw [tsum_actualWholeContinuousPairVector_eq_nonlinearOutput]
  rw [show
      (∑' first : IntegerWavevector,
        wholeRestartContactPairOccurrenceTable
          initial index output first) =
        wholeStateVorticityNonlinearCoefficientAt
          (run initial index).contact.physicalState output by
    unfold wholeRestartContactPairOccurrenceTable
      wholeStateVorticityNonlinearCoefficientAt
    rfl]

/-- The old `next` readout is exactly the contact pair table after the actual
source-owned restart update. -/
theorem wholeRestartNextPairOccurrence_eq_contact_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector) :
    wholeRestartNextPairOccurrence initial index output first =
      wholeRestartContactPairOccurrenceTable
        initial (index + 1) output first := by
  rfl

/-- One actual time slice spliced into the already generated future restart
lineage.  Stage zero is the chosen slice of the current outgoing receipt;
every positive stage is an actual later contact, not an auxiliary state. -/
def wholeRestartSplicedPairOccurrenceTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ℕ → WholeRestartPairOccurrenceTable
  | 0 => fun output first =>
      actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first time
  | later + 1 =>
      wholeRestartContactPairOccurrenceTable
        initial (index + later + 1)

@[simp] theorem wholeRestartSplicedPairOccurrenceTable_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    wholeRestartSplicedPairOccurrenceTable initial index time 0 =
      fun output first =>
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time := by
  rfl

@[simp] theorem wholeRestartSplicedPairOccurrenceTable_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (later : ℕ) :
    wholeRestartSplicedPairOccurrenceTable
        initial index time (later + 1) =
      wholeRestartContactPairOccurrenceTable
        initial (index + later + 1) := by
  rfl

/-- Forced componentwise trace of each consecutive actual table. -/
def wholeRestartSplicedPairOccurrenceTraceRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (stage : ℕ) : WholeRestartPairOccurrenceTable :=
  wholeRestartSplicedPairOccurrenceTable initial index time stage -
    wholeRestartSplicedPairOccurrenceTable initial index time (stage + 1)

/-- Chronological pre-quotient write-back of the component trace rows already
generated by the spliced actual path.  Individual rows remain separate even
when their aggregate sum cancels. -/
def wholeRestartSplicedPairOccurrenceTraceLedger
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (steps : ℕ) : List WholeRestartPairOccurrenceTable :=
  (List.range steps).reverse.map
    (wholeRestartSplicedPairOccurrenceTraceRow initial index time)

/-- The same actual successor event writes its forced component trace row
before advancing the chronological ledger. -/
theorem wholeRestartSplicedPairOccurrenceTraceLedger_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (steps : ℕ) :
    wholeRestartSplicedPairOccurrenceTraceLedger
        initial index time (steps + 1) =
      wholeRestartSplicedPairOccurrenceTraceRow
          initial index time steps ::
        wholeRestartSplicedPairOccurrenceTraceLedger
          initial index time steps := by
  simp [wholeRestartSplicedPairOccurrenceTraceLedger, List.range_succ]

/-- Future tail of the actual spliced pair-occurrence path. -/
abbrev WholeRestartSplicedPairOccurrenceTail :=
  ℕ → WholeRestartPairOccurrenceTable

/-- Forget exactly the pair table written by the current actual stage. -/
def wholeRestartSplicedPairOccurrenceTailKeep :
    WholeRestartSplicedPairOccurrenceTail →ₗ[ℂ]
      WholeRestartSplicedPairOccurrenceTail where
  toFun residual offset := residual (offset + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual future pair-occurrence residual beginning at one spliced stage. -/
def wholeRestartSplicedPairOccurrenceTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (stage : ℕ) : WholeRestartSplicedPairOccurrenceTail :=
  fun offset =>
    wholeRestartSplicedPairOccurrenceTable
      initial index time (stage + offset)

/-- The chosen actual receipt slice followed by the source-owned whole restart
run is an effective residual process on the complete pair-occurrence carrier.
No pair, output, branch, nonzero witness, horizon or metric enters the process
mouth. -/
def generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    EffectiveResidualProcess
      ℂ WholeRestartSplicedPairOccurrenceTail ℕ where
  target := 0
  keep := wholeRestartSplicedPairOccurrenceTailKeep
  residual :=
    wholeRestartSplicedPairOccurrenceTail initial index time
  update := Nat.succ
  residual_transport_law := by
    intro stage
    funext offset
    simp only [wholeRestartSplicedPairOccurrenceTail,
      wholeRestartSplicedPairOccurrenceTailKeep,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    omega

@[simp] theorem
    generatedWholeRestartSplicedPairOccurrenceEffectiveProcess_pathState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (stage steps : ℕ) :
    (generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
      initial index time).pathState stage steps =
      stage + steps := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [EffectiveResidualProcess.pathState_succ,
        inductionHypothesis]
      rfl

/-- Whole-carrier commuting square for every actual stage of the pair path. -/
theorem wholeRestartSplicedPairOccurrence_transport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (stage : ℕ) :
    wholeRestartSplicedPairOccurrenceTail
        initial index time (stage + 1) =
      wholeRestartSplicedPairOccurrenceTailKeep
        (wholeRestartSplicedPairOccurrenceTail
          initial index time stage) :=
  (generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
    initial index time).residual_transport_law stage

/-- The process trace at every head is exactly the componentwise difference
written by that actual transition. -/
theorem wholeRestartSplicedPairOccurrence_trace_head
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (stage : ℕ) :
    linearResidualTrace wholeRestartSplicedPairOccurrenceTailKeep
          (wholeRestartSplicedPairOccurrenceTail
            initial index time stage) 0 =
      wholeRestartSplicedPairOccurrenceTraceRow
        initial index time stage := by
  rfl

/-- At the receipt splice, the unique whole-carrier residual trace is exactly
the pre-quotient pair occurrence trace of that same actual time slice. -/
theorem wholeRestartSplicedPairOccurrence_trace_head_apply_eq_pairOccurrenceTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (output first : IntegerWavevector) :
    (linearResidualTrace wholeRestartSplicedPairOccurrenceTailKeep
        (wholeRestartSplicedPairOccurrenceTail initial index time 0)
        0) output first =
      wholeRestartPairOccurrenceTrace
        initial index output first time := by
  rw [wholeRestartSplicedPairOccurrence_trace_head]
  rfl

/-- Finite-path conservation on the entire output-by-pair carrier. -/
theorem wholeRestartSplicedPairOccurrence_path_split
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (steps : ℕ) :
    wholeRestartSplicedPairOccurrenceTable initial index time 0 =
      wholeRestartSplicedPairOccurrenceTable initial index time steps +
        ((generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
            initial index time).pathTrace 0 steps) 0 := by
  have split :=
    (generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
      initial index time).pathTrace_split 0 steps
  rw [generatedWholeRestartSplicedPairOccurrenceEffectiveProcess_pathState]
    at split
  simpa [generatedWholeRestartSplicedPairOccurrenceEffectiveProcess,
    wholeRestartSplicedPairOccurrenceTail] using congrFun split 0

/-- A nonzero pair occurrence cannot be erased after any finite number of
actual restarts: it is still present at the actual future contact or occurs in
the uniquely accumulated path trace.  No uniform quantum is required. -/
theorem actualWholeContinuousPairVector_ne_zero_future_or_pathTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (steps : ℕ)
    (currentNonzero :
      actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time ≠ 0) :
    wholeRestartSplicedPairOccurrenceTable
          initial index time steps output first ≠ 0 ∨
      ((generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
          initial index time).pathTrace 0 steps) 0 output first ≠ 0 := by
  by_cases futureNonzero :
      wholeRestartSplicedPairOccurrenceTable
        initial index time steps output first ≠ 0
  · exact Or.inl futureNonzero
  · right
    intro traceZero
    apply currentNonzero
    have split := congrFun
      (congrFun
        (wholeRestartSplicedPairOccurrence_path_split
          initial index time steps) output) first
    simp only [Pi.add_apply] at split
    rw [not_ne_iff.mp futureNonzero, traceZero, zero_add] at split
    simpa using split

/-- If a complete pair table is nonzero but its visible aggregation vanishes,
the kernel contains a genuine critical pair: one nonzero component is balanced
by a nonzero complementary component.  The first component is simultaneously
transported by the actual next write or recorded by its forced trace.

This theorem does not attach a new norm to provenance and does not use a
Boolean terminal law. -/
theorem pairAggregationKernel_componentwise_nativeTransport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (tableNonzero :
      (fun first : IntegerWavevector =>
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time) ≠ 0)
    (aggregateZero :
      (∑' first : IntegerWavevector,
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time) = 0) :
    ∃ first second : IntegerWavevector,
      first ≠ second ∧
        actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first time ≠ 0 ∧
        actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output second time ≠ 0 ∧
        ((∑' other : IntegerWavevector,
            if other = first then 0 else
              actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output other time) =
          -actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first time) ∧
        (wholeRestartNextPairOccurrence
              initial index output first ≠ 0 ∨
          wholeRestartPairOccurrenceTrace
            initial index output first time ≠ 0) := by
  let table : IntegerWavevector → ComplexCoordinateVector :=
    fun first =>
      actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first time
  have tableSummable : Summable table :=
    summable_actualWholeContinuousPairVector
      (run initial index).nextContact.prefixReceipt output time
  have existsFirst : ∃ first, table first ≠ 0 := by
    by_contra allZero
    push Not at allZero
    apply tableNonzero
    funext first
    exact allZero first
  obtain ⟨first, firstNonzero⟩ := existsFirst
  have aggregateSplit :
      (∑' other : IntegerWavevector, table other) =
        table first +
          ∑' other : IntegerWavevector,
            if other = first then 0 else table other :=
    tableSummable.tsum_eq_add_tsum_ite first
  have complementEq :
      (∑' other : IntegerWavevector,
        if other = first then 0 else table other) = -table first := by
    rw [aggregateZero] at aggregateSplit
    exact eq_neg_of_add_eq_zero_right aggregateSplit.symm
  have complementNonzero :
      (∑' other : IntegerWavevector,
        if other = first then 0 else table other) ≠ 0 := by
    rw [complementEq]
    exact neg_ne_zero.mpr firstNonzero
  have existsSecond :
      ∃ second : IntegerWavevector,
        second ≠ first ∧ table second ≠ 0 := by
    by_contra noSecond
    push Not at noSecond
    apply complementNonzero
    have complementFunctionZero :
        (fun second : IntegerWavevector =>
          if second = first then 0 else table second) = 0 := by
      funext second
      split_ifs with secondEq
      · rfl
      · exact noSecond second secondEq
    rw [complementFunctionZero]
    exact tsum_zero
  obtain ⟨second, secondNeFirst, secondNonzero⟩ := existsSecond
  refine ⟨first, second, secondNeFirst.symm,
    firstNonzero, secondNonzero, complementEq, ?_⟩
  exact actualWholeContinuousPairVector_ne_zero_next_or_trace
    initial index output first time firstNonzero

/-- The same kernel component is protected across every finite prefix of the
actual restart lineage.  At each horizon it either survives at that concrete
future contact or appears in the uniquely accumulated pre-quotient path
trace.  This is the no-uniform-quantum finite-path strengthening of the
one-step native transport above. -/
theorem pairAggregationKernel_componentwise_nativePathTransport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (tableNonzero :
      (fun first : IntegerWavevector =>
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time) ≠ 0)
    (aggregateZero :
      (∑' first : IntegerWavevector,
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time) = 0) :
    ∃ first second : IntegerWavevector,
      first ≠ second ∧
        actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first time ≠ 0 ∧
        actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output second time ≠ 0 ∧
        ((∑' other : IntegerWavevector,
            if other = first then 0 else
              actualWholeContinuousPairVector
                (run initial index).nextContact.prefixReceipt
                output other time) =
          -actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first time) ∧
        ∀ steps : ℕ,
          wholeRestartSplicedPairOccurrenceTable
                initial index time steps output first ≠ 0 ∨
            ((generatedWholeRestartSplicedPairOccurrenceEffectiveProcess
                initial index time).pathTrace 0 steps)
              0 output first ≠ 0 := by
  obtain ⟨first, second, distinct, firstNonzero, secondNonzero,
      complementEq, _oneStep⟩ :=
    pairAggregationKernel_componentwise_nativeTransport
      initial index output time tableNonzero aggregateZero
  refine ⟨first, second, distinct, firstNonzero, secondNonzero,
    complementEq, ?_⟩
  intro steps
  exact actualWholeContinuousPairVector_ne_zero_future_or_pathTrace
    initial index output first time steps firstNonzero

/-- Type-valued responsibility of one kernel component under the actual whole
restart write.  The alternatives retain the concrete next value or the forced
same-component trace; neither is a Boolean terminal disposition. -/
inductive WholeRestartPairOccurrenceNativeResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) : Type
  | continued
      (nextNonzero :
        wholeRestartNextPairOccurrence
          initial index output first ≠ 0)
  | traced
      (traceNonzero :
        wholeRestartPairOccurrenceTrace
          initial index output first time ≠ 0)

/-- A nonzero aggregation-kernel event with its concrete critical-pair
provenance and its source-owned next/trace responsibility. -/
structure PairAggregationKernelNativeTransportReceipt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) where
  first : IntegerWavevector
  second : IntegerWavevector
  distinct : first ≠ second
  firstNonzero :
    actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first time ≠ 0
  secondNonzero :
    actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output second time ≠ 0
  complement_eq :
    (∑' other : IntegerWavevector,
      if other = first then 0 else
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output other time) =
      -actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first time
  responsibility :
    WholeRestartPairOccurrenceNativeResponsibility
      initial index output first time

theorem pairAggregationKernelNativeTransportReceipt_nonempty
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (tableNonzero :
      (fun first : IntegerWavevector =>
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time) ≠ 0)
    (aggregateZero :
      (∑' first : IntegerWavevector,
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time) = 0) :
    Nonempty
      (PairAggregationKernelNativeTransportReceipt
        initial index output time) := by
  obtain ⟨first, second, distinct, firstNonzero, secondNonzero,
      complementEq, responsibility⟩ :=
    pairAggregationKernel_componentwise_nativeTransport
      initial index output time tableNonzero aggregateZero
  have responsibilityNonempty :
      Nonempty
        (WholeRestartPairOccurrenceNativeResponsibility
          initial index output first time) := by
    cases responsibility with
    | inl nextNonzero =>
        exact ⟨.continued nextNonzero⟩
    | inr traceNonzero =>
        exact ⟨.traced traceNonzero⟩
  refine ⟨
    { first := first
      second := second
      distinct := distinct
      firstNonzero := firstNonzero
      secondNonzero := secondNonzero
      complement_eq := complementEq
      responsibility := Classical.choice responsibilityNonempty }⟩

/-- Select the concrete critical pair and its native responsibility from an
actual nonzero kernel table.  The source-owned whole update, output, pair
values and trace are fixed before this selection; callers supply no branch or
target state. -/
noncomputable def pairAggregationKernelNativeTransportReceipt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (tableNonzero :
      (fun first : IntegerWavevector =>
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time) ≠ 0)
    (aggregateZero :
      (∑' first : IntegerWavevector,
        actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time) = 0) :
    PairAggregationKernelNativeTransportReceipt
      initial index output time := by
  exact Classical.choice
    (pairAggregationKernelNativeTransportReceipt_nonempty
      initial index output time tableNonzero aggregateZero)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
end NavierStokes
end SaturationMonoid
