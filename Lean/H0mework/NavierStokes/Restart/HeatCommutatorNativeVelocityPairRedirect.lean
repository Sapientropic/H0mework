import H0mework.NavierStokes.PairRestart.PairDuhamelKineticTriadRedirect

/-!
# Native velocity-pair redirect for the causal heat commutator

The reflected kinetic relation can leave a nonzero causal heat commutator
before the velocity-pair carrier is curled into the vorticity pair table.
This module settles that branch on its native carrier.

For one actual outgoing whole-restart receipt, the source-owned positive-time
path is spliced directly into the already generated future restart run.  The
complete ordered velocity-pair table is shifted by the literal native
successor, and its trace is the uniquely forced componentwise difference.
A nonzero heat commutator therefore generates a time at which its actual
ordered kinetic occurrence is nonzero; the corresponding velocity-pair
occurrence then remains in the next physical current or writes a nonzero
whole-carrier trace.

No pair, time, branch, target state, continuation witness, curl-faithfulness
law, norm on provenance, or nonzero certificate enters the process mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect

open scoped BigOperators Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open AffineRelaxation
open ResidualProjection

noncomputable section

/-! ## Actual ordered velocity-pair write -/

/-- Complete ordered velocity-pair table before curl or output aggregation. -/
abbrev WholeRestartVelocityPairOccurrenceTable :=
  IntegerWavevector → IntegerWavevector → ComplexCoordinateVector

/-- Ordered velocity-pair table of one actual whole-restart contact. -/
def wholeRestartContactVelocityPairOccurrenceTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : WholeRestartVelocityPairOccurrenceTable :=
  fun first second =>
    finiteStateVelocityBilinearPairContribution
      (run initial index).contact.physicalState
      (run initial index).contact.physicalState
      (first, second)

/-- The same ordered velocity pair after the actual source-owned restart
write.  This is a component of the next physical current. -/
def wholeRestartNextVelocityPairOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector) : ComplexCoordinateVector :=
  wholeRestartContactVelocityPairOccurrenceTable
    initial (index + 1) first second

/-- Forced trace from a time slice of the actual outgoing receipt to the
ordered velocity-pair component of the next physical current. -/
def wholeRestartVelocityPairOccurrenceTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ComplexCoordinateVector :=
  actualWholeContinuousVelocityPairVector
      (run initial index).nextContact.prefixReceipt
      first second time -
    wholeRestartNextVelocityPairOccurrence initial index first second

/-- The terminal read of the actual outgoing receipt is literally the
ordered velocity-pair component of the next native restart current. -/
theorem actualWholeContinuousVelocityPairVector_terminal_eq_next
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector) :
    actualWholeContinuousVelocityPairVector
        (run initial index).nextContact.prefixReceipt
        first second
        ⟨(run initial index).nextContact.time.1,
          ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩ =
      wholeRestartNextVelocityPairOccurrence
        initial index first second := by
  unfold actualWholeContinuousVelocityPairVector
    wholeRestartNextVelocityPairOccurrence
    wholeRestartContactVelocityPairOccurrenceTable
  rw [(run initial index).nextContact_prefix_terminal]
  rw [run_succ]
  rfl

/-- Exact read/write split on every ordered velocity-pair occurrence of the
same actual positive-time event. -/
theorem actualWholeContinuousVelocityPairVector_eq_next_add_trace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    actualWholeContinuousVelocityPairVector
        (run initial index).nextContact.prefixReceipt
        first second time =
      wholeRestartNextVelocityPairOccurrence initial index first second +
        wholeRestartVelocityPairOccurrenceTrace
          initial index first second time := by
  unfold wholeRestartVelocityPairOccurrenceTrace
  abel

/-- A nonzero ordered velocity-pair occurrence cannot disappear through the
actual write: it remains in the next physical current or writes the uniquely
forced same-component trace. -/
theorem actualWholeContinuousVelocityPairVector_ne_zero_next_or_trace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (currentNonzero :
      actualWholeContinuousVelocityPairVector
          (run initial index).nextContact.prefixReceipt
          first second time ≠ 0) :
    wholeRestartNextVelocityPairOccurrence initial index first second ≠ 0 ∨
      wholeRestartVelocityPairOccurrenceTrace
        initial index first second time ≠ 0 := by
  by_cases nextNonzero :
      wholeRestartNextVelocityPairOccurrence
        initial index first second ≠ 0
  · exact Or.inl nextNonzero
  · right
    intro traceZero
    apply currentNonzero
    rw [actualWholeContinuousVelocityPairVector_eq_next_add_trace,
      not_ne_iff.mp nextNonzero, traceZero, zero_add]

/-! ## Whole-carrier residual transport -/

/-- One actual receipt slice spliced into the source-owned future restart
lineage.  Every positive stage is an actual later contact. -/
def wholeRestartSplicedVelocityPairOccurrenceTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ℕ → WholeRestartVelocityPairOccurrenceTable
  | 0 => fun first second =>
      actualWholeContinuousVelocityPairVector
        (run initial index).nextContact.prefixReceipt
        first second time
  | later + 1 =>
      wholeRestartContactVelocityPairOccurrenceTable
        initial (index + later + 1)

/-- Future tail of the actual spliced ordered velocity-pair path. -/
abbrev WholeRestartSplicedVelocityPairOccurrenceTail :=
  ℕ → WholeRestartVelocityPairOccurrenceTable

/-- Forget exactly the ordered velocity-pair table written by the current
actual stage. -/
def wholeRestartSplicedVelocityPairOccurrenceTailKeep :
    WholeRestartSplicedVelocityPairOccurrenceTail →ₗ[ℂ]
      WholeRestartSplicedVelocityPairOccurrenceTail where
  toFun residual offset := residual (offset + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual future ordered velocity-pair residual beginning at one spliced
stage. -/
def wholeRestartSplicedVelocityPairOccurrenceTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (stage : ℕ) : WholeRestartSplicedVelocityPairOccurrenceTail :=
  fun offset =>
    wholeRestartSplicedVelocityPairOccurrenceTable
      initial index time (stage + offset)

/-- The chosen actual receipt slice followed by the actual whole-restart run
is an effective residual process on the complete ordered velocity-pair
carrier. -/
def generatedWholeRestartSplicedVelocityPairOccurrenceEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    EffectiveResidualProcess
      ℂ WholeRestartSplicedVelocityPairOccurrenceTail ℕ where
  target := 0
  keep := wholeRestartSplicedVelocityPairOccurrenceTailKeep
  residual :=
    wholeRestartSplicedVelocityPairOccurrenceTail initial index time
  update := Nat.succ
  residual_transport_law := by
    intro stage
    funext offset
    simp only [wholeRestartSplicedVelocityPairOccurrenceTail,
      wholeRestartSplicedVelocityPairOccurrenceTailKeep,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    omega

/-- Whole-carrier commuting square for every actual stage of the ordered
velocity-pair path. -/
theorem wholeRestartSplicedVelocityPairOccurrence_transport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (stage : ℕ) :
    wholeRestartSplicedVelocityPairOccurrenceTail
        initial index time (stage + 1) =
      wholeRestartSplicedVelocityPairOccurrenceTailKeep
        (wholeRestartSplicedVelocityPairOccurrenceTail
          initial index time stage) :=
  (generatedWholeRestartSplicedVelocityPairOccurrenceEffectiveProcess
    initial index time).residual_transport_law stage

/-- The head of the forced whole-carrier trace is exactly the same-receipt
ordered velocity-pair trace. -/
theorem
    wholeRestartSplicedVelocityPairOccurrence_trace_head_apply_eq_occurrenceTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (first second : IntegerWavevector) :
    (linearResidualTrace
        wholeRestartSplicedVelocityPairOccurrenceTailKeep
        (wholeRestartSplicedVelocityPairOccurrenceTail
          initial index time 0) 0) first second =
      wholeRestartVelocityPairOccurrenceTrace
        initial index first second time := by
  rfl

/-! ## Heat-commutator obstruction redirects into the native process -/

/-- A nonzero heat commutator on one actual receipt generates a nonzero
ordered kinetic occurrence at an actual physical time.  That same occurrence
is nonzero on the ordered velocity-pair carrier and is settled by the native
next contact or by the exact head trace of the whole-carrier process.

The source chooses the time through nonvanishing of its own integral; callers
do not supply a time, pair branch, or continuation. -/
theorem
    wholeRestartVelocityTriadHeatCommutatorTrace_ne_zero_generates_nativeVelocityPairResponsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (first second : IntegerWavevector)
    (commutatorNonzero :
      wholeRestartVelocityTriadHeatCommutatorTrace
        initial index first second ≠ 0) :
    ∃ time :
        Icc (0 : ℝ) (run initial index).nextContact.time.1,
      actualWholeVelocityBilinearEnergyOccurrence
          (run initial index).nextContact.prefixReceipt
          first second time ≠ 0 ∧
        actualWholeContinuousVelocityPairVector
          (run initial index).nextContact.prefixReceipt
          first second time ≠ 0 ∧
        (wholeRestartNextVelocityPairOccurrence
              initial index first second ≠ 0 ∨
          (linearResidualTrace
              wholeRestartSplicedVelocityPairOccurrenceTailKeep
              (wholeRestartSplicedVelocityPairOccurrenceTail
                initial index time 0) 0) first second ≠ 0) ∧
        run initial (index + 1) = (run initial index).next := by
  have energyOccurrenceExists :
      ∃ time :
          Icc (0 : ℝ) (run initial index).nextContact.time.1,
        actualWholeVelocityBilinearEnergyOccurrence
          (run initial index).nextContact.prefixReceipt
          first second time ≠ 0 := by
    by_contra everyOccurrenceZero
    push Not at everyOccurrenceZero
    apply commutatorNonzero
    unfold wholeRestartVelocityTriadHeatCommutatorTrace
      actualWholeVelocityTriadHeatCommutatorTrace
    simp [everyOccurrenceZero]
  obtain ⟨time, energyNonzero⟩ := energyOccurrenceExists
  have velocityPairNonzero :
      actualWholeContinuousVelocityPairVector
          (run initial index).nextContact.prefixReceipt
          first second time ≠ 0 := by
    intro velocityPairZero
    apply energyNonzero
    unfold actualWholeVelocityBilinearEnergyOccurrence
      finiteStateVelocityBilinearEnergyOccurrence
      actualWholeContinuousVelocityPairVector at *
    rw [velocityPairZero]
    exact complexCoordinateRealInner_zero_right _
  have nativeResponsibility :=
    actualWholeContinuousVelocityPairVector_ne_zero_next_or_trace
      initial index first second time velocityPairNonzero
  refine ⟨time, energyNonzero, velocityPairNonzero, ?_, rfl⟩
  rcases nativeResponsibility with nextNonzero | traceNonzero
  · exact Or.inl nextNonzero
  · exact Or.inr (by
      rw [
        wholeRestartSplicedVelocityPairOccurrence_trace_head_apply_eq_occurrenceTrace]
      exact traceNonzero)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
end NavierStokes
end SaturationMonoid
