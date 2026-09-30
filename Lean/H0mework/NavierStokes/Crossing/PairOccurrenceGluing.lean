import H0mework.NavierStokes.PairRestart.PairOccurrenceRateSettlement
import H0mework.NavierStokes.Crossing.WholeSourceGluingLedger

/-!
# Receipt-wide pair-occurrence gluing at an actual whole restart crossing

The existing crossing compiler generates a finite ordered list of primitive
source occurrences whose compiled states sum to the finite crossing core.
This module performs the nonlinear polarization before Fourier aggregation.
For every time of the same outgoing unforced receipt and every ordered input
pair, the actual pair occurrence is exactly

```text
primitive source self occurrence + complete outgoing gluing occurrence.
```

The complete gluing term contains both the source-component/tail gluing at
the contact and the dynamic polarization written by the actual positive-time
receipt.  It is not defined as an unnamed difference, and no path, cutoff,
target state, faithfulness law or branch choice occurs in the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing

open scoped BigOperators ENNReal

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement

noncomputable section

/-! ## Pair-level list polarization -/

/-- Ordered cross responsibility before aggregation over the first input
frequency.  Both orientations against every later source occurrence are
retained. -/
def wholeComponentCrossGluingPairOccurrence :
    List ComplexVorticityHilbertState →
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair →
        ComplexCoordinateVector
  | [], _pair => 0
  | head :: tail, pair =>
      wholeComponentCrossGluingPairOccurrence tail pair +
        (tail.map fun other =>
          finiteStateVorticityBilinearPairContribution head other pair).sum +
        (tail.map fun other =>
          finiteStateVorticityBilinearPairContribution other head pair).sum

theorem finiteStateVorticityNonlinearPairContribution_add
    (left right : ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityNonlinearPairContribution (left + right) pair =
      finiteStateVorticityNonlinearPairContribution left pair +
        finiteStateVorticityNonlinearPairContribution right pair +
      finiteStateVorticityBilinearPairContribution left right pair +
        finiteStateVorticityBilinearPairContribution right left pair := by
  simp [finiteStateVorticityNonlinearPairContribution,
    finiteStateVorticityBilinearPairContribution,
    finiteStateVelocityCoefficient_add, dotProduct_add, smul_add]
  module

@[simp] theorem finiteStateVorticityBilinearPairContribution_self
    (state : ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityBilinearPairContribution state state pair =
      finiteStateVorticityNonlinearPairContribution state pair := by
  rfl

theorem finiteStateVorticityBilinearPairContribution_listSum_left
    (components : List ComplexVorticityHilbertState)
    (right : ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityBilinearPairContribution
        components.sum right pair =
      (components.map fun component =>
        finiteStateVorticityBilinearPairContribution
          component right pair).sum := by
  induction components with
  | nil =>
      simp [finiteStateVorticityBilinearPairContribution]
  | cons head tail inductionHypothesis =>
      rw [List.sum_cons,
        finiteStateVorticityBilinearPairContribution_add_left,
        inductionHypothesis]
      rfl

theorem finiteStateVorticityBilinearPairContribution_listSum_right
    (left : ComplexVorticityHilbertState)
    (components : List ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityBilinearPairContribution
        left components.sum pair =
      (components.map fun component =>
        finiteStateVorticityBilinearPairContribution
          left component pair).sum := by
  induction components with
  | nil =>
      simp [finiteStateVorticityBilinearPairContribution]
  | cons head tail inductionHypothesis =>
      rw [List.sum_cons,
        finiteStateVorticityBilinearPairContribution_add_right,
        inductionHypothesis]
      rfl

/-- Exact quadratic expansion of a finite ordered source list, before the
input-pair table is aggregated to an output coefficient. -/
theorem finiteStateVorticityNonlinearPairContribution_listSum_self_cross
    (components : List ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityNonlinearPairContribution components.sum pair =
      (components.map fun component =>
        finiteStateVorticityNonlinearPairContribution component pair).sum +
      wholeComponentCrossGluingPairOccurrence components pair := by
  induction components with
  | nil =>
      simp [finiteStateVorticityNonlinearPairContribution,
        wholeComponentCrossGluingPairOccurrence]
  | cons head tail inductionHypothesis =>
      rw [List.sum_cons,
        finiteStateVorticityNonlinearPairContribution_add,
        inductionHypothesis,
        finiteStateVorticityBilinearPairContribution_listSum_right,
        finiteStateVorticityBilinearPairContribution_listSum_left]
      simp only [List.map_cons, List.sum_cons,
        wholeComponentCrossGluingPairOccurrence]
      abel

/-! ## Actual crossing source and outgoing gluing occurrences -/

/-- Sum of the nonlinear self occurrences of every source-generated finite
component at one ordered input pair. -/
def wholeRestartCrossingFiniteComponentSelfPairOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  ((wholeRestartCrossingFiniteComponents initial index crossed).map
    fun component =>
      finiteStateVorticityNonlinearPairContribution component
        (first, output - first)).sum

/-- The source-generated component count is retained before pair
aggregation: every primitive self occurrence is exactly the reciprocal-count
copy of the corresponding finite-core pair occurrence. -/
theorem wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq_core_smul
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector) :
    wholeRestartCrossingFiniteComponentSelfPairOccurrence
        initial index crossed output first =
      ((canonicalHalfCriticalComponentCount ν
          (wholeRestartCrossingFiniteCoreState initial index crossed) : ℝ)⁻¹ : ℂ) •
        finiteStateVorticityNonlinearPairContribution
          (wholeRestartCrossingFiniteCoreState initial index crossed)
          (first, output - first) := by
  let count := canonicalHalfCriticalComponentCount ν
    (wholeRestartCrossingFiniteCoreState initial index crossed)
  have countNe : count ≠ 0 :=
    canonicalHalfCriticalComponentCount_ne_zero _ _
  unfold wholeRestartCrossingFiniteComponentSelfPairOccurrence
  rw [show wholeRestartCrossingFiniteComponents initial index crossed =
      List.replicate count
        (((count : ℝ)⁻¹) •
          wholeRestartCrossingFiniteCoreState initial index crossed) by
    rfl]
  simp only [List.map_replicate, List.sum_replicate]
  rw [finiteStateVorticityNonlinearPairContribution_real_smul]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  simp only [smul_smul]
  push_cast
  field_simp
  simp [count]

/-- Ordered cross occurrence internal to the generated finite component
list. -/
def wholeRestartCrossingFiniteComponentCrossPairOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  wholeComponentCrossGluingPairOccurrence
    (wholeRestartCrossingFiniteComponents initial index crossed)
    (first, output - first)

/-- Contact-time gluing occurrence between the generated finite core and the
retained whole tail.  The first term includes the tail self occurrence and
the tail/core orientation; the second term records the core/tail orientation.
-/
def wholeRestartCrossingFiniteTailPairGluingOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector) : ComplexCoordinateVector :=
  finiteStateVorticityBilinearPairContribution
      (wholeRestartCrossingFiniteTail initial index crossed)
      (run initial index).contact.physicalState
      (first, output - first) +
    finiteStateVorticityBilinearPairContribution
      (wholeRestartCrossingFiniteCoreState initial index crossed)
      (wholeRestartCrossingFiniteTail initial index crossed)
      (first, output - first)

/-- Dynamic polarization created by the actual positive-time whole receipt
relative to its own contact state. -/
def wholeRestartCrossingDynamicPairGluingOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ComplexCoordinateVector :=
  let current := (run initial index).contact.physicalState
  let actual := (run initial index).nextContact.prefixReceipt.wholePath time
  finiteStateVorticityBilinearPairContribution
      (actual - current) actual (first, output - first) +
    finiteStateVorticityBilinearPairContribution
      current (actual - current) (first, output - first)

/-- The retained finite-tail role is exactly the nonlinear pair residual
created by the source-owned sharp-core split.  This identification is made
before output or input-pair aggregation. -/
theorem
    wholeRestartCrossingFiniteTailPairGluingOccurrence_eq_nonlinearPair_sub
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector) :
    wholeRestartCrossingFiniteTailPairGluingOccurrence
        initial index crossed output first =
      finiteStateVorticityNonlinearPairContribution
          (run initial index).contact.physicalState
          (first, output - first) -
        finiteStateVorticityNonlinearPairContribution
          (wholeRestartCrossingFiniteCoreState initial index crossed)
          (first, output - first) := by
  simpa [wholeRestartCrossingFiniteTailPairGluingOccurrence,
    wholeRestartCrossingFiniteTail] using
    (finiteStateVorticityNonlinearPairContribution_sub
      (run initial index).contact.physicalState
      (wholeRestartCrossingFiniteCoreState initial index crossed)
      (first, output - first)).symm

/-- Dynamic gluing is the exact nonlinear pair increment of the same actual
unforced receipt.  The source contact is its baseline; the later path state
and the write-bearing receipt generate the difference. -/
theorem
    wholeRestartCrossingDynamicPairGluingOccurrence_eq_nonlinearPair_sub
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    wholeRestartCrossingDynamicPairGluingOccurrence
        initial index output first time =
      actualWholeContinuousPairVector
          (run initial index).nextContact.prefixReceipt
          output first time -
        wholeRestartContactPairOccurrenceTable
          initial index output first := by
  simpa [wholeRestartCrossingDynamicPairGluingOccurrence,
    actualWholeContinuousPairVector,
    wholeRestartContactPairOccurrenceTable] using
    (finiteStateVorticityNonlinearPairContribution_sub
      ((run initial index).nextContact.prefixReceipt.wholePath time)
      ((run initial index).contact.physicalState)
      (first, output - first)).symm

/-- The same dynamic role is therefore the difference of two read/write
traces on the actual receipt.  No component can be lost in the contact
baseline quotient. -/
theorem wholeRestartCrossingDynamicPairGluingOccurrence_eq_traceInnovation
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    wholeRestartCrossingDynamicPairGluingOccurrence
        initial index output first time =
      wholeRestartPairOccurrenceTrace initial index output first time -
        wholeRestartPairOccurrenceTrace initial index output first
          ⟨0, ⟨le_rfl,
            (run initial index).nextContact.time_pos.le⟩⟩ := by
  rw [wholeRestartCrossingDynamicPairGluingOccurrence_eq_nonlinearPair_sub]
  rw [actualWholeContinuousPairVector_eq_contact_add_traceInnovation]
  abel

/-- Complete pre-quotient gluing occurrence on one outgoing actual receipt.
It retains finite-component cross terms, finite-tail terms and the dynamic
positive-time polarization as separate generated summands. -/
def wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    ComplexCoordinateVector :=
  wholeRestartCrossingFiniteComponentCrossPairOccurrence
      initial index crossed output first +
    wholeRestartCrossingFiniteTailPairGluingOccurrence
      initial index crossed output first +
    wholeRestartCrossingDynamicPairGluingOccurrence
      initial index output first time

private theorem contactPair_eq_sourceSelf_add_gluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector) :
    finiteStateVorticityNonlinearPairContribution
        (run initial index).contact.physicalState
        (first, output - first) =
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
          initial index crossed output first +
        wholeRestartCrossingFiniteComponentCrossPairOccurrence
          initial index crossed output first +
        wholeRestartCrossingFiniteTailPairGluingOccurrence
          initial index crossed output first := by
  let components :=
    wholeRestartCrossingFiniteComponents initial index crossed
  let core := wholeRestartCrossingFiniteCoreState initial index crossed
  let tail := wholeRestartCrossingFiniteTail initial index crossed
  let current := (run initial index).contact.physicalState
  let pair := (first, output - first)
  have currentEq :
      (run initial index).contact.physicalState = core + tail := by
    simpa [current, core, tail] using
      wholeRestartCrossingPhysicalState_eq_core_add_tail
        initial index crossed
  have coreEq : components.sum = core := by
    simpa [components, core,
      wholeRestartCrossingFiniteComponents] using
      canonicalHalfCriticalComponents_sum ν
        (wholeRestartCrossingFiniteCoreState initial index crossed)
  have componentLedger :=
    finiteStateVorticityNonlinearPairContribution_listSum_self_cross
      components pair
  rw [coreEq] at componentLedger
  rw [currentEq,
    finiteStateVorticityNonlinearPairContribution_add]
  rw [componentLedger]
  unfold wholeRestartCrossingFiniteComponentSelfPairOccurrence
    wholeRestartCrossingFiniteComponentCrossPairOccurrence
    wholeRestartCrossingFiniteTailPairGluingOccurrence
  simp only [components, core, tail, pair]
  rw [currentEq,
    finiteStateVorticityBilinearPairContribution_add_right]
  rw [finiteStateVorticityBilinearPairContribution_self]
  abel

/-- Receipt-wide consume-before-quotient identity.  Every actual pair
occurrence on the outgoing unforced receipt is exactly the source-generated
primitive self occurrence plus its complete gluing responsibility. -/
theorem actualWholeContinuousPairVector_eq_crossingSourceSelf_add_completeGluing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output first : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    actualWholeContinuousPairVector
        (run initial index).nextContact.prefixReceipt
        output first time =
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
          initial index crossed output first +
        wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
          initial index crossed output first time := by
  unfold actualWholeContinuousPairVector
    wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
    wholeRestartCrossingDynamicPairGluingOccurrence
  have dynamicLedger :=
    finiteStateVorticityNonlinearPairContribution_sub
      ((run initial index).nextContact.prefixReceipt.wholePath time)
      ((run initial index).contact.physicalState)
      (first, output - first)
  have contactLedger :=
    contactPair_eq_sourceSelf_add_gluing
      initial index crossed output first
  rw [contactLedger] at dynamicLedger
  have actualEq := (sub_eq_iff_eq_add).mp dynamicLedger
  rw [actualEq]
  module

/-! ## Aggregation after the pair responsibility has been formed -/

private theorem summable_listNonlinearSelfPairOccurrence
    (components : List ComplexVorticityHilbertState)
    (allTransverse :
      ∀ component ∈ components, WholeStateTransverse component)
    (output : IntegerWavevector) :
    Summable fun first : IntegerWavevector =>
      (components.map fun component =>
        finiteStateVorticityNonlinearPairContribution component
          (first, output - first)).sum := by
  revert allTransverse
  induction components with
  | nil =>
      intro _allTransverse
      simp
  | cons head tail inductionHypothesis =>
      intro allTransverse
      have headTransverse : WholeStateTransverse head :=
        allTransverse head (by simp)
      have tailTransverse :
          ∀ component ∈ tail, WholeStateTransverse component := by
        intro component componentMem
        exact allTransverse component (by simp [componentMem])
      simp only [List.map_cons, List.sum_cons]
      exact
        (summable_wholeStateVorticityNonlinearPair
          head headTransverse output).add
        (inductionHypothesis tailTransverse)

private theorem tsum_listNonlinearSelfPairOccurrence_eq
    (components : List ComplexVorticityHilbertState)
    (allTransverse :
      ∀ component ∈ components, WholeStateTransverse component)
    (output : IntegerWavevector) :
    (∑' first : IntegerWavevector,
      (components.map fun component =>
        finiteStateVorticityNonlinearPairContribution component
          (first, output - first)).sum) =
      (components.map fun component =>
        wholeStateVorticityNonlinearCoefficientAt component output).sum := by
  revert allTransverse
  induction components with
  | nil =>
      intro _allTransverse
      simp
  | cons head tail inductionHypothesis =>
      intro allTransverse
      have headTransverse : WholeStateTransverse head :=
        allTransverse head (by simp)
      have tailTransverse :
          ∀ component ∈ tail, WholeStateTransverse component := by
        intro component componentMem
        exact allTransverse component (by simp [componentMem])
      have headSummable :=
        summable_wholeStateVorticityNonlinearPair
          head headTransverse output
      have tailSummable :=
        summable_listNonlinearSelfPairOccurrence
          tail tailTransverse output
      simp only [List.map_cons, List.sum_cons]
      rw [Summable.tsum_add headSummable tailSummable,
        inductionHypothesis tailTransverse]
      rfl

theorem summable_finiteComponentSelfPairOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    Summable fun first : IntegerWavevector =>
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        initial index crossed output first := by
  let components :=
    wholeRestartCrossingFiniteComponents initial index crossed
  have coreTransverse :
      WholeStateTransverse
        (wholeRestartCrossingFiniteCoreState initial index crossed) :=
    wholeStateTransverse_sharpSupportProjection
      (wholeRestartCrossingFiniteCoreModes initial index crossed)
      (run initial index).contact.physicalState
      (run initial index).contact.transverse
  have allTransverse :
      ∀ component ∈ components, WholeStateTransverse component := by
    intro component componentMem
    exact canonicalHalfCriticalComponents_forall_transverse
      ν (wholeRestartCrossingFiniteCoreState initial index crossed)
      component coreTransverse
      (by simpa [components,
        wholeRestartCrossingFiniteComponents] using componentMem)
  unfold wholeRestartCrossingFiniteComponentSelfPairOccurrence
  change Summable fun first : IntegerWavevector =>
    (components.map fun component =>
      finiteStateVorticityNonlinearPairContribution component
        (first, output - first)).sum
  exact summable_listNonlinearSelfPairOccurrence
    components allTransverse output

/-- Aggregating the primitive source-self occurrence table gives exactly the
existing source-self output row. -/
theorem tsum_wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector) :
    (∑' first : IntegerWavevector,
      wholeRestartCrossingFiniteComponentSelfPairOccurrence
        initial index crossed output first) =
      wholeRestartCrossingFiniteComponentSelfRow
        initial index crossed output := by
  let components :=
    wholeRestartCrossingFiniteComponents initial index crossed
  have coreTransverse :
      WholeStateTransverse
        (wholeRestartCrossingFiniteCoreState initial index crossed) :=
    wholeStateTransverse_sharpSupportProjection
      (wholeRestartCrossingFiniteCoreModes initial index crossed)
      (run initial index).contact.physicalState
      (run initial index).contact.transverse
  have allTransverse :
      ∀ component ∈ components, WholeStateTransverse component := by
    intro component componentMem
    exact canonicalHalfCriticalComponents_forall_transverse
      ν (wholeRestartCrossingFiniteCoreState initial index crossed)
      component coreTransverse
      (by simpa [components,
        wholeRestartCrossingFiniteComponents] using componentMem)
  rw [wholeRestartCrossingFiniteComponentSelfRow_eq_componentStates]
  unfold wholeRestartCrossingFiniteComponentSelfPairOccurrence
  change
    (∑' first : IntegerWavevector,
      (components.map fun component =>
        finiteStateVorticityNonlinearPairContribution component
          (first, output - first)).sum) =
      (components.map fun component =>
        wholeStateVorticityNonlinearCoefficientAt component output).sum
  exact tsum_listNonlinearSelfPairOccurrence_eq
    components allTransverse output

theorem summable_wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    Summable fun first : IntegerWavevector =>
      wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
        initial index crossed output first time := by
  have actualSummable :=
    summable_actualWholeContinuousPairVector
      (run initial index).nextContact.prefixReceipt output time
  have sourceSummable :=
    summable_finiteComponentSelfPairOccurrence
      initial index crossed output
  exact (actualSummable.sub sourceSummable).congr fun first => by
    have split :=
      actualWholeContinuousPairVector_eq_crossingSourceSelf_add_completeGluing
        initial index crossed output first time
    rw [split]
    abel

/-- After the pre-quotient gluing table has been formed, its visible readout
is exactly the actual nonlinear output minus the primitive source-self row.
This theorem does not identify a zero aggregate with zero componentwise
responsibility. -/
theorem tsum_wholeRestartCrossingCompleteOutgoingPairGluingOccurrence_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (output : IntegerWavevector)
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1) :
    (∑' first : IntegerWavevector,
      wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
        initial index crossed output first time) =
      wholeStateVorticityNonlinearCoefficientAt
          ((run initial index).nextContact.prefixReceipt.wholePath time)
          output -
        wholeRestartCrossingFiniteComponentSelfRow
          initial index crossed output := by
  have actualSummable :=
    summable_actualWholeContinuousPairVector
      (run initial index).nextContact.prefixReceipt output time
  have sourceSummable :=
    summable_finiteComponentSelfPairOccurrence
      initial index crossed output
  have pointwise :
      (fun first : IntegerWavevector =>
        wholeRestartCrossingCompleteOutgoingPairGluingOccurrence
          initial index crossed output first time) =
      fun first =>
        actualWholeContinuousPairVector
            (run initial index).nextContact.prefixReceipt
            output first time -
          wholeRestartCrossingFiniteComponentSelfPairOccurrence
            initial index crossed output first := by
    funext first
    have split :=
      actualWholeContinuousPairVector_eq_crossingSourceSelf_add_completeGluing
        initial index crossed output first time
    rw [split]
    abel
  rw [pointwise, Summable.tsum_sub actualSummable sourceSummable,
    tsum_actualWholeContinuousPairVector_eq_nonlinearOutput,
    tsum_wholeRestartCrossingFiniteComponentSelfPairOccurrence_eq]

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingPairOccurrenceGluing
end NavierStokes
end SaturationMonoid
