import H0mework.Realization.Process.NativeResponseDisposition
import H0mework.NavierStokes.Restart.HeatCommutatorNativeVelocityPairRedirect

/-!
# Anchored reflected-pair native process on the actual whole-restart run

The three-slot kinetic involution is not confined to a diagonal state.  This
module fixes its testing anchor to the actual contact at the beginning of one
source-generated restart segment and lets the advecting/testing state follow
the later actual unforced receipt.  The reflected occurrence therefore keeps
the cross-contact angular responsibility before any scalar pair quotient.

The anchor, current receipt, terminal endpoint, next contact, and response edge
are all computed from two natural-number indices in the authoritative
`GeneratedWholeRestartCurrent.run`.  The response has no caller-supplied path,
branch, target state, nonzero witness, sign law, or continuation certificate.

On each generated edge:

* the three-slot reflected relation holds almost everywhere;
* causal heat transport leaves exactly its multiplier commutator;
* the reflected ordered pair is transported by the literal native successor;
* every nonzero direct work is exhausted by that commutator or by a nonzero
  next/trace responsibility on the complete ordered-pair carrier.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess

open scoped BigOperators Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open SourceGeneratedNativeResponseDisposition
open AffineRelaxation
open ResidualProjection

noncomputable section

/-! ## Source-owned anchored frame and response -/

/-- A source-owned occurrence frame.  `start` chooses an actual contact of
the generated run; `offset` chooses the later actual edge while preserving
that contact as the reflected-pair anchor. -/
structure WholeRestartAnchoredReflectedPairFrame where
  start : ℕ
  offset : ℕ
deriving DecidableEq

namespace WholeRestartAnchoredReflectedPairFrame

/-- Actual run index read by an anchored frame. -/
def currentIndex (frame : WholeRestartAnchoredReflectedPairFrame) : ℕ :=
  frame.start + frame.offset

/-- Literal native successor of an anchored frame. -/
def next (frame : WholeRestartAnchoredReflectedPairFrame) :
    WholeRestartAnchoredReflectedPairFrame where
  start := frame.start
  offset := frame.offset + 1

@[simp] theorem next_start
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    frame.next.start = frame.start :=
  rfl

@[simp] theorem next_offset
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    frame.next.offset = frame.offset + 1 :=
  rfl

@[simp] theorem currentIndex_next
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    frame.next.currentIndex = frame.currentIndex + 1 := by
  simp [currentIndex, next]
  omega

end WholeRestartAnchoredReflectedPairFrame

open WholeRestartAnchoredReflectedPairFrame

/-- The actual dependent edge advancing one anchored reflected-pair frame.
Its only constructor is the already generated `run_succ` event. -/
inductive GeneratedWholeRestartAnchoredReflectedPairNativeStep
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    WholeRestartAnchoredReflectedPairFrame →
      WholeRestartAnchoredReflectedPairFrame → Type
  | actualWrite (frame : WholeRestartAnchoredReflectedPairFrame) :
      GeneratedWholeRestartAnchoredReflectedPairNativeStep
        initial frame frame.next

/-- Total source-owned response on every anchored frame. -/
def generatedWholeRestartAnchoredReflectedPairNativeResponse
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    Response
      (GeneratedWholeRestartAnchoredReflectedPairNativeStep initial)
      frame :=
  ⟨frame.next,
    GeneratedWholeRestartAnchoredReflectedPairNativeStep.actualWrite frame⟩

@[simp] theorem
    generatedWholeRestartAnchoredReflectedPairNativeResponse_next
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    (generatedWholeRestartAnchoredReflectedPairNativeResponse
      initial frame).1 =
      frame.next :=
  rfl

/-- Physical observation of the generated anchored response is exactly the
existing actual whole unforced restart successor. -/
theorem generatedWholeRestartAnchoredReflectedPairNativeResponse_physical
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    run initial
        (generatedWholeRestartAnchoredReflectedPairNativeResponse
          initial frame).1.currentIndex =
      (run initial frame.currentIndex).next := by
  rw [generatedWholeRestartAnchoredReflectedPairNativeResponse_next,
    currentIndex_next, run_succ]

/-! ## Actual anchored reflected-pair carrier -/

/-- The actual state retained as the testing anchor of a frame. -/
def wholeRestartAnchoredReflectedPairAnchor
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    ComplexVorticityHilbertState :=
  (run initial frame.start).contact.physicalState

/-- Complete reflected ordered-pair table at the current actual contact.
The advecting slot is current and the transported slot is the source-owned
anchor. -/
def wholeRestartAnchoredReflectedContactVelocityPairOccurrenceTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    WholeRestartVelocityPairOccurrenceTable :=
  fun first second =>
    finiteStateVelocityBilinearPairContribution
      (run initial frame.currentIndex).contact.physicalState
      (wholeRestartAnchoredReflectedPairAnchor initial frame)
      (first, second)

/-- Reflected ordered-pair vector along the actual unforced receipt selected
by the current frame. -/
def actualWholeRestartAnchoredReflectedVelocityPairVector
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector)
    (time :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1) :
    ComplexCoordinateVector :=
  finiteStateVelocityBilinearPairContribution
    ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
      time)
    (wholeRestartAnchoredReflectedPairAnchor initial frame)
    (first, second)

/-- The same anchored ordered pair after the exact native response. -/
def wholeRestartAnchoredReflectedNextVelocityPairOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    ComplexCoordinateVector :=
  wholeRestartAnchoredReflectedContactVelocityPairOccurrenceTable
    initial frame.next first second

/-- Unique pointwise trace from an actual receipt slice to the ordered pair
written in the next physical current. -/
def wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector)
    (time :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1) :
    ComplexCoordinateVector :=
  actualWholeRestartAnchoredReflectedVelocityPairVector
      initial frame first second time -
    wholeRestartAnchoredReflectedNextVelocityPairOccurrence
      initial frame first second

/-- Terminal read of the actual receipt is literally the anchored ordered
pair in the next native current. -/
theorem
    actualWholeRestartAnchoredReflectedVelocityPairVector_terminal_eq_next
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    actualWholeRestartAnchoredReflectedVelocityPairVector
        initial frame first second
        ⟨(run initial frame.currentIndex).nextContact.time.1,
          ⟨(run initial frame.currentIndex).nextContact.time_pos.le,
            le_rfl⟩⟩ =
      wholeRestartAnchoredReflectedNextVelocityPairOccurrence
        initial frame first second := by
  unfold actualWholeRestartAnchoredReflectedVelocityPairVector
    wholeRestartAnchoredReflectedNextVelocityPairOccurrence
    wholeRestartAnchoredReflectedContactVelocityPairOccurrenceTable
  rw [(run initial frame.currentIndex).nextContact_prefix_terminal]
  rw [currentIndex_next, run_succ]
  rfl

/-- Exact residual split on every actual anchored ordered-pair occurrence. -/
theorem
    actualWholeRestartAnchoredReflectedVelocityPairVector_eq_next_add_trace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector)
    (time :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1) :
    actualWholeRestartAnchoredReflectedVelocityPairVector
        initial frame first second time =
      wholeRestartAnchoredReflectedNextVelocityPairOccurrence
          initial frame first second +
        wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
          initial frame first second time := by
  unfold wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
  abel

/-- A nonzero actual anchored occurrence is retained in the next physical
current or in its uniquely forced same-component trace. -/
theorem
    actualWholeRestartAnchoredReflectedVelocityPairVector_ne_zero_next_or_trace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector)
    (time :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1)
    (currentNonzero :
      actualWholeRestartAnchoredReflectedVelocityPairVector
          initial frame first second time ≠ 0) :
    wholeRestartAnchoredReflectedNextVelocityPairOccurrence
          initial frame first second ≠ 0 ∨
      wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
        initial frame first second time ≠ 0 := by
  by_cases nextNonzero :
      wholeRestartAnchoredReflectedNextVelocityPairOccurrence
        initial frame first second ≠ 0
  · exact Or.inl nextNonzero
  · right
    intro traceZero
    apply currentNonzero
    rw [
      actualWholeRestartAnchoredReflectedVelocityPairVector_eq_next_add_trace,
      not_ne_iff.mp nextNonzero, traceZero, zero_add]

/-! ## Whole-carrier commuting transport -/

/-- Future anchored ordered-pair residual beginning at an actual frame. -/
abbrev WholeRestartAnchoredReflectedVelocityPairOccurrenceTail :=
  ℕ → WholeRestartVelocityPairOccurrenceTable

/-- Forget exactly the anchored ordered-pair table written by the current
actual stage. -/
def wholeRestartAnchoredReflectedVelocityPairOccurrenceTailKeep :
    WholeRestartAnchoredReflectedVelocityPairOccurrenceTail →ₗ[ℂ]
      WholeRestartAnchoredReflectedVelocityPairOccurrenceTail where
  toFun residual offset := residual (offset + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual future anchored ordered-pair tail of one frame. -/
def wholeRestartAnchoredReflectedVelocityPairOccurrenceTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    WholeRestartAnchoredReflectedVelocityPairOccurrenceTail :=
  fun later =>
    wholeRestartAnchoredReflectedContactVelocityPairOccurrenceTable
      initial
      { start := frame.start
        offset := frame.offset + later }

/-- The source-owned anchored response is an effective residual process on
the complete ordered-pair tail. -/
def generatedWholeRestartAnchoredReflectedPairEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    EffectiveResidualProcess
      ℂ
      WholeRestartAnchoredReflectedVelocityPairOccurrenceTail
      WholeRestartAnchoredReflectedPairFrame where
  target := 0
  keep := wholeRestartAnchoredReflectedVelocityPairOccurrenceTailKeep
  residual :=
    wholeRestartAnchoredReflectedVelocityPairOccurrenceTail initial
  update := fun frame =>
    (generatedWholeRestartAnchoredReflectedPairNativeResponse
      initial frame).1
  residual_transport_law := by
    intro frame
    funext later
    simp only [
      generatedWholeRestartAnchoredReflectedPairNativeResponse_next,
      WholeRestartAnchoredReflectedPairFrame.next,
      wholeRestartAnchoredReflectedVelocityPairOccurrenceTail,
      wholeRestartAnchoredReflectedVelocityPairOccurrenceTailKeep,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr 2
    omega

/-- Whole-carrier commuting square for every generated anchored response. -/
theorem generatedWholeRestartAnchoredReflectedPairEffectiveProcess_transport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    wholeRestartAnchoredReflectedVelocityPairOccurrenceTail
        initial frame.next =
      wholeRestartAnchoredReflectedVelocityPairOccurrenceTailKeep
        (wholeRestartAnchoredReflectedVelocityPairOccurrenceTail
          initial frame) :=
  (generatedWholeRestartAnchoredReflectedPairEffectiveProcess
    initial).residual_transport_law frame

/-- Head trace of the whole anchored carrier is the exact difference between
adjacent actual contact tables. -/
theorem
    generatedWholeRestartAnchoredReflectedPairEffectiveProcess_trace_head
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    linearResidualTrace
        wholeRestartAnchoredReflectedVelocityPairOccurrenceTailKeep
        (wholeRestartAnchoredReflectedVelocityPairOccurrenceTail
          initial frame) 0 =
      wholeRestartAnchoredReflectedContactVelocityPairOccurrenceTable
          initial frame -
        wholeRestartAnchoredReflectedContactVelocityPairOccurrenceTable
          initial frame.next := by
  rfl

/-! ## Mixed reflected relation and causal heat transport -/

/-- Direct angular occurrence: the source anchor tests the self-convection
of the actual later receipt state. -/
def wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector)
    (time :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1) : ℝ :=
  finiteStateVelocityBilinearEnergyOccurrence
    (wholeRestartAnchoredReflectedPairAnchor initial frame)
    ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
      time)
    ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
      time)
    first second

/-- Reflected angular occurrence: the actual later receipt tests the
convection of the source anchor by that same later state. -/
def wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector)
    (time :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1) : ℝ :=
  finiteStateVelocityBilinearEnergyOccurrence
    ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
      time)
    ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
      time)
    (wholeRestartAnchoredReflectedPairAnchor initial frame)
    first (outputNegSecondEquiv first second)

/-- Same-event three-slot skew for the actual source anchor and later
unforced receipt. -/
theorem
    actualWholeRestartAnchoredVelocityBilinearEnergyOccurrence_reflect_swap_ae
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure
        (run initial frame.currentIndex).nextContact.time.1),
      wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
          initial frame first second time =
        -wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
          initial frame first second time := by
  have anchorReality :
      FiniteStateFourierReality
        (wholeRestartAnchoredReflectedPairAnchor initial frame) :=
    (run initial frame.start).contact.reality
  filter_upwards [
    wholePath_fourierReality_ae
      (run initial frame.currentIndex).nextContact.prefixReceipt
    ] with time pathReality
  exact
    finiteStateVelocityBilinearEnergyOccurrence_reflect_swap
      (wholeRestartAnchoredReflectedPairAnchor initial frame)
      ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
        time)
      ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
        time)
      anchorReality pathReality first second

theorem
    actualWholeRestartAnchoredReflectedVelocityPairVector_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    Continuous fun time :
        Icc (0 : ℝ)
          (run initial frame.currentIndex).nextContact.time.1 =>
      actualWholeRestartAnchoredReflectedVelocityPairVector
        initial frame first second time := by
  have velocityFirstContinuous :
      Continuous fun time :
          Icc (0 : ℝ)
            (run initial frame.currentIndex).nextContact.time.1 =>
        finiteStateVelocityCoefficient
          ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
            time)
          first :=
    (finiteStateVelocityCoefficient_contDiff first).continuous.comp
      (run initial frame.currentIndex).nextContact.prefixReceipt.wholePath.continuous
  have derivativeContinuous :
      Continuous fun time :
          Icc (0 : ℝ)
            (run initial frame.currentIndex).nextContact.time.1 =>
        complexWavevector second ⬝ᵥ
          finiteStateVelocityCoefficient
            ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
              time)
            first :=
    continuous_const.dotProduct velocityFirstContinuous
  unfold actualWholeRestartAnchoredReflectedVelocityPairVector
    finiteStateVelocityBilinearPairContribution
  exact
    (continuous_const.mul derivativeContinuous).neg.smul continuous_const

theorem
    wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    Continuous
      (wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
        initial frame first second) := by
  have pairContinuous :=
    actualWholeContinuousVelocityPairVector_continuous
      (run initial frame.currentIndex).nextContact.prefixReceipt
      first second
  unfold wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
    finiteStateVelocityBilinearEnergyOccurrence at *
  exact
    complexCoordinateRealInner_prod_continuous.comp
      (continuous_const.prodMk pairContinuous)

theorem
    wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    Continuous
      (wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
        initial frame first second) := by
  have testContinuous :
      Continuous fun time :
          Icc (0 : ℝ)
            (run initial frame.currentIndex).nextContact.time.1 =>
        finiteStateVelocityCoefficient
          ((run initial frame.currentIndex).nextContact.prefixReceipt.wholePath
            time)
          (first + outputNegSecondEquiv first second) :=
    (finiteStateVelocityCoefficient_contDiff
      (first + outputNegSecondEquiv first second)).continuous.comp
        (run initial frame.currentIndex).nextContact.prefixReceipt.wholePath.continuous
  have pairContinuous :=
    actualWholeRestartAnchoredReflectedVelocityPairVector_continuous
      initial frame first (outputNegSecondEquiv first second)
  unfold wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
    finiteStateVelocityBilinearEnergyOccurrence at *
  exact
    complexCoordinateRealInner_prod_continuous.comp
      (testContinuous.prodMk pairContinuous)

/-- Source-generated terminal time of the current actual receipt. -/
def wholeRestartAnchoredReflectedPairTerminalTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    Icc (0 : ℝ)
      (run initial frame.currentIndex).nextContact.time.1 :=
  ⟨(run initial frame.currentIndex).nextContact.time.1,
    ⟨(run initial frame.currentIndex).nextContact.time_pos.le, le_rfl⟩⟩

/-- Causal heat-weighted direct anchored work on the source-owned receipt. -/
def wholeRestartAnchoredDirectVelocityBilinearEnergyWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) : ℝ :=
  ∫ earlier in Iic
      (wholeRestartAnchoredReflectedPairTerminalTime initial frame),
    finiteStateVorticityHeatMultiplier
        ν.coeff
        ((wholeRestartAnchoredReflectedPairTerminalTime initial frame).1 -
          earlier.1)
        (first + second) *
      wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
        initial frame first second earlier
    ∂(commonTimeMeasure
      (run initial frame.currentIndex).nextContact.time.1)

/-- Causal heat-weighted reflected anchored work on the same receipt. -/
def wholeRestartAnchoredReflectedVelocityBilinearEnergyWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) : ℝ :=
  ∫ earlier in Iic
      (wholeRestartAnchoredReflectedPairTerminalTime initial frame),
    finiteStateVorticityHeatMultiplier
        ν.coeff
        ((wholeRestartAnchoredReflectedPairTerminalTime initial frame).1 -
          earlier.1)
        (first + outputNegSecondEquiv first second) *
      wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
        initial frame first second earlier
    ∂(commonTimeMeasure
      (run initial frame.currentIndex).nextContact.time.1)

/-- Exact causal heat commutator forced by transporting the mixed reflected
relation through two output-dependent multipliers. -/
def wholeRestartAnchoredVelocityTriadHeatCommutatorTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) : ℝ :=
  ∫ earlier in Iic
      (wholeRestartAnchoredReflectedPairTerminalTime initial frame),
    (finiteStateVorticityHeatMultiplier
          ν.coeff
          ((wholeRestartAnchoredReflectedPairTerminalTime initial frame).1 -
            earlier.1)
          (first + second) -
        finiteStateVorticityHeatMultiplier
          ν.coeff
          ((wholeRestartAnchoredReflectedPairTerminalTime initial frame).1 -
            earlier.1)
          (first + outputNegSecondEquiv first second)) *
      wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
        initial frame first second earlier
    ∂(commonTimeMeasure
      (run initial frame.currentIndex).nextContact.time.1)

/-- The mixed reflected source relation commutes with actual causal heat up
to exactly the generated multiplier commutator. -/
theorem
    wholeRestartAnchoredVelocityBilinearEnergyWork_add_reflect_eq_heatCommutator
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    wholeRestartAnchoredDirectVelocityBilinearEnergyWork
        initial frame first second +
      wholeRestartAnchoredReflectedVelocityBilinearEnergyWork
        initial frame first second =
      wholeRestartAnchoredVelocityTriadHeatCommutatorTrace
        initial frame first second := by
  let endpoint :=
    wholeRestartAnchoredReflectedPairTerminalTime initial frame
  let μ :=
    (commonTimeMeasure
      (run initial frame.currentIndex).nextContact.time.1).restrict
        (Iic endpoint)
  let direct := fun earlier :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1 =>
    finiteStateVorticityHeatMultiplier
        ν.coeff (endpoint.1 - earlier.1) (first + second) *
      wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
        initial frame first second earlier
  let reflected := fun earlier :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1 =>
    finiteStateVorticityHeatMultiplier
        ν.coeff (endpoint.1 - earlier.1)
          (first + outputNegSecondEquiv first second) *
      wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
        initial frame first second earlier
  have directContinuous : Continuous direct := by
    have heatContinuous :
        Continuous fun earlier :
            Icc (0 : ℝ)
              (run initial frame.currentIndex).nextContact.time.1 =>
          finiteStateVorticityHeatMultiplier
            ν.coeff (endpoint.1 - earlier.1) (first + second) := by
      unfold finiteStateVorticityHeatMultiplier
      fun_prop
    exact heatContinuous.mul
      (wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence_continuous
        initial frame first second)
  have reflectedContinuous : Continuous reflected := by
    have heatContinuous :
        Continuous fun earlier :
            Icc (0 : ℝ)
              (run initial frame.currentIndex).nextContact.time.1 =>
          finiteStateVorticityHeatMultiplier
            ν.coeff (endpoint.1 - earlier.1)
              (first + outputNegSecondEquiv first second) := by
      unfold finiteStateVorticityHeatMultiplier
      fun_prop
    exact heatContinuous.mul
      (wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence_continuous
        initial frame first second)
  have directIntegrable : Integrable direct μ :=
    (directContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  have reflectedIntegrable : Integrable reflected μ :=
    (reflectedContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  unfold wholeRestartAnchoredDirectVelocityBilinearEnergyWork
    wholeRestartAnchoredReflectedVelocityBilinearEnergyWork
    wholeRestartAnchoredVelocityTriadHeatCommutatorTrace
  change (∫ earlier, direct earlier ∂μ) +
      (∫ earlier, reflected earlier ∂μ) = _
  rw [← integral_add directIntegrable reflectedIntegrable]
  apply integral_congr_ae
  have reflectedAE :=
    (actualWholeRestartAnchoredVelocityBilinearEnergyOccurrence_reflect_swap_ae
      initial frame first second).filter_mono
        (ae_restrict_le
          (s := Iic
            (wholeRestartAnchoredReflectedPairTerminalTime initial frame)))
  filter_upwards [reflectedAE] with earlier reflectedEq
  unfold direct reflected endpoint
  rw [reflectedEq]
  ring

/-! ## Collective-ready no-silent exhaustion -/

/-- Every direct anchored causal work is exhausted without an angular sign
premise.  It is faithfully zero, leaves the exact heat commutator, or its
same-event reflected occurrence remains in the next actual ordered-pair
current or in the uniquely forced pointwise trace.

The witness time is generated by nonvanishing of the actual reflected
integral.  The physical successor equality is the response edge itself. -/
theorem wholeRestartAnchoredVelocityBilinearEnergyWork_nativeExhaustion
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    wholeRestartAnchoredDirectVelocityBilinearEnergyWork
          initial frame first second = 0 ∨
      wholeRestartAnchoredVelocityTriadHeatCommutatorTrace
          initial frame first second ≠ 0 ∨
      ∃ time :
          Icc (0 : ℝ)
            (run initial frame.currentIndex).nextContact.time.1,
        wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
            initial frame first second time ≠ 0 ∧
          actualWholeRestartAnchoredReflectedVelocityPairVector
              initial frame first
                (outputNegSecondEquiv first second) time ≠ 0 ∧
          (wholeRestartAnchoredReflectedNextVelocityPairOccurrence
                initial frame first
                  (outputNegSecondEquiv first second) ≠ 0 ∨
            wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
                initial frame first
                  (outputNegSecondEquiv first second) time ≠ 0) ∧
          run initial frame.next.currentIndex =
            (run initial frame.currentIndex).next := by
  by_cases directZero :
      wholeRestartAnchoredDirectVelocityBilinearEnergyWork
        initial frame first second = 0
  · exact Or.inl directZero
  · right
    by_cases commutatorNonzero :
        wholeRestartAnchoredVelocityTriadHeatCommutatorTrace
          initial frame first second ≠ 0
    · exact Or.inl commutatorNonzero
    · right
      have reflectedNonzero :
          wholeRestartAnchoredReflectedVelocityBilinearEnergyWork
            initial frame first second ≠ 0 := by
        intro reflectedZero
        apply directZero
        have workIdentity :=
          wholeRestartAnchoredVelocityBilinearEnergyWork_add_reflect_eq_heatCommutator
            initial frame first second
        rw [reflectedZero, add_zero,
          not_ne_iff.mp commutatorNonzero] at workIdentity
        exact workIdentity
      have reflectedOccurrenceExists :
          ∃ time :
              Icc (0 : ℝ)
                (run initial frame.currentIndex).nextContact.time.1,
            wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
              initial frame first second time ≠ 0 := by
        by_contra everyOccurrenceZero
        push Not at everyOccurrenceZero
        apply reflectedNonzero
        unfold wholeRestartAnchoredReflectedVelocityBilinearEnergyWork
        simp [everyOccurrenceZero]
      obtain ⟨time, occurrenceNonzero⟩ := reflectedOccurrenceExists
      have pairNonzero :
          actualWholeRestartAnchoredReflectedVelocityPairVector
              initial frame first
                (outputNegSecondEquiv first second) time ≠ 0 := by
        intro pairZero
        apply occurrenceNonzero
        unfold wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
          finiteStateVelocityBilinearEnergyOccurrence
          actualWholeRestartAnchoredReflectedVelocityPairVector at *
        rw [pairZero]
        exact complexCoordinateRealInner_zero_right _
      have nativeResponsibility :=
        actualWholeRestartAnchoredReflectedVelocityPairVector_ne_zero_next_or_trace
          initial frame first
            (outputNegSecondEquiv first second) time pairNonzero
      exact
        ⟨time, occurrenceNonzero, pairNonzero, nativeResponsibility,
          generatedWholeRestartAnchoredReflectedPairNativeResponse_physical
            initial frame⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess
end NavierStokes
end SaturationMonoid
