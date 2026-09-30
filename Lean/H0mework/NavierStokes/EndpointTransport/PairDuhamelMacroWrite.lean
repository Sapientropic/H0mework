import H0mework.Realization.Residual.PathProduct
import H0mework.NavierStokes.EndpointTransport.PairCausalWriteBack
import H0mework.NavierStokes.VelocityEndpoint.MacroKineticEnergyAtom

/-!
# Cofinal pair-Duhamel residual written by the endpoint macro

Finite accumulation generates an increasing lineage of actual restart
receipts carrying nonzero causal pair-Duhamel occurrences.  This module pulls
the already existing complete `output × input-pair` residual process back
along that source-selected lineage.  Consecutive pullback states are connected
by the literal nonempty native gap path, so the new process is not a table
assembled after the endpoint.

The endpoint read then writes one product residual:

* the existing component/kinetic aligned responsibility;
* the complete cofinal pair-Duhamel tail before pair aggregation.

Both coordinate projections commute with the endpoint keep and forced trace.
The written pair coordinate is the actual Duhamel value on the generated
receipt, while the kinetic coordinate retains the exact endpoint energy atom.
The physical coordinate of the identical macro event remains the existing
source-generated unforced positive-time endpoint successor.

No event index, pair, cutoff, branch, target path, continuation witness,
nonzero witness, defect value, or faithfulness certificate is supplied by a
caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite

open Filter Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCofinalPairCausalCommutatorLineage
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCofinalPairCausalCommutatorLineage.GeneratedWholeRestartCofinalPairCausalCommutatorReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedWholeRestartEndpointMacroStep
open ResidualProjection PathIndexedResidualTransport
open AffineRelaxation

noncomputable section

/-! ## Source-selected pullback of the actual pair-Duhamel process -/

/-- Complete pair-Duhamel table at one source-generated cofinal relation
event. -/
def wholeRestartEndpointCofinalPairDuhamelTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) : WholeRestartPairDuhamelTable :=
  wholeRestartPairDuhamelTable initial
    (generatedWholeRestartCofinalPairCausalCommutatorIndex
      initial elapsedBounded index)

/-- Future pair-Duhamel residual along the source-selected cofinal lineage. -/
def wholeRestartEndpointCofinalPairDuhamelTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage : ℕ) : WholeRestartPairDuhamelTail :=
  fun offset =>
    wholeRestartEndpointCofinalPairDuhamelTable
      initial elapsedBounded (stage + offset)

/-- Consecutive cofinal pair states use the same tail-shift keep as the full
native pair-Duhamel process. -/
theorem wholeRestartEndpointCofinalPairDuhamel_transport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage : ℕ) :
    wholeRestartEndpointCofinalPairDuhamelTail
        initial elapsedBounded (stage + 1) =
      wholeRestartPairDuhamelTailKeep
        (wholeRestartEndpointCofinalPairDuhamelTail
          initial elapsedBounded stage) := by
  funext offset
  change
    wholeRestartEndpointCofinalPairDuhamelTable initial elapsedBounded
        (stage + 1 + offset) =
      wholeRestartEndpointCofinalPairDuhamelTable initial elapsedBounded
        (stage + (offset + 1))
  congr 1
  omega

/-- The cofinal pullback is an actual effective residual process on the
complete pre-aggregation pair carrier. -/
def generatedWholeRestartEndpointCofinalPairDuhamelEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    EffectiveResidualProcess ℂ WholeRestartPairDuhamelTail ℕ where
  target := 0
  keep := wholeRestartPairDuhamelTailKeep
  residual :=
    wholeRestartEndpointCofinalPairDuhamelTail initial elapsedBounded
  update := Nat.succ
  residual_transport_law :=
    wholeRestartEndpointCofinalPairDuhamel_transport
      initial elapsedBounded

@[simp] theorem
    generatedWholeRestartEndpointCofinalPairDuhamelEffectiveProcess_pathState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage steps : ℕ) :
    (generatedWholeRestartEndpointCofinalPairDuhamelEffectiveProcess
      initial elapsedBounded).pathState stage steps =
        stage + steps := by
  induction steps with
  | zero => simp
  | succ steps inductionHypothesis =>
      rw [EffectiveResidualProcess.pathState_succ,
        inductionHypothesis]
      rfl

/-- Forced trace between two consecutive complete cofinal pair tables. -/
def wholeRestartEndpointCofinalPairDuhamelTraceRow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage : ℕ) : WholeRestartPairDuhamelTable :=
  wholeRestartEndpointCofinalPairDuhamelTable
      initial elapsedBounded stage -
    wholeRestartEndpointCofinalPairDuhamelTable
      initial elapsedBounded (stage + 1)

/-- The head of the forced tail trace is the literal componentwise
difference of the two source-selected actual pair tables. -/
theorem wholeRestartEndpointCofinalPairDuhamel_trace_head
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage : ℕ) :
    linearResidualTrace wholeRestartPairDuhamelTailKeep
          (wholeRestartEndpointCofinalPairDuhamelTail
            initial elapsedBounded stage) 0 =
      wholeRestartEndpointCofinalPairDuhamelTraceRow
        initial elapsedBounded stage := by
  rfl

/-- Finite-path conservation on the cofinal pre-aggregation pair carrier. -/
theorem wholeRestartEndpointCofinalPairDuhamel_path_split
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (steps : ℕ) :
    wholeRestartEndpointCofinalPairDuhamelTable initial elapsedBounded 0 =
      wholeRestartEndpointCofinalPairDuhamelTable
          initial elapsedBounded steps +
        ((generatedWholeRestartEndpointCofinalPairDuhamelEffectiveProcess
          initial elapsedBounded).pathTrace 0 steps) 0 := by
  have split :=
    (generatedWholeRestartEndpointCofinalPairDuhamelEffectiveProcess
      initial elapsedBounded).pathTrace_split 0 steps
  rw [
    generatedWholeRestartEndpointCofinalPairDuhamelEffectiveProcess_pathState]
    at split
  simpa [generatedWholeRestartEndpointCofinalPairDuhamelEffectiveProcess,
    wholeRestartEndpointCofinalPairDuhamelTail] using congrFun split 0

/-- A nonzero occurrence in a cofinal table remains in the future cofinal
table or in the uniquely generated componentwise path trace. -/
theorem
    wholeRestartEndpointCofinalPairDuhamelOccurrence_ne_zero_future_or_pathTrace
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (output first : IntegerWavevector)
    (steps : ℕ)
    (currentNonzero :
      wholeRestartEndpointCofinalPairDuhamelTable
        initial elapsedBounded 0 output first ≠ 0) :
    wholeRestartEndpointCofinalPairDuhamelTable
          initial elapsedBounded steps output first ≠ 0 ∨
      ((generatedWholeRestartEndpointCofinalPairDuhamelEffectiveProcess
          initial elapsedBounded).pathTrace 0 steps)
            0 output first ≠ 0 := by
  by_cases futureNonzero :
      wholeRestartEndpointCofinalPairDuhamelTable
        initial elapsedBounded steps output first ≠ 0
  · exact Or.inl futureNonzero
  · right
    intro traceZero
    apply currentNonzero
    have split := congrFun
      (congrFun
        (wholeRestartEndpointCofinalPairDuhamel_path_split
          initial elapsedBounded steps) output) first
    simp only [Pi.add_apply] at split
    rw [not_ne_iff.mp futureNonzero, traceZero, zero_add] at split
    exact split

/-- Drop a source-generated number of literal native pair-Duhamel states. -/
def wholeRestartPairDuhamelTailDrop
    (steps : ℕ) :
    WholeRestartPairDuhamelTail →ₗ[ℂ] WholeRestartPairDuhamelTail where
  toFun residual offset := residual (steps + offset)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The cofinal carrier is the concrete pullback of the full native tail
along the source-selected increasing event map. -/
def wholeRestartEndpointCofinalPairDuhamelPullback
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage : ℕ) :
    WholeRestartPairDuhamelTail →ₗ[ℂ] WholeRestartPairDuhamelTail where
  toFun residual offset :=
    residual
      (generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (stage + offset) -
        generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded stage)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pulling the actual full native tail back at a cofinal stage recovers the
complete cofinal tail, on the whole `output × pair` carrier. -/
theorem wholeRestartEndpointCofinalPairDuhamelPullback_actualTail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage : ℕ) :
    wholeRestartEndpointCofinalPairDuhamelPullback
        initial elapsedBounded stage
        (wholeRestartPairDuhamelTail initial
          (generatedWholeRestartCofinalPairCausalCommutatorIndex
            initial elapsedBounded stage) 0) =
      wholeRestartEndpointCofinalPairDuhamelTail
        initial elapsedBounded stage := by
  funext offset
  have indexLe :
      generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded stage ≤
        generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (stage + offset) :=
    (generatedWholeRestartCofinalPairCausalCommutatorIndex_strictMono
      initial elapsedBounded).monotone (Nat.le_add_right stage offset)
  simp only [wholeRestartEndpointCofinalPairDuhamelPullback,
    wholeRestartPairDuhamelTail,
    wholeRestartPairDuhamelPathTable,
    wholeRestartEndpointCofinalPairDuhamelTail,
    wholeRestartEndpointCofinalPairDuhamelTable,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 2
  omega

/-- Edge-dependent pullback commutes on every full native tail with the exact
generated gap drop and the cofinal keep.  This is a whole-carrier square, not
an equality checked only on the actual residual. -/
theorem wholeRestartEndpointCofinalPairDuhamelPullback_keep_commuting
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage : ℕ)
    (residual : WholeRestartPairDuhamelTail) :
    wholeRestartEndpointCofinalPairDuhamelPullback
        initial elapsedBounded (stage + 1)
        (wholeRestartPairDuhamelTailDrop
          (generatedWholeRestartCofinalPairCausalCommutatorGap
            initial elapsedBounded stage) residual) =
      wholeRestartPairDuhamelTailKeep
        (wholeRestartEndpointCofinalPairDuhamelPullback
          initial elapsedBounded stage residual) := by
  have strict :=
    generatedWholeRestartCofinalPairCausalCommutatorIndex_lt_succ
      initial elapsedBounded stage
  funext offset
  have nextLe :
      generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (stage + 1) ≤
        generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (stage + 1 + offset) :=
    (generatedWholeRestartCofinalPairCausalCommutatorIndex_strictMono
      initial elapsedBounded).monotone
        (Nat.le_add_right (stage + 1) offset)
  simp only [wholeRestartEndpointCofinalPairDuhamelPullback,
    wholeRestartPairDuhamelTailDrop,
    wholeRestartPairDuhamelTailKeep,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  unfold generatedWholeRestartCofinalPairCausalCommutatorGap
  have sameIndex :
      stage + 1 + offset = stage + (offset + 1) := by
    omega
  rw [sameIndex]
  have nextLe' :
      generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (stage + 1) ≤
        generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (stage + (offset + 1)) := by
    simpa only [sameIndex] using nextLe
  simpa only [Nat.add_comm] using
    (Nat.sub_add_sub_cancel nextLe' (Nat.le_of_lt strict))

/-- The complementary trace equation is forced by the preceding
whole-carrier square.  The two edge-dependent pullbacks are evaluated before
subtraction, so no false global injectivity is assumed. -/
theorem wholeRestartEndpointCofinalPairDuhamelPullback_trace_commuting
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (stage : ℕ)
    (residual : WholeRestartPairDuhamelTail) :
    wholeRestartEndpointCofinalPairDuhamelPullback
          initial elapsedBounded stage residual -
        wholeRestartEndpointCofinalPairDuhamelPullback
          initial elapsedBounded (stage + 1)
          (wholeRestartPairDuhamelTailDrop
            (generatedWholeRestartCofinalPairCausalCommutatorGap
              initial elapsedBounded stage) residual) =
      linearResidualTrace wholeRestartPairDuhamelTailKeep
        (wholeRestartEndpointCofinalPairDuhamelPullback
          initial elapsedBounded stage residual) := by
  rw [
    wholeRestartEndpointCofinalPairDuhamelPullback_keep_commuting]
  rfl

/-- Each source-selected jump of the full native pair process is the exact
gap drop on the complete future tail. -/
theorem wholeRestartPairDuhamelTail_nativeGapTransport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartPairDuhamelTail initial
        (generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (index + 1)) 0 =
      wholeRestartPairDuhamelTailDrop
        (generatedWholeRestartCofinalPairCausalCommutatorGap
          initial elapsedBounded index)
        (wholeRestartPairDuhamelTail initial
          (generatedWholeRestartCofinalPairCausalCommutatorIndex
            initial elapsedBounded index) 0) := by
  have strict :=
    generatedWholeRestartCofinalPairCausalCommutatorIndex_lt_succ
      initial elapsedBounded index
  funext offset
  simp only [wholeRestartPairDuhamelTailDrop,
    wholeRestartPairDuhamelTail,
    wholeRestartPairDuhamelPathTable,
    LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  unfold generatedWholeRestartCofinalPairCausalCommutatorGap
  omega

/-- The generated native gap is the literal path state of the authoritative
full pair-Duhamel effective process. -/
theorem wholeRestartEndpointCofinalPairDuhamel_nativeProcessPathState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartPairDuhamelTail initial
        (generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded (index + 1)) 0 =
      (generatedWholeRestartPairDuhamelEffectiveProcess initial
        (generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded index)).residual
        ((generatedWholeRestartPairDuhamelEffectiveProcess initial
          (generatedWholeRestartCofinalPairCausalCommutatorIndex
            initial elapsedBounded index)).pathState 0
          (generatedWholeRestartCofinalPairCausalCommutatorGap
            initial elapsedBounded index)) := by
  rw [
    generatedWholeRestartPairDuhamelEffectiveProcess_pathState]
  rw [wholeRestartPairDuhamelTail_nativeGapTransport]
  funext offset
  simp [wholeRestartPairDuhamelTailDrop,
    generatedWholeRestartPairDuhamelEffectiveProcess,
    wholeRestartPairDuhamelTail,
    wholeRestartPairDuhamelPathTable]

/-! ## Whole endpoint residual: aligned kinetic responsibility × cofinal pair
responsibility -/

/-- Whole endpoint carrier retaining both the aligned component/kinetic
stream and the complete source-selected pair-Duhamel tail. -/
abbrev WholeRestartEndpointCausalResponsibility :=
  WholeRestartEndpointAlignedResponsibilityTail ×
    WholeRestartPairDuhamelTail

/-- Before the endpoint write both complete responsibilities are pending. -/
def wholeRestartEndpointCausalMacroPending
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      WholeRestartEndpointCausalResponsibility
  | accumulationRead =>
      (wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0,
        wholeRestartEndpointCofinalPairDuhamelTail
          initial elapsedBounded 0)
  | endpointWritten => 0

/-- The same endpoint event writes both whole carriers before any finite
observer quotient. -/
def wholeRestartEndpointCausalMacroTraceLedger
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    WholeRestartEndpointComponentMacroPhase →
      WholeRestartEndpointCausalResponsibility
  | accumulationRead => 0
  | endpointWritten =>
      (wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0,
        wholeRestartEndpointCofinalPairDuhamelTail
          initial elapsedBounded 0)

/-- Product keep of the two endpoint macro carriers.  Both responsibilities
are fully written into the same trace event. -/
def wholeRestartEndpointCausalMacroKeep :
    WholeRestartEndpointCausalResponsibility →ₗ[ℂ]
      WholeRestartEndpointCausalResponsibility :=
  productKeep wholeRestartEndpointAlignedMacroKeep 0

/-- Effective residual process of the combined endpoint read/write. -/
def generatedWholeRestartEndpointCausalMacroEffectiveProcess
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    EffectiveResidualProcess ℂ
      WholeRestartEndpointCausalResponsibility
      WholeRestartEndpointComponentMacroPhase where
  target := 0
  keep := wholeRestartEndpointCausalMacroKeep
  residual := wholeRestartEndpointCausalMacroPending
    initial elapsedBounded
  update := wholeRestartEndpointComponentMacroUpdate
  residual_transport_law := by
    intro phase
    cases phase <;> rfl

/-- The endpoint contact reads both whole carriers and writes the existing
source-owned endpoint phase. -/
def generatedWholeRestartEndpointCausalMacroQuery
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ReflexiveQuery WholeRestartEndpointComponentMacroPhase
      WholeRestartEndpointCausalResponsibility where
  read := wholeRestartEndpointCausalMacroPending initial elapsedBounded
  write := wholeRestartEndpointComponentMacroUpdate

@[simp] theorem generatedWholeRestartEndpointCausalMacroQuery_run
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (generatedWholeRestartEndpointCausalMacroQuery
      initial elapsedBounded).run accumulationRead =
      ((wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0,
        wholeRestartEndpointCofinalPairDuhamelTail
          initial elapsedBounded 0),
        endpointWritten) := by
  rfl

/-- The uniquely forced endpoint trace is the complete two-coordinate
responsibility. -/
theorem wholeRestartEndpointCausalMacro_trace_eq_responsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    linearResidualTrace wholeRestartEndpointCausalMacroKeep
        (wholeRestartEndpointCausalMacroPending
          initial elapsedBounded accumulationRead) =
      (wholeRestartEndpointAlignedResponsibilityTail
          initial elapsedBounded 0,
        wholeRestartEndpointCofinalPairDuhamelTail
          initial elapsedBounded 0) := by
  simp [linearResidualTrace, wholeRestartEndpointCausalMacroKeep,
    wholeRestartEndpointCausalMacroPending, productKeep,
    wholeRestartEndpointAlignedMacroKeep]

/-- The left projection commutes with endpoint keep and forced trace on the
whole product carrier. -/
theorem wholeRestartEndpointCausalMacro_fst_commuting
    (residual : WholeRestartEndpointCausalResponsibility) :
    productFst (K := ℂ)
        (E := WholeRestartEndpointAlignedResponsibilityTail)
        (F := WholeRestartPairDuhamelTail)
        (wholeRestartEndpointCausalMacroKeep residual) =
        wholeRestartEndpointAlignedMacroKeep
          (productFst (K := ℂ)
            (E := WholeRestartEndpointAlignedResponsibilityTail)
            (F := WholeRestartPairDuhamelTail) residual) ∧
      productFst (K := ℂ)
          (E := WholeRestartEndpointAlignedResponsibilityTail)
          (F := WholeRestartPairDuhamelTail)
          (linearResidualTrace
            wholeRestartEndpointCausalMacroKeep residual) =
        linearResidualTrace wholeRestartEndpointAlignedMacroKeep
          (productFst (K := ℂ)
            (E := WholeRestartEndpointAlignedResponsibilityTail)
            (F := WholeRestartPairDuhamelTail) residual) := by
  constructor <;>
    simp [wholeRestartEndpointCausalMacroKeep, productKeep,
      productFst, linearResidualTrace,
      wholeRestartEndpointAlignedMacroKeep]

/-- The right projection commutes with endpoint keep and forced trace on the
whole product carrier. -/
theorem wholeRestartEndpointCausalMacro_snd_commuting
    (residual : WholeRestartEndpointCausalResponsibility) :
    productSnd (K := ℂ)
        (E := WholeRestartEndpointAlignedResponsibilityTail)
        (F := WholeRestartPairDuhamelTail)
        (wholeRestartEndpointCausalMacroKeep residual) =
        (0 : WholeRestartPairDuhamelTail →ₗ[ℂ]
          WholeRestartPairDuhamelTail)
          (productSnd (K := ℂ)
            (E := WholeRestartEndpointAlignedResponsibilityTail)
            (F := WholeRestartPairDuhamelTail) residual) ∧
      productSnd (K := ℂ)
          (E := WholeRestartEndpointAlignedResponsibilityTail)
          (F := WholeRestartPairDuhamelTail)
          (linearResidualTrace
            wholeRestartEndpointCausalMacroKeep residual) =
        linearResidualTrace
          (0 : WholeRestartPairDuhamelTail →ₗ[ℂ]
            WholeRestartPairDuhamelTail)
          (productSnd (K := ℂ)
            (E := WholeRestartEndpointAlignedResponsibilityTail)
            (F := WholeRestartPairDuhamelTail) residual) := by
  constructor <;>
    simp [wholeRestartEndpointCausalMacroKeep, productKeep,
      productSnd, linearResidualTrace]

/-- Exact write-back of both endpoint responsibility carriers. -/
theorem wholeRestartEndpointCausalMacro_ledger_writeBack
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointCausalMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      wholeRestartEndpointCausalMacroTraceLedger
          initial elapsedBounded accumulationRead +
        linearResidualTrace wholeRestartEndpointCausalMacroKeep
          (wholeRestartEndpointCausalMacroPending
            initial elapsedBounded accumulationRead) := by
  simp [wholeRestartEndpointCausalMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointCausalMacro_trace_eq_responsibility]

/-- Pending plus written responsibility is conserved on the complete product
carrier. -/
theorem wholeRestartEndpointCausalMacro_noSilentLoss
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointCausalMacroPending
          initial elapsedBounded accumulationRead +
        wholeRestartEndpointCausalMacroTraceLedger
          initial elapsedBounded accumulationRead =
      wholeRestartEndpointCausalMacroPending initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead) +
        wholeRestartEndpointCausalMacroTraceLedger initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead) := by
  simp [wholeRestartEndpointCausalMacroPending,
    wholeRestartEndpointCausalMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate]

/-! ## Exact written coordinates and physical write -/

/-- Every generated cofinal event is a literal complete pair table in the
written endpoint trace. -/
theorem wholeRestartEndpointCausalMacro_writtenCofinalPairTable
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    (wholeRestartEndpointCausalMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).2 index =
      wholeRestartPairDuhamelTable initial
        (generatedWholeRestartCofinalPairCausalCommutatorIndex
          initial elapsedBounded index) := by
  simp [wholeRestartEndpointCausalMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate,
    wholeRestartEndpointCofinalPairDuhamelTail,
    wholeRestartEndpointCofinalPairDuhamelTable]

/-- The source-generated nonzero pair receipt survives as its actual value
inside the endpoint macro trace. -/
theorem wholeRestartEndpointCausalMacro_writtenCofinalPair_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    let receipt :=
      generatedWholeRestartCofinalPairCausalCommutatorReceipt
        initial elapsedBounded index
    (wholeRestartEndpointCausalMacroTraceLedger initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).2
          index receipt.output receipt.first ≠ 0 := by
  dsimp only
  rw [wholeRestartEndpointCausalMacro_writtenCofinalPairTable]
  change
    wholeRestartPairDuhamelOccurrence initial
      (generatedWholeRestartCofinalPairCausalCommutatorIndex
        initial elapsedBounded index)
      (generatedWholeRestartCofinalPairCausalCommutatorReceipt
        initial elapsedBounded index).output
      (generatedWholeRestartCofinalPairCausalCommutatorReceipt
        initial elapsedBounded index).first ≠ 0
  simpa only [generatedWholeRestartCofinalPairCausalCommutatorIndex] using
    (generatedWholeRestartCofinalPairCausalCommutatorLineage_noSilentLoss
      initial elapsedBounded index).1

/-- The complete pair-Duhamel coordinate makes the generated endpoint trace
nonzero before any observer quotient. -/
theorem wholeRestartEndpointCausalMacro_trace_ne_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    linearResidualTrace wholeRestartEndpointCausalMacroKeep
        (wholeRestartEndpointCausalMacroPending
          initial elapsedBounded accumulationRead) ≠ 0 := by
  intro traceZero
  let receipt :=
    generatedWholeRestartCofinalPairCausalCommutatorReceipt
      initial elapsedBounded 0
  have coordinateZero := congrArg
    (fun residual : WholeRestartEndpointCausalResponsibility =>
      residual.2 0 receipt.output receipt.first) traceZero
  rw [wholeRestartEndpointCausalMacro_trace_eq_responsibility] at coordinateZero
  have coordinateNonzero :=
    wholeRestartEndpointCausalMacro_writtenCofinalPair_ne_zero
      initial elapsedBounded 0
  apply coordinateNonzero
  simpa [wholeRestartEndpointCausalMacroTraceLedger,
    wholeRestartEndpointComponentMacroUpdate] using coordinateZero

/-- The kinetic coordinate of the same whole endpoint trace retains the
actual stage's exact endpoint energy atom. -/
theorem wholeRestartEndpointCausalMacro_kineticTrace_tendsto_energyAtom
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Tendsto
      (fun index =>
        ‖((linearResidualTrace wholeRestartEndpointCausalMacroKeep
          (wholeRestartEndpointCausalMacroPending
            current step.elapsedBounded accumulationRead)).1 index).2‖ ^ 2)
      atTop (nhds step.physicalStageKineticEnergyAtom) := by
  have traceFst :
      (linearResidualTrace wholeRestartEndpointCausalMacroKeep
          (wholeRestartEndpointCausalMacroPending
            current step.elapsedBounded accumulationRead)).1 =
        linearResidualTrace wholeRestartEndpointAlignedMacroKeep
          (wholeRestartEndpointAlignedMacroPending
            current step.elapsedBounded accumulationRead) := by
    have commuting :=
      (wholeRestartEndpointCausalMacro_fst_commuting
        (wholeRestartEndpointCausalMacroPending
          current step.elapsedBounded accumulationRead)).2
    change
      productFst (K := ℂ)
          (E := WholeRestartEndpointAlignedResponsibilityTail)
          (F := WholeRestartPairDuhamelTail)
          (linearResidualTrace wholeRestartEndpointCausalMacroKeep
            (wholeRestartEndpointCausalMacroPending
              current step.elapsedBounded accumulationRead)) =
        linearResidualTrace wholeRestartEndpointAlignedMacroKeep
          (productFst (K := ℂ)
            (E := WholeRestartEndpointAlignedResponsibilityTail)
            (F := WholeRestartPairDuhamelTail)
            (wholeRestartEndpointCausalMacroPending
              current step.elapsedBounded accumulationRead))
    exact commuting
  rw [traceFst]
  exact step.alignedMacroKineticTrace_norm_sq_tendsto_energyAtom

/-- The common endpoint frame carries the actual physical macro current,
both pending whole carriers, and their exact trace ledger. -/
def wholeRestartEndpointCausalMacroFrame
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (phase : WholeRestartEndpointComponentMacroPhase) :
    GeneratedWholeRestartCurrent ν ×
      (WholeRestartEndpointCausalResponsibility ×
        WholeRestartEndpointCausalResponsibility) :=
  (wholeRestartEndpointComponentMacroPhysicalCurrent
      initial elapsedBounded phase,
    wholeRestartEndpointCausalMacroPending
      initial elapsedBounded phase,
    wholeRestartEndpointCausalMacroTraceLedger
      initial elapsedBounded phase)

/-- One source-owned endpoint equation writes the existing unforced physical
successor and both full residual carriers. -/
theorem wholeRestartEndpointCausalMacroFrame_update
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartEndpointCausalMacroFrame initial elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (sourceGeneratedWholeRestartVelocityEndpointNextCurrent
          initial elapsedBounded,
        0,
        (wholeRestartEndpointAlignedResponsibilityTail
            initial elapsedBounded 0,
          wholeRestartEndpointCofinalPairDuhamelTail
            initial elapsedBounded 0)) := by
  rfl

/-- The physical projection of this exact product write is the generated
unforced endpoint successor. -/
theorem wholeRestartEndpointCausalMacroFrame_physical_update
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    (wholeRestartEndpointCausalMacroFrame initial elapsedBounded
      (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 =
        sourceGeneratedWholeRestartVelocityEndpointNextCurrent
          initial elapsedBounded := by
  rfl

/-- The physical write is genuinely at positive absolute time past the old
accumulation endpoint and its next native receipt starts at that written
state. -/
theorem wholeRestartEndpointCausalMacroFrame_unforcedPastEndpoint
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    wholeRestartVelocityAccumulationTime initial <
        (sourceGeneratedWholeRestartVelocityEndpointSelectedAbsoluteTime
          initial elapsedBounded).1 ∧
      let next :=
        (wholeRestartEndpointCausalMacroFrame initial elapsedBounded
          (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1
      0 < next.duration ∧
        next.receipt.wholePath
            ⟨0, ⟨le_rfl, next.receipt.requestedTimePos.le⟩⟩ =
          next.initialState := by
  let continuation :=
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      initial elapsedBounded
  exact
    ⟨continuation.selectedAbsoluteTime_gt_accumulation,
      continuation.next_duration_pos,
      continuation.next_receipt_initial⟩

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointCofinalPairDuhamelMacroWrite
end NavierStokes
end SaturationMonoid
