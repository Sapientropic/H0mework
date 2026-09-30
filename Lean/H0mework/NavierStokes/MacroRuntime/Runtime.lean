import H0mework.NavierStokes.VelocityEndpoint.AlignedResponsibilityNativeReachableWrite
import H0mework.NavierStokes.Restart.GlobalPhysicalTrajectory
import H0mework.NavierStokes.Restart.NativeAccumulationWholeNSVelocityJoin

/-!
# Conditional endpoint-macro history above the actual native root

For an already generated whole-restart current, the analytic scheduler below
classifies the entire recursively generated elapsed-time function as bounded
or unbounded.  In the bounded case its conditional endpoint edge writes the
complete component/kinetic trace; in the unbounded case the existing global
physical trajectory is available.  This classification is not the primitive
source response.

Classically auditing the completed responder graph gives two logical shapes:

* finitely many endpoint writes followed by a current whose ordinary native
  restart clock is unbounded; or
* an infinite lineage of conditional endpoint macro writes.

Every bounded endpoint write advances its physical macro clock by more than
`1/2`, because the existing H¹ slice producer selects its time in `(1/2, 1]`.
Therefore any supplied infinite macro lineage is non-Zeno without a
caller-supplied time lower bound.

This module no longer treats the classical choice between a terminal run and
a completed infinite lineage as source authority.  The original actual root
is `GeneratedWholeRestartCurrent.next/run`, exposed by
`GeneratedWholeRestartNativeActualRoot`; its finite occurrences are generated
before any whole-future terminal verdict is available.  The audit below is
retained only for ordinary classical consequences of an already completed
responder graph.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped BigOperators

open Set
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityNativeReachableWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationWholeNSVelocityJoin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointNativeReachableContinuation.GeneratedWholeRestartVelocityEndpointRuntimeState
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory

noncomputable section

/-! ## Conditional analytic endpoint scheduler -/

/-- The bounded analytic endpoint compiler recognizes the physical current
executed by the original root's exact cofinal occurrence. -/
theorem sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    sourceGeneratedWholeRestartVelocityEndpointNextCurrent
        initial elapsedBounded =
      generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        initial (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence := by
  calc
    sourceGeneratedWholeRestartVelocityEndpointNextCurrent
        initial elapsedBounded =
        sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial := by
      unfold sourceGeneratedWholeRestartVelocityEndpointNextCurrent
      unfold sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent
      unfold sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1NativeReentry
      unfold sourceGeneratedNativeTemporalPositiveTimeH1NativeReentry
      unfold sourceGeneratedWholeRestartVelocityEndpointPositiveTimeH1Slice
      unfold sourceGeneratedNativeTemporalPositiveTimeH1Slice
      unfold sourceGeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
      unfold sourceGeneratedNativeTemporalWholeMildReadWriteReceipt
      rw [
        sourceGeneratedWholeRestartVelocityEndpointLedger_toCore_eq_nativeTemporal
          initial elapsedBounded]
    _ = generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
          initial (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence :=
      (nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent
        initial).symm

/-- A bounded analytic clock recognizes one edge whose target is executed by
the original root's exact cofinal occurrence. -/
inductive GeneratedWholeRestartEndpointMacroStep
    (ν : Viscosity) :
    GeneratedWholeRestartCurrent ν →
      GeneratedWholeRestartCurrent ν → Type
  | advance
      (current : GeneratedWholeRestartCurrent ν)
      (elapsedBounded : BddAbove (Set.range (elapsedTime current))) :
      GeneratedWholeRestartEndpointMacroStep ν current
        (generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
          current (nativeTemporalCofinalVisitAuthority current).toLedgerReadout.occurrence)

namespace GeneratedWholeRestartEndpointMacroStep

/-- Recover the bounded source law carried by an actual endpoint edge. -/
theorem elapsedBounded
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν} :
    GeneratedWholeRestartEndpointMacroStep ν current next →
      BddAbove (Set.range (elapsedTime current))
  | @advance _ current bounded => bounded

/-- The exact physical time from the current's zero clock to the selected
next current on this endpoint edge. -/
def clockAdvance
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) : ℝ :=
  match step with
  | @advance _ current _bounded =>
      wholeRestartVelocityAccumulationTime current +
        (sourceGeneratedNativeTemporalPositiveTimeH1Slice current).time.1

/-- Every recursive endpoint edge advances the actual macro clock by more
than one half-unit. -/
theorem half_lt_clockAdvance
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    (1 : ℝ) / 2 < step.clockAdvance := by
  cases step with
  | advance bounded =>
      have accumulationNonneg :
          0 ≤ wholeRestartVelocityAccumulationTime current := by
        unfold wholeRestartVelocityAccumulationTime
        simpa using (le_ciSup bounded 0)
      change
        (1 : ℝ) / 2 <
          wholeRestartVelocityAccumulationTime current +
            (sourceGeneratedNativeTemporalPositiveTimeH1Slice current).time.1
      linarith [
        (sourceGeneratedNativeTemporalPositiveTimeH1Slice
          current).time_half_lt]

/-- The target current of a recursive macro edge is the physical current
recognized by its aligned endpoint frame. -/
theorem next_eq_alignedMacroPhysical
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    next =
      (wholeRestartEndpointAlignedMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead)).1 := by
  cases step
  change
    generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
        current (nativeTemporalCofinalVisitAuthority current).toLedgerReadout.occurrence =
      sourceGeneratedWholeRestartVelocityEndpointNextCurrent current _
  exact
    (sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
      current _).symm

/-- The same edge writes the actual next current, clears pending
responsibility, and records the complete aligned trace stream. -/
theorem alignedMacroFrame_update
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    wholeRestartEndpointAlignedMacroFrame current step.elapsedBounded
        (wholeRestartEndpointComponentMacroUpdate accumulationRead) =
      (next,
        0,
        wholeRestartEndpointAlignedResponsibilityTail
          current step.elapsedBounded 0) := by
  cases step with
  | advance bounded =>
      rw [wholeRestartEndpointAlignedMacroFrame_update bounded]
      rw [
        sourceGeneratedWholeRestartVelocityEndpointNextCurrent_eq_rootCofinalPhysicalNext
          current bounded]

end GeneratedWholeRestartEndpointMacroStep

/-- Conditional endpoint scheduler.  Bounded elapsed time produces the exact
aligned edge; an unbounded clock is the `none` case.  Because this test reads
the whole range of `elapsedTime current`, it is not the original root
responder. -/
noncomputable def generatedWholeRestartEndpointMacroRespond
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    Option
      (Response (GeneratedWholeRestartEndpointMacroStep ν) current) := by
  classical
  exact
    if bounded : BddAbove (Set.range (elapsedTime current)) then
      some
        ⟨generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
            current (nativeTemporalCofinalVisitAuthority current).toLedgerReadout.occurrence,
          .advance current bounded⟩
    else
      none

@[simp] theorem generatedWholeRestartEndpointMacroRespond_eq_some
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime current))) :
    generatedWholeRestartEndpointMacroRespond current =
      some
        ⟨generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence
            current (nativeTemporalCofinalVisitAuthority current).toLedgerReadout.occurrence,
          .advance current elapsedBounded⟩ := by
  simp [generatedWholeRestartEndpointMacroRespond, elapsedBounded]

theorem generatedWholeRestartEndpointMacroRespond_eq_none_iff
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν) :
    generatedWholeRestartEndpointMacroRespond current = none ↔
      ¬ BddAbove (Set.range (elapsedTime current)) := by
  simp [generatedWholeRestartEndpointMacroRespond]

/-! ## Finite terminal: the old native run is already global -/

/-- A finite exact recursive macro run ending at the first current whose
ordinary native restart clock is unbounded. -/
structure GeneratedWholeRestartEndpointMacroTerminalRun
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν) : Type where
  terminal : GeneratedWholeRestartCurrent ν
  arrival :
    NativeReachable seed generatedWholeRestartEndpointMacroRespond terminal
  stopped : generatedWholeRestartEndpointMacroRespond terminal = none

namespace GeneratedWholeRestartEndpointMacroTerminalRun

/-- The terminal current's native elapsed time is unbounded by the exact
meaning of the stopped source response. -/
theorem timeUnbounded
    {ν : Viscosity}
    {seed : GeneratedWholeRestartCurrent ν}
    (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) :
    ¬ BddAbove (Set.range (elapsedTime run.terminal)) :=
  (generatedWholeRestartEndpointMacroRespond_eq_none_iff
    run.terminal).mp run.stopped

/-- A stopped recursive endpoint run therefore generates the existing
global actual unforced trajectory rooted at that exact terminal current. -/
noncomputable def globalPhysicalTrajectory
    {ν : Viscosity}
    {seed : GeneratedWholeRestartCurrent ν}
    (run : GeneratedWholeRestartEndpointMacroTerminalRun seed) :
    GeneratedWholeGlobalPhysicalTrajectory run.terminal :=
  generatedWholeGlobalPhysicalTrajectory_of_unbounded
    run.terminal run.timeUnbounded

end GeneratedWholeRestartEndpointMacroTerminalRun

/-! ## Infinite source-owned endpoint lineage -/

private theorem exists_forcedEndpointMacroResponse
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν)
    (noTerminal :
      ¬ Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed))
    (node :
      Σ current : GeneratedWholeRestartCurrent ν,
        NativeReachable seed generatedWholeRestartEndpointMacroRespond
          current) :
    ∃ response :
        Response (GeneratedWholeRestartEndpointMacroStep ν) node.1,
      generatedWholeRestartEndpointMacroRespond node.1 = some response := by
  cases generated :
      generatedWholeRestartEndpointMacroRespond node.1 with
  | none =>
      exact False.elim <|
        noTerminal <|
          ⟨{ terminal := node.1
             arrival := node.2
             stopped := generated }⟩
  | some response =>
      exact ⟨response, rfl⟩

private noncomputable def forcedEndpointMacroResponse
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν)
    (noTerminal :
      ¬ Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed))
    (node :
      Σ current : GeneratedWholeRestartCurrent ν,
        NativeReachable seed generatedWholeRestartEndpointMacroRespond
          current) :
    Response (GeneratedWholeRestartEndpointMacroStep ν) node.1 :=
  Classical.choose
    (exists_forcedEndpointMacroResponse seed noTerminal node)

private theorem forcedEndpointMacroResponse_generated
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν)
    (noTerminal :
      ¬ Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed))
    (node :
      Σ current : GeneratedWholeRestartCurrent ν,
        NativeReachable seed generatedWholeRestartEndpointMacroRespond
          current) :
    generatedWholeRestartEndpointMacroRespond node.1 =
      some (forcedEndpointMacroResponse seed noTerminal node) :=
  Classical.choose_spec
    (exists_forcedEndpointMacroResponse seed noTerminal node)

private noncomputable def infiniteReachableEndpointMacroRun
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν)
    (noTerminal :
      ¬ Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed)) :
    ℕ →
      Σ current : GeneratedWholeRestartCurrent ν,
        NativeReachable seed generatedWholeRestartEndpointMacroRespond
          current
  | 0 => ⟨seed, NativeReachable.initial⟩
  | index + 1 =>
      let node :=
        infiniteReachableEndpointMacroRun seed noTerminal index
      let response :=
        forcedEndpointMacroResponse seed noTerminal node
      ⟨response.1,
        NativeReachable.step node.2
          (forcedEndpointMacroResponse_generated
            seed noTerminal node)⟩

/-- An infinite source-owned lineage of exact aligned endpoint macro writes. -/
structure GeneratedInfiniteWholeRestartEndpointMacroLineage
    (ν : Viscosity) : Type where
  current : ℕ → GeneratedWholeRestartCurrent ν
  step :
    ∀ index : ℕ,
      GeneratedWholeRestartEndpointMacroStep ν
        (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedWholeRestartEndpointMacroRespond (current index) =
        some ⟨current (index + 1), step index⟩

private noncomputable def infiniteEndpointMacroLineageOfNoTerminal
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν)
    (noTerminal :
      ¬ Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed)) :
    GeneratedInfiniteWholeRestartEndpointMacroLineage ν where
  current index :=
    (infiniteReachableEndpointMacroRun seed noTerminal index).1
  step index :=
    (forcedEndpointMacroResponse seed noTerminal
      (infiniteReachableEndpointMacroRun
        seed noTerminal index)).2
  generated index :=
    forcedEndpointMacroResponse_generated seed noTerminal
      (infiniteReachableEndpointMacroRun seed noTerminal index)

@[simp] theorem infiniteEndpointMacroLineageOfNoTerminal_current_zero
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν)
    (noTerminal :
      ¬ Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed)) :
    (infiniteEndpointMacroLineageOfNoTerminal
      seed noTerminal).current 0 = seed :=
  rfl

/-! ## Classical whole-future audit (not source authority) -/

/-- Logical audit of a completed endpoint-macro responder graph. -/
inductive ClassicalWholeRestartEndpointMacroRuntimeAudit
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν) : Type
  | terminal
      (run : GeneratedWholeRestartEndpointMacroTerminalRun seed)
      (trajectory : GeneratedWholeGlobalPhysicalTrajectory run.terminal)
  | infinite
      (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
      (startsAtSeed : lineage.current 0 = seed)

/-- Classical excluded-middle audit over all future responder occurrences.
It must not be used to construct the original source or its runtime identity. -/
noncomputable def classicalWholeRestartEndpointMacroRuntimeAudit
    {ν : Viscosity}
    (seed : GeneratedWholeRestartCurrent ν) :
    ClassicalWholeRestartEndpointMacroRuntimeAudit seed := by
  by_cases terminalExists :
      Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed)
  · let run := Classical.choice terminalExists
    exact .terminal run run.globalPhysicalTrajectory
  · exact
      .infinite
        (infiniteEndpointMacroLineageOfNoTerminal
          seed terminalExists)
        (infiniteEndpointMacroLineageOfNoTerminal_current_zero
          seed terminalExists)

/-! ## Exact non-Zeno clock of the infinite branch -/

namespace GeneratedInfiniteWholeRestartEndpointMacroLineage

/-- Actual physical clock accumulated by the first `length` endpoint macro
writes. -/
def macroClock
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    (lineage.step index).clockAdvance

/-- Every finite prefix pays at least one half-unit per actual macro write. -/
theorem half_length_le_macroClock
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν)
    (length : ℕ) :
    (length : ℝ) / 2 ≤ lineage.macroClock length := by
  unfold macroClock
  calc
    (length : ℝ) / 2 =
        ∑ _index ∈ Finset.range length, (1 : ℝ) / 2 := by
          simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro index indexMem
      exact (lineage.step index).half_lt_clockAdvance.le

/-- The infinite endpoint macro lineage has an unbounded generated physical
clock.  This is a consequence of the source-selected late H¹ times, not an
external non-Zeno premise. -/
theorem macroClock_not_bddAbove
    {ν : Viscosity}
    (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage ν) :
    ¬ BddAbove (Set.range lineage.macroClock) := by
  rintro ⟨upper, upperBound⟩
  obtain ⟨length : ℕ, lengthLarge⟩ :=
    exists_nat_gt (2 * max upper 0)
  have clockLower := lineage.half_length_le_macroClock length
  have clockUpper : lineage.macroClock length ≤ upper :=
    upperBound ⟨length, rfl⟩
  have maxUpperLt : max upper 0 < (length : ℝ) / 2 := by
    linarith
  linarith [le_max_left upper 0]

end GeneratedInfiniteWholeRestartEndpointMacroLineage

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
