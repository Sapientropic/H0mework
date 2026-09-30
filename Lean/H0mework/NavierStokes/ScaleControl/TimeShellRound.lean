import H0mework.NavierStokes.ShellSources.RuntimeDisposition
import H0mework.NavierStokes.ScaleControl.TimeReflexiveLedger

/-!
# Maximal shell bursts followed by actual physical-time writes

The total reflexive producer acts one event at a time.  The PDE cascade is
more naturally consumed in maximal source-owned rounds:

```text
finite generated shell burst
→ exact shell receipt-square ledger
→ first outer-shell zero
→ actual positive physical-time write
```

or else the shell burst itself is infinite and enters the existing infinite
receipt-square lineage.

This module generates that dichotomy from the literal source.  In the finite
branch it proves that the shell arrival lifts to the same total reflexive
write chain with unchanged elapsed time and that the very next write is the
quantified physical Picard event.  No horizon, stopping certificate, branch,
target source, field bound, or time is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound

open scoped BigOperators

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite
open ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareCascadeBound
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellRuntimeDisposition
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveLedger

noncomputable section

/-! ## Lift an arbitrary generated shell path into the total write chain -/

/--
Every exact generated shell arrival is literally the prefix of the total
scale-or-time reflexive chain before its first physical-time write.
-/
theorem currentAt_generatedShellArrival
    {seed terminal : RawVorticityFourierSource}
    (ν : Viscosity)
    (elapsed : ℝ)
    (arrival : GeneratedIntegerShellReachable seed terminal) :
    currentAt ν
        { source := seed
          elapsed := elapsed }
        arrival.occurrence =
      { source := terminal
        elapsed := elapsed } := by
  induction arrival with
  | initial =>
      rfl
  | @step current arrival response generated inductionHypothesis =>
      rw [NativeReachable.occurrence]
      rw [currentAt_succ]
      rw [inductionHypothesis]
      have run :=
        scaleTimeReflexiveQuery_run_of_some
          ν
          { source := current
            elapsed := elapsed }
          response generated
      simpa [ReflexiveQuery.run, shellTarget] using
        congrArg Prod.snd run

/-- Observation at the next edge of a lifted shell arrival is its exact receipt. -/
theorem observationAt_generatedShellArrival_next
    {seed current : RawVorticityFourierSource}
    (ν : Viscosity)
    (elapsed : ℝ)
    (arrival : GeneratedIntegerShellReachable seed current)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response) :
    observationAt ν
        { source := seed
          elapsed := elapsed }
        arrival.occurrence =
      .shell
        (receiptOfResponse current response generated) := by
  unfold observationAt
  rw [currentAt_generatedShellArrival
    ν elapsed arrival]
  exact
    congrArg Prod.fst
      (scaleTimeReflexiveQuery_run_of_some
        ν
        { source := current
          elapsed := elapsed }
        response generated)

/--
The total-chain shell-square ledger on a lifted shell arrival is exactly the
pre-existing orthogonal generated-path receipt-square mass.
-/
theorem shellReceiptSquareMass_generatedShellArrival
    {seed terminal : RawVorticityFourierSource}
    (ν : Viscosity)
    (elapsed : ℝ)
    (arrival : GeneratedIntegerShellReachable seed terminal) :
    shellReceiptSquareMass ν
        { source := seed
          elapsed := elapsed }
        arrival.occurrence =
      generatedPathReceiptTraceSquareMass arrival := by
  induction arrival with
  | initial =>
      rfl
  | @step current arrival response generated inductionHypothesis =>
      rw [NativeReachable.occurrence]
      rw [shellReceiptSquareMass_succ]
      rw [
        observationAt_generatedShellArrival_next
          ν elapsed arrival response generated]
      rw [inductionHypothesis]
      unfold generatedPathReceiptTraceSquareMass
      simp [
        generatedIntegerShellReachableReceipts,
        receiptOfResponse,
        ScaleTimeObservation.shellQuantum]

/-- No physical time is silently inserted inside a generated shell burst. -/
theorem physicalTimeOccupancy_generatedShellArrival
    {seed terminal : RawVorticityFourierSource}
    (ν : Viscosity)
    (elapsed : ℝ)
    (arrival : GeneratedIntegerShellReachable seed terminal) :
    physicalTimeOccupancy ν
        { source := seed
          elapsed := elapsed }
        arrival.occurrence =
      0 := by
  have elapsedLedger :=
    currentAt_elapsed_eq_initial_add_physicalTimeOccupancy
      ν
      { source := seed
        elapsed := elapsed }
      arrival.occurrence
  rw [
    currentAt_generatedShellArrival
      ν elapsed arrival] at elapsedLedger
  dsimp at elapsedLedger
  linarith

/-! ## One maximal finite shell/time round -/

/--
A finite round is completely determined by the maximal shell run generated
from the current source.
-/
structure GeneratedFiniteRound
    (ν : Viscosity)
    (current : ScaleTimeCurrent) : Type where
  shellRun : GeneratedIntegerShellTerminalRun current.source

namespace GeneratedFiniteRound

/-- Number of shell events before the generated time event. -/
def shellLength
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) : ℕ :=
  round.shellRun.arrival.occurrence

/-- Canonical time receipt generated at the terminal of the shell burst. -/
def timeReceipt
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    GeneratedTimeAdvanceReceipt
      round.shellRun.terminal ν.coeff :=
  generatedTimeAdvanceReceipt
    round.shellRun.terminal ν.coeff

/-- Source current written by the entire shell/time round. -/
def next
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    ScaleTimeCurrent where
  source := round.timeReceipt.nextSource
  elapsed := current.elapsed + round.timeReceipt.duration

/-- The shell prefix reaches the generated terminal with elapsed time fixed. -/
theorem currentAt_shellLength
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    currentAt ν current round.shellLength =
      { source := round.shellRun.terminal
        elapsed := current.elapsed } := by
  rcases current with ⟨source, elapsed⟩
  exact
    currentAt_generatedShellArrival
      ν elapsed round.shellRun.arrival

/-- The next total event after the maximal shell burst is the exact time receipt. -/
theorem observationAt_shellLength
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    observationAt ν current round.shellLength =
      .time round.shellRun.terminal
        round.timeReceipt := by
  unfold observationAt
  rw [round.currentAt_shellLength]
  exact
    congrArg Prod.fst
      (scaleTimeReflexiveQuery_run_of_none
        ν
        { source := round.shellRun.terminal
          elapsed := current.elapsed }
        round.shellRun.stopped)

/--
The entire maximal shell burst plus its time event is an exact prefix of the
total reflexive chain.
-/
theorem currentAt_shellLength_succ
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    currentAt ν current (round.shellLength + 1) =
      round.next := by
  rw [currentAt_succ]
  rw [round.currentAt_shellLength]
  have run :=
    scaleTimeReflexiveQuery_run_of_none
      ν
      { source := round.shellRun.terminal
        elapsed := current.elapsed }
      round.shellRun.stopped
  simpa [ReflexiveQuery.run, next, timeTarget, timeReceipt] using
    congrArg Prod.snd run

/-- Exact orthogonal receipt-square mass of the round's shell burst. -/
theorem shellReceiptSquareMass_shellLength
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    shellReceiptSquareMass ν current round.shellLength =
      generatedPathReceiptTraceSquareMass
        round.shellRun.arrival := by
  rcases current with ⟨source, elapsed⟩
  exact
    shellReceiptSquareMass_generatedShellArrival
      ν elapsed round.shellRun.arrival

/-- The shell part of the round consumes no physical time. -/
theorem physicalTimeOccupancy_shellLength
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    physicalTimeOccupancy ν current round.shellLength = 0 := by
  rcases current with ⟨source, elapsed⟩
  exact
    physicalTimeOccupancy_generatedShellArrival
      ν elapsed round.shellRun.arrival

/-- The whole round consumes exactly its generated Picard duration. -/
theorem physicalTimeOccupancy_shellLength_succ
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    physicalTimeOccupancy ν current
        (round.shellLength + 1) =
      round.timeReceipt.duration := by
  rw [physicalTimeOccupancy_succ]
  rw [
    round.physicalTimeOccupancy_shellLength,
    round.observationAt_shellLength]
  simp [ScaleTimeObservation.timeDuration]

/--
The time event of every finite round pays the exact canonical
field-weighted quantum.
-/
theorem timeReceipt_fieldWeightedQuantum
    {ν : Viscosity}
    {current : ScaleTimeCurrent}
    (round : GeneratedFiniteRound ν current) :
    4 * round.timeReceipt.duration *
        ((round.timeReceipt.fieldBound : ℝ) + 1) =
      1 :=
  GeneratedTimeAdvanceReceipt.four_mul_duration_mul_fieldBound_add_one
    round.timeReceipt

end GeneratedFiniteRound

/-! ## Maximal source-generated round disposition -/

/--
From one total current the source either generates a finite shell burst and
the following physical-time event, or an actual infinite shell lineage.
-/
inductive GeneratedRoundDisposition
    (ν : Viscosity)
    (current : ScaleTimeCurrent) : Type
  | finite
      (round : GeneratedFiniteRound ν current)
  | infinite
      (lineage : GeneratedIntegerShellInfiniteLineage)
      (startsAtCurrent :
        lineage.current 0 = current.source)

/--
Generate the maximal round directly from the current source.  The internal
runtime split supplies both the finite shell path and the infinite lineage;
the caller supplies neither.
-/
noncomputable def generatedRoundDisposition
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    GeneratedRoundDisposition ν current := by
  cases generatedIntegerShellRuntimeDisposition
      current.source with
  | terminal run =>
      exact .finite ⟨run⟩
  | infinite lineage startsAtSource =>
      exact .infinite lineage startsAtSource

end

end ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound
end NavierStokes
end SaturationMonoid
