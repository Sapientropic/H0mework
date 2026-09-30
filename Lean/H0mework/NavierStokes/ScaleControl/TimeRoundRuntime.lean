import H0mework.NavierStokes.ScaleControl.TimeShellRound

/-!
# Maximal runtime of source-generated shell/time rounds

One maximal round either exposes an infinite shell lineage or performs a
finite shell burst followed by one actual physical-time write.  Iterating
that source-owned round response gives the global alternative required by
the cascade attack:

* after finitely many physical-time rounds, an actual infinite shell lineage
  is generated; or
* there is an infinite lineage of finite shell/time rounds.

In the second branch every round carries its own canonical `F` and `T` and
pays exactly

```text
4 T (F + 1) = 1.
```

Consequently every finite prefix of `n` time rounds pays the exact weighted
time debt `n / 4`.  No caller supplies a horizon, path, round count, branch,
time, field bound, or non-Zeno certificate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedScaleTimeRoundRuntime

open scoped BigOperators

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedPathReceiptSquareCascadeBound
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveLedger
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound

noncomputable section

/-! ## Source-owned round response -/

/-- One native macro edge is exactly one generated finite shell/time round. -/
inductive RoundStep
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    ScaleTimeCurrent → Type
  | advance
      (round : GeneratedFiniteRound ν current) :
      RoundStep ν current round.next

namespace RoundStep

/-- Recover the exact generated finite round carried by a macro edge. -/
def round
    {ν : Viscosity}
    {current next : ScaleTimeCurrent} :
    RoundStep ν current next →
      GeneratedFiniteRound ν current
  | .advance round => round

/-- The target of a macro edge is its round's actual next current. -/
theorem next_eq_round_next
    {ν : Viscosity}
    {current next : ScaleTimeCurrent}
    (step : RoundStep ν current next) :
    next = step.round.next := by
  cases step
  rfl

end RoundStep

/--
The round responder returns `some` exactly for the finite shell/time branch.
Its `none` branch retains no silence: it will be decoded below as an actual
infinite shell lineage.
-/
noncomputable def generatedRoundRespond
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    Option (Response (RoundStep ν) current) :=
  match generatedRoundDisposition ν current with
  | .finite round =>
      some ⟨round.next, .advance round⟩
  | .infinite _lineage _startsAtCurrent =>
      none

/-- Typed meaning of a stopped round response. -/
structure GeneratedInfiniteShellAt
    (current : ScaleTimeCurrent) : Type where
  lineage : GeneratedIntegerShellInfiniteLineage
  startsAtCurrent :
    lineage.current 0 = current.source

/-- A stopped macro responder always generates an actual infinite shell run. -/
theorem generatedRoundRespond_eq_none_generates_infiniteShell
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (stopped : generatedRoundRespond ν current = none) :
    Nonempty (GeneratedInfiniteShellAt current) := by
  unfold generatedRoundRespond at stopped
  cases generated :
      generatedRoundDisposition ν current with
  | finite round =>
      rw [generated] at stopped
      contradiction
  | infinite lineage startsAtCurrent =>
      exact
        ⟨{ lineage := lineage
           startsAtCurrent := startsAtCurrent }⟩

/-! ## Maximal round runtime -/

/-- A finite chain of time rounds ending where an infinite shell run begins. -/
structure GeneratedRoundTerminalRun
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) : Type where
  terminal : ScaleTimeCurrent
  arrival :
    NativeReachable seed (generatedRoundRespond ν) terminal
  stopped :
    generatedRoundRespond ν terminal = none

/-- The terminal of a finite round run contains a generated infinite shell lineage. -/
noncomputable def GeneratedRoundTerminalRun.infiniteShell
    {ν : Viscosity}
    {seed : ScaleTimeCurrent}
    (run : GeneratedRoundTerminalRun ν seed) :
    GeneratedInfiniteShellAt run.terminal :=
  Classical.choice
    (generatedRoundRespond_eq_none_generates_infiniteShell
      ν run.terminal run.stopped)

/-- If no finite round terminal exists, every reachable current has a round response. -/
private theorem exists_forcedRoundResponse
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedRoundTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        NativeReachable seed (generatedRoundRespond ν) current) :
    ∃ response : Response (RoundStep ν) node.1,
      generatedRoundRespond ν node.1 = some response := by
  cases generated :
      generatedRoundRespond ν node.1 with
  | none =>
      exact False.elim <|
        noTerminal <|
          ⟨{ terminal := node.1
             arrival := node.2
             stopped := generated }⟩
  | some response =>
      exact ⟨response, rfl⟩

/-- Canonical forced round response in the nonterminating branch. -/
private noncomputable def forcedRoundResponse
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedRoundTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        NativeReachable seed (generatedRoundRespond ν) current) :
    Response (RoundStep ν) node.1 :=
  Classical.choose
    (exists_forcedRoundResponse ν seed noTerminal node)

private theorem forcedRoundResponse_generated
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedRoundTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        NativeReachable seed (generatedRoundRespond ν) current) :
    generatedRoundRespond ν node.1 =
      some (forcedRoundResponse ν seed noTerminal node) :=
  Classical.choose_spec
    (exists_forcedRoundResponse ν seed noTerminal node)

/-- Proof-relevant reachable run of forced finite rounds. -/
private noncomputable def infiniteReachableRoundRun
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedRoundTerminalRun ν seed)) :
    ℕ →
      Σ current : ScaleTimeCurrent,
        NativeReachable seed (generatedRoundRespond ν) current
  | 0 =>
      ⟨seed, NativeReachable.initial⟩
  | index + 1 =>
      let node :=
        infiniteReachableRoundRun ν seed noTerminal index
      let response :=
        forcedRoundResponse ν seed noTerminal node
      ⟨response.1,
        NativeReachable.step node.2
          (forcedRoundResponse_generated
            ν seed noTerminal node)⟩

/--
An infinite sequence of actual finite shell/time rounds.  Every adjacent
macro edge is the literal output of `generatedRoundRespond`.
-/
structure GeneratedInfiniteRoundLineage
    (ν : Viscosity) : Type where
  current : ℕ → ScaleTimeCurrent
  step :
    ∀ index : ℕ,
      RoundStep ν (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedRoundRespond ν (current index) =
        some ⟨current (index + 1), step index⟩

/-- Absence of a finite terminal generates the infinite round lineage. -/
private noncomputable def infiniteRoundLineageOfNoTerminal
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedRoundTerminalRun ν seed)) :
    GeneratedInfiniteRoundLineage ν where
  current index :=
    (infiniteReachableRoundRun
      ν seed noTerminal index).1
  step index :=
    (forcedRoundResponse
      ν seed noTerminal
      (infiniteReachableRoundRun
        ν seed noTerminal index)).2
  generated index :=
    forcedRoundResponse_generated
      ν seed noTerminal
      (infiniteReachableRoundRun
        ν seed noTerminal index)

@[simp] theorem infiniteRoundLineageOfNoTerminal_current_zero
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedRoundTerminalRun ν seed)) :
    (infiniteRoundLineageOfNoTerminal
      ν seed noTerminal).current 0 =
      seed :=
  rfl

/-- Global source-generated maximal round runtime. -/
inductive GeneratedRoundRuntimeDisposition
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) : Type
  | shellInfinite
      (run : GeneratedRoundTerminalRun ν seed)
      (infiniteShell : GeneratedInfiniteShellAt run.terminal)
  | timeInfinite
      (lineage : GeneratedInfiniteRoundLineage ν)
      (startsAtSeed : lineage.current 0 = seed)

/--
Generate the global runtime from one literal current: finitely many time
rounds followed by an infinite shell lineage, or infinitely many actual time
rounds.
-/
noncomputable def generatedRoundRuntimeDisposition
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) :
    GeneratedRoundRuntimeDisposition ν seed := by
  by_cases terminalExists :
      Nonempty (GeneratedRoundTerminalRun ν seed)
  · let run := Classical.choice terminalExists
    exact .shellInfinite run run.infiniteShell
  · exact
      .timeInfinite
        (infiniteRoundLineageOfNoTerminal
          ν seed terminalExists)
        (infiniteRoundLineageOfNoTerminal_current_zero
          ν seed terminalExists)

/-! ## Exact cumulative debt of an infinite time-round lineage -/

namespace GeneratedInfiniteRoundLineage

/-- Exact finite round carried at one lineage index. -/
def round
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (index : ℕ) :
    GeneratedFiniteRound ν (lineage.current index) :=
  (lineage.step index).round

/-- Source-generated physical-time receipt of one round. -/
def timeReceipt
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (index : ℕ) :
    GeneratedTimeAdvanceReceipt
      (lineage.round index).shellRun.terminal ν.coeff :=
  (lineage.round index).timeReceipt

/-- Every lineage successor is exactly the next current of its finite round. -/
theorem current_succ_eq_round_next
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (index : ℕ) :
    lineage.current (index + 1) =
      (lineage.round index).next :=
  (lineage.step index).next_eq_round_next

/-- Physical elapsed time advances by exactly the generated receipt duration. -/
theorem elapsed_succ
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (index : ℕ) :
    (lineage.current (index + 1)).elapsed =
      (lineage.current index).elapsed +
        (lineage.timeReceipt index).duration := by
  rw [lineage.current_succ_eq_round_next index]
  rfl

/-- Field-weighted time paid by the first `length` generated rounds. -/
def fieldWeightedTime
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    (lineage.timeReceipt index).duration *
      (((lineage.timeReceipt index).fieldBound : ℝ) + 1)

/--
Exact linear debt: `length` generated time rounds pay field-weighted time
`length / 4`.
-/
theorem four_mul_fieldWeightedTime_eq_length
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (length : ℕ) :
    4 * lineage.fieldWeightedTime length =
      length := by
  unfold fieldWeightedTime
  rw [Finset.mul_sum]
  calc
    (∑ index ∈ Finset.range length,
        4 *
          ((lineage.timeReceipt index).duration *
            (((lineage.timeReceipt index).fieldBound : ℝ) + 1))) =
        ∑ _index ∈ Finset.range length, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro index indexMem
          simpa only [mul_assoc] using
            GeneratedTimeAdvanceReceipt.four_mul_duration_mul_fieldBound_add_one
              (lineage.timeReceipt index)
    _ = length := by
      simp

/-- Actual physical time accumulated by the first `length` rounds. -/
def physicalTime
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    (lineage.timeReceipt index).duration

/-- Elapsed time in the lineage is the exact sum of its actual time receipts. -/
theorem elapsed_eq_initial_add_physicalTime
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν) :
    ∀ length : ℕ,
      (lineage.current length).elapsed =
        (lineage.current 0).elapsed +
          lineage.physicalTime length
  | 0 => by
      simp [physicalTime]
  | length + 1 => by
      rw [lineage.elapsed_succ length]
      rw [
        elapsed_eq_initial_add_physicalTime
          lineage length]
      simp [physicalTime, Finset.sum_range_succ]
      ring

/-- Sum of the exact within-round orthogonal shell receipt-square masses. -/
def shellReceiptSquareMass
    {ν : Viscosity}
    (lineage : GeneratedInfiniteRoundLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    generatedPathReceiptTraceSquareMass
      (lineage.round index).shellRun.arrival

end GeneratedInfiniteRoundLineage

end

end ThreeDimensionalVorticityCoefficientGeneratedScaleTimeRoundRuntime
end NavierStokes
end SaturationMonoid
