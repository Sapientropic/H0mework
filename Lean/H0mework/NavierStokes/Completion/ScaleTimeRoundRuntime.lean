import H0mework.NavierStokes.Completion.ScaleTimeShellRound

/-!
# Runtime of complete-support shell/time macro rounds

The legacy round runtime advances directly from the radial shell terminal.
This version changes only the macro target:

```text
old source-owned maximal shell path
→ optional conservative complete-support write
→ actual positive-time unforced endpoint.
```

Iterating this exact macro gives either a finite sequence ending at a
genuine infinite old-q shell lineage, or an infinite sequence of complete
physical-time rounds.  On every finite prefix the whole physical write is
the exact sum of the already-consumed within-round shell traces and the
actual unforced generator integrals.

No cross-round occurrence norm is introduced.  Vector summation happens
only after each round's physical responsibility has been settled on its
own complete carrier.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedCompleteScaleTimeRoundRuntime

open scoped BigOperators Interval

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageReceiptSquare
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellJumpLedger

noncomputable section

/-! ## One complete macro response -/

set_option maxHeartbeats 800000

/-- One macro edge carries the exact old-q round and writes its complete
support/time endpoint. -/
inductive CompleteRoundStep
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    ScaleTimeCurrent → Type
  | advance
      (round : GeneratedFiniteRound ν current) :
      CompleteRoundStep ν current round.completeNext

namespace CompleteRoundStep

def round
    {ν : Viscosity}
    {current next : ScaleTimeCurrent} :
    CompleteRoundStep ν current next →
      GeneratedFiniteRound ν current
  | .advance round => round

theorem next_eq_completeNext
    {ν : Viscosity}
    {current next : ScaleTimeCurrent}
    (step : CompleteRoundStep ν current next) :
    next = step.round.completeNext := by
  cases step
  rfl

end CompleteRoundStep

/--
The source responder returns a macro edge exactly when its old-q shell
producer terminates.  The endpoint is the versioned complete-support
physical write, not the legacy radial endpoint.
-/
noncomputable def generatedCompleteRoundRespond
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    Option (Response (CompleteRoundStep ν) current) :=
  match generatedRoundDisposition ν current with
  | .finite round =>
      some ⟨round.completeNext, .advance round⟩
  | .infinite _lineage _startsAtCurrent =>
      none

/-- Typed old-q lineage exposed by a stopped complete macro responder. -/
structure GeneratedCompleteInfiniteShellAt
    (current : ScaleTimeCurrent) : Type where
  lineage : GeneratedIntegerShellInfiniteLineage
  startsAtCurrent :
    lineage.current 0 = current.source

noncomputable def generatedCompleteRoundRespond_infiniteShell
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (stopped :
      generatedCompleteRoundRespond ν current = none) :
    GeneratedCompleteInfiniteShellAt current := by
  unfold generatedCompleteRoundRespond at stopped
  cases generated :
      generatedRoundDisposition ν current with
  | finite round =>
      rw [generated] at stopped
      contradiction
  | infinite lineage startsAtCurrent =>
      exact
        { lineage := lineage
          startsAtCurrent := startsAtCurrent }

/-! ## Maximal complete-round runtime -/

structure GeneratedCompleteRoundTerminalRun
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) : Type where
  terminal : ScaleTimeCurrent
  arrival :
    NativeReachable seed
      (generatedCompleteRoundRespond ν) terminal
  stopped :
    generatedCompleteRoundRespond ν terminal = none

noncomputable def GeneratedCompleteRoundTerminalRun.infiniteShell
    {ν : Viscosity}
    {seed : ScaleTimeCurrent}
    (run : GeneratedCompleteRoundTerminalRun ν seed) :
    GeneratedCompleteInfiniteShellAt run.terminal :=
  generatedCompleteRoundRespond_infiniteShell
    ν run.terminal run.stopped

private theorem exists_forcedCompleteRoundResponse
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedCompleteRoundTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        NativeReachable seed
          (generatedCompleteRoundRespond ν) current) :
    ∃ response : Response (CompleteRoundStep ν) node.1,
      generatedCompleteRoundRespond ν node.1 =
        some response := by
  cases generated :
      generatedCompleteRoundRespond ν node.1 with
  | none =>
      exact False.elim <|
        noTerminal <|
          ⟨{ terminal := node.1
             arrival := node.2
             stopped := generated }⟩
  | some response =>
      exact ⟨response, rfl⟩

private noncomputable def forcedCompleteRoundResponse
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedCompleteRoundTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        NativeReachable seed
          (generatedCompleteRoundRespond ν) current) :
    Response (CompleteRoundStep ν) node.1 :=
  Classical.choose
    (exists_forcedCompleteRoundResponse
      ν seed noTerminal node)

private theorem forcedCompleteRoundResponse_generated
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedCompleteRoundTerminalRun ν seed))
    (node :
      Σ current : ScaleTimeCurrent,
        NativeReachable seed
          (generatedCompleteRoundRespond ν) current) :
    generatedCompleteRoundRespond ν node.1 =
      some
        (forcedCompleteRoundResponse
          ν seed noTerminal node) :=
  Classical.choose_spec
    (exists_forcedCompleteRoundResponse
      ν seed noTerminal node)

private noncomputable def infiniteReachableCompleteRoundRun
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedCompleteRoundTerminalRun ν seed)) :
    ℕ →
      Σ current : ScaleTimeCurrent,
        NativeReachable seed
          (generatedCompleteRoundRespond ν) current
  | 0 =>
      ⟨seed, NativeReachable.initial⟩
  | index + 1 =>
      let node :=
        infiniteReachableCompleteRoundRun
          ν seed noTerminal index
      let response :=
        forcedCompleteRoundResponse
          ν seed noTerminal node
      ⟨response.1,
        NativeReachable.step node.2
          (forcedCompleteRoundResponse_generated
            ν seed noTerminal node)⟩

/-- Infinite lineage of exact complete-support physical macro writes. -/
structure GeneratedCompleteInfiniteRoundLineage
    (ν : Viscosity) : Type where
  current : ℕ → ScaleTimeCurrent
  step :
    ∀ index : ℕ,
      CompleteRoundStep ν
        (current index) (current (index + 1))
  generated :
    ∀ index : ℕ,
      generatedCompleteRoundRespond ν (current index) =
        some ⟨current (index + 1), step index⟩

private noncomputable def
    infiniteCompleteRoundLineageOfNoTerminal
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedCompleteRoundTerminalRun ν seed)) :
    GeneratedCompleteInfiniteRoundLineage ν where
  current index :=
    (infiniteReachableCompleteRoundRun
      ν seed noTerminal index).1
  step index :=
    (forcedCompleteRoundResponse
      ν seed noTerminal
      (infiniteReachableCompleteRoundRun
        ν seed noTerminal index)).2
  generated index :=
    forcedCompleteRoundResponse_generated
      ν seed noTerminal
      (infiniteReachableCompleteRoundRun
        ν seed noTerminal index)

@[simp] theorem
    infiniteCompleteRoundLineageOfNoTerminal_current_zero
    (ν : Viscosity)
    (seed : ScaleTimeCurrent)
    (noTerminal :
      ¬ Nonempty (GeneratedCompleteRoundTerminalRun ν seed)) :
    (infiniteCompleteRoundLineageOfNoTerminal
      ν seed noTerminal).current 0 =
      seed :=
  rfl

inductive GeneratedCompleteRoundRuntimeDisposition
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) : Type
  | shellInfinite
      (run : GeneratedCompleteRoundTerminalRun ν seed)
      (infiniteShell :
        GeneratedCompleteInfiniteShellAt run.terminal)
  | timeInfinite
      (lineage : GeneratedCompleteInfiniteRoundLineage ν)
      (startsAtSeed : lineage.current 0 = seed)

/--
One literal seed generates either a genuine shell-infinite terminal or an
infinite lineage of complete physical macro rounds.
-/
noncomputable def generatedCompleteRoundRuntimeDisposition
    (ν : Viscosity)
    (seed : ScaleTimeCurrent) :
    GeneratedCompleteRoundRuntimeDisposition ν seed := by
  by_cases terminalExists :
      Nonempty (GeneratedCompleteRoundTerminalRun ν seed)
  · let run := Classical.choice terminalExists
    exact .shellInfinite run run.infiniteShell
  · exact
      .timeInfinite
        (infiniteCompleteRoundLineageOfNoTerminal
          ν seed terminalExists)
        (infiniteCompleteRoundLineageOfNoTerminal_current_zero
          ν seed terminalExists)

/-! ## Exact finite-prefix physical write-back -/

namespace GeneratedCompleteInfiniteRoundLineage

def round
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (index : ℕ) :
    GeneratedFiniteRound ν (lineage.current index) :=
  (lineage.step index).round

def timeReceipt
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (index : ℕ) :
    GeneratedTimeAdvanceReceipt
      (lineage.round index).completeTimeCurrent.source
      ν.coeff :=
  (lineage.round index).completeTimeReceipt

theorem current_succ_eq_completeNext
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (index : ℕ) :
    lineage.current (index + 1) =
      (lineage.round index).completeNext :=
  (lineage.step index).next_eq_completeNext

theorem elapsed_succ
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (index : ℕ) :
    (lineage.current (index + 1)).elapsed =
      (lineage.current index).elapsed +
        (lineage.timeReceipt index).duration := by
  rw [lineage.current_succ_eq_completeNext index]
  change
    (lineage.round index).completeTimeCurrent.elapsed +
          (lineage.round index).completeTimeReceipt.duration =
      (lineage.current index).elapsed +
        (lineage.round index).completeTimeReceipt.duration
  rw [(lineage.round index).completeTimeCurrent_elapsed]

def physicalTime
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    (lineage.timeReceipt index).duration

theorem elapsed_eq_initial_add_physicalTime
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν) :
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

def fieldWeightedTime
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    (lineage.timeReceipt index).duration *
      (((lineage.timeReceipt index).fieldBound : ℝ) + 1)

theorem four_mul_fieldWeightedTime_eq_length
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
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
          simpa only [timeReceipt, mul_assoc] using
            (lineage.round index).completeTimeReceipt_fieldWeightedQuantum
    _ = length := by
      simp

/-! ## Complete-support anti-Zeno hard gate -/

theorem timeReceipt_duration_pos
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (index : ℕ) :
    0 < (lineage.timeReceipt index).duration :=
  (lineage.timeReceipt index).duration_pos

/--
If actual physical time remains below one horizon, the complete-support
field bounds generated by the same macro receipts escape every real bound.
-/
theorem fieldBound_unbounded_of_physicalTime_bounded
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (horizon : ℝ)
    (physicalTimeLe :
      ∀ length : ℕ,
        lineage.physicalTime length ≤ horizon) :
    ∀ bound : ℝ,
      ∃ index : ℕ,
        bound <
          ((lineage.timeReceipt index).fieldBound : ℝ) := by
  intro bound
  by_contra notEscape
  push Not at notEscape
  have boundNonneg : 0 ≤ bound :=
    (NNReal.coe_nonneg
      (lineage.timeReceipt 0).fieldBound).trans
        (notEscape 0)
  have horizonNonneg : 0 ≤ horizon := by
    have atZero := physicalTimeLe 0
    simpa [physicalTime] using atZero
  have weightedLe :
      ∀ length : ℕ,
        lineage.fieldWeightedTime length ≤
          (bound + 1) *
            lineage.physicalTime length := by
    intro length
    unfold fieldWeightedTime physicalTime
    calc
      (∑ index ∈ Finset.range length,
          (lineage.timeReceipt index).duration *
            (((lineage.timeReceipt index).fieldBound : ℝ) + 1)) ≤
          ∑ index ∈ Finset.range length,
            (lineage.timeReceipt index).duration *
              (bound + 1) := by
                apply Finset.sum_le_sum
                intro index indexMem
                exact
                  mul_le_mul_of_nonneg_left
                    (by linarith [notEscape index])
                    (lineage.timeReceipt_duration_pos index).le
      _ =
          (bound + 1) *
            (∑ index ∈ Finset.range length,
              (lineage.timeReceipt index).duration) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro index indexMem
            ring
  have weightedUniformLe :
      ∀ length : ℕ,
        lineage.fieldWeightedTime length ≤
          (bound + 1) * horizon := by
    intro length
    exact
      (weightedLe length).trans
        (mul_le_mul_of_nonneg_left
          (physicalTimeLe length)
          (by linarith))
  obtain ⟨length, lengthLarge⟩ :=
    exists_nat_gt
      (4 * ((bound + 1) * horizon))
  have exactDebt :=
    lineage.four_mul_fieldWeightedTime_eq_length length
  have debtLe :
      (length : ℝ) ≤
        4 * ((bound + 1) * horizon) := by
    calc
      (length : ℝ) =
          4 * lineage.fieldWeightedTime length :=
        exactDebt.symm
      _ ≤ 4 * ((bound + 1) * horizon) :=
        mul_le_mul_of_nonneg_left
          (weightedUniformLe length) (by norm_num)
  exact (not_lt_of_ge debtLe) lengthLarge

/--
An infinite lineage of complete actual time writes cannot keep both
physical time and its source-generated complete field bounded.
-/
theorem physicalTime_or_fieldBound_unbounded
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν) :
    (∀ horizon : ℝ,
        ∃ length : ℕ,
          horizon < lineage.physicalTime length) ∨
      (∀ bound : ℝ,
        ∃ index : ℕ,
          bound <
            ((lineage.timeReceipt index).fieldBound : ℝ)) := by
  by_cases timeUnbounded :
      ∀ horizon : ℝ,
        ∃ length : ℕ,
          horizon < lineage.physicalTime length
  · exact Or.inl timeUnbounded
  · right
    push Not at timeUnbounded
    obtain ⟨horizon, physicalTimeLe⟩ :=
      timeUnbounded
    exact
      lineage.fieldBound_unbounded_of_physicalTime_bounded
        horizon physicalTimeLe

/--
Type-valued anti-Zeno producer retained for downstream runtime composition.
Unlike the propositional readout above, this carrier can drive a later
source-owned disposition without reconstructing data from `Or`.
-/
inductive GeneratedCompleteInfiniteRoundAntiZenoDisposition
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν) : Type
  | physicalTimeUnbounded
      (escape :
        ∀ horizon : ℝ,
          ∃ length : ℕ,
            horizon < lineage.physicalTime length)
  | fieldBoundUnbounded
      (escape :
        ∀ bound : ℝ,
          ∃ index : ℕ,
            bound <
              ((lineage.timeReceipt index).fieldBound : ℝ))

noncomputable def antiZenoDisposition
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν) :
    GeneratedCompleteInfiniteRoundAntiZenoDisposition lineage := by
  by_cases timeUnbounded :
      ∀ horizon : ℝ,
        ∃ length : ℕ,
          horizon < lineage.physicalTime length
  · exact .physicalTimeUnbounded timeUnbounded
  · push Not at timeUnbounded
    let horizon : ℝ :=
      Classical.choose timeUnbounded
    have physicalTimeLe :
        ∀ length : ℕ,
          lineage.physicalTime length ≤ horizon :=
      Classical.choose_spec timeUnbounded
    exact
      .fieldBoundUnbounded
        (lineage.fieldBound_unbounded_of_physicalTime_bounded
          horizon physicalTimeLe)

/-- Vector sum of the old-q traces, retained round-by-round until after
their local physical consumers have run. -/
def shellTraceSum
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (length : ℕ) : ComplexVorticityHilbertState :=
  ∑ index ∈ Finset.range length,
    generatedIntegerShellPathStateTrace
      (lineage.round index).shellRun.arrival

/-- Vector sum of the actual unforced generator integrals. -/
def unforcedIntegralSum
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (length : ℕ) : ComplexVorticityHilbertState :=
  ∑ index ∈ Finset.range length,
    ∫ time in (0 : ℝ)..
        (lineage.timeReceipt index).duration,
      finiteStateVorticityGenerator
        (generatedSupport
          (lineage.round index).completeTimeCurrent.source)
        ν.coeff
        ((lineage.timeReceipt index).trajectory time)

/--
Exact whole-carrier transport along every finite prefix:

```text
physical(final) - physical(initial)
  = Σ already-consumed shell traces
    + Σ actual unforced generator integrals.
```
-/
theorem prefixMacroPhysicalWriteBack
    {ν : Viscosity}
    (lineage : GeneratedCompleteInfiniteRoundLineage ν)
    (length : ℕ) :
    generatedComplexVorticityState
          (lineage.current length).source
          (generatedSupport
            (lineage.current length).source) -
        generatedComplexVorticityState
          (lineage.current 0).source
          (generatedSupport
            (lineage.current 0).source) =
      lineage.shellTraceSum length +
        lineage.unforcedIntegralSum length := by
  induction length with
  | zero =>
      simp [shellTraceSum, unforcedIntegralSum]
  | succ length inductionHypothesis =>
      have successorStateEq :
          generatedComplexVorticityState
              (lineage.current (length + 1)).source
              (generatedSupport
                (lineage.current (length + 1)).source) =
            generatedComplexVorticityState
              (lineage.round length).completeNext.source
              (generatedSupport
                (lineage.round length).completeNext.source) :=
        congrArg
          (fun next : ScaleTimeCurrent =>
            generatedComplexVorticityState next.source
              (generatedSupport next.source))
          (lineage.current_succ_eq_completeNext length)
      have oneRound :=
        @ThreeDimensionalVorticityCoefficientGeneratedScaleTimeShellRound.GeneratedFiniteRound.completeMacroPhysicalWriteBack_eq_shellTrace_add_unforcedIntegral
          ν (lineage.current length) (lineage.round length)
      calc
        generatedComplexVorticityState
              (lineage.current (length + 1)).source
              (generatedSupport
                (lineage.current (length + 1)).source) -
            generatedComplexVorticityState
              (lineage.current 0).source
              (generatedSupport
                (lineage.current 0).source) =
          generatedComplexVorticityState
                (lineage.round length).completeNext.source
                (generatedSupport
                  (lineage.round length).completeNext.source) -
              generatedComplexVorticityState
                (lineage.current 0).source
                (generatedSupport
                  (lineage.current 0).source) := by
            rw [successorStateEq]
        _ =
          (generatedComplexVorticityState
                (lineage.round length).completeNext.source
                (generatedSupport
                  (lineage.round length).completeNext.source) -
              generatedComplexVorticityState
                (lineage.current length).source
                (generatedSupport
                  (lineage.current length).source)) +
            (generatedComplexVorticityState
                (lineage.current length).source
                (generatedSupport
                  (lineage.current length).source) -
              generatedComplexVorticityState
                (lineage.current 0).source
                (generatedSupport
                  (lineage.current 0).source)) := by
            abel
        _ =
          (generatedIntegerShellPathStateTrace
                (lineage.round length).shellRun.arrival +
              ∫ time in (0 : ℝ)..
                  (lineage.round length).completeTimeReceipt.duration,
                finiteStateVorticityGenerator
                  (generatedSupport
                    (lineage.round length).completeTimeCurrent.source)
                  ν.coeff
                  ((lineage.round length).completeTimeReceipt.trajectory
                    time)) +
            (lineage.shellTraceSum length +
              lineage.unforcedIntegralSum length) := by
            rw [oneRound, inductionHypothesis]
        _ =
          lineage.shellTraceSum (length + 1) +
            lineage.unforcedIntegralSum (length + 1) := by
            unfold shellTraceSum unforcedIntegralSum
            simp only [timeReceipt, Finset.sum_range_succ]
            abel

end GeneratedCompleteInfiniteRoundLineage

end

end
    ThreeDimensionalVorticityCoefficientGeneratedCompleteScaleTimeRoundRuntime
end NavierStokes
end SaturationMonoid
