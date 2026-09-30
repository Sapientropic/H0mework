import H0mework.NavierStokes.ScaleControl.TimeReflexiveResponse

/-!
# Source-generated scale/time responsibility ledger

The total scale-or-time responder already makes the decisive source choice:
one reflexive event either emits a nonzero integer-shell receipt and writes
the native shell successor, or emits a positive physical-time receipt and
writes the recompiled physical endpoint.  This module iterates that producer
without introducing a continuation branch.

For the canonical `Nat`-indexed write chain it records two complementary
quantities:

* squared shell-receipt mass;
* actual elapsed physical time.

Every event contributes strictly to exactly one of them.  Physical elapsed
time is the exact sum of the time receipts, while the combined responsibility
ledger is strictly increasing at every source-generated write.  This is the
finite-prefix seam needed by the receipt-square / time-occupancy attack; it
does not assert a uniform quantum, non-Zeno time, or a global PDE budget.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveLedger

open scoped BigOperators

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse

noncomputable section

namespace ScaleTimeObservation

/-- Positive shell quantum read from a shell event, zero on a time event. -/
def shellQuantum
    {ν : Viscosity} :
    Observation ν → ℝ
  | .shell receipt =>
      coefficientCarrierNormSq
        (generatedIntegerShellReceiptTrace receipt)
  | .time _source _receipt => 0

/-- Positive physical duration read from a time event, zero on a shell event. -/
def timeDuration
    {ν : Viscosity} :
    Observation ν → ℝ
  | .shell _receipt => 0
  | .time _source receipt => receipt.duration

/-- Canonical Picard field bound carried by a time event, zero on a shell event. -/
def timeFieldBound
    {ν : Viscosity} :
    Observation ν → ℝ
  | .shell _receipt => 0
  | .time _source receipt => receipt.fieldBound

/-- Real-valued indicator of a generated physical-time write. -/
def timeEventMass
    {ν : Viscosity} :
    Observation ν → ℝ
  | .shell _receipt => 0
  | .time _source _receipt => 1

/--
The combined cost of one event.  The shell contribution is squared because
this is the quantity entering the existing orthogonal receipt ledger.
-/
def responsibilityQuantum
    {ν : Viscosity}
    (observation : Observation ν) : ℝ :=
  shellQuantum observation ^ 2 +
    timeDuration observation

@[simp] theorem shellQuantum_shell
    {ν : Viscosity}
    (receipt : GeneratedIntegerShellReceipt) :
    shellQuantum (ν := ν) (.shell receipt) =
      coefficientCarrierNormSq
        (generatedIntegerShellReceiptTrace receipt) :=
  rfl

@[simp] theorem shellQuantum_time
    {ν : Viscosity}
    (source : RawVorticityFourierSource)
    (receipt :
      GeneratedTimeAdvanceReceipt source ν.coeff) :
    shellQuantum (.time source receipt) = 0 :=
  rfl

@[simp] theorem timeDuration_shell
    {ν : Viscosity}
    (receipt : GeneratedIntegerShellReceipt) :
    timeDuration (ν := ν) (.shell receipt) = 0 :=
  rfl

@[simp] theorem timeDuration_time
    {ν : Viscosity}
    (source : RawVorticityFourierSource)
    (receipt :
      GeneratedTimeAdvanceReceipt source ν.coeff) :
    timeDuration (.time source receipt) =
      receipt.duration :=
  rfl

/--
Every time event pays one exact field-weighted time quantum.  Thus a short
physical duration can occur only together with a correspondingly large
source-generated field bound.
-/
theorem four_mul_timeDuration_mul_fieldBound_add_one
    {ν : Viscosity}
    (observation : Observation ν) :
    4 * timeDuration observation *
        (timeFieldBound observation + 1) =
      timeEventMass observation := by
  cases observation with
  | shell receipt =>
      norm_num [timeDuration, timeFieldBound, timeEventMass]
  | time source receipt =>
      exact
        receipt.four_mul_duration_mul_fieldBound_add_one

end ScaleTimeObservation

/-! ## One event pays exactly one responsibility channel -/

/--
At an arbitrary current the source-generated read/write event has exactly one
positive responsibility channel.

The shell branch preserves elapsed physical time.  The time branch advances
elapsed time by the duration read by that very event.  There is no third
`continuation` outcome.
-/
theorem oneStep_exact_responsibility
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    (0 <
          ScaleTimeObservation.shellQuantum
            ((scaleTimeReflexiveQuery ν).read current) ∧
        ScaleTimeObservation.timeDuration
            ((scaleTimeReflexiveQuery ν).read current) = 0 ∧
        ((scaleTimeReflexiveQuery ν).write current).elapsed =
          current.elapsed) ∨
      (ScaleTimeObservation.shellQuantum
            ((scaleTimeReflexiveQuery ν).read current) = 0 ∧
        0 <
          ScaleTimeObservation.timeDuration
            ((scaleTimeReflexiveQuery ν).read current) ∧
        ((scaleTimeReflexiveQuery ν).write current).elapsed =
          current.elapsed +
            ScaleTimeObservation.timeDuration
              ((scaleTimeReflexiveQuery ν).read current)) := by
  cases generated :
      generatedIntegerShellRespond current.source with
  | some response =>
      have run :=
        scaleTimeReflexiveQuery_run_of_some
          ν current response generated
      have readEq :
          (scaleTimeReflexiveQuery ν).read current =
            .shell
              (receiptOfResponse
                current.source response generated) :=
        congrArg Prod.fst run
      have writeEq :
          (scaleTimeReflexiveQuery ν).write current =
            shellTarget current response :=
        congrArg Prod.snd run
      left
      rw [readEq, writeEq]
      exact
        ⟨generatedIntegerShellReceiptTrace_normSq_pos
            (receiptOfResponse
              current.source response generated),
          rfl,
          rfl⟩
  | none =>
      have run :=
        scaleTimeReflexiveQuery_run_of_none
          ν current generated
      have readEq :
          (scaleTimeReflexiveQuery ν).read current =
            .time current.source
              (generatedTimeAdvanceReceipt
                current.source ν.coeff) :=
        congrArg Prod.fst run
      have writeEq :
          (scaleTimeReflexiveQuery ν).write current =
            timeTarget ν current :=
        congrArg Prod.snd run
      right
      rw [readEq, writeEq]
      exact
        ⟨rfl,
          (generatedTimeAdvanceReceipt
              current.source ν.coeff).duration_pos,
          rfl⟩

/-- Every actual scale-or-time event carries a strictly positive cost. -/
theorem oneStep_responsibilityQuantum_pos
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    0 <
      ScaleTimeObservation.responsibilityQuantum
        ((scaleTimeReflexiveQuery ν).read current) := by
  rcases oneStep_exact_responsibility ν current with
    shell | time
  · unfold ScaleTimeObservation.responsibilityQuantum
    rw [shell.2.1]
    simpa using sq_pos_of_pos shell.1
  · unfold ScaleTimeObservation.responsibilityQuantum
    rw [time.1]
    simpa using time.2.1

/-! ## Canonical source-owned write chain -/

/-- Current written after exactly `occurrence` total source responses. -/
def currentAt
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (occurrence : ℕ) :
    ScaleTimeCurrent :=
  (reflexiveQueryIteratedTimeField
    (scaleTimeReflexiveQuery ν) initial).stateAt occurrence

/-- Observation emitted by the exact event at `occurrence`. -/
def observationAt
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (occurrence : ℕ) :
    Observation ν :=
  (scaleTimeReflexiveQuery ν).read
    (currentAt ν initial occurrence)

@[simp] theorem currentAt_zero
    (ν : Viscosity)
    (initial : ScaleTimeCurrent) :
    currentAt ν initial 0 = initial :=
  rfl

theorem currentAt_succ
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (occurrence : ℕ) :
    currentAt ν initial (occurrence + 1) =
      (scaleTimeReflexiveQuery ν).write
        (currentAt ν initial occurrence) := by
  exact
    reflexiveQueryIterated_stateAt_succ
      (scaleTimeReflexiveQuery ν) initial occurrence

/-- Exact source-generated disposition at every canonical occurrence. -/
def dispositionAt
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (occurrence : ℕ) :
    GeneratedDisposition ν
      (currentAt ν initial occurrence) :=
  generatedDisposition ν
    (currentAt ν initial occurrence)

/-- Every occurrence pays exactly one of the two responsibility channels. -/
theorem exact_responsibilityAt
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (occurrence : ℕ) :
    (0 <
          ScaleTimeObservation.shellQuantum
            (observationAt ν initial occurrence) ∧
        ScaleTimeObservation.timeDuration
            (observationAt ν initial occurrence) = 0 ∧
        (currentAt ν initial (occurrence + 1)).elapsed =
          (currentAt ν initial occurrence).elapsed) ∨
      (ScaleTimeObservation.shellQuantum
            (observationAt ν initial occurrence) = 0 ∧
        0 <
          ScaleTimeObservation.timeDuration
            (observationAt ν initial occurrence) ∧
        (currentAt ν initial (occurrence + 1)).elapsed =
          (currentAt ν initial occurrence).elapsed +
            ScaleTimeObservation.timeDuration
              (observationAt ν initial occurrence)) := by
  rw [currentAt_succ]
  exact
    oneStep_exact_responsibility ν
      (currentAt ν initial occurrence)

/-! ## Exact finite-prefix accumulation -/

/-- Existing receipt-square channel accumulated along the total write chain. -/
def shellReceiptSquareMass
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) : ℝ :=
  ∑ occurrence ∈ Finset.range length,
    ScaleTimeObservation.shellQuantum
      (observationAt ν initial occurrence) ^ 2

/-- Sum of the actual positive physical durations emitted along the chain. -/
def physicalTimeOccupancy
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) : ℝ :=
  ∑ occurrence ∈ Finset.range length,
    ScaleTimeObservation.timeDuration
      (observationAt ν initial occurrence)

/--
Time occupancy weighted by the canonical Picard field bound generated at the
same event.
-/
def fieldWeightedTimeOccupancy
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) : ℝ :=
  ∑ occurrence ∈ Finset.range length,
    ScaleTimeObservation.timeDuration
        (observationAt ν initial occurrence) *
      (ScaleTimeObservation.timeFieldBound
          (observationAt ν initial occurrence) + 1)

/-- Number of physical-time events, regarded as a real prefix mass. -/
def timeEventCountMass
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) : ℝ :=
  ∑ occurrence ∈ Finset.range length,
    ScaleTimeObservation.timeEventMass
      (observationAt ν initial occurrence)

/-- Total source responsibility accumulated by a finite prefix. -/
def responsibilityMass
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) : ℝ :=
  ∑ occurrence ∈ Finset.range length,
    ScaleTimeObservation.responsibilityQuantum
      (observationAt ν initial occurrence)

@[simp] theorem shellReceiptSquareMass_zero
    (ν : Viscosity)
    (initial : ScaleTimeCurrent) :
    shellReceiptSquareMass ν initial 0 = 0 := by
  simp [shellReceiptSquareMass]

theorem shellReceiptSquareMass_succ
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) :
    shellReceiptSquareMass ν initial (length + 1) =
      shellReceiptSquareMass ν initial length +
        ScaleTimeObservation.shellQuantum
          (observationAt ν initial length) ^ 2 := by
  simp [shellReceiptSquareMass, Finset.sum_range_succ]

@[simp] theorem physicalTimeOccupancy_zero
    (ν : Viscosity)
    (initial : ScaleTimeCurrent) :
    physicalTimeOccupancy ν initial 0 = 0 := by
  simp [physicalTimeOccupancy]

theorem physicalTimeOccupancy_succ
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) :
    physicalTimeOccupancy ν initial (length + 1) =
      physicalTimeOccupancy ν initial length +
        ScaleTimeObservation.timeDuration
          (observationAt ν initial length) := by
  simp [physicalTimeOccupancy, Finset.sum_range_succ]

theorem responsibilityMass_succ
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) :
    responsibilityMass ν initial (length + 1) =
      responsibilityMass ν initial length +
        ScaleTimeObservation.responsibilityQuantum
          (observationAt ν initial length) := by
  simp [responsibilityMass, Finset.sum_range_succ]

/--
The elapsed-time state is not metadata: it is exactly the accumulated time
receipt channel of the same source-generated write prefix.
-/
theorem currentAt_elapsed_eq_initial_add_physicalTimeOccupancy
    (ν : Viscosity)
    (initial : ScaleTimeCurrent) :
    ∀ length : ℕ,
      (currentAt ν initial length).elapsed =
        initial.elapsed +
          physicalTimeOccupancy ν initial length
  | 0 => by
      simp
  | length + 1 => by
      rcases exact_responsibilityAt
          ν initial length with shell | time
      · rw [shell.2.2]
        rw [
          currentAt_elapsed_eq_initial_add_physicalTimeOccupancy
            ν initial length,
          physicalTimeOccupancy_succ,
          shell.2.1,
          add_zero]
      · rw [time.2.2]
        rw [
          currentAt_elapsed_eq_initial_add_physicalTimeOccupancy
            ν initial length,
          physicalTimeOccupancy_succ]
        ring

/-- The combined ledger is exactly shell-square mass plus elapsed time. -/
theorem responsibilityMass_eq_shell_add_time
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) :
    responsibilityMass ν initial length =
      shellReceiptSquareMass ν initial length +
        physicalTimeOccupancy ν initial length := by
  simp only [
    responsibilityMass,
    ScaleTimeObservation.responsibilityQuantum,
    shellReceiptSquareMass,
    physicalTimeOccupancy,
    Finset.sum_add_distrib]

/--
Exact anti-Zeno ledger: every generated time write contributes precisely
`1/4` after weighting its duration by its own canonical field bound.
-/
theorem four_mul_fieldWeightedTimeOccupancy_eq_timeEventCountMass
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) :
    4 * fieldWeightedTimeOccupancy ν initial length =
      timeEventCountMass ν initial length := by
  unfold fieldWeightedTimeOccupancy timeEventCountMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro occurrence occurrenceMem
  simpa only [mul_assoc] using
    ScaleTimeObservation.four_mul_timeDuration_mul_fieldBound_add_one
      (observationAt ν initial occurrence)

/-- Every further source-generated write strictly increases responsibility. -/
theorem responsibilityMass_strictMono_step
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) :
    responsibilityMass ν initial length <
      responsibilityMass ν initial (length + 1) := by
  rw [responsibilityMass_succ]
  exact
    lt_add_of_pos_right _
      (oneStep_responsibilityQuantum_pos ν
        (currentAt ν initial length))

/--
No nonempty generated prefix is silent in the joint receipt-square / physical
time carrier.
-/
theorem responsibilityMass_pos
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    {length : ℕ}
    (lengthPos : 0 < length) :
    0 < responsibilityMass ν initial length := by
  obtain ⟨prior, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt lengthPos)
  have nonneg :
      0 ≤ responsibilityMass ν initial prior := by
    apply Finset.sum_nonneg
    intro occurrence occurrenceMem
    exact
      (oneStep_responsibilityQuantum_pos ν
        (currentAt ν initial occurrence)).le
  rw [responsibilityMass_succ]
  exact
    add_pos_of_nonneg_of_pos nonneg
      (oneStep_responsibilityQuantum_pos ν
        (currentAt ν initial prior))

/--
The repeated stateful program executes precisely this source-owned prefix;
the ledger above therefore measures actual reflexive reads and writes, not a
caller-supplied horizon path.
-/
theorem repeatEval_canonical
    (ν : Viscosity)
    (initial : ScaleTimeCurrent)
    (length : ℕ) :
    StatefulGenAlg.repeatEval
        (reflexiveQueryPrimitive
          (scaleTimeReflexiveQuery ν))
        (reflexiveQueryStatefulPlan
          (scaleTimeReflexiveQuery ν))
        length initial
        (reflexiveQueryIteratedObservationTrace
          (scaleTimeReflexiveQuery ν) initial length)
        (currentAt ν initial length) := by
  exact
    reflexiveStatefulPlan_repeatEval_canonical
      (scaleTimeReflexiveQuery ν) initial length

end

end ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveLedger
end NavierStokes
end SaturationMonoid
