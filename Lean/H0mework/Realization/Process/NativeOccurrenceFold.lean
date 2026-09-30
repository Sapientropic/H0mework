import H0mework.Realization.Process.NativeBoundedRun

/-!
# Exact occurrence fold of a source-generated reachability proof

`NativeReachable` is the least proof-relevant closure of a dependent source
responder.  Each `.step` retains the exact response and literal producer
equality, but the core module deliberately exposes no chronological table.

This module folds an arbitrary finite reachability proof into the existing
`BoundedRun.ActualOccurrence` carrier.  The fold is source chronological:
each new `.step` appends exactly one row containing its current, next state,
edge, and producer equality.  It introduces no fuel, target, route length,
coverage family, or response certificate.

The same fold composes under `prependNativeReachable` and agrees exactly with
the occurrence table already stored by an inclusive bounded run.  These are
generic proof-cost donors.  They do not interpret an occurrence, generate a
nonzero invariant, or choose a domain-specific consumer.
-/

namespace SaturationMonoid
namespace SourceGeneratedNativeResponseDisposition

open SourceGeneratedNativeBoundedRun

universe uState uStep

variable {State : Type uState}
variable {Step : State → State → Type uStep}

namespace NativeReachable

/-- Chronological exact source occurrences in one proof-relevant finite
arrival. -/
def actualOccurrenceTable
    {initial current : State}
    {respond : ∀ state : State, Option (Response Step state)} :
    NativeReachable initial respond current →
      List (SourceGeneratedNativeBoundedRun.BoundedRun.ActualOccurrence respond)
  | .initial => []
  | @NativeReachable.step _ _ _ _ prior arrival response generated =>
      (actualOccurrenceTable arrival).concat
        ⟨prior, response.1, ⟨response.2, generated⟩⟩

/-- Executing one more literal source response appends exactly that occurrence
to the chronological table. -/
@[simp] theorem actualOccurrenceTable_step
    {initial current : State}
    {respond : ∀ state : State, Option (Response Step state)}
    (arrival : NativeReachable initial respond current)
    (response : Response Step current)
    (generated : respond current = some response) :
    (NativeReachable.step arrival generated).actualOccurrenceTable =
      arrival.actualOccurrenceTable.concat
        ⟨current, response.1, ⟨response.2, generated⟩⟩ :=
  rfl

@[simp] theorem actualOccurrenceTable_length
    {initial current : State}
    {respond : ∀ state : State, Option (Response Step state)}
    (arrival : NativeReachable initial respond current) :
    arrival.actualOccurrenceTable.length = arrival.occurrence := by
  induction arrival with
  | initial => rfl
  | step arrival generated inductionHypothesis =>
      simp [actualOccurrenceTable, occurrence, inductionHypothesis]

/-- Occurrence chronology concatenates under the already existing reachability
prepend operation. -/
theorem actualOccurrenceTable_prependNativeReachable
    {respond : ∀ state : State, Option (Response Step state)}
    {initial current endpoint : State}
    (headArrival : NativeReachable initial respond current)
    (suffix : NativeReachable current respond endpoint) :
    (SourceGeneratedNativeBoundedRun.BoundedRun.prependNativeReachable
        headArrival suffix).actualOccurrenceTable =
      headArrival.actualOccurrenceTable ++ suffix.actualOccurrenceTable := by
  induction suffix with
  | initial =>
      simp only [SourceGeneratedNativeBoundedRun.BoundedRun.prependNativeReachable,
        actualOccurrenceTable, List.append_nil]
  | @step prior suffix response generated inductionHypothesis =>
      simp only [SourceGeneratedNativeBoundedRun.BoundedRun.prependNativeReachable,
        actualOccurrenceTable]
      rw [inductionHypothesis]
      simp [List.concat_eq_append, List.append_assoc]

end NativeReachable

end SourceGeneratedNativeResponseDisposition

namespace SourceGeneratedNativeBoundedRun.BoundedRun

open SourceGeneratedNativeResponseDisposition

universe uState uStep

variable {State : Type uState}
variable {Step : State → State → Type uStep}

/-- The least reachability reconstructed from a bounded run contains exactly
the bounded run's executed occurrence table, not merely the same length. -/
theorem endNativeReachable_actualOccurrenceTable
    {respond : ∀ state : State, Option (Response Step state)}
    {current : State}
    {fuel : Nat}
    (run : SourceGeneratedNativeBoundedRun.BoundedRun respond current fuel) :
    run.endNativeReachable.actualOccurrenceTable = run.actualOccurrenceTable := by
  induction run with
  | terminal stopped => rfl
  | cutoff transition => rfl
  | @continued current next fuel transition rest inductionHypothesis =>
      cases transition with
      | mk edge generated =>
          change
            (prependNativeReachable
                (.step (.initial) generated)
                rest.endNativeReachable).actualOccurrenceTable =
              ⟨current, next, ⟨edge, generated⟩⟩ :: rest.actualOccurrenceTable
          rw [NativeReachable.actualOccurrenceTable_prependNativeReachable]
          simp only [NativeReachable.actualOccurrenceTable]
          rw [inductionHypothesis]
          simp [List.concat_eq_append]

/-- A live cutoff response remains outside the executed table.  If that exact
response is subsequently executed, it becomes the unique new final row. -/
theorem endNativeReachable_step_actualOccurrenceTable
    {respond : ∀ state : State, Option (Response Step state)}
    {current : State}
    {fuel : Nat}
    (run : SourceGeneratedNativeBoundedRun.BoundedRun respond current fuel)
    {next : State}
    (transition : NativeResponseStep respond run.endState next) :
    (NativeReachable.step
        run.endNativeReachable transition.generated).actualOccurrenceTable =
      run.actualOccurrenceTable.concat
        ⟨run.endState, next, transition⟩ := by
  cases transition with
  | mk edge generated =>
      rw [SourceGeneratedNativeResponseDisposition.NativeReachable.actualOccurrenceTable_step,
        run.endNativeReachable_actualOccurrenceTable]

end SourceGeneratedNativeBoundedRun.BoundedRun

end SaturationMonoid
