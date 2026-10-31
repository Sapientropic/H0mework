import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeHistory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.SamePath
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.LocalRenewal

/-! Every continuation is read at an actual source cut.  The programme
retains the source's current-dependent emitter; its finite observations
are the original root visits, not a replacement future-state table. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.GeneratedLaw

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Source.ProgrammeControl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def programAt (cut : Nat) : RawProgram Party Good Port Technology Instrument where
  law := input.law
  initial := ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (cut + 1)).current
  body := ProgrammeSource.wordAt input

omit [DecidableEq Port] in
theorem actual_word_is_source_emission (index : Nat) :
    ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input (index + 1)).current =
      ProgrammeSource.wordAt input
        (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (index + 1)).current) := by
  change ProgrammeSource.rawEvent input
      (ProgrammeSource.next input (ProgrammeHistory.visitAt input index).current) =
    ProgrammeSource.wordAt input (ProgrammeSource.rawCurrent input
      (ProgrammeSource.next input (ProgrammeHistory.visitAt input index).current))
  cases (ProgrammeHistory.visitAt input index).current <;> rfl

omit [DecidableEq Port] in
theorem original_root_generates_every_finite_prefix (cut length : Nat) :
    ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (cut + length + 1)).current =
      (programAt input cut).currentAt length := by
  induction length with
  | zero => rfl
  | succ length prior =>
      change ProgrammeSource.rawCurrent input
        (ProgrammeSource.next input (ProgrammeHistory.visitAt input (cut + length + 1)).current) = _
      rw [ProgrammeSource.actual_raw_next, actual_word_is_source_emission, prior]
      rfl

omit [DecidableEq Port] in
theorem original_instruction_trace_is_literal (cut offset : Nat) :
    input.law.rawItems
        (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (cut + offset + 1)).current)
        (ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input (cut + offset + 1)).current) =
      (programAt input cut).law.rawItems ((programAt input cut).currentAt offset)
        ((programAt input cut).emit ((programAt input cut).currentAt offset)) := by
  rw [actual_word_is_source_emission, original_root_generates_every_finite_prefix]
  rfl

omit [DecidableEq Port] in
/-- The universal alternative is consumed on this very source's trajectory.
The family is a relation readout on its original intermediate trace items. -/
theorem source_native_structural_alternative (cut : Nat) (group : List Party)
    (family : (offset : Nat) → At (programAt input cut) offset → List Port) :
    (∀ length, ProgrammeSource.rawCurrent input
      (ProgrammeHistory.visitAt input (cut + length + 1)).current =
        (programAt input cut).currentAt length) ∧
    (Recurrently (ActualControlAt (programAt input cut) family) ∨
      Recurrently (OriginalObstructionAt (programAt input cut) group) ∨
      ∃ start, ActualIndependentTail (programAt input cut) group family start) :=
  ⟨original_root_generates_every_finite_prefix input cut,
    control_or_original_obstruction_or_actual_independent_tail (programAt input cut) group family⟩

omit [DecidableEq Port] in
theorem local_source_generates_actual_root_continuations (cut : Nat)
    (members : RawCurrent Party Good Technology Instrument → List Party)
    (invariant : RawCurrent Party Good Technology Instrument → Prop)
    (initial : invariant (ProgrammeSource.rawCurrent input
      (ProgrammeHistory.visitAt input (cut + 1)).current))
    (preserved : ∀ current, invariant current → invariant ((programAt input cut).tick current))
    (available : ∀ current, invariant current →
      Exit.LocalRenewal.attempt (programAt input cut) members current ≠ none) :
    ∀ start,
      Exit.LocalRenewal.PaidTail (programAt input cut) members start ∧
      (∀ length, Exit.LocalRenewal.run (programAt input cut) members
        (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (cut + start + 1)).current)
        length = some (ProgrammeSource.rawCurrent input
          (ProgrammeHistory.visitAt input (cut + (start + length) + 1)).current)) := by
  have generated := Exit.LocalRenewal.local_source_generates_paid_continuation
    (programAt input cut) members invariant initial preserved available
  intro start
  refine ⟨generated start, ?_⟩
  intro length
  rw [original_root_generates_every_finite_prefix, original_root_generates_every_finite_prefix]
  exact (generated start).1 length

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.GeneratedLaw
