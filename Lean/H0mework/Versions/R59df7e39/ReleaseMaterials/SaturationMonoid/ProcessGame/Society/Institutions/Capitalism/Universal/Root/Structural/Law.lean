import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Family
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Interpretation.Trajectory

/-! The universal mouth has one source input.  Its actors, relation family,
original instructions, responsibilities and continuation all come from that
same root; neither family labels nor a completed future are public inputs. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Source.ProgrammeControl Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def ControlAt (cut : Nat) : Nat → Prop :=
  ActualControlAt (GeneratedLaw.programAt input cut) (family input cut)

def ResidualAt (cut : Nat) : Nat → Prop :=
  Exit.Interpretation.ResidualAt (GeneratedLaw.programAt input cut) (family input cut) (GeneratedLaw.members input)

def IndependentTail (cut start : Nat) : Prop :=
  Exit.Interpretation.PaidInterpretedTail (GeneratedLaw.programAt input cut) (family input cut)
    (GeneratedLaw.members input) start

def Total : Prop := ∀ cut,
  Recurrently (ControlAt input cut) ∨ Recurrently (ResidualAt input cut) ∨ ∃ start, IndependentTail input cut start

theorem all_source_forms_total : Total input := by
  intro cut
  exact Exit.Interpretation.original_control_or_residual_or_paid_tail
    (GeneratedLaw.programAt input cut) (family input cut) (GeneratedLaw.members input)

theorem no_independent_tail_forces_original_recurrence (cut : Nat)
    (noTail : ∀ start, ¬ IndependentTail input cut start) :
    Recurrently (ControlAt input cut) ∨ Recurrently (ResidualAt input cut) := by
  rcases all_source_forms_total input cut with control | residual | ⟨start, independent⟩
  · exact Or.inl control
  · exact Or.inr residual
  · exact False.elim (noTail start independent)

theorem paid_tail_is_the_original_generated_future (cut start : Nat)
    (independent : IndependentTail input cut start) (length : Nat) :
    Exit.LocalRenewal.run (GeneratedLaw.programAt input cut) (GeneratedLaw.members input)
      (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (cut + start + 1)).current) length =
    some (ProgrammeSource.rawCurrent input (ProgrammeHistory.visitAt input (cut + (start + length) + 1)).current) := by
  rw [GeneratedLaw.original_root_generates_every_finite_prefix,
    GeneratedLaw.original_root_generates_every_finite_prefix]
  exact independent.1.1 length

theorem unexplained_item_has_original_row (cut offset : Nat)
    (item : At (GeneratedLaw.programAt input cut) offset)
    (_unknown : Exit.Interpretation.UnexplainedAt input.law
      ((GeneratedLaw.programAt input cut).currentAt offset)
      ((GeneratedLaw.programAt input cut).emit ((GeneratedLaw.programAt input cut).currentAt offset))
      (family input cut offset) (GeneratedLaw.members input ((GeneratedLaw.programAt input cut).currentAt offset)) item) :
    (originalOrigin input cut offset item).instruction? input = some item.val ∧
      Nonempty (LedgerEntryDispositionAt (ProgrammeSource.N input)
        ((originalOrigin input cut offset item).row input)) :=
  ⟨(original_item_is_not_replayed input cut offset item).2,
    ⟨(originalOrigin input cut offset item).disposition input⟩⟩

omit [DecidableEq Port] in
theorem unpaid_needs_keep_original_M0 (cut offset : Nat)
    (unpaid : Law.NativeTrajectory.UnpaidAt (GeneratedLaw.programAt input cut) (GeneratedLaw.members input) offset) :
    ∃ person ∈ GeneratedLaw.members input ((GeneratedLaw.programAt input cut).currentAt offset),
      Nonempty (ActualBirth.At input (ProgrammeHistory.visitAt input (cut + offset + 1)) person) ∧
      (¬ Exit.Necessity.BundlePaid input.law ((GeneratedLaw.programAt input cut).currentAt offset)
        ((GeneratedLaw.programAt input cut).emit ((GeneratedLaw.programAt input cut).currentAt offset)) person
        (input.law.necessities ((GeneratedLaw.programAt input cut).currentAt offset) person) .necessity ∨
       ¬ Exit.Necessity.BundlePaid input.law ((GeneratedLaw.programAt input cut).currentAt offset)
        ((GeneratedLaw.programAt input cut).emit ((GeneratedLaw.programAt input cut).currentAt offset)) person
        (input.law.mandatoryMaintenance ((GeneratedLaw.programAt input cut).currentAt offset) person) .maintenance) := by
  obtain ⟨person, member, missing⟩ := unpaid
  exact ⟨person, member, ⟨GeneratedLaw.memberBirth input cut offset person member⟩, missing⟩

#print axioms all_source_forms_total
#print axioms paid_tail_is_the_original_generated_future
#print axioms unexplained_item_has_original_row
#print axioms unpaid_needs_keep_original_M0

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural
