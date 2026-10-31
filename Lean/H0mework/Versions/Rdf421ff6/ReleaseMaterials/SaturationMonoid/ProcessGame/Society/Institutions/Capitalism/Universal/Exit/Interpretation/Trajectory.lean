import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Interpretation.Step
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Law.NativeTrajectory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Interpretation

open Source.Program Source.ProgrammeControl

universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (program : RawProgram Party Good Port Technology Instrument)
  (family : (n : Nat) → At program n → List Port)
  (members : RawCurrent Party Good Technology Instrument → List Party)

def ChecksAt (n : Nat) : Prop := Checks program.law (program.currentAt n)
  (program.emit (program.currentAt n)) (family n) (members (program.currentAt n))

def ResidualAt (n : Nat) : Prop :=
  (∃ item, UnexplainedAt program.law (program.currentAt n) (program.emit (program.currentAt n))
    (family n) (members (program.currentAt n)) item) ∨ Law.NativeTrajectory.UnpaidAt program members n

def PaidInterpretedTail (start : Nat) : Prop :=
  LocalRenewal.PaidTail program members start ∧ ∀ offset, ChecksAt program family members (start + offset)

theorem checked_source_generates_next (n : Nat) (checked : ChecksAt program family members n) :
    ∃ alternative, LocalRenewal.attempt program members (program.currentAt n) = some alternative ∧
      program.law.next (program.currentAt n) alternative = program.tick (program.currentAt n) ∧
      Necessity.AllNeedsPaid program.law (program.currentAt n) (members (program.currentAt n)) alternative := by
  obtain ⟨alternative, generated, nextEq, paid, _valid, _operations⟩ :=
    checked_word_generates_paid_next program.law _ _ _ _ checked
  exact ⟨alternative, by simp only [LocalRenewal.attempt, if_pos checked.2, generated], nextEq, paid⟩

theorem original_source_step (n : Nat) :
    ActualControlAt program family n ∨ ResidualAt program family members n ∨ ChecksAt program family members n := by
  rcases source_step_is_exhaustive program.law (program.currentAt n) (program.emit (program.currentAt n))
    (family n) (members (program.currentAt n)) with control | unknown | unpaid | checked
  · exact Or.inl control
  · exact Or.inr (Or.inl (Or.inl unknown))
  · exact Or.inr (Or.inl (Or.inr ((Law.NativeTrajectory.unpaid_iff_missing_needs program members n).mpr unpaid)))
  · exact Or.inr (Or.inr checked)

theorem original_checks_generate_tail (start : Nat)
    (checked : ∀ offset, ChecksAt program family members (start + offset)) :
    PaidInterpretedTail program family members start := by
  refine ⟨LocalRenewal.successful_tail_generated program members start ?_, checked⟩
  intro offset
  obtain ⟨alternative, generated, _next, _paid⟩ :=
    checked_source_generates_next program family members (start + offset) (checked offset)
  rw [generated]
  exact Option.some_ne_none _

/-- One cutoff is shared by the complete source word and every member.
Control cannot be removed by putting its holder inside the group. -/
theorem original_control_or_residual_or_paid_tail :
    Recurrently (ActualControlAt program family) ∨ Recurrently (ResidualAt program family members) ∨
      ∃ start, PaidInterpretedTail program family members start := by
  classical
  by_cases control : Recurrently (ActualControlAt program family)
  · exact Or.inl control
  right
  by_cases residual : Recurrently (ResidualAt program family members)
  · exact Or.inl residual
  right
  unfold Recurrently at control residual
  push Not at control residual
  obtain ⟨afterControl, noControl⟩ := control
  obtain ⟨afterResidual, noResidual⟩ := residual
  refine ⟨max afterControl afterResidual, original_checks_generate_tail program family members _ ?_⟩
  intro offset
  rcases original_source_step program family members (max afterControl afterResidual + offset) with
    controlled | unexplained | checked
  · exact False.elim (noControl _ (by omega) controlled)
  · exact False.elim (noResidual _ (by omega) unexplained)
  · exact checked

#print axioms original_source_step
#print axioms original_control_or_residual_or_paid_tail

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Interpretation
