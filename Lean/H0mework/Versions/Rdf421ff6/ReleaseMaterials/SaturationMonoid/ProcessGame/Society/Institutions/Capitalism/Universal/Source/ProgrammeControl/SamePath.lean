import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Word
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Exit.JointProgramme

/-! One generated trajectory, one common tail cut.  The control family is
read at each original intermediate current.  Alternatives preserve the raw
state; they do not replace the original trace, actor or responsibility. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (program : RawProgram Party Good Port Technology Instrument) (group : List Party)

abbrev At (n : Nat) := OriginalItem program.law (program.currentAt n) (program.emit (program.currentAt n))

variable (family : (n : Nat) → At program n → List Port)

def ActualControlAt (n : Nat) : Prop :=
  Nonempty (ControlUse program.law (program.currentAt n) (program.emit (program.currentAt n)) (family n))

def OriginalObstructionAt (n : Nat) : Prop :=
  Nonempty (ObstructedItem program.law (program.currentAt n) (program.emit (program.currentAt n)) group)

def Recurrently (P : Nat → Prop) : Prop := ∀ cutoff, ∃ n ≥ cutoff, P n

/-- C-free refers to the actual tail.  The independently reauthorized
programme is an additional generated capability, not an identity of roots. -/
def ActualIndependentTail (start : Nat) : Prop :=
  (∀ offset, ∀ item : At program (start + offset),
    program.law.Valid item.val.before item.val.request ∧
      ∀ port ∈ program.law.requiredPorts item.val.before item.val.request,
        port ∉ family (start + offset) item) ∧
  Exit.JointProgramme.SelfExecutableTail program group start

omit [DecidableEq Port] in
theorem absence_of_obstruction_generates_joint_word (n : Nat)
    (clear : ¬ OriginalObstructionAt program group n) :
    Exit.JointProgramme.attempt program group (program.currentAt n) ≠ none := by
  apply program.law.jointWord_complete
  intro item member
  have notBlocked : ¬ Blocked program.law (program.currentAt n)
      (program.emit (program.currentAt n)) group ⟨item, member⟩ := by
    intro blocked
    exact clear ⟨⟨⟨item, member⟩, blocked⟩⟩
  have accepted : program.law.Valid item.before item.request := by
    by_contra refused
    exact notBlocked (Or.inl refused)
  refine ⟨accepted, ?_⟩
  cases found : program.law.jointSigner group item.before item.request with
  | none => exact False.elim (notBlocked (Or.inr found))
  | some signer =>
      obtain ⟨inside, legal⟩ := program.law.jointSigner_sound group _ _ signer found
      exact ⟨signer, inside, legal⟩

omit [DecidableEq Port] in
theorem no_control_no_obstruction_generates_original_tail (start : Nat)
    (controlFree : ∀ n ≥ start, ¬ ActualControlAt program family n)
    (clear : ∀ n ≥ start, ¬ OriginalObstructionAt program group n) :
    ActualIndependentTail program group family start := by
  refine ⟨?_, Exit.JointProgramme.successful_tail_generated program group start ?_⟩
  · intro offset item
    have accepted : program.law.Valid item.val.before item.val.request := by
      by_contra refused
      exact clear (start + offset) (by omega) ⟨⟨item, Or.inl refused⟩⟩
    refine ⟨accepted, ?_⟩
    intro port required controlled
    exact controlFree (start + offset) (by omega) ⟨⟨item, accepted, port, required, controlled⟩⟩
  · intro offset
    exact absence_of_obstruction_generates_joint_word program group (start + offset)
      (clear (start + offset) (by omega))

omit [DecidableEq Port] in
/-- No finite reserve, uniform cost, fixed population or wage premise.
This is the topological tail alternative for the original instruction
path; quantitative necessity bounds can be consumed independently. -/
theorem control_or_original_obstruction_or_actual_independent_tail :
    Recurrently (ActualControlAt program family) ∨
    Recurrently (OriginalObstructionAt program group) ∨
    ∃ start, ActualIndependentTail program group family start := by
  classical
  by_cases control : Recurrently (ActualControlAt program family)
  · exact Or.inl control
  · right
    by_cases blocked : Recurrently (OriginalObstructionAt program group)
    · exact Or.inl blocked
    · right
      unfold Recurrently at control blocked
      push Not at control blocked
      obtain ⟨afterControl, noControl⟩ := control
      obtain ⟨afterBlocked, noBlocked⟩ := blocked
      refine ⟨max afterControl afterBlocked,
        no_control_no_obstruction_generates_original_tail program group family _ ?_ ?_⟩
      · intro n after
        exact noControl n (le_trans (le_max_left _ _) after)
      · intro n after
        exact noBlocked n (le_trans (le_max_right _ _) after)

omit [DecidableEq Port] in
theorem no_reachable_independent_tail_forces_same_path_recurrence
    (noTail : ∀ start, ¬ ActualIndependentTail program group family start) :
    Recurrently (ActualControlAt program family) ∨
    Recurrently (OriginalObstructionAt program group) := by
  rcases control_or_original_obstruction_or_actual_independent_tail program group family with
    control | blocked | ⟨start, tail⟩
  · exact Or.inl control
  · exact Or.inr blocked
  · exact False.elim (noTail start tail)

omit [DecidableEq Port] in
theorem complete_original_classification_forces_control_recurrence
    (noTail : ∀ start, ¬ ActualIndependentTail program group family start)
    (clear : ∀ n, ¬ OriginalObstructionAt program group n) :
    Recurrently (ActualControlAt program family) := by
  rcases no_reachable_independent_tail_forces_same_path_recurrence program group family noTail with
    control | blocked
  · exact control
  · obtain ⟨n, _, witness⟩ := blocked 0
    exact False.elim (clear n witness)

#print axioms control_or_original_obstruction_or_actual_independent_tail
#print axioms complete_original_classification_forces_control_recurrence

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl
