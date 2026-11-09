import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Write
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Dispatch

/-!
The candidate's own literal prefix supplies every authority, answer lane
and material damage check. The menu provides only proposed words.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution
open Reparation.Actual
open ExposureGuard

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument}

local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Proposal" => Reparation.Actual.Input Party Good Port Technology Instrument

variable (community : Party → Community) (answers : ReceiptAnswers seed)

/-- The actual authority, inherited and current answer lanes, and original
damage inventory at the candidate's next literal input. -/
def EligibleAt (anchor past : Word) (input : Proposal) : Prop :=
  Admitted (bearers seed community anchor ++ bearers seed community past) answers past input ∧
    Boundary.Actual.damages (endAt seed past) input community = []

instance (anchor past : Word) (input : Proposal) : Decidable (EligibleAt community answers anchor past input) :=
  match inspectAdmission (bearers seed community anchor ++ bearers seed community past) answers past input with
  | .inl refusal => isFalse fun eligible => refusal.refutes _ _ _ _ eligible.1
  | .inr admitted =>
    if noDamage : Boundary.Actual.damages (endAt seed past) input community = [] then
      isTrue ⟨admitted.down, noDamage⟩
    else isFalse fun eligible => noDamage eligible.2

/-- A word is eligible exactly when each actual input passes at its own
source successor, including any generated native accounting inputs. -/
def EligibleFrom (anchor : Word) : Word → Word → Prop
  | _, [] => True
  | past, input :: tail =>
    EligibleAt community answers anchor past input ∧ EligibleFrom anchor (past ++ [input]) tail

private def decideEligibleFrom (anchor : Word) : (past word : Word) →
    Decidable (EligibleFrom community answers anchor past word)
  | _, [] => isTrue trivial
  | past, input :: tail => by
    letI := decideEligibleFrom anchor (past ++ [input]) tail
    change Decidable (EligibleAt community answers anchor past input ∧
      EligibleFrom community answers anchor (past ++ [input]) tail)
    infer_instance

instance (anchor past word : Word) : Decidable (EligibleFrom community answers anchor past word) :=
  decideEligibleFrom community answers anchor past word

theorem eligible_checks_every_literal_position (anchor past front tail : Word) (input : Proposal)
    (checked : EligibleFrom community answers anchor past (front ++ input :: tail)) :
    EligibleAt community answers anchor (past ++ front) input := by
  induction front generalizing past with
  | nil =>
    rw [List.append_nil]
    exact checked.1
  | cons first front ih =>
    rw [show past ++ first :: front = (past ++ [first]) ++ front from by
      rw [List.append_assoc]; rfl]
    exact ih (past ++ [first]) checked.2

theorem eligible_preserves_the_literal_original_loss_inventory (anchor past word : Word)
    (checked : EligibleFrom community answers anchor past word) :
    originalLosses seed community (past ++ word) = originalLosses seed community past := by
  induction word generalizing past with
  | nil => rw [List.append_nil]
  | cons input tail ih =>
    have rest := ih (past ++ [input]) checked.2
    rw [show past ++ input :: tail = (past ++ [input]) ++ tail from by
      rw [List.append_assoc]; rfl, rest, losses_snoc]
    have safe : Boundary.Actual.damages (endAt seed past) input community = [] := checked.1.2
    simp [openings, safe]

theorem an_eligible_word_has_original_source_authority (anchor past word : Word)
    (checked : EligibleFrom community answers anchor past word) :
    SourceAuthority (endAt seed past) word := by
  induction word generalizing past with
  | nil =>
    intro item listed
    exact (List.not_mem_nil listed).elim
  | cons input tail ih =>
    intro item listed
    change item ∈ inventory (endAt seed past) ([input] ++ tail) at listed
    rw [inventory_append] at listed
    rcases List.mem_append.mp listed with first | later
    · exact checked.1.1.1 item first
    · have lawful := ih (past ++ [input]) checked.2
      rw [endAt_append] at lawful
      have authority := lawful item later
      rw [endAt_input] at authority
      exact authority

variable {community}

def Eligible (loss : Reparation.Actual.Occurrence seed community) (word : Word) : Prop :=
  EligibleFrom community answers (history loss) (history loss) word

instance (loss : Reparation.Actual.Occurrence seed community) (word : Word) :
    Decidable (Eligible answers loss word) :=
  inferInstanceAs (Decidable (EligibleFrom community answers (history loss) (history loss) word))

theorem retain_is_eligible (loss : Reparation.Actual.Occurrence seed community) :
    Eligible answers loss [] := trivial

#print axioms eligible_checks_every_literal_position
#print axioms an_eligible_word_has_original_source_authority

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence
