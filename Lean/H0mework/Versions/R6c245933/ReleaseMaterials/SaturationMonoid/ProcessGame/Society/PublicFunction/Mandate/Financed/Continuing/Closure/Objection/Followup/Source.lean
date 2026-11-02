import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable (fuel : ℚ) (inputs : List (List Action))

def Later (first second : Position fuel inputs) : Prop :=
  first.ordinal < second.ordinal ∨ (first.ordinal = second.ordinal ∧ first.index.val < second.index.val)

instance (first second : Position fuel inputs) : Decidable (Later fuel inputs first second) :=
  inferInstanceAs (Decidable (_ ∨ _))

private theorem lookup_retained (ordinal distance : Nat) (witness : ActualBirth.Witness (I fuel inputs))
    (found : ActualBirth.lookup (I fuel inputs) (ProgrammeHistory.visitAt (I fuel inputs) ordinal) false = some witness) :
    ActualBirth.lookup (I fuel inputs) (ProgrammeHistory.visitAt (I fuel inputs) (ordinal + distance)) false = some witness := by
  induction distance with
  | zero => exact found
  | succ distance ih =>
      exact ActualBirth.lookup_retains_original_birth (I fuel inputs) _ rfl false witness ih

theorem same_original_actor (first second : Claim fuel inputs)
    (later : Later fuel inputs first.position second.position) : second.actor fuel inputs = first.actor fuel inputs := by
  have le : first.position.ordinal ≤ second.position.ordinal := by
    rcases later with lt | ⟨same, _⟩
    · exact Nat.le_of_lt lt
    · exact Nat.le_of_eq same
  have found := lookup_retained fuel inputs first.position.ordinal
    (second.position.ordinal - first.position.ordinal) (first.birth fuel inputs).original
    (first.birth fuel inputs).generated
  rw [Nat.add_sub_of_le le] at found
  have same := Option.some.inj ((second.birth fuel inputs).generated.symm.trans found)
  exact congrArg (ActualBirth.Witness.actor (I fuel inputs)) same

/-- A later actual challenge signature by the original M0 actor updates the
snapshot being followed. It neither replaces the admission nor settles it. -/
structure Reconfirmation (original : Claim fuel inputs) where
  private mk ::
  target : Claim fuel inputs
  later : Later fuel inputs original.position target.position
  actor : target.actor fuel inputs = original.actor fuel inputs

def readReconfirmation (original : Claim fuel inputs) (position : Position fuel inputs) :
    Option (Reconfirmation fuel inputs original) :=
  match read fuel inputs position with
  | none => none
  | some target =>
      if later : Later fuel inputs original.position target.position then
        some ⟨target, later, same_original_actor fuel inputs original target later⟩
      else none

inductive Target (original : Claim fuel inputs)
  | initial
  | renewed (receipt : Reconfirmation fuel inputs original)

def Target.claim {original : Claim fuel inputs} : Target fuel inputs original → Claim fuel inputs
  | .initial => original
  | .renewed receipt => receipt.target

theorem Target.actor {original : Claim fuel inputs} (target : Target fuel inputs original) :
    (target.claim fuel inputs).actor fuel inputs = original.actor fuel inputs := by
  cases target with
  | initial => rfl
  | renewed receipt => exact receipt.actor

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup
