import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {fuel : ℚ} {originInputs : List (List Action)}

/-- The two roots keep their own occurrences. Only their actual instruction
prefix is identified; in particular their M0 actors are not equated. -/
structure Anchor (original : Claim fuel originInputs) (inputs : List (List Action)) where
  image : Claim fuel inputs
  ordinal : image.position.ordinal = original.position.ordinal
  index : image.position.index.val = original.position.index.val
  item : image.position.item fuel inputs = original.position.item fuel originInputs
  common : ∀ ordinal, ordinal ≤ original.position.ordinal →
    Registered.traceItems (I fuel inputs) (ProgrammeHistory.visitAt (I fuel inputs) ordinal).current =
      Registered.traceItems (I fuel originInputs) (ProgrammeHistory.visitAt (I fuel originInputs) ordinal).current

def Anchor.self (original : Claim fuel originInputs) : Anchor original originInputs :=
  ⟨original, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem actor_of_ordinal_le {inputs : List (List Action)} (first second : Claim fuel inputs)
    (le : first.position.ordinal ≤ second.position.ordinal) : second.actor fuel inputs = first.actor fuel inputs := by
  rcases Nat.eq_or_lt_of_le le with same | later
  · have visits : (first.origin fuel inputs).visit = (second.origin fuel inputs).visit := by
      change ProgrammeHistory.visitAt _ first.position.ordinal = ProgrammeHistory.visitAt _ second.position.ordinal
      rw [same]
    let original := (first.birth fuel inputs).original
    have found : ActualBirth.lookup (I fuel inputs) (first.origin fuel inputs).visit false = some original :=
      (first.birth fuel inputs).generated
    have transported : ActualBirth.lookup (I fuel inputs) (second.origin fuel inputs).visit false = some original :=
      (congrArg (fun visit => ActualBirth.lookup (I fuel inputs) visit false) visits).symm.trans found
    have born := Option.some.inj ((second.birth fuel inputs).generated.symm.trans transported)
    exact congrArg (ActualBirth.Witness.actor (I fuel inputs)) born
  · exact same_original_actor fuel inputs first second (.inl later)

structure Target (original : Claim fuel originInputs) (inputs : List (List Action)) where
  anchor : Anchor original inputs
  claim : Claim fuel inputs
  afterOrigin : anchor.image.position.ordinal < claim.position.ordinal ∨
    (anchor.image.position.ordinal = claim.position.ordinal ∧ anchor.image.position.index.val ≤ claim.position.index.val)

theorem Target.origin_ordinal_le {original : Claim fuel originInputs} {inputs : List (List Action)} (target : Target original inputs) :
    target.anchor.image.position.ordinal ≤ target.claim.position.ordinal := by rcases target.afterOrigin with later | ⟨same, _⟩ <;> omega

theorem Target.actor {original : Claim fuel originInputs} {inputs : List (List Action)} (target : Target original inputs) :
    target.claim.actor fuel inputs = target.anchor.image.actor fuel inputs :=
  actor_of_ordinal_le _ _ target.origin_ordinal_le

def Target.snapshot {original : Claim fuel originInputs} {inputs : List (List Action)} (target : Target original inputs) :=
  target.claim.snapshot fuel inputs

def Target.local {original : Claim fuel originInputs} (target : Followup.Target fuel originInputs original) :
    Target original originInputs := by
  cases target with
  | initial => exact ⟨Anchor.self original, original, .inr ⟨rfl, Nat.le_refl _⟩⟩
  | renewed receipt =>
      refine ⟨Anchor.self original, receipt.target, ?_⟩
      rcases receipt.later with later | ⟨same, index⟩
      · exact .inl later
      · exact .inr ⟨same, Nat.le_of_lt index⟩

structure Reconfirmation {original : Claim fuel originInputs} {inputs : List (List Action)} (previous : Target original inputs) where
  private mk ::
  claim : Claim fuel inputs
  later : Later fuel inputs previous.claim.position claim.position

def Reconfirmation.target {original : Claim fuel originInputs} {inputs : List (List Action)}
    {previous : Target original inputs} (receipt : Reconfirmation previous) : Target original inputs :=
  ⟨previous.anchor, receipt.claim, by
    rcases previous.afterOrigin with previousLater | ⟨previousSame, previousIndex⟩ <;>
      rcases receipt.later with later | ⟨same, index⟩ <;> omega⟩

def readReconfirmation {original : Claim fuel originInputs} {inputs : List (List Action)}
    (target : Target original inputs) (position : Position fuel inputs) : Option (Reconfirmation target) :=
  match read fuel inputs position with
  | none => none
  | some claim =>
      if later : Later fuel inputs target.claim.position claim.position then some ⟨claim, later⟩ else none

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Followup.Cross
