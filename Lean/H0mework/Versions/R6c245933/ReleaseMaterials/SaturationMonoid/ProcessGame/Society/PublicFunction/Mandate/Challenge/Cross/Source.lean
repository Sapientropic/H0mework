import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Prefix

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type}
  (bound : ProgrammeFamily base scope Index)
  {originInputs : Index}

/-- Actual input occurrences have their own actors. The old native bearer
stays literal; this anchor relates the original signed instruction prefix. -/
structure Anchor (original : Claim bound originInputs)
    (inputs : Index) where
  image : Claim bound inputs
  ordinal : image.position.ordinal = original.position.ordinal
  index : image.position.index.val = original.position.index.val
  item : image.position.item bound inputs = original.position.item bound originInputs
  common : ∀ ordinal, ordinal ≤ original.position.ordinal →
    Registered.traceItems (I bound inputs) (ProgrammeHistory.visitAt (I bound inputs) ordinal).current =
      Registered.traceItems (I bound originInputs) (ProgrammeHistory.visitAt (I bound originInputs) ordinal).current

def Anchor.self (original : Claim bound originInputs) : Anchor bound original originInputs :=
  ⟨original, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem actor_of_ordinal_le {inputs : Index}
    (first second : Claim bound inputs) (le : first.position.ordinal ≤ second.position.ordinal)
    (signer : second.signer bound inputs = first.signer bound inputs) : second.actor bound inputs = first.actor bound inputs := by
  rcases Nat.eq_or_lt_of_le le with same | later
  · have visits : (first.origin bound inputs).visit = (second.origin bound inputs).visit := by
      change ProgrammeHistory.visitAt _ first.position.ordinal = ProgrammeHistory.visitAt _ second.position.ordinal
      rw [same]
    have sameLookup := congrArg (fun signer => ActualBirth.lookup (I bound inputs) (second.origin bound inputs).visit signer) signer
    have firstFound := (congrArg (fun visit => ActualBirth.lookup (I bound inputs) visit (first.signer bound inputs)) visits).symm.trans
      (first.birth bound inputs).generated
    have secondFound := sameLookup.symm.trans (second.birth bound inputs).generated
    have born := Option.some.inj (secondFound.symm.trans firstFound)
    exact congrArg (ActualBirth.Witness.actor (I bound inputs)) born
  · exact same_original_actor bound inputs first second (.inl later) signer

structure Target (original : Claim bound originInputs)
    (inputs : Index) where
  anchor : Anchor bound original inputs
  claim : Claim bound inputs
  afterOrigin : anchor.image.position.ordinal < claim.position.ordinal ∨
    (anchor.image.position.ordinal = claim.position.ordinal ∧ anchor.image.position.index.val ≤ claim.position.index.val)
  signer : claim.signer bound inputs = anchor.image.signer bound inputs

theorem Target.origin_ordinal_le {original : Claim bound originInputs}
    {inputs : Index} (target : Target bound original inputs) :
    target.anchor.image.position.ordinal ≤ target.claim.position.ordinal := by
  rcases target.afterOrigin with later | ⟨same, _⟩ <;> omega

theorem Target.actor {original : Claim bound originInputs}
    {inputs : Index} (target : Target bound original inputs) :
    target.claim.actor bound inputs = target.anchor.image.actor bound inputs :=
  actor_of_ordinal_le bound _ _ target.origin_ordinal_le target.signer

def Target.snapshot {original : Claim bound originInputs}
    {inputs : Index} (target : Target bound original inputs) :=
  target.claim.snapshot bound inputs

def Target.local {original : Claim bound originInputs} (target : Challenge.Target bound originInputs original) :
    Target bound original originInputs := by
  cases target with
  | initial => exact ⟨Anchor.self bound original, original, .inr ⟨rfl, Nat.le_refl _⟩, rfl⟩
  | renewed receipt =>
      refine ⟨Anchor.self bound original, receipt.target, ?_, receipt.signer⟩
      rcases receipt.later with later | ⟨same, index⟩
      · exact .inl later
      · exact .inr ⟨same, Nat.le_of_lt index⟩

structure Reconfirmation {original : Claim bound originInputs}
    {inputs : Index} (previous : Target bound original inputs) where
  private mk ::
  claim : Claim bound inputs
  later : Later bound inputs previous.claim.position claim.position
  signer : claim.signer bound inputs = previous.claim.signer bound inputs

def Reconfirmation.target {original : Claim bound originInputs}
    {inputs : Index}
    {previous : Target bound original inputs} (receipt : Reconfirmation bound previous) : Target bound original inputs :=
  ⟨previous.anchor, receipt.claim, by
    rcases previous.afterOrigin with previousLater | ⟨previousSame, previousIndex⟩ <;>
      rcases receipt.later with later | ⟨same, index⟩ <;> omega,
    receipt.signer.trans previous.signer⟩

def readReconfirmation {original : Claim bound originInputs}
    {inputs : Index}
    (target : Target bound original inputs) (position : Position bound inputs) : Option (Reconfirmation bound target) :=
  match read bound inputs position with
  | none => none
  | some claim =>
      if checked : Later bound inputs target.claim.position claim.position ∧ claim.signer bound inputs = target.claim.signer bound inputs then
        some ⟨claim, checked.1, checked.2⟩
      else none

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
