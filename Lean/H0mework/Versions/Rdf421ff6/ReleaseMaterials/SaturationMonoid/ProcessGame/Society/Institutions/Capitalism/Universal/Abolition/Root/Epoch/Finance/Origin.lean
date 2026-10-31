import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Coordinates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Source.ProgrammeFace

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

abbrev ActualItem := Interface.ActualItem input depth count

def ActualItem.instruction (origin : ActualItem input depth count) :=
  Interface.ActualItem.instruction input depth count origin

/-- The actual source tag owns the current institutional interpretation;
legacy tags reduce to the original law. -/
abbrev ActualItem.interpreter (origin : ActualItem input depth count) :
    RawLaw Party Good Port Technology Instrument :=
  Interface.interpreter input depth count origin.tag

def ActualItem.actualDebit (origin : ActualItem input depth count) : Flow Party Good :=
  (origin.interpreter input depth count).actualDebit (origin.instruction input depth count).before
    (origin.instruction input depth count).request

def ActualItem.actualCredit (origin : ActualItem input depth count) : Flow Party Good :=
  (origin.interpreter input depth count).actualCredit (origin.instruction input depth count).before
    (origin.instruction input depth count).request

def ActualItem.row (origin : ActualItem input depth count) :=
  Interface.ActualItem.row input depth count origin

theorem ActualItem.original_inventory (origin : ActualItem input depth count) :
    origin.instruction input depth count ∈ (Interface.execution input depth count origin.tag origin.visit.current).items :=
  Interface.ActualItem.original_inventory input depth count origin

theorem ActualItem.participant_is_actual (origin : ActualItem input depth count)
    (party : Party) (present : party ∈ operationParties
      (origin.instruction input depth count).request.operation) :
    party ∈ Interface.Actors.actualParties input depth count origin.tag origin.visit := by
  rw [Interface.Actors.actualParties_are_the_execution_inventory]
  apply List.mem_dedup.mpr
  exact List.mem_flatMap.mpr ⟨origin.instruction input depth count,
    origin.original_inventory input depth count,
    operation_party_mem_itemParties (origin.interpreter input depth count) _ party present⟩

inductive Origin where
  | original (origin : Financial.InstructionOrigin input)
  | epoch (origin : ActualItem input depth count)

structure NewClaim where
  private mk ::
  origin : ActualItem input depth count
  instrument : Instrument
  debtor : Party
  holder : Party
  quantity : ℚ
  operation : (origin.instruction input depth count).request.operation =
    .issue instrument debtor holder quantity
  accepted : (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
    (origin.instruction input depth count).request
  debtorBirth : Interface.Actors.At input depth count origin.tag origin.visit debtor
  holderBirth : Interface.Actors.At input depth count origin.tag origin.visit holder

def readNewClaim (origin : ActualItem input depth count) :
    Option (NewClaim input depth count) :=
  match operation : (origin.instruction input depth count).request.operation with
  | .issue instrument debtor holder quantity =>
      if accepted : (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
          (origin.instruction input depth count).request then
        some ⟨origin, instrument, debtor, holder, quantity, operation, accepted,
          Interface.Actors.generate input depth count origin.tag origin.visit debtor
            (origin.participant_is_actual input depth count debtor (by rw [operation]; simp [operationParties])),
          Interface.Actors.generate input depth count origin.tag origin.visit holder
            (origin.participant_is_actual input depth count holder (by rw [operation]; simp [operationParties]))⟩
      else none
  | _ => none

theorem readNewClaim_origin (origin : ActualItem input depth count)
    (claim : NewClaim input depth count)
    (returned : readNewClaim input depth count origin = some claim) : claim.origin = origin := by
  unfold readNewClaim at returned
  repeat' first
    | contradiction
    | split at returned
    | (cases Option.some.inj returned; rfl)

theorem different_occurrences_keep_different_claim_origins
    (first second : NewClaim input depth count)
    (different : first.origin ≠ second.origin) :
    Origin.epoch first.origin ≠ (Origin.epoch second.origin : Origin input depth count) := by
  intro same
  exact different (Origin.epoch.inj same)

abbrev Claim := Financial.IssuedClaim input ⊕ NewClaim input depth count

def Claim.origin : Claim input depth count → Origin input depth count
  | .inl claim => .original claim.origin
  | .inr claim => .epoch claim.origin

def Claim.instrument : Claim input depth count → Instrument
  | .inl claim => claim.instrument
  | .inr claim => claim.instrument

def Claim.debtor : Claim input depth count → Party
  | .inl claim => claim.debtor
  | .inr claim => claim.debtor

def Claim.holder : Claim input depth count → Party
  | .inl claim => claim.holder
  | .inr claim => claim.holder

def Claim.quantity : Claim input depth count → ℚ
  | .inl claim => claim.quantity
  | .inr claim => claim.quantity

def Claim.debtorActor : Claim input depth count → Interface.Actors.Image input depth count
  | .inl claim => .inl (claim.debtorActor input)
  | .inr claim => claim.debtorBirth.actor input depth count

def Claim.holderActor : Claim input depth count → Interface.Actors.Image input depth count
  | .inl claim => .inl (claim.holderActor input)
  | .inr claim => claim.holderBirth.actor input depth count

theorem old_and_new_claim_origins_are_distinct (old : Financial.IssuedClaim input)
    (fresh : NewClaim input depth count) :
    Claim.origin input depth count (.inl old) ≠
      Claim.origin input depth count (.inr fresh) := by
  intro same
  cases same

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance
