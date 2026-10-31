import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Actors.Prelude

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source Source.Program Source.ProgrammeFace

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def actualParties (tag : Tag input depth count) (visit : Visit input depth count tag) : List Party :=
  parties (interpreter input depth count tag) (body input depth count tag visit)

theorem actualParties_are_the_execution_inventory (tag : Tag input depth count) (visit : Visit input depth count tag) :
    actualParties input depth count tag visit =
      ((execution input depth count tag visit.current).items.flatMap (itemParties (interpreter input depth count tag))).dedup := by
  unfold actualParties parties
  rw [body_is_the_same_actual_inventory]

def presentAt (tag : Tag input depth count) (visit : Visit input depth count tag) (party : Party) : Prop :=
  party ∈ parties (interpreter input depth count tag) (body input depth count tag visit)

instance (tag : Tag input depth count) (visit : Visit input depth count tag) (party : Party) :
    Decidable (presentAt input depth count tag visit party) := by
  unfold presentAt
  infer_instance

abbrev ActorAt (tag : Tag input depth count) (visit : Visit input depth count tag) :=
  ProgrammeFace.Actor (interpreter input depth count tag) (body input depth count tag) visit

def actorAt (tag : Tag input depth count) (visit : Visit input depth count tag) (party : Party)
    (present : presentAt input depth count tag visit party) : ActorAt input depth count tag visit :=
  ProgrammeFace.actor (interpreter input depth count tag) (body input depth count tag) visit party present

/-- Only existing source M0 images inhabit this union. Distinct source tags
are distinct occurrences until an actual entry transports an earlier image. -/
abbrev Image := ActualBirth.Actor input ⊕
  ((datum : Admission.Datum input (Admission.frame input depth count)) × Epoch.Actors.FeeActor input depth count datum) ⊕
  ((tag : Tag input depth count) × (visit : Visit input depth count tag) × ActorAt input depth count tag visit)

inductive Location : Type
  | original (witness : ActualBirth.Witness input)
  | fee (datum : Admission.Datum input (Admission.frame input depth count)) (party : Party)
      (present : party ∈ Epoch.Actors.feeParties input depth count datum)
  | epoch (tag : Tag input depth count) (visit : Visit input depth count tag) (party : Party)
      (present : presentAt input depth count tag visit party)

def Location.party : Location input depth count → Party
  | .original witness => witness.party
  | .fee _ party _ | .epoch _ _ party _ => party

def Location.actor : Location input depth count → Image input depth count
  | .original witness => .inl (witness.actor input)
  | .fee datum party present => .inr (.inl ⟨datum, Epoch.Actors.feeActor input depth count datum party present⟩)
  | .epoch tag visit party present => .inr (.inr ⟨tag, visit, actorAt input depth count tag visit party present⟩)


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors
