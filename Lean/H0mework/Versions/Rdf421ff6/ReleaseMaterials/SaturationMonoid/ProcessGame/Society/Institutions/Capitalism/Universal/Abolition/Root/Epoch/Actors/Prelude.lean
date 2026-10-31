import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Actors

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source Source.Program Source.ProgrammeFace

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count))

def oldLookup (party : Party) := ActualBirth.lookup input (Settlement.committedVisit input depth count) party

abbrev feeRoot := (Settlement.sourceRoot input depth count datum).toAuthoritativeRoot.toRoot
abbrev feeVisit := (feeRoot input depth count datum).initialVisit

def feeBody (visit : RootVisit (feeRoot input depth count datum)) : Origin Party Good Port Technology Instrument :=
  ⟨visit.current, [(Admission.code input depth count datum).request]⟩

def feeParties : List Party := parties input.law (feeBody input depth count datum (feeVisit input depth count datum))

abbrev FeeActor := ProgrammeFace.Actor input.law (feeBody input depth count datum) (feeVisit input depth count datum)

def feeActor (party : Party) (present : party ∈ feeParties input depth count datum) : FeeActor input depth count datum :=
  ProgrammeFace.actor input.law (feeBody input depth count datum) (feeVisit input depth count datum) party present

variable (limit : Nat)

/-- A dependent union of existing M0 images, retaining their actual source
locations. This is not an actor identifier assigned to a raw party key. -/
abbrev Image := ActualBirth.Actor input ⊕
  (FeeActor input depth count datum ⊕ ((visit : Visit input depth count datum limit) × ActorAt input depth count datum limit visit))

inductive Location : Type
  | original (witness : ActualBirth.Witness input)
  | fee (party : Party) (present : party ∈ feeParties input depth count datum)
  | epoch (visit : Visit input depth count datum limit) (party : Party)
      (present : party ∈ actualParties input depth count datum limit visit)

def Location.party : Location input depth count datum limit → Party
  | .original witness => witness.party
  | .fee party _ | .epoch _ party _ => party

def Location.actor : Location input depth count datum limit → Image input depth count datum limit
  | .original witness => .inl (witness.actor input)
  | .fee party present => .inr (.inl (feeActor input depth count datum party present))
  | .epoch visit party present => .inr (.inr ⟨visit, actorAt input depth count datum limit visit party present⟩)

def prelude (party : Party) : Option (Location input depth count datum limit) :=
  match oldLookup input depth count party with
  | some witness => some (.original witness)
  | none => if present : party ∈ feeParties input depth count datum then some (.fee party present) else none

def here (visit : Visit input depth count datum limit) (party : Party) : Option (Location input depth count datum limit) :=
  if present : party ∈ actualParties input depth count datum limit visit then some (.epoch visit party present) else none

theorem prelude_keeps_old_actor (party : Party) (witness : ActualBirth.Witness input)
    (found : oldLookup input depth count party = some witness) :
    prelude input depth count datum limit party = some (.original witness) := by
  simp only [prelude, found]

theorem prelude_key (party : Party) (location : Location input depth count datum limit)
    (found : prelude input depth count datum limit party = some location) : location.party input depth count datum limit = party := by
  unfold prelude at found
  split at found
  next witness original =>
    cases Option.some.inj found
    exact ActualBirth.lookup_has_the_requested_key input (Settlement.committedVisit input depth count) party witness original
  next absent =>
    split at found
    · cases Option.some.inj found; rfl
    · cases found

theorem here_key (visit : Visit input depth count datum limit) (party : Party)
    (location : Location input depth count datum limit)
    (found : here input depth count datum limit visit party = some location) : location.party input depth count datum limit = party := by
  unfold here at found
  split at found
  · cases Option.some.inj found; rfl
  · cases found

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Actors
