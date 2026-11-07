import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.ActualPast
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicPast

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source Source.Program Source.ProgrammeFace

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

def prelude (tag : Tag input depth count) (party : Party) : Option (Location input depth count) :=
  match Epoch.Actors.oldLookup input depth count party with
  | some witness => some (.original witness)
  | none => match tag with
    | .review datum _ => if present : party ∈ Epoch.Actors.feeParties input depth count datum then
        some (.fee datum party present) else none
    | .migration .. => none
    | .actual prefixLimit renewalLimit start => ActualPast.first input depth count prefixLimit renewalLimit start.past party
    | .publicActual prefixLimit renewalLimit oldPast start =>
        (ActualPast.first input depth count prefixLimit renewalLimit oldPast party).orElse
          (fun _ => PublicPast.first input depth count prefixLimit renewalLimit oldPast start.past party)

def locationHere (tag : Tag input depth count) (visit : Visit input depth count tag) (party : Party)
    (present : presentAt input depth count tag visit party) : Location input depth count :=
  .epoch (ActualOccurrence.tagOf input depth count tag visit) (ActualOccurrence.visitOf input depth count tag visit) party
    (by
      change party ∈ parties (interpreter input depth count _) (body input depth count _ _)
      rw [ActualOccurrence.same_interpreter, ActualOccurrence.same_body]
      exact present)

def here (tag : Tag input depth count) (visit : Visit input depth count tag) (party : Party) :
    Option (Location input depth count) :=
  if present : presentAt input depth count tag visit party then some (locationHere input depth count tag visit party present) else none

theorem prelude_keeps_original (tag : Tag input depth count) (party : Party) (witness : ActualBirth.Witness input)
    (found : Epoch.Actors.oldLookup input depth count party = some witness) :
    prelude input depth count tag party = some (.original witness) := by
  simp only [prelude, found]

theorem prelude_key (tag : Tag input depth count) (party : Party) (location : Location input depth count)
    (found : prelude input depth count tag party = some location) : location.party input depth count = party := by
  unfold prelude at found
  split at found
  next witness original =>
    cases Option.some.inj found
    exact ActualBirth.lookup_has_the_requested_key input (Settlement.committedVisit input depth count) party witness original
  next absent =>
    cases tag with
    | migration prefixLimit renewalLimit => cases found
    | actual prefixLimit renewalLimit start =>
        exact ActualPast.first_key input depth count prefixLimit renewalLimit start.past party location found
    | publicActual prefixLimit renewalLimit oldPast start =>
        dsimp only at found
        cases old : ActualPast.first input depth count prefixLimit renewalLimit oldPast party with
        | some oldLocation =>
            simp only [old, Option.orElse_some, Option.some.injEq] at found
            subst location
            exact ActualPast.first_key input depth count prefixLimit renewalLimit oldPast party oldLocation old
        | none =>
            simp only [old, Option.orElse_none] at found
            exact PublicPast.first_key input depth count prefixLimit renewalLimit oldPast start.past party location found
    | review datum limit =>
        dsimp only at found
        split at found
        · cases Option.some.inj found; rfl
        · cases found

theorem here_key (tag : Tag input depth count) (visit : Visit input depth count tag) (party : Party)
    (location : Location input depth count) (found : here input depth count tag visit party = some location) :
    location.party input depth count = party := by
  unfold here at found
  split at found
  · cases Option.some.inj found; rfl
  · cases found

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors
