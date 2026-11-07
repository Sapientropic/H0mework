import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Prelude

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source Source.Program Source.ProgrammeFace

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (tag : Tag input depth count)

private def fold : {current : (V input depth count tag).Current} →
    (root input depth count tag).ReachableAt current → Party → Option (Location input depth count)
  | _, .initial, party => (prelude input depth count tag party).orElse
      (fun _ => here input depth count tag (root input depth count tag).initialVisit party)
  | target, .step prior nextEq, party => (fold prior party).orElse
      (fun _ => here input depth count tag ⟨target, .step prior nextEq⟩ party)

def lookup (visit : Visit input depth count tag) (party : Party) := fold input depth count tag visit.history party

theorem lookup_next (visit : Visit input depth count tag)
    {target : (V input depth count tag).Current}
    (nextEq : ((root input depth count tag).evolutionAt visit.current).nextCurrent? = some target)
    (party : Party) :
    lookup input depth count tag (visit.next nextEq) party =
      (lookup input depth count tag visit party).orElse
        (fun _ => here input depth count tag (visit.next nextEq) party) := rfl

theorem lookup_retains_original_birth (visit : Visit input depth count tag)
    {target : (V input depth count tag).Current}
    (nextEq : ((root input depth count tag).evolutionAt visit.current).nextCurrent? = some target)
    (party : Party) (location : Location input depth count)
    (found : lookup input depth count tag visit party = some location) :
    lookup input depth count tag (visit.next nextEq) party = some location := by
  rw [lookup_next, found]
  rfl

theorem lookup_retains_original_programme_actor (visit : Visit input depth count tag)
    (party : Party) (witness : ActualBirth.Witness input)
    (found : Epoch.Actors.oldLookup input depth count party = some witness) :
    lookup input depth count tag visit party = some (.original witness) := by
  rcases visit with ⟨current, history⟩
  induction history with
  | initial =>
      simp only [lookup, fold, prelude_keeps_original input depth count tag party witness found, Option.orElse_some]
  | step prior nextEq induction =>
      change (fold input depth count tag prior party).orElse _ = _
      rw [show fold input depth count tag prior party = some (.original witness) from induction]
      rfl

theorem original_image_agrees_across_sources
    (otherTag : Tag input depth count) (visit : Visit input depth count tag)
    (other : Visit input depth count otherTag) (party : Party) (witness : ActualBirth.Witness input)
    (found : Epoch.Actors.oldLookup input depth count party = some witness) :
    lookup input depth count tag visit party = some (.original witness) ∧
      lookup input depth count otherTag other party = some (.original witness) :=
  ⟨lookup_retains_original_programme_actor input depth count tag visit party witness found,
    lookup_retains_original_programme_actor input depth count otherTag other party witness found⟩

theorem current_participation_has_generated_birth (visit : Visit input depth count tag) (party : Party)
    (present : party ∈ parties (interpreter input depth count tag) (body input depth count tag visit)) :
    (lookup input depth count tag visit party).isSome = true := by
  rcases visit with ⟨current, history⟩
  cases history with
  | initial =>
      dsimp only [lookup, fold]
      have actual : party ∈ parties (interpreter input depth count tag) (body input depth count tag (root input depth count tag).initialVisit) := present
      cases prelude input depth count tag party with
      | some location => rfl
      | none =>
          simp only [Option.orElse_none, here]
          split
          · rfl
          · next absent => exact False.elim (absent actual)
  | step prior nextEq =>
      change ((fold input depth count tag prior party).orElse _).isSome = true
      cases fold input depth count tag prior party with
      | some location => rfl
      | none =>
          simp only [Option.orElse_none, here]
          split
          · rfl
          · next absent => exact False.elim (absent present)

theorem lookup_key (visit : Visit input depth count tag) (party : Party)
    (location : Location input depth count)
    (found : lookup input depth count tag visit party = some location) :
    location.party input depth count = party := by
  rcases visit with ⟨current, history⟩
  induction history with
  | initial =>
      change (prelude input depth count tag party).orElse _ = some location at found
      cases old : prelude input depth count tag party with
      | some prior =>
          simp only [old, Option.orElse_some, Option.some.injEq] at found
          subst location
          exact prelude_key input depth count tag party prior old
      | none =>
          simp only [old, Option.orElse_none] at found
          exact here_key input depth count tag _ party location found
  | step prior nextEq induction =>
      change (fold input depth count tag prior party).orElse _ = some location at found
      cases old : fold input depth count tag prior party with
      | some previous =>
          simp only [old, Option.orElse_some, Option.some.injEq] at found
          subst location
          exact induction old
      | none =>
          simp only [old, Option.orElse_none] at found
          exact here_key input depth count tag _ party location found

structure At (visit : Visit input depth count tag) (party : Party) where
  private mk ::
  location : Location input depth count
  generated : lookup input depth count tag visit party = some location

def generate (visit : Visit input depth count tag) (party : Party)
    (present : party ∈ parties (interpreter input depth count tag) (body input depth count tag visit)) : At input depth count tag visit party :=
  ⟨(lookup input depth count tag visit party).get
      (current_participation_has_generated_birth input depth count tag visit party present),
    (Option.some_get (current_participation_has_generated_birth input depth count tag visit party present)).symm⟩

def At.actor {visit : Visit input depth count tag} {party : Party}
    (birth : At input depth count tag visit party) : Image input depth count :=
  birth.location.actor input depth count

theorem At.key_exact {visit : Visit input depth count tag} {party : Party}
    (birth : At input depth count tag visit party) :
    birth.location.party input depth count = party :=
  lookup_key input depth count tag visit party birth.location birth.generated

def At.next {visit : Visit input depth count tag} {party : Party}
    (birth : At input depth count tag visit party)
    {target : (V input depth count tag).Current}
    (nextEq : ((root input depth count tag).evolutionAt visit.current).nextCurrent? = some target) :
    At input depth count tag (visit.next nextEq) party :=
  ⟨birth.location, lookup_retains_original_birth input depth count tag visit nextEq party birth.location birth.generated⟩

theorem At.next_keeps_the_original_M0_image {visit : Visit input depth count tag} {party : Party}
    (birth : At input depth count tag visit party)
    {target : (V input depth count tag).Current}
    (nextEq : ((root input depth count tag).evolutionAt visit.current).nextCurrent? = some target) :
    (birth.next input depth count tag nextEq).actor input depth count tag =
      birth.actor input depth count tag := rfl

#print axioms lookup_retains_original_programme_actor
#print axioms current_participation_has_generated_birth
#print axioms At.next_keeps_the_original_M0_image

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors
