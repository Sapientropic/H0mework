import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.RegisteredProgramme

/-! Birth lookup folds only the already generated root history.  It keeps
the first original M0 occurrence for a key, including keys first encountered
after programme registration.  The returned actor is the existing M0 image
at that occurrence; no actor or authority is installed by a raw key alone. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.ActualBirth

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev root := (Root.ProgrammeLiving.livingRoot input).toAuthoritativeRoot.toRoot
abbrev Visit := RootVisit (root input)

def occurrence (visit : Visit input) : OriginalOccurrence (Root.ProgrammeSource.ledgerSource input) :=
  ⟨visit.current, Root.ProgrammeSource.emitted input visit.current⟩

def presentAt (visit : Visit input) (party : Party) : Prop :=
  party ∈ parties input.law ((Registered.reader input).raw (occurrence input visit))

instance (visit : Visit input) (party : Party) : Decidable (presentAt input visit party) :=
  inferInstanceAs (Decidable (party ∈ parties input.law ((Registered.reader input).raw (occurrence input visit))))

structure Witness where
  private mk ::
  visit : Visit input
  party : Party
  present : presentAt input visit party

/-- A dependent union of the existing source-generated M0 actors.  Its
original visit is retained, so equal display keys do not erase provenance. -/
abbrev Actor := (visit : Visit input) ×
  ProgrammeFace.Actor input.law (Registered.reader input).raw (occurrence input visit)

def Witness.actor (witness : Witness input) : Actor input :=
  ⟨witness.visit, ProgrammeFace.actor input.law (Registered.reader input).raw
    (occurrence input witness.visit) witness.party witness.present⟩

private def here (visit : Visit input) (party : Party) : Option (Witness input) :=
  if present : presentAt input visit party then some ⟨visit, party, present⟩ else none

private def fold : {current : (Root.ProgrammeSource.V input).Current} →
    (root input).ReachableAt current → Party → Option (Witness input)
  | _, .initial, party => here input (root input).initialVisit party
  | target, .step prior nextEq, party =>
      (fold prior party).orElse (fun _ => here input ⟨target, .step prior nextEq⟩ party)

def lookup (visit : Visit input) (party : Party) : Option (Witness input) := fold input visit.history party

private def partyFold : {current : (Root.ProgrammeSource.V input).Current} →
    (root input).ReachableAt current → List Party
  | _, .initial => parties input.law ((Registered.reader input).raw
      (occurrence input (root input).initialVisit))
  | target, .step prior nextEq =>
      (partyFold prior ++ parties input.law ((Registered.reader input).raw
        (occurrence input ⟨target, .step prior nextEq⟩))).dedup

/-- Historical participants are read from the existing finite history.
Absence from one new word cannot silently remove an original need bearer. -/
def participants (visit : Visit input) : List Party := partyFold input visit.history

omit [DecidableEq Port] in
theorem participants_next (visit : Visit input)
    {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some target) :
    participants input (visit.next nextEq) =
      (participants input visit ++ parties input.law ((Registered.reader input).raw
        (occurrence input (visit.next nextEq)))).dedup := rfl

omit [DecidableEq Port] in
theorem original_participant_is_retained (visit : Visit input)
    {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some target)
    (party : Party) (present : party ∈ participants input visit) :
    party ∈ participants input (visit.next nextEq) := by
  rw [participants_next]
  exact List.mem_dedup.mpr (List.mem_append_left _ present)

omit [DecidableEq Port] in
theorem participant_has_generated_birth (visit : Visit input) (party : Party)
    (present : party ∈ participants input visit) : (lookup input visit party).isSome = true := by
  rcases visit with ⟨current, history⟩
  induction history with
  | initial =>
      change presentAt input (root input).initialVisit party at present
      dsimp only [lookup, fold]
      simp only [here, dif_pos present, Option.isSome_some]
  | @step previous next prior nextEq earlier =>
      change party ∈ (partyFold input prior ++ parties input.law
        ((Registered.reader input).raw (occurrence input ⟨next, .step prior nextEq⟩))).dedup at present
      change ((fold input prior party).orElse
        (fun _ => here input ⟨next, .step prior nextEq⟩ party)).isSome = true
      rcases List.mem_append.mp (List.mem_dedup.mp present) with old | fresh
      · have found := earlier old
        change (fold input prior party).isSome = true at found
        cases selected : fold input prior party with
        | none => rw [selected] at found; cases found
        | some witness => rfl
      · have born : presentAt input ⟨next, .step prior nextEq⟩ party := fresh
        cases fold input prior party with
        | none => simp only [Option.orElse_none, here, dif_pos born, Option.isSome_some]
        | some witness => rfl

omit [DecidableEq Port] in
theorem lookup_next (visit : Visit input) {next : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some next) (party : Party) :
    lookup input (visit.next nextEq) party =
      (lookup input visit party).orElse (fun _ => here input (visit.next nextEq) party) := rfl

omit [DecidableEq Port] in
theorem lookup_map_initial {α : Type}
    (read : (Root.ProgrammeSource.V input).Current → Party → α) (party : Party) :
    (lookup input (root input).initialVisit party).map (fun witness => read witness.visit.current witness.party) =
      if presentAt input (root input).initialVisit party then
        some (read (root input).initialVisit.current party) else none := by
  change (here input (root input).initialVisit party).map _ = _
  unfold here
  split <;> rfl

omit [DecidableEq Port] in
theorem lookup_map_next {α : Type}
    (read : (Root.ProgrammeSource.V input).Current → Party → α)
    (visit : Visit input) {next : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some next) (party : Party) :
    (lookup input (visit.next nextEq) party).map (fun witness => read witness.visit.current witness.party) =
      ((lookup input visit party).map (fun witness => read witness.visit.current witness.party)).orElse
        (fun _ => if presentAt input (visit.next nextEq) party then some (read next party) else none) := by
  rw [lookup_next]
  cases lookup input visit party with
  | some witness => rfl
  | none =>
      change (here input (visit.next nextEq) party).map _ = _
      unfold here
      split <;> rfl

omit [DecidableEq Port] in
theorem lookup_retains_original_birth (visit : Visit input)
    {next : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some next)
    (party : Party) (witness : Witness input) (found : lookup input visit party = some witness) :
    lookup input (visit.next nextEq) party = some witness := by
  rw [lookup_next, found]
  rfl

omit [DecidableEq Port] in
theorem lookup_has_the_requested_key (visit : Visit input) (party : Party)
    (witness : Witness input) (found : lookup input visit party = some witness) : witness.party = party := by
  rcases visit with ⟨current, history⟩
  induction history with
  | initial =>
      unfold lookup fold here at found
      split at found
      · cases Option.some.inj found
        rfl
      · cases found
  | @step previous next prior nextEq earlier =>
      change (fold input prior party).orElse
        (fun _ => here input ⟨next, .step prior nextEq⟩ party) = some witness at found
      cases original : fold input prior party with
      | some old =>
          simp only [original, Option.orElse_some, Option.some.injEq] at found
          subst witness
          exact earlier original
      | none =>
          simp only [original, Option.orElse_none, here] at found
          split at found
          · cases Option.some.inj found
            rfl
          · cases found

omit [DecidableEq Port] in
theorem current_participation_generates_birth (visit : Visit input) (party : Party)
    (present : presentAt input visit party) : (lookup input visit party).isSome = true := by
  rcases visit with ⟨current, history⟩
  cases history with
  | initial =>
      dsimp only [lookup, fold]
      have actual : presentAt input (root input).initialVisit party := present
      simp only [here, dif_pos actual, Option.isSome_some]
  | step prior nextEq =>
      change ((fold input prior party).orElse (fun _ => here input ⟨_, .step prior nextEq⟩ party)).isSome = true
      cases fold input prior party with
      | none => simp only [Option.orElse_none, here, dif_pos present, Option.isSome_some]
      | some old => rfl

def atCurrent (visit : Visit input) (party : Party) (present : presentAt input visit party) : Witness input :=
  (lookup input visit party).get (current_participation_generates_birth input visit party present)

omit [DecidableEq Port] in
theorem atCurrent_is_original (visit : Visit input) (party : Party) (present : presentAt input visit party) :
    lookup input visit party = some (atCurrent input visit party present) :=
  (Option.some_get (current_participation_generates_birth input visit party present)).symm

omit [DecidableEq Port] in
theorem atCurrent_key (visit : Visit input) (party : Party) (present : presentAt input visit party) :
    (atCurrent input visit party present).party = party :=
  lookup_has_the_requested_key input visit party _ (atCurrent_is_original input visit party present)

structure At (visit : Visit input) (party : Party) where
  private mk ::
  original : Witness input
  generated : lookup input visit party = some original

def fromHistory (visit : Visit input) (party : Party) (present : party ∈ participants input visit) :
    At input visit party :=
  ⟨(lookup input visit party).get (participant_has_generated_birth input visit party present),
    (Option.some_get (participant_has_generated_birth input visit party present)).symm⟩

def generate (visit : Visit input) (party : Party) (present : presentAt input visit party) :
    At input visit party :=
  ⟨atCurrent input visit party present, atCurrent_is_original input visit party present⟩

def At.actor {visit : Visit input} {party : Party} (birth : At input visit party) : Actor input :=
  birth.original.actor input

omit [DecidableEq Port] in
theorem At.key_exact {visit : Visit input} {party : Party} (birth : At input visit party) :
    birth.original.party = party := lookup_has_the_requested_key input visit party birth.original birth.generated

def At.next {visit : Visit input} {party : Party} (birth : At input visit party)
    {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some target) :
    At input (visit.next nextEq) party :=
  ⟨birth.original, lookup_retains_original_birth input visit nextEq party birth.original birth.generated⟩

theorem At.next_keeps_the_original_M0_actor {visit : Visit input} {party : Party}
    (birth : At input visit party) {target : (Root.ProgrammeSource.V input).Current}
    (nextEq : ((root input).evolutionAt visit.current).nextCurrent? = some target) :
    (birth.next input nextEq).actor input = birth.actor input := rfl

#print axioms current_participation_generates_birth
#print axioms At.next_keeps_the_original_M0_actor

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.ActualBirth
