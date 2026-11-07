import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Prelude
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Census

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source Source.Program Source.ProgrammeFace
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
private theorem original_lookup_iff (visit : ActualBirth.Visit input) (party : Party) :
    (ActualBirth.lookup input visit party).isSome = true ↔ party ∈ ActualBirth.participants input visit := by
  constructor
  · intro found
    rcases visit with ⟨current, history⟩
    induction history with
    | initial =>
        change (ActualBirth.lookup input (ActualBirth.root input).initialVisit party).isSome = true at found
        have mapped := ActualBirth.lookup_map_initial input (fun _ _ => ()) party
        have isSome : ((ActualBirth.lookup input (ActualBirth.root input).initialVisit party).map
            (fun witness => (fun _ _ => ()) witness.visit.current witness.party)).isSome = true := by
          simpa using found
        rw [mapped] at isSome
        split at isSome
        next present => exact present
        next => cases isSome
    | @step previous target prior nextEq ih =>
        let before : ActualBirth.Visit input := ⟨previous, prior⟩
        let after := before.next nextEq
        change (ActualBirth.lookup input after party).isSome = true at found
        change party ∈ ActualBirth.participants input after
        rw [ActualBirth.participants_next]
        apply List.mem_dedup.mpr
        cases old : ActualBirth.lookup input before party with
        | some witness =>
            apply List.mem_append_left
            exact ih (by rw [old]; rfl)
        | none =>
            apply List.mem_append_right
            have mapped := ActualBirth.lookup_map_next input (fun _ _ => ()) before nextEq party
            have isSome : ((ActualBirth.lookup input after party).map
                (fun witness => (fun _ _ => ()) witness.visit.current witness.party)).isSome = true := by
              simpa using found
            rw [mapped, old] at isSome
            simp only [Option.map_none, Option.orElse_none] at isSome
            split at isSome
            next present => exact present
            next => cases isSome
  · exact ActualBirth.participant_has_generated_birth input visit party

variable (depth count prefixLimit renewalLimit : Nat)

abbrev Input := Compile.RawInput Party Good Port Technology Instrument

private def eventParties (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : List Party :=
  actualParties input depth count (ActualOccurrence.eventTag input depth count prefixLimit renewalLimit past raw)
    (ActualOccurrence.eventVisit input depth count prefixLimit renewalLimit past raw)

private theorem event_lookup_iff
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) (party : Party) :
    (ActualPast.atEvent input depth count prefixLimit renewalLimit past raw party).isSome = true ↔
      party ∈ eventParties input depth count prefixLimit renewalLimit past raw := by
  unfold ActualPast.atEvent
  split
  next present => exact ⟨fun _ => present, fun _ => rfl⟩
  next absent => exact ⟨fun impossible => Bool.noConfusion impossible, fun member => (absent member).elim⟩

private theorem scan_lookup_iff
    (past remaining : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (party : Party) :
    (ActualPast.scan input depth count prefixLimit renewalLimit past remaining party).isSome = true ↔
      ∃ position : Fin remaining.length,
        party ∈ eventParties input depth count prefixLimit renewalLimit
          (past ++ remaining.take position.val) (remaining.get position) := by
  induction remaining generalizing past with
  | nil => simp [ActualPast.scan]
  | cons raw remaining ih =>
      have next := ih (past ++ [raw])
      have head := event_lookup_iff input depth count prefixLimit renewalLimit past raw party
      simp only [ActualPast.scan, List.length_cons, Fin.exists_fin_succ,
        Fin.val_zero, List.take_zero, List.append_nil, List.get_eq_getElem,
        Fin.val_succ, List.take_succ_cons, List.getElem_cons_zero, List.getElem_cons_succ]
      have tailEq : (∃ position : Fin remaining.length,
          party ∈ eventParties input depth count prefixLimit renewalLimit
            (past ++ raw :: remaining.take position.val) remaining[position.val]) ↔
          (ActualPast.scan input depth count prefixLimit renewalLimit (past ++ [raw]) remaining party).isSome = true := by
        simpa only [List.append_assoc, List.singleton_append, List.get_eq_getElem] using next.symm
      rw [tailEq, ← head]
      cases ActualPast.atEvent input depth count prefixLimit renewalLimit past raw party <;> simp

/-- Only the completed raw prefix contributes new keys. The next incoming
request is deliberately absent from this finite source-derived census. -/
def parties (snapshot : Physical.Cursor Party Good Port Technology Instrument) : List Party :=
  (Actual.members input depth count ++
    (List.finRange snapshot.past.length).flatMap fun position =>
      actualParties input depth count (.actual prefixLimit renewalLimit (Physical.Prefix.eventCursor snapshot.past position))
        (root input depth count (.actual prefixLimit renewalLimit (Physical.Prefix.eventCursor snapshot.past position))).initialVisit).dedup

theorem membership_is_exactly_the_original_prelude
    (snapshot : Physical.Cursor Party Good Port Technology Instrument) (party : Party) :
    party ∈ parties input depth count prefixLimit renewalLimit snapshot ↔
      (prelude input depth count (.actual prefixLimit renewalLimit snapshot) party).isSome = true := by
  simp only [parties, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
  have old := original_lookup_iff input (Settlement.committedVisit input depth count) party
  have later := scan_lookup_iff input depth count prefixLimit renewalLimit [] snapshot.past party
  change (party ∈ Actual.members input depth count ∨ _) ↔ _
  have historical : (ActualPast.first input depth count prefixLimit renewalLimit snapshot.past party).isSome = true ↔
      ∃ position : Fin snapshot.past.length,
        party ∈ actualParties input depth count
          (.actual prefixLimit renewalLimit (Physical.Prefix.eventCursor snapshot.past position))
          (root input depth count (.actual prefixLimit renewalLimit (Physical.Prefix.eventCursor snapshot.past position))).initialVisit := by
    simpa only [ActualPast.first, List.nil_append, eventParties, ActualOccurrence.eventTag,
      ActualOccurrence.eventVisit, ActualOccurrence.eventCursor, Physical.Prefix.eventCursor] using later
  rw [← historical]
  change (party ∈ ActualBirth.participants input (Settlement.committedVisit input depth count) ∨ _) ↔ _
  rw [← old]
  unfold prelude Epoch.Actors.oldLookup
  cases ActualBirth.lookup input (Settlement.committedVisit input depth count) party <;> simp

def image? (snapshot : Physical.Cursor Party Good Port Technology Instrument) (party : Party) : Option (Image input depth count) :=
  (prelude input depth count (.actual prefixLimit renewalLimit snapshot) party).map (Location.actor input depth count)

theorem membership_generates_the_existing_M0_image
    (snapshot : Physical.Cursor Party Good Port Technology Instrument) (party : Party) :
    party ∈ parties input depth count prefixLimit renewalLimit snapshot ↔
      (image? input depth count prefixLimit renewalLimit snapshot party).isSome = true := by
  simpa only [image?, Option.isSome_map] using
    membership_is_exactly_the_original_prelude input depth count prefixLimit renewalLimit snapshot party

theorem member_has_its_existing_source_location
    (snapshot : Physical.Cursor Party Good Port Technology Instrument) (party : Party)
    (member : party ∈ parties input depth count prefixLimit renewalLimit snapshot) :
    ∃ location : Location input depth count,
      prelude input depth count (.actual prefixLimit renewalLimit snapshot) party = some location ∧
      location.party input depth count = party ∧
      image? input depth count prefixLimit renewalLimit snapshot party = some (location.actor input depth count) := by
  have present := (membership_is_exactly_the_original_prelude input depth count prefixLimit renewalLimit snapshot party).mp member
  let location := (prelude input depth count (.actual prefixLimit renewalLimit snapshot) party).get present
  have same : prelude input depth count (.actual prefixLimit renewalLimit snapshot) party = some location :=
    (Option.some_get present).symm
  exact ⟨location, same, prelude_key input depth count _ party location same, by simp only [image?, same, Option.map_some]⟩

theorem incoming_code_cannot_create_current_standing
    (snapshot : Physical.Cursor Party Good Port Technology Instrument)
    (incoming : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    parties input depth count prefixLimit renewalLimit (Physical.receive snapshot incoming) =
      parties input depth count prefixLimit renewalLimit snapshot ∧
    image? input depth count prefixLimit renewalLimit (Physical.receive snapshot incoming) =
      image? input depth count prefixLimit renewalLimit snapshot := ⟨rfl, rfl⟩

#print axioms membership_is_exactly_the_original_prelude
#print axioms membership_generates_the_existing_M0_image
#print axioms member_has_its_existing_source_location
#print axioms incoming_code_cannot_create_current_standing

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Census
