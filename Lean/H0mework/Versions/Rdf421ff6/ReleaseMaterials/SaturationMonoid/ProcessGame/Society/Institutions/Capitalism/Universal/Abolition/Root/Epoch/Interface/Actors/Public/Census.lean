import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Public.Scan
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Census
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicContinuity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))

/-- Existing M0 locations are inherited first. Only already consumed
public events add locations; incoming syntax supplies no current actor. -/
def parties (snapshot : Physical.Cursor Party Good Port Technology Instrument) : List Party :=
  (Census.parties input depth count prefixLimit renewalLimit (Physical.Prefix.cursor oldPast) ++
    (List.finRange snapshot.past.length).flatMap fun position =>
      actualParties input depth count (.publicActual prefixLimit renewalLimit oldPast (Physical.Prefix.eventCursor snapshot.past position))
        (root input depth count (.publicActual prefixLimit renewalLimit oldPast (Physical.Prefix.eventCursor snapshot.past position))).initialVisit).dedup

theorem membership_is_exactly_the_inherited_or_new_M0_location
    (snapshot : Physical.Cursor Party Good Port Technology Instrument) (party : Party) :
    party ∈ parties input depth count prefixLimit renewalLimit oldPast snapshot ↔
      (prelude input depth count (.publicActual prefixLimit renewalLimit oldPast snapshot) party).isSome = true := by
  simp only [parties, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
  have old := Census.membership_is_exactly_the_original_prelude input depth count prefixLimit renewalLimit
    (Physical.Prefix.cursor oldPast) party
  have later := scan_lookup_iff input depth count prefixLimit renewalLimit oldPast [] snapshot.past party
  have historical : (PublicPast.first input depth count prefixLimit renewalLimit oldPast snapshot.past party).isSome = true ↔
      ∃ position : Fin snapshot.past.length,
        party ∈ actualParties input depth count
          (.publicActual prefixLimit renewalLimit oldPast (Physical.Prefix.eventCursor snapshot.past position))
          (root input depth count (.publicActual prefixLimit renewalLimit oldPast (Physical.Prefix.eventCursor snapshot.past position))).initialVisit := by
    simpa only [PublicPast.first, List.nil_append, eventParties, PublicPast.eventTag, PublicPast.eventVisit,
      ActualOccurrence.eventCursor, Physical.Prefix.eventCursor] using later
  rw [old, ← historical]
  unfold prelude
  simp only [Physical.Prefix.past_readback]
  cases Epoch.Actors.oldLookup input depth count party <;>
    cases ActualPast.first input depth count prefixLimit renewalLimit oldPast party <;> simp

theorem every_old_member_keeps_current_standing
    (snapshot : Physical.Cursor Party Good Port Technology Instrument) (party : Party)
    (old : party ∈ Census.parties input depth count prefixLimit renewalLimit (Physical.Prefix.cursor oldPast)) :
    party ∈ parties input depth count prefixLimit renewalLimit oldPast snapshot :=
  List.mem_dedup.mpr (List.mem_append_left _ old)

theorem incoming_code_cannot_create_public_current_standing
    (snapshot : Physical.Cursor Party Good Port Technology Instrument)
    (incoming : Compile.RawInput Party Good Port Technology Instrument) :
    parties input depth count prefixLimit renewalLimit oldPast (Physical.receive snapshot incoming) =
      parties input depth count prefixLimit renewalLimit oldPast snapshot := rfl

#print axioms membership_is_exactly_the_inherited_or_new_M0_location
#print axioms every_old_member_keeps_current_standing
#print axioms incoming_code_cannot_create_public_current_standing

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicCensus
