import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.ReviewPhase.Context

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}

/-- Input equality transports the already registered creator. It does not
identify its original task with a later raw declaration. -/
def registeredOrigin (review : Option (ReviewPhase.ContextAt input)) : Option (OriginAt input) :=
  review.map (fun context => Eq.mp (congrArg OriginAt context.source_eq) (.outstanding context.source))

theorem a_registered_legacy_creator_is_not_undisclosed (context : ReviewPhase.ContextAt input) :
    ∃ origin, registeredOrigin (some context) = some origin := ⟨_, rfl⟩

variable [DecidableEq Port]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (snapshot : Physical.Cursor Party Good Port Technology Instrument)

/-- These are two restrictions of already supplied source data. Neither
known creator overrides the other, even if their displayed tasks agree. -/
structure ReadoutsAt where
  explicit : ReadoutAt input depth count prefixLimit renewalLimit snapshot
  registered : ReadoutAt input depth count prefixLimit renewalLimit snapshot

def readouts (explicit : Option (OriginAt input)) (review : Option (ReviewPhase.ContextAt input)) :
    ReadoutsAt input depth count prefixLimit renewalLimit snapshot :=
  ⟨readout input depth count prefixLimit renewalLimit snapshot explicit,
    readout input depth count prefixLimit renewalLimit snapshot (registeredOrigin review)⟩

theorem both_known_creators_keep_their_own_complete_state
    (explicit : OriginAt input) (review : ReviewPhase.ContextAt input) :
    ∃ left right,
      (readouts input depth count prefixLimit renewalLimit snapshot (some explicit) (some review)).explicit = .recorded left ∧
      (readouts input depth count prefixLimit renewalLimit snapshot (some explicit) (some review)).registered = .recorded right ∧
      left.origin = explicit ∧ some right.origin = registeredOrigin (some review) :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

#print axioms both_known_creators_keep_their_own_complete_state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native
