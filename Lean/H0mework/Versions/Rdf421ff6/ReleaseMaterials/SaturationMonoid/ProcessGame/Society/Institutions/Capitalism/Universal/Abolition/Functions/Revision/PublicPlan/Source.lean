import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Candidates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (snapshot : Physical.Cursor Party Good Port Technology Instrument)

abbrev oldCurrent := Physical.stateAt input depth count prefixLimit renewalLimit snapshot.past
abbrev publicStart := Physical.initial (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)

def executable (word : RawEvent Party Good Port Technology Instrument) :=
  word.map (fun request => request.resign request.signer)

def currentWord : List (RawEvent Party Good Port Technology Instrument) :=
  match (oldCurrent input depth count prefixLimit renewalLimit snapshot).phase with
  | .renewal word => [word]
  | .seeking => []

def proposedWords : Compile.RawInput Party Good Port Technology Instrument →
    List (RawEvent Party Good Port Technology Instrument)
  | .primitive request => [[request]]
  | .execute word => [word]
  | .migrate pair => [pair.1 ++ pair.2]
  | .advance | .review _ | .code _ | .stopReview => []

def alphabet :=
  Material.Migration.sourceAlphabet input (oldCurrent input depth count prefixLimit renewalLimit snapshot).raw ++
    (currentWord input depth count prefixLimit renewalLimit snapshot).flatten

/-- The finite current code and unfiltered local attempts supply the
domain. Old-law permission never filters a proposed public action. -/
def candidates :=
  proposedWords snapshot.incoming ++ currentWord input depth count prefixLimit renewalLimit snapshot ++
    [ProgrammeSource.wordAt input (oldCurrent input depth count prefixLimit renewalLimit snapshot).raw] ++
    PublicFunction.words (alphabet input depth count prefixLimit renewalLimit snapshot) (prefixLimit + renewalLimit)

abbrev Checks (word : RawEvent Party Good Port Technology Instrument) :=
  Macro.Public.Scope.Checks input depth count prefixLimit renewalLimit snapshot.past publicStart (executable word)

instance (word : RawEvent Party Good Port Technology Instrument) :
    Decidable (Checks input depth count prefixLimit renewalLimit snapshot word) := by
  unfold Checks Macro.Public.Scope.Checks Review.Guarded.Checks
  infer_instance

theorem checks_use_the_literal_original_current :
    Macro.Public.Scope.actualState input depth count prefixLimit renewalLimit snapshot.past publicStart =
      oldCurrent input depth count prefixLimit renewalLimit snapshot := rfl

theorem every_actual_member_is_checked (word : RawEvent Party Good Port Technology Instrument)
    (person : Party) (present : person ∈ Epoch.Interface.Actors.Census.parties input depth count
      prefixLimit renewalLimit (Physical.Prefix.cursor snapshot.past)) :
    person ∈ Macro.Public.Scope.scope input depth count prefixLimit renewalLimit snapshot.past publicStart
      (executable word) :=
  Macro.Public.Scope.every_current_standing_is_checked input depth count prefixLimit renewalLimit snapshot.past
    publicStart (executable word) person
    (Epoch.Interface.Actors.PublicCensus.every_old_member_keeps_current_standing input depth count
      prefixLimit renewalLimit snapshot.past publicStart person present)

#print axioms candidates
#print axioms every_actual_member_is_checked

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan
