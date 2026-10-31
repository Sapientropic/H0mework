import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.Public.Census
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Result
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

/-- This is only the existing checker's law parameter. No source, actor,
account, history or initial current is constructed from this view. -/
def checkInput := { input with law := Physical.Public.interpreter input }

def actualState := Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast current.past

def periodWord? (raw : Compile.RawInput Party Good Port Technology Instrument) :
    Option (RawEvent Party Good Port Technology Instrument) :=
  match raw with
  | .advance | .execute _ => Physical.Public.wordAt (actualState input depth count prefixLimit renewalLimit oldPast current) raw
  | .primitive _ | .code _ | .migrate _ | .review _ | .stopReview => none

def scope (word : RawEvent Party Good Port Technology Instrument) : List Party :=
  (Epoch.Interface.Actors.PublicCensus.parties input depth count prefixLimit renewalLimit oldPast current ++
    Source.ProgrammeFace.parties (Physical.Public.interpreter input)
      ((actualState input depth count prefixLimit renewalLimit oldPast current).raw, word)).dedup

abbrev Checks (word : RawEvent Party Good Port Technology Instrument) :=
  Review.Guarded.Checks (checkInput input) (Actual.origin input depth count)
    (actualState input depth count prefixLimit renewalLimit oldPast current).raw
    (scope input depth count prefixLimit renewalLimit oldPast current word) word

theorem every_current_standing_is_checked
    (word : RawEvent Party Good Port Technology Instrument) (person : Party)
    (present : person ∈ Epoch.Interface.Actors.PublicCensus.parties input depth count prefixLimit renewalLimit oldPast current) :
    person ∈ scope input depth count prefixLimit renewalLimit oldPast current word :=
  List.mem_dedup.mpr (List.mem_append_left _ present)

theorem a_primitive_is_a_microstep_without_a_period_guard
    (request : Request Party Good Port Technology Instrument) :
    periodWord? input depth count prefixLimit renewalLimit oldPast current (.primitive request) = none := rfl

theorem an_explicit_word_uses_its_own_period_check
    (word : RawEvent Party Good Port Technology Instrument) :
    periodWord? input depth count prefixLimit renewalLimit oldPast current (.execute word) =
      some (word.map (fun request => request.resign request.signer)) := rfl

#print axioms actualState
#print axioms scope
#print axioms every_current_standing_is_checked

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope
