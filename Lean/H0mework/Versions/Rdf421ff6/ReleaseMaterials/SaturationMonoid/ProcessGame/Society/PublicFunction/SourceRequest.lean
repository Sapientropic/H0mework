import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction

open Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Admission of primitive source requests, not a service plan or endpoint.
The interpreter checks each request at its own preceding execution state. -/
structure IncomingWord (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument) where
  private mk ::
  word : RawEvent Party Good Port Technology Instrument
  nonempty : word ≠ []
  accepted : ∀ item ∈ law.rawItems current word, law.Valid item.before item.request

namespace IncomingWord

def check (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Option (IncomingWord law current) :=
  if nonempty : word ≠ [] then
    if accepted : ∀ item ∈ law.rawItems current word, law.Valid item.before item.request then
      some ⟨word, nonempty, accepted⟩
    else none
  else none

theorem checked_word (law : RawLaw Party Good Port Technology Instrument) (current) (word)
    (incoming : IncomingWord law current) (checked : check law current word = some incoming) :
    incoming.word = word := by
  unfold check at checked
  split at checked
  · split at checked
    · cases Option.some.inj checked
      rfl
    · cases checked
  · cases checked

end IncomingWord
end SaturationMonoid.ProcessGame.Society.PublicFunction
