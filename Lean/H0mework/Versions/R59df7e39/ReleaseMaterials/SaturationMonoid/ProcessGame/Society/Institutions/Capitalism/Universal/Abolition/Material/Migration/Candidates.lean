import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Renewal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Root.ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev CodePair (Party Good Port Technology Instrument : Type) :=
  RawEvent Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument

def sourceAlphabet (current : RawCurrent Party Good Technology Instrument) :=
  input.localAttempts current ++ Root.ProgrammeSource.wordAt input current

def sourceWords (current : RawCurrent Party Good Technology Instrument) (limit : Nat) :=
  PublicFunction.words (sourceAlphabet input current) limit

/-- The second alphabet is read only after interpreting the actual prefix
code. Neither a target state nor a successful pair is an input. -/
def sourcePairs (current : RawCurrent Party Good Technology Instrument)
    (prefixLimit renewalLimit : Nat) : List (CodePair Party Good Port Technology Instrument) :=
  (sourceWords input current prefixLimit).flatMap fun front =>
    (sourceWords input (input.law.next current front) renewalLimit).map (fun renewal => (front, renewal))

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem sourceWords_complete (current : RawCurrent Party Good Technology Instrument)
    (limit : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    word ∈ sourceWords input current limit ↔ word.length ≤ limit ∧
      ∀ request ∈ word, request ∈ sourceAlphabet input current :=
  PublicFunction.mem_words_iff _ limit word

theorem sourcePairs_complete (current : RawCurrent Party Good Technology Instrument)
    (prefixLimit renewalLimit : Nat) (pair : CodePair Party Good Port Technology Instrument) :
    pair ∈ sourcePairs input current prefixLimit renewalLimit ↔
      (pair.1.length ≤ prefixLimit ∧ ∀ request ∈ pair.1, request ∈ sourceAlphabet input current) ∧
      (pair.2.length ≤ renewalLimit ∧ ∀ request ∈ pair.2,
        request ∈ sourceAlphabet input (input.law.next current pair.1)) := by
  constructor
  · intro member
    obtain ⟨front, generated, second⟩ := List.mem_flatMap.mp member
    obtain ⟨renewal, subsequent, same⟩ := List.mem_map.mp second
    cases same
    exact ⟨(sourceWords_complete input current prefixLimit front).mp generated,
      (sourceWords_complete input _ renewalLimit renewal).mp subsequent⟩
  · rintro ⟨front, renewal⟩
    exact List.mem_flatMap.mpr ⟨pair.1, (sourceWords_complete input _ _ _).mpr front,
      List.mem_map.mpr ⟨pair.2, (sourceWords_complete input _ _ _).mpr renewal, Prod.eta _⟩⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration
