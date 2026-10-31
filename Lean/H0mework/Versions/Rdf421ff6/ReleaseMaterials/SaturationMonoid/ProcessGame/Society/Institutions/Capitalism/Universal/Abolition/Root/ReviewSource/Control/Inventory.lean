import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control.History
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Candidates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Registered

variable {Party Good Port Technology Instrument : Type}

/-- Both words come from the one finite registered alphabet. Their guards
are checked only after the next fee is actually paid. These lengths count
code, not resources, service payments, or elapsed physical time. -/
def Code.candidates (code : Code Party Good Port Technology Instrument)
    (prefixLimit renewalLimit : Nat) : List (Abolition.Material.Migration.CodePair Party Good Port Technology Instrument) :=
  (PublicFunction.words code.alphabet prefixLimit).flatMap fun front =>
    (PublicFunction.words code.alphabet renewalLimit).map fun tail => (front, tail)

theorem Code.candidates_are_exactly_the_original_finite_code
    (code : Code Party Good Port Technology Instrument) (prefixLimit renewalLimit : Nat)
    (pair : Abolition.Material.Migration.CodePair Party Good Port Technology Instrument) :
    pair ∈ code.candidates prefixLimit renewalLimit ↔
      (pair.1.length ≤ prefixLimit ∧ ∀ request ∈ pair.1, request ∈ code.alphabet) ∧
      (pair.2.length ≤ renewalLimit ∧ ∀ request ∈ pair.2, request ∈ code.alphabet) := by
  constructor
  · intro present
    obtain ⟨front, first, second⟩ := List.mem_flatMap.mp present
    obtain ⟨tail, latter, same⟩ := List.mem_map.mp second
    cases same
    exact ⟨(PublicFunction.mem_words_iff _ _ _).mp first,
      (PublicFunction.mem_words_iff _ _ _).mp latter⟩
  · rintro ⟨front, tail⟩
    exact List.mem_flatMap.mpr ⟨pair.1, (PublicFunction.mem_words_iff _ _ _).mpr front,
      List.mem_map.mpr ⟨pair.2, (PublicFunction.mem_words_iff _ _ _).mpr tail, Prod.eta _⟩⟩

noncomputable section

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

def sourceInventory (current : Physical.Cursor Party Good Port Technology Instrument) :=
  (recovered input depth count prefixLimit renewalLimit current).map fun located =>
    located.registration.code.candidates prefixLimit renewalLimit

theorem later_proposals_cannot_refill_the_original_candidate_inventory
    (current : Physical.Cursor Party Good Port Technology Instrument)
    (located : Located input depth count prefixLimit renewalLimit)
    (original : recovered input depth count prefixLimit renewalLimit current = some located)
    (proposal : Compile.RawInput Party Good Port Technology Instrument) :
    sourceInventory input depth count prefixLimit renewalLimit (Physical.next (Physical.receive current proposal)) =
      some (located.registration.code.candidates prefixLimit renewalLimit) := by
  unfold sourceInventory
  rw [later_registered_code_cannot_replace_the_original_epoch input depth count prefixLimit renewalLimit current located original proposal]
  rfl

#print axioms Code.candidates_are_exactly_the_original_finite_code
#print axioms later_proposals_cannot_refill_the_original_candidate_inventory

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Control
