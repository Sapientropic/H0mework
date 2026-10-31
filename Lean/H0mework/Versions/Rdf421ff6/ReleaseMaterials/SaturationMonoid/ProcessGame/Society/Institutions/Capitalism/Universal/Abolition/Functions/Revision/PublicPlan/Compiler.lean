import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan.Types
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Source

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

theorem a_publicly_available_source_word_cannot_be_vetoed
    (available : ∃ word ∈ candidates input depth count prefixLimit renewalLimit snapshot,
      Checks input depth count prefixLimit renewalLimit snapshot word) :
    ∃ plan, compile input depth count prefixLimit renewalLimit snapshot = .accepted plan := by
  cases generated : compile input depth count prefixLimit renewalLimit snapshot with
  | accepted plan => exact ⟨plan, rfl⟩
  | obstructed obstruction =>
      obtain ⟨word, present, checked⟩ := available
      exact (obstruction.excluded word present checked).elim

/-- Only automatic renewal is rewritten to this finite actual program.
New requests keep their original raw source and are checked at their own cut. -/
def reader (plan : Plan input depth count prefixLimit renewalLimit snapshot)
    (original : Macro.Raw.Reader input depth count) : Macro.Raw.Reader input depth count :=
  fun current account => match original current account with
    | .advance => .execute plan.rawWord
    | other => other

theorem the_selected_program_does_not_require_an_old_renewal_phase
    (plan : Plan input depth count prefixLimit renewalLimit snapshot) :
    Macro.Public.Scope.Checks input depth count prefixLimit renewalLimit snapshot.past publicStart
      (executable plan.rawWord) := plan.checked

#print axioms compile
#print axioms a_publicly_available_source_word_cannot_be_vetoed
#print axioms reader

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.PublicPlan
