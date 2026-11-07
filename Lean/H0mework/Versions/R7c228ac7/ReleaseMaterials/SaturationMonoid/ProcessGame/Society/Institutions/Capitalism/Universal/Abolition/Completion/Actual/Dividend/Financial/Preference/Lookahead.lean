import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Functions.Revision.Adaptive.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Lookahead

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (current : Physical.Cursor Party Good Port Technology Instrument)

/-- Only the next current's original finite syntax and full current guard
are inspected. No future execution or receipt is installed by this test. -/
def Available : Prop :=
  ∃ word ∈ Functions.Revision.Adaptive.candidates input depth count prefixLimit renewalLimit oldPast current,
    Functions.Revision.Adaptive.Checks input depth count prefixLimit renewalLimit oldPast current word

instance : Decidable (Available input depth count prefixLimit renewalLimit oldPast current) := by
  unfold Available
  infer_instance

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Preference.Lookahead
