import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Root.Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Functions.Revision.InitialAdmissionAt origin}
  (frame : Macro.Public.Runtime.Frame origin admission)

def assess : Decision input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot :=
  check input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot

theorem the_full_assessment_keeps_the_same_actual_current_and_native_account :
    Dividend.publicCurrent input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot =
      (Macro.Runtime.ActivatedFrame.enacted origin admission frame).actualState ∧
    (Macro.Runtime.ActivatedFrame.enacted origin admission frame).nativeAccount = frame.account := ⟨rfl, rfl⟩

theorem every_actual_assessment_returns_strict_full_account_gain_or_its_original_issue :
    match assess frame with
    | .accepted _checked =>
        (Dividend.publicCurrent input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot).raw.clock =
          (Dividend.oldEndpoint input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot).clock ∧
        (∀ person good, 0 ≤ delta input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot person good) ∧
        (∃ person good, 0 < delta input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot person good)
    | .rejected _ => ¬ Checks input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot := by
  split
  · rename_i checked generated
    exact ⟨checked.2.2.1,
      all_original_bearers_and_goods_keep_their_full_account_share _ _ _ _ _ _ _ checked,
      one_original_bearer_and_unit_has_strict_full_account_gain _ _ _ _ _ _ _ checked⟩
  · rename_i issue generated
    exact issue.refutes _ _ _ _ _ _ _

#print axioms assess
#print axioms every_actual_assessment_returns_strict_full_account_gain_or_its_original_issue

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial
