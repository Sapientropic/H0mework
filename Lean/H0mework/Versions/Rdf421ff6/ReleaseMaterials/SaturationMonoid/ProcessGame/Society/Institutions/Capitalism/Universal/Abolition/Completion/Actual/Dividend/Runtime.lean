import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Claims
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend

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

/-- The current package, rather than a proposed endpoint, supplies the
literal admission seed, consumed public execution and original account. -/
def assess : Decision input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot :=
  check input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot

theorem the_assessment_reads_the_original_actual_current :
    publicCurrent input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot =
      (Macro.Runtime.ActivatedFrame.enacted origin admission frame).actualState := rfl

theorem the_assessment_preserves_the_literal_original_native_account :
    (Macro.Runtime.ActivatedFrame.enacted origin admission frame).nativeAccount = frame.account := rfl

theorem every_actual_assessment_returns_strict_same_window_gain_or_its_original_issue :
    match assess frame with
    | .accepted _checked =>
        (publicCurrent input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot).raw.clock =
          (oldEndpoint input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot).clock ∧
        (∀ person good,
          (oldEndpoint input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot).stock person good ≤
            (Macro.Runtime.ActivatedFrame.enacted origin admission frame).actualState.raw.stock person good) ∧
        (∃ person good,
          (oldEndpoint input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot).stock person good <
            (Macro.Runtime.ActivatedFrame.enacted origin admission frame).actualState.raw.stock person good) ∧
        (Macro.Runtime.ActivatedFrame.enacted origin admission frame).actualState.raw.claims =
          (seed input depth count prefixLimit renewalLimit origin.germ.snapshot.past).raw.claims
    | .rejected _ => ¬ Checks input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.snapshot := by
  split
  · rename_i checked generated
    exact ⟨checked.2.2.2.1,
      all_original_bearers_and_goods_have_no_material_loss _ _ _ _ _ _ _ checked,
      one_literal_material_unit_strictly_increases _ _ _ _ _ _ _ checked,
      (a_strict_actual_material_dividend_keeps_all_original_raw_claims _ _ _ _ _ _ _ checked).2⟩
  · rename_i issue generated
    exact issue.refutes _ _ _ _ _ _ _

#print axioms assess
#print axioms every_actual_assessment_returns_strict_same_window_gain_or_its_original_issue

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend
