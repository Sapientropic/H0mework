import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Origin

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue
open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
noncomputable section

theorem an_actual_accepted_issue_generates_its_original_native_claim
    (input : ProgrammeSource.Input Bool Bool Bool Unit Unit) (depth count : Nat)
    (item : Abolition.Root.Epoch.Finance.ActualItem input depth count)
    (original : (item.instruction input depth count).request.operation = .issue () false true 1)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request) :
    (Abolition.Root.Epoch.Finance.readNewClaim input depth count item).isSome = true := by
  unfold Abolition.Root.Epoch.Finance.readNewClaim
  split <;> simp_all

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Consumers.Issue
