import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Inventory
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Terminal

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Consumers

open ResponsibilityLifecycle Source.Program
open Abolition.Root
open Abolition.Completion.Actual.Dividend

noncomputable section

private theorem the_two_original_trial_payments_are_settlements (version : Nat) :
    (∃ debtor holder quantity, (Innovation.Installation.firstSettlement version).operation = .settle () debtor holder quantity) ∧
    (∃ debtor holder quantity, (Innovation.Installation.lastSettlement version).operation = .settle () debtor holder quantity) := by
  by_cases zero : version = 0
  · exact ⟨⟨1,0,Innovation.Control.Scenario.coverageUnits,by
        simp [Innovation.Installation.firstSettlement,zero,Innovation.Control.Scenario.failureCoverage,Innovation.Control.Scenario.request]⟩,
      ⟨0,1,3,by
        simp [Innovation.Installation.lastSettlement,zero,Innovation.Control.Scenario.repay,Innovation.Control.Scenario.request]⟩⟩
  · exact ⟨⟨0,1,3,by
        simp [Innovation.Installation.firstSettlement,zero,Innovation.Control.Scenario.repay,Innovation.Control.Scenario.request]⟩,
      ⟨0,1,Innovation.Control.Scenario.premiumUnits,by
        simp [Innovation.Installation.lastSettlement,zero,Innovation.Control.Scenario.successPayment,Innovation.Control.Scenario.request]⟩⟩

/-- These are the actual items consumed by the original root. Their cash is
already the performance of their original claims, not a second book profit. -/
theorem actual_native_contribution_settlement_is_not_counted_as_new_profit_again
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    ∃ first last : Epoch.Finance.ActualItem Innovation.Installation.input 0 Innovation.Installation.count,
      (Innovation.Installation.current (Innovation.Control.Scenario.discovery version)
        (Innovation.Installation.boundaryTick (Innovation.Control.Scenario.discovery version) 12)).nativeAccount =
        Innovation.Installation.Native.Settlement.paidNativePair Innovation.Installation.input 0 Innovation.Installation.count
          (Innovation.Installation.actualPublicVisit (Innovation.Control.Scenario.discovery version) 9).account first last ∧
      Financial.fullChange (first.interpreter Innovation.Installation.input 0 Innovation.Installation.count)
        (first.instruction Innovation.Installation.input 0 Innovation.Installation.count).before
        (first.instruction Innovation.Installation.input 0 Innovation.Installation.count).request = 0 ∧
      Financial.fullChange (last.interpreter Innovation.Installation.input 0 Innovation.Installation.count)
        (last.instruction Innovation.Installation.input 0 Innovation.Installation.count).before
        (last.instruction Innovation.Installation.input 0 Innovation.Installation.count).request = 0 := by
  obtain ⟨loan,risk,first,last,loanArchive,riskArchive,
    _,_,_,_,_,_,_,_,firstOperation,_,lastOperation,_,paid,root,_,_,_⟩ :=
      Innovation.Installation.Native.the_actual_original_native_account_archives_both_contributions_and_retains_the_inherited_debt version tested
  obtain ⟨⟨firstDebtor,firstHolder,firstQuantity,firstKind⟩,⟨lastDebtor,lastHolder,lastQuantity,lastKind⟩⟩ :=
    the_two_original_trial_payments_are_settlements version
  refine ⟨first,last,root.trans paid,?_,?_⟩
  · exact Financial.settlement_is_neutral_for_every_original_bearer _ _ _ ()
      firstDebtor firstHolder firstQuantity (firstOperation.trans firstKind)
  · exact Financial.settlement_is_neutral_for_every_original_bearer _ _ _ ()
      lastDebtor lastHolder lastQuantity (lastOperation.trans lastKind)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Consumers
