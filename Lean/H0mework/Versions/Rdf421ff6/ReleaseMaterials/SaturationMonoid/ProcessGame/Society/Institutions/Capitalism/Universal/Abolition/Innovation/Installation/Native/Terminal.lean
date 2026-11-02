import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Payments
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Allocate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered

noncomputable section

def OriginalNativePaidAt (version : Nat) : Prop :=
  ∃ loan risk : Epoch.Finance.NewClaim input 0 count,
    ∃ first last : Epoch.Finance.ActualItem input 0 count,
    ∃ loanArchive riskArchive : TerminalArchive (Epoch.Finance.vocabulary input 0 count),
      loan.instrument = () ∧ loan.debtor = 0 ∧ loan.holder = 1 ∧ loan.quantity = 3 ∧
      risk.instrument = () ∧ risk.debtor = Settlement.Preparation.riskDebtor version ∧
        risk.holder = Settlement.Preparation.riskHolder version ∧
        risk.quantity = Settlement.Preparation.riskUnits version ∧
      (first.instruction input 0 count).request.operation = (firstSettlement version).operation ∧
      (first.interpreter input 0 count).Valid (first.instruction input 0 count).before
        (first.instruction input 0 count).request ∧
      (last.instruction input 0 count).request.operation = (lastSettlement version).operation ∧
      (last.interpreter input 0 count).Valid (last.instruction input 0 count).before
        (last.instruction input 0 count).request ∧
      (actualPublicVisit (Control.Scenario.discovery version) 11).account =
        Settlement.paidNativePair input 0 count (actualPublicVisit (Control.Scenario.discovery version) 9).account first last ∧
      (current (Control.Scenario.discovery version) (boundaryTick (Control.Scenario.discovery version) 12)).nativeAccount =
        (actualPublicVisit (Control.Scenario.discovery version) 11).account ∧
      (actualPublicVisit (Control.Scenario.discovery version) 11).account.current.slots =
        [.live Settlement.Inherited.originalOwner,.terminal loanArchive,.terminal riskArchive] ∧
      loanArchive.obligation = (Epoch.Finance.admission input 0 count (.inr loan)).toObligation ∧
      riskArchive.obligation = (Epoch.Finance.admission input 0 count (.inr risk)).toObligation

theorem the_actual_original_native_account_archives_both_contributions_and_retains_the_inherited_debt
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) : OriginalNativePaidAt version := by
  let nature := Control.Scenario.discovery version
  have beforeReflexive : (actualPublicVisit nature 9).account = (actualPublicVisit nature 9).account := rfl
  generalize beforeEq : (actualPublicVisit nature 9).account = before at beforeReflexive
  obtain ⟨loan,risk,loanInstrument,loanDebtor,loanHolder,loanQuantity,
    riskInstrument,riskDebtor,riskHolder,riskQuantity,slots⟩ :=
      Settlement.Bindings.the_actual_work_cut_generates_its_two_original_native_claims version tested
  obtain ⟨first,last,firstOperation,firstAccepted,lastOperation,lastAccepted,paid⟩ :=
    Settlement.Bindings.the_actual_terminal_account_consumes_its_two_original_accepted_payments version tested
  let failed : Bool := decide (version = 0)
  have riskDebtorEq : risk.debtor = if failed then 1 else 0 := by
    simpa only [Settlement.Preparation.riskDebtor,failed,decide_eq_true_eq] using riskDebtor
  have riskHolderEq : risk.holder = if failed then 0 else 1 := by
    simpa only [Settlement.Preparation.riskHolder,failed,decide_eq_true_eq] using riskHolder
  have riskQuantityEq : risk.quantity = if failed then 1 else 3 / 2 := by
    simpa only [Settlement.Preparation.riskUnits,failed,decide_eq_true_eq,
      Control.Scenario.the_native_claim_sizes_use_the_original_settlement_rate.1,
      Control.Scenario.the_native_claim_sizes_use_the_original_settlement_rate.2] using riskQuantity
  have firstTyped : (first.instruction input 0 count).request.operation = Settlement.firstRiskSettlement failed := by
    rw [firstOperation]
    by_cases zero : version = 0 <;>
      simp [firstSettlement,Settlement.firstRiskSettlement,failed,zero,
        Control.Scenario.failureCoverage,Control.Scenario.repay,Control.Scenario.request,
        Control.Scenario.the_native_claim_sizes_use_the_original_settlement_rate.2]
  have lastTyped : (last.instruction input 0 count).request.operation = Settlement.lastRiskSettlement failed := by
    rw [lastOperation]
    by_cases zero : version = 0 <;>
      simp [lastSettlement,Settlement.lastRiskSettlement,failed,zero,
        Control.Scenario.successPayment,Control.Scenario.repay,Control.Scenario.request,
        Control.Scenario.the_native_claim_sizes_use_the_original_settlement_rate.1]
  have beforeSlots : before.current.slots = [.live Settlement.Inherited.originalOwner,
      .live (Epoch.Finance.admission input 0 count (.inr loan)).toObligation,
      .live (Epoch.Finance.admission input 0 count (.inr risk)).toObligation] :=
    (congrArg (fun account : Settlement.Bindings.Account => account.current.slots) beforeEq).symm.trans slots
  obtain ⟨loanArchive,riskArchive,terminal,loanOriginal,riskOriginal⟩ :=
    Settlement.the_original_three_slot_allocation_pays_the_two_new_claims input 0 count before
      Settlement.Inherited.originalOwner loan risk failed beforeSlots
      Settlement.Inherited.the_original_owner_keeps_its_exact_debtor_holder_and_residual.1
      Settlement.Inherited.the_original_owner_keeps_its_exact_debtor_holder_and_residual.2.2
      loanDebtor loanHolder loanQuantity riskDebtorEq riskHolderEq riskQuantityEq
      first last firstTyped lastTyped firstAccepted lastAccepted
  have samePaid := congrArg (fun account : Settlement.Bindings.Account =>
    Settlement.paidNativePair input 0 count account first last) beforeEq
  have finalSlots := (congrArg (fun account : Settlement.Bindings.Account => account.current.slots) paid).trans
    ((congrArg (fun account : Settlement.Bindings.Account => account.current.slots) samePaid).trans terminal)
  have source := every_public_visit_is_the_same_original_activated_frame nature (actualAdmission nature)
    (the_first_admission_is_the_actual_source_compiler_choice nature) 11
  have installed : (current nature (boundaryTick nature 12)).nativeAccount =
      (actualPublicVisit nature 11).account := congrArg Macro.Runtime.ActivatedFrame.nativeAccount source
  exact ⟨loan,risk,first,last,loanArchive,riskArchive,
    loanInstrument,loanDebtor,loanHolder,loanQuantity,riskInstrument,riskDebtor,riskHolder,riskQuantity,
    firstOperation,firstAccepted,lastOperation,lastAccepted,paid,installed,finalSlots,loanOriginal,riskOriginal⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native
