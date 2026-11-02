import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Principal
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.Risk

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Source.Program

noncomputable section

variable {Good : Type} [DecidableEq Good]
  (source : ProgrammeSource.Input Party Good Bool Nat Unit) (depth count : Nat)

def firstRiskSettlement (failed : Bool) : Operation Party Good Nat Unit :=
  if failed then .settle () 1 0 1 else .settle () 0 1 3

def lastRiskSettlement (failed : Bool) : Operation Party Good Nat Unit :=
  if failed then .settle () 0 1 3 else .settle () 0 1 (3 / 2)

def paidNativePair (before : (Epoch.Finance.process source depth count).GeneratedState)
    (first last : Epoch.Finance.ActualItem source depth count) :=
  (Epoch.Finance.consume source depth count last
    ((Epoch.Finance.consume source depth count first before).next source depth count)).next source depth count

/-- The two actual payments archive the two original contributions while
retaining the complete inherited obligation. -/
theorem the_original_three_slot_allocation_pays_the_two_new_claims
    (before : (Epoch.Finance.process source depth count).GeneratedState)
    (old : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (loan risk : Epoch.Finance.NewClaim source depth count) (failed : Bool)
    (slots : before.current.slots = [.live old,
      .live (Epoch.Finance.admission source depth count (.inr loan)).toObligation,
      .live (Epoch.Finance.admission source depth count (.inr risk)).toObligation])
    (oldDebtor : old.content.debtor source depth count = 0)
    (oldBalance : old.residual = Finsupp.single 2 1)
    (loanDebtor : loan.debtor = 0) (loanHolder : loan.holder = 1) (loanQuantity : loan.quantity = 3)
    (riskDebtor : risk.debtor = if failed then 1 else 0)
    (riskHolder : risk.holder = if failed then 0 else 1)
    (riskQuantity : risk.quantity = if failed then 1 else 3 / 2)
    (first last : Epoch.Finance.ActualItem source depth count)
    (firstOperation : (first.instruction source depth count).request.operation = firstRiskSettlement failed)
    (lastOperation : (last.instruction source depth count).request.operation = lastRiskSettlement failed)
    (firstAccepted : (first.interpreter source depth count).Valid (first.instruction source depth count).before
      (first.instruction source depth count).request)
    (lastAccepted : (last.interpreter source depth count).Valid (last.instruction source depth count).before
      (last.instruction source depth count).request) :
    ∃ loanArchive riskArchive : TerminalArchive (Epoch.Finance.vocabulary source depth count),
      (paidNativePair source depth count before first last).current.slots =
        [.live old,.terminal loanArchive,.terminal riskArchive] ∧
      loanArchive.obligation = (Epoch.Finance.admission source depth count (.inr loan)).toObligation ∧
      riskArchive.obligation = (Epoch.Finance.admission source depth count (.inr risk)).toObligation := by
  let loanObligation := (Epoch.Finance.admission source depth count (.inr loan)).toObligation
  let riskObligation := (Epoch.Finance.admission source depth count (.inr risk)).toObligation
  have loanBalance : loanObligation.residual = Finsupp.single 1 3 := by
    change Epoch.Finance.claimInitial source depth count (.inr loan) = _
    rw [Epoch.Finance.new_initial_balance_is_the_same_single,loanHolder,loanQuantity]
  have riskBalance : riskObligation.residual = Finsupp.single risk.holder risk.quantity :=
    Epoch.Finance.new_initial_balance_is_the_same_single source depth count risk
  cases failed <;>
    simp only [firstRiskSettlement,lastRiskSettlement,Bool.false_eq_true,if_false,if_true]
      at firstOperation lastOperation riskDebtor riskHolder riskQuantity
  · obtain ⟨firstMove,_,_,_,_,firstQuantity,firstStep⟩ :=
      the_actual_payment_uses_only_its_source_allocation source depth count first 0 1 3 firstOperation firstAccepted before
    obtain ⟨loanArchive,firstSlots,loanOriginal⟩ :=
      the_original_principal_payment_archives_the_loan_and_preserves_its_other_slots source depth count first firstMove before
        old loanObligation (.live riskObligation) slots oldDebtor oldBalance loanDebtor loanBalance
        (by
          intro obligation same
          cases ObligationSlot.live.inj same
          rw [riskBalance,riskHolder,riskQuantity]
          simp)
        firstOperation firstAccepted firstQuantity
    let middle := (Epoch.Finance.allocate source depth count first firstMove before).after
    obtain ⟨lastMove,_,_,_,_,lastQuantity,lastStep⟩ :=
      the_actual_payment_uses_only_its_source_allocation source depth count last 0 1 (3/2) lastOperation lastAccepted middle
    obtain ⟨riskArchive,lastSlots,riskOriginal⟩ :=
      the_original_success_premium_pays_its_risk_without_touching_the_old_slot_or_loan_archive source depth count
        middle old riskObligation loanArchive (3/2) firstSlots oldDebtor oldBalance riskDebtor
        (by simpa only [riskHolder,riskQuantity] using riskBalance)
        last lastOperation lastAccepted lastMove lastQuantity
    refine ⟨loanArchive,riskArchive,?_,loanOriginal,riskOriginal⟩
    unfold paidNativePair
    rw [firstStep,lastStep]
    exact lastSlots
  · obtain ⟨firstMove,_,_,_,_,firstQuantity,firstStep⟩ :=
      the_actual_payment_uses_only_its_source_allocation source depth count first 1 0 1 firstOperation firstAccepted before
    obtain ⟨riskArchive,firstSlots,riskOriginal⟩ :=
      the_original_failure_coverage_pays_its_risk_without_touching_the_two_prior_slots source depth count before
        old loanObligation riskObligation slots oldDebtor loanDebtor riskDebtor
        (by simpa only [riskHolder,riskQuantity] using riskBalance)
        first firstOperation firstAccepted firstMove firstQuantity
    let middle := (Epoch.Finance.allocate source depth count first firstMove before).after
    obtain ⟨lastMove,_,_,_,_,lastQuantity,lastStep⟩ :=
      the_actual_payment_uses_only_its_source_allocation source depth count last 0 1 3 lastOperation lastAccepted middle
    obtain ⟨loanArchive,lastSlots,loanOriginal⟩ :=
      the_original_principal_payment_archives_the_loan_and_preserves_its_other_slots source depth count last lastMove middle
        old loanObligation (.terminal riskArchive) firstSlots oldDebtor oldBalance loanDebtor loanBalance
        (by intro obligation impossible; cases impossible) lastOperation lastAccepted lastQuantity
    refine ⟨loanArchive,riskArchive,?_,loanOriginal,riskOriginal⟩
    unfold paidNativePair
    rw [firstStep,lastStep]
    exact lastSlots

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement
