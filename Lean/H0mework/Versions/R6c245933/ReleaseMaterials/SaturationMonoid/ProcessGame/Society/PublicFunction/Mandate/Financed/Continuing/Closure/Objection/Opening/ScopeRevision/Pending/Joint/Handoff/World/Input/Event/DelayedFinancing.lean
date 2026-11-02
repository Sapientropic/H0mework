import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.ControlFinancing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.DelayedFinancing
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Financial.Family.Migration.Posting
noncomputable section
variable {first last : Packet} (actual : Evolution first last)

def fullRun := first.2.finance.generated.concatRuns _ (Future.Expiry.Progress.Response.financeAlong actual)
def births := Financial.Family.Migration.Exposure.admissions sources (fullRun actual)
def marked := Financial.Family.Migration.DelayedFinancing.marked sources (births actual)

def nativeCharge (selected : Bool) (party : Bool) (good : Good) : ℚ :=
  ((Future.Expiry.Progress.Response.financeAlong actual).events.map fun event =>
    let original := Financial.Family.Migration.sourceEvent sources event
    if marked actual event.slot = selected then
      Balance.issued sources original .debit party good - Balance.issued sources original .credit party good -
        Balance.assigned sources original .credit party good
    else 0).sum

/-- The entire actual cash remainder stays independent of the classified native cohort. -/
def cashRemainder (party : Bool) (good : Good) : ℚ :=
  Costs.cost actual party (.operating good) - FinancialBalance.otherCredits actual party good

def account (selected : Bool) (party : Bool) (good : Good) : ℚ :=
  nativeCharge actual selected party good + if selected then 0 else cashRemainder actual party good

theorem actual_native_partition (party : Bool) (good : Good) :
    nativeCharge actual true party good + nativeCharge actual false party good =
      FinancialBalance.issues actual .debit party good - FinancialBalance.issues actual .credit party good -
        FinancialBalance.assignments actual .credit party good := by
  unfold nativeCharge FinancialBalance.issues FinancialBalance.assignments Balance.newIssues Balance.assignments
  induction (Future.Expiry.Progress.Response.financeAlong actual).events with
  | nil => simp only [List.map_nil,List.sum_nil,sub_self,add_zero]
  | cons event rest ih =>
      simp only [List.map_cons,List.sum_cons]
      cases marked actual event.slot <;>
        simp only [Bool.false_eq_true,Bool.true_eq_false,if_false,if_true] <;> linarith

theorem actual_complete_net_partition (party : Bool) (good : Good) :
    account actual true party good + account actual false party good =
      Costs.cost actual party (.operating good) - FinancialBalance.otherCredits actual party good -
        FinancialBalance.issues actual .credit party good + FinancialBalance.issues actual .debit party good -
          FinancialBalance.assignments actual .credit party good := by
  have native := actual_native_partition actual party good
  simp only [account,Bool.false_eq_true,if_true,if_false,add_zero,cashRemainder]
  linarith

theorem actual_net_position_change (party : Bool) (good : Good) :
    account actual true party good + account actual false party good =
      FinancialBalance.quotedNet first party good - FinancialBalance.quotedNet last party good := by
  rw [actual_complete_net_partition]
  have original := FinancialBalance.actual_net_balance actual party good
  linarith

theorem classified_slot_has_its_actual_original_return (index : Nat) (selected : marked actual index = true) :
    ∃ birth ∈ births actual, birth.index = index ∧
      Nonempty (Financial.Family.Migration.DelayedFinancing.Returned sources birth) := by
  obtain ⟨birth,member,same,nonempty⟩ := (Financial.Family.Migration.DelayedFinancing.marked_exact sources _ index).mp selected
  refine ⟨birth,member,same,?_⟩
  cases reports : Financial.Family.Migration.DelayedFinancing.reports sources birth with
  | nil => simp only [reports,List.isEmpty_nil] at nonempty; cases nonempty
  | cons report rest => exact ⟨report⟩

theorem every_original_and_new_financial_slot_is_present_once :
    (births actual).map Financial.Family.Migration.Exposure.Birth.index = List.range last.2.finance.current.slots.length := by
  simpa only [births,ResponsibilityState.empty,List.length_nil,List.range_zero,List.nil_append] using
    Financial.Family.Migration.Exposure.admission_indices sources (fullRun actual)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.DelayedFinancing
