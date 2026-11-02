import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus.Financing
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.FinancialBalance

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.ControlFinancing

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
open Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.ActualSurplus
open Financial.Family.Migration.Posting
noncomputable section

def claimMarked (claim : Financial.Family.Claim sources) : Bool :=
  Financing.marked (sources claim.1).law
    (ProgrammeSource.rawCurrent (sources claim.1) claim.2.origin.visit.current)
    (ProgrammeSource.rawEvent (sources claim.1) claim.2.origin.visit.current)
    .issuance claim.2.instruction.index

theorem marked_native_claim_has_its_original_control_evidence (claim : Financial.Family.Claim sources)
    (selected : claimMarked claim = true) :
    let law := (sources claim.1).law
    let initial := ProgrammeSource.rawCurrent (sources claim.1) claim.2.origin.visit.current
    let word := ProgrammeSource.rawEvent (sources claim.1) claim.2.origin.visit.current
    ∃ witness ∈ Payments.financialWitnesses law initial word, ∃ path : Financial.ReturnPath law initial word,
      witness.evidence = .financialReturn path ∧ path.issuance.val = claim.2.instruction ∧
      Financial.ReturnPath.Checks law initial word witness.dependency.proposal.access path := by
  obtain ⟨witness, member, path, evidence, same, checked⟩ :=
    Financing.marked_issuance_is_the_original_checked_claim _ _ _
      ⟨claim.2.instruction, claim.2.original_inventory_provenance _⟩ selected
  exact ⟨witness, member, path, evidence, congrArg Subtype.val same, checked⟩

def eventMarked : Financial.Family.Event sources → Bool
  | .birth claim => claimMarked claim
  | .review claim .. => claimMarked claim

/-- The same original claim selects its issue and every later holder movement.
An actual cash settlement is canceled by retirement in the original net balance. -/
def nativeCharge (selected : Bool) {first last : Packet} (path : Evolution first last)
    (party : Bool) (good : Good) : ℚ :=
  ((Future.Expiry.Progress.Response.financeAlong path).events.map fun event =>
    let original := Financial.Family.Migration.sourceEvent sources event
    if eventMarked original = selected then
      Balance.issued sources original .debit party good -
        Balance.issued sources original .credit party good - Balance.assigned sources original .credit party good
    else 0).sum

theorem nativeCharge_partition {first last : Packet} (path : Evolution first last) (party : Bool) (good : Good) :
    nativeCharge true path party good + nativeCharge false path party good =
      FinancialBalance.issues path .debit party good - FinancialBalance.issues path .credit party good -
        FinancialBalance.assignments path .credit party good := by
  unfold nativeCharge FinancialBalance.issues FinancialBalance.assignments Balance.newIssues Balance.assignments
  induction (Future.Expiry.Progress.Response.financeAlong path).events with
  | nil => simp only [List.map_nil, List.sum_nil, sub_self, add_zero]
  | cons event rest ih =>
      simp only [List.map_cons, List.sum_cons]
      cases eventMarked (Financial.Family.Migration.sourceEvent sources event) <;>
        simp only [Bool.false_eq_true, Bool.true_eq_false, if_false, if_true] <;> linarith

def cashAt (entry : PublicFunction.Costs.Visits.Window sources) (selected credit : Bool) (party : Bool) (good : Good) :=
  Financing.cash (sources entry.1).law
    (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
    (ProgrammeSource.rawEvent (sources entry.1) entry.2.current) selected credit party good

def cashTotal : List (PublicFunction.Costs.Visits.Window sources) → Bool → Bool → Bool → Good → ℚ
  | [], _, _, _, _ => 0
  | entry :: rest, selected, credit, party, good =>
      cashAt entry selected credit party good + cashTotal rest selected credit party good

theorem cashAt_debit_partition (entry : PublicFunction.Costs.Visits.Window sources) (party : Bool) (good : Good) :
    cashAt entry true false party good + cashAt entry false false party good =
      PublicFunction.Costs.Visits.atVisit sources entry party (.operating good) :=
  Financing.cash_partition _ _ _ false party good

theorem cashAt_credit_partition (entry : PublicFunction.Costs.Visits.Window sources) (party : Bool) (good : Good) :
    cashAt entry true true party good + cashAt entry false true party good =
      FinancialBalance.otherAt entry party good :=
  Financing.cash_partition _ _ _ true party good

theorem cashTotal_debit_partition (entries : List (PublicFunction.Costs.Visits.Window sources)) (party : Bool) (good : Good) :
    cashTotal entries true false party good + cashTotal entries false false party good =
      PublicFunction.Costs.Visits.total sources entries party (.operating good) := by
  induction entries with
  | nil => simp only [cashTotal, PublicFunction.Costs.Visits.total, Pi.zero_apply, add_zero]
  | cons entry rest ih =>
      change (_ + cashTotal rest true false party good) + (_ + cashTotal rest false false party good) = _ + _
      have head := cashAt_debit_partition entry party good
      linarith

theorem cashTotal_credit_partition (entries : List (PublicFunction.Costs.Visits.Window sources)) (party : Bool) (good : Good) :
    cashTotal entries true true party good + cashTotal entries false true party good =
      FinancialBalance.otherTotal entries party good := by
  induction entries with
  | nil => simp only [cashTotal, FinancialBalance.otherTotal, add_zero]
  | cons entry rest ih =>
      change (_ + cashTotal rest true true party good) + (_ + cashTotal rest false true party good) = _ + _
      have head := cashAt_credit_partition entry party good
      linarith

/-- A signed control-linked net financing account, in each original good.
The complementary account is folded independently from all remaining events. -/
def account {first last : Packet} (path : Evolution first last) (selected : Bool) (party : Bool) (good : Good) : ℚ :=
  cashTotal (Costs.records path) selected false party good -
    cashTotal (Costs.records path) selected true party good + nativeCharge selected path party good

theorem exact_net_account_partition {first last : Packet} (path : Evolution first last) (party : Bool) (good : Good) :
    account path true party good + account path false party good =
      Costs.cost path party (.operating good) - FinancialBalance.otherCredits path party good -
        FinancialBalance.issues path .credit party good + FinancialBalance.issues path .debit party good -
          FinancialBalance.assignments path .credit party good := by
  have debit := cashTotal_debit_partition (Costs.records path) party good
  have credit := cashTotal_credit_partition (Costs.records path) party good
  have native := nativeCharge_partition path party good
  unfold account Costs.cost FinancialBalance.otherCredits
  linarith

theorem financing_and_complement_are_the_actual_net_position_change {first last : Packet}
    (path : Evolution first last) (party : Bool) (good : Good) :
    account path true party good + account path false party good =
      FinancialBalance.quotedNet first party good - FinancialBalance.quotedNet last party good := by
  rw [exact_net_account_partition]
  have original := FinancialBalance.actual_net_balance path party good
  linarith

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.ControlFinancing
