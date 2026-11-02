import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing.Joint

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing.Joint.Posting
open ResponsibilityLifecycle Financial.Family.Migration.Posting
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

/-- A payment is queried at the actual review visit, not at the debt's birth. -/
def eventWindow : Family.Event sources → Exposure.Window sources
  | .birth claim => Exposure.windowOf sources claim
  | .review _ receipt _ _ => ⟨receipt.origin.1,receipt.origin.2.visit⟩

def allocation (entry : Entry sources) (selected : Bool) : ℚ :=
  if selected then entry.before.selectedUsed entry.boundary.receipt.sender entry.boundary.cap
  else entry.before.remainderUsed entry.boundary.receipt.sender entry.boundary.cap

def payment (entry : Entry sources) (selected : Bool) (side : Side) (party : Party) (good : Good) : ℚ :=
  match entry.boundary.receipt.kind with
  | .assignment => 0
  | .payment =>
      let claim := entry.obligation.content
      let actor := match side with | .debit => claim.2.debtor | .credit => entry.boundary.receipt.sender
      if actor = party ∧ (sources claim.1).law.settlementUnit claim.2.instrument = good then
        allocation sources entry selected * (sources claim.1).law.settlementRate claim.2.instrument else 0

/-- Cohort relabelling cancels between the two accounts. It is neither a new
loan nor a material payment; the sum is the original signed asset transfer. -/
def assignment (entry : Entry sources) (selected : Bool) (side : Side) (party : Party) (good : Good) : ℚ :=
  match entry.boundary.receipt.kind with
  | .payment => 0
  | .assignment =>
      let claim := entry.obligation.content
      let fresh := entry.result.fresh
      match side with
      | .debit =>
          if claim.2.debtor = party ∧ (sources claim.1).law.settlementUnit claim.2.instrument = good then
            (if selected then fresh else -fresh) * (sources claim.1).law.settlementRate claim.2.instrument else 0
      | .credit =>
          if (sources claim.1).law.settlementUnit claim.2.instrument = good then
            ((if entry.boundary.receipt.recipient = party then
                allocation sources entry selected + (if selected then fresh else -fresh) else 0) -
              (if entry.boundary.receipt.sender = party then allocation sources entry selected else 0)) *
                (sources claim.1).law.settlementRate claim.2.instrument else 0

theorem payment_partition (entry : Entry sources) (side : Side) (party : Party) (good : Good) :
    payment sources entry true side party good + payment sources entry false side party good =
      Financial.Family.Migration.Posting.amount sources entry.event side party good := by
  have quota := entry.before.quota entry.boundary.receipt.sender entry.boundary.cap
  have valued := congrArg (fun quantity => quantity * (sources entry.obligation.content.1).law.settlementRate
    entry.obligation.content.2.instrument) quota
  dsimp only [Share.Split.used] at valued
  cases kind : entry.boundary.receipt.kind <;> cases side <;>
    simp only [payment,allocation,Financial.Family.Migration.Posting.amount,Entry.event,Boundary.event,
      kind,Bool.false_eq_true,if_true,if_false,add_zero] <;> split_ifs <;> linarith only [valued]

theorem assignment_partition (entry : Entry sources) (side : Side) (party : Party) (good : Good) :
    assignment sources entry true side party good + assignment sources entry false side party good =
      Financial.Family.Migration.Posting.Balance.assigned sources entry.event side party good := by
  have quota := entry.before.quota entry.boundary.receipt.sender entry.boundary.cap
  have valued := congrArg (fun quantity => quantity * (sources entry.obligation.content.1).law.settlementRate
    entry.obligation.content.2.instrument) quota
  dsimp only [Share.Split.used] at valued
  cases kind : entry.boundary.receipt.kind <;> cases side <;>
    simp only [assignment,allocation,Financial.Family.Migration.Posting.Balance.assigned,Entry.event,Boundary.event,
      kind,Bool.false_eq_true,if_true,if_false,add_zero] <;> split_ifs <;> nlinarith only [valued]

def beforeShares (entry : Entry sources) (selected : Bool) : Shares (Party := Party) :=
  if selected then entry.before.selected else entry.before.remainder

def afterShares (entry : Entry sources) (selected : Bool) : Shares (Party := Party) :=
  if selected then entry.result.final.selected else entry.result.final.remainder

theorem entry_balance (entry : Entry sources) (selected : Bool) (side : Side) (party : Party) (good : Good) :
    Financial.Family.Migration.Posting.Balance.holding sources entry.obligation.content (afterShares sources entry selected) side party good +
      payment sources entry selected side party good =
    Financial.Family.Migration.Posting.Balance.holding sources entry.obligation.content (beforeShares sources entry selected) side party good +
      assignment sources entry selected side party good := by
  cases explanations : origins sources entry.boundary with
  | nil =>
    cases selected <;> cases kind : entry.boundary.receipt.kind <;> cases side <;>
      simp only [beforeShares,afterShares,Entry.result,step,explanations,withExplanations,
        Share.Split.reindex,Share.Split.step,Share.Split.move,Financial.Family.Migration.Posting.Balance.holding,
        payment,assignment,allocation,kind,Bool.false_eq_true,if_false,if_true,Financial.pay_total,
        Financial.assign_total,pay_apply,assign_apply,eq_comm] <;> split_ifs <;> first | (exfalso; tauto) | ring
  | cons origin rest =>
    cases selected <;> cases side <;>
      simp only [beforeShares,afterShares,Entry.result,step,explanations,withExplanations,promote,
        Share.Split.reindex,Financial.Family.Migration.Posting.Balance.holding,payment,assignment,allocation,
        origin.assignment,Bool.false_eq_true,if_false,if_true,Financial.pay_total,Financial.assign_total,
        pay_apply,assign_apply,eq_comm] <;> split_ifs <;> first | (exfalso; tauto) | ring

def payments (entries : List (Entry sources)) (selected : Bool) (side : Side) (party : Party) (good : Good)
    (window : Exposure.Window sources → Bool) : ℚ :=
  (entries.map fun entry => if window (eventWindow sources entry.event) then payment sources entry selected side party good else 0).sum

def assignments (entries : List (Entry sources)) (selected : Bool) (side : Side) (party : Party) (good : Good)
    (window : Exposure.Window sources → Bool) : ℚ :=
  (entries.map fun entry => if window (eventWindow sources entry.event) then assignment sources entry selected side party good else 0).sum

def actualPayments {first last : ObligationSlot (vocabulary sources)} (path : Path sources first last)
    (side : Side) (party : Party) (good : Good) (window : Exposure.Window sources → Bool) : ℚ :=
  ((path.events sources).map fun event => if window (eventWindow sources event) then
    Financial.Family.Migration.Posting.amount sources event side party good else 0).sum

def actualAssignments {first last : ObligationSlot (vocabulary sources)} (path : Path sources first last)
    (side : Side) (party : Party) (good : Good) (window : Exposure.Window sources → Bool) : ℚ :=
  ((path.events sources).map fun event => if window (eventWindow sources event) then
    Financial.Family.Migration.Posting.Balance.assigned sources event side party good else 0).sum

private theorem sum_partition (entries : List (Entry sources)) (left right original : Entry sources → ℚ)
    (partition : ∀ entry, left entry + right entry = original entry) :
    (entries.map left).sum + (entries.map right).sum = (entries.map original).sum := by
  induction entries with
  | nil => exact add_zero 0
  | cons entry rest ih =>
    simp only [List.map_cons,List.sum_cons]
    linarith [partition entry]

theorem exact_payments {first last : ObligationSlot (vocabulary sources)}
    {path : Path sources first last} {initial : Share.Split (slotBalance sources first)}
    (flow : Flow sources path initial) (side : Side) (party : Party) (good : Good) (window : Exposure.Window sources → Bool) :
    payments sources flow.entries true side party good window + payments sources flow.entries false side party good window =
      actualPayments sources path side party good window := by
  unfold payments actualPayments
  rw [← flow.events_exact,List.map_map]
  apply sum_partition
  intro entry
  cases chosen : window (eventWindow sources entry.event) <;>
    simp only [Function.comp_apply,chosen,Bool.false_eq_true,if_false,if_true,add_zero]
  exact payment_partition sources entry side party good

theorem exact_assignments {first last : ObligationSlot (vocabulary sources)}
    {path : Path sources first last} {initial : Share.Split (slotBalance sources first)}
    (flow : Flow sources path initial) (side : Side) (party : Party) (good : Good) (window : Exposure.Window sources → Bool) :
    assignments sources flow.entries true side party good window + assignments sources flow.entries false side party good window =
      actualAssignments sources path side party good window := by
  unfold assignments actualAssignments
  rw [← flow.events_exact,List.map_map]
  apply sum_partition
  intro entry
  cases chosen : window (eventWindow sources entry.event) <;>
    simp only [Function.comp_apply,chosen,Bool.false_eq_true,if_false,if_true,add_zero]
  exact assignment_partition sources entry side party good

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing.Joint.Posting
