import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Protected
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Writer

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (Ready ReviewAvailable)
open Conflict.Consumers.Evolving (C compact returnAt)
open Quantities.Execution
open Reparation Reparation.Actual
open Reparation.Actual.Allocation (Position originalItem itemPositions)
open ExposureGuard (stop)

noncomputable section

private theorem delivered_six : payerCredit Original.seed.native.input.law
    (originalItem Original.seed protectedPast payerInput paidPosition) Original.occurrence.key = 6 := by
  rw [item_at_paid_position, Conflict.Consumers.Evolving.sourceInput, protected_stock]
  decide +kernel

def receiptSix : JointReceipt Original.seed Original.occurrence.key :=
  ⟨protectedPast, payerInput, paidPosition, replies, the_protected_payment_has_each_original_reply _ true,
    the_protected_payment_has_each_original_reply _ false, by
      change 0 < payerCredit Original.seed.native.input.law
        (originalItem Original.seed protectedPast payerInput paidPosition) Original.occurrence.key
      rw [delivered_six]
      norm_num⟩

theorem the_same_position_issues_the_actual_joint_receipt :
    jointOffer replies protectedPast payerInput paidPosition Original.occurrence.key = some receiptSix := by
  unfold jointOffer
  rw [dif_pos ⟨receiptSix.payer, receiptSix.victim, receiptSix.positive⟩]
  rfl

private theorem receipt_follows_original_loss : jointLater Original.occurrence receiptSix := by
  left
  change Original.born.IsPrefix protectedPast
  have actual : protectedPast = Original.history ++ [stop] :=
    the_original_installation_writes_its_literal_first_input (fun _ _ _ _ => false)
  rw [actual, Original.exact_history, List.append_assoc]
  exact List.prefix_append _ _

private theorem posted_balances_exact :
    (posted protectedCut.state payerInput).stack.balances = [(Original.occurrence, Original.balance)] := by
  rw [posted_balances]
  have absent : openings Original.seed Original.community protectedPast payerInput = [] := by
    unfold openings
    rw [the_protected_payment_creates_no_damage]
    rfl
  rw [absent, List.map_nil, List.append_nil]
  unfold protectedCut
  exact (the_revised_visit_keeps_the_exact_original_reparation_portfolio opening
    (fun _ _ _ _ => false) openProbe stop).trans Original.balances_exact

private theorem positions_exact : itemPositions (seed := Original.seed) protectedPast payerInput = [paidPosition] := by
  have width : (Boundary.Actual.items physicalCut payerInput).length = 1 :=
    congrArg List.length actual_payment_items
  obtain ⟨position, same⟩ := List.length_eq_one_iff.mp (List.length_finRange.trans width)
  change List.finRange (Boundary.Actual.items physicalCut payerInput).length = [paidPosition]
  rw [same, one_position position]

def paidBody : State Original.seed Original.community (protectedPast ++ [payerInput]) :=
  Settlement.writeTick replies protectedCut.state payerInput

def clearedBalance : Balance := ⟨0, le_rfl⟩

private theorem demand_six :
    demand (jointOffer replies protectedPast payerInput paidPosition) false
      (posted protectedCut.state payerInput).stack.balances = 6 := by
  classical
  rw [posted_balances_exact]
  change (if Original.occurrence.key.2.2 = false then
    rowDemand (jointOffer replies protectedPast payerInput paidPosition) Original.occurrence Original.balance else 0) + 0 = 6
  simp only [show Original.occurrence.key.2.2 = false from rfl, if_true, add_zero,
    rowDemand, the_same_position_issues_the_actual_joint_receipt, if_pos receipt_follows_original_loss,
    Original.balance_six]

theorem the_paid_body_closes_the_original_six :
    paidBody.stack.balances = [(Original.occurrence, clearedBalance)] := by
  let atBody := posted protectedCut.state payerInput
  let plan := atPosition replies protectedPast payerInput paidPosition atBody
  have cap : limitAt protectedPast payerInput paidPosition false = 6 :=
    (the_original_limit_is_the_selected_quantity replies protectedPast payerInput paidPosition
      Original.occurrence.key receiptSix the_same_position_issues_the_actual_joint_receipt).trans delivered_six
  have charged := plan.tight false
  change limitAt protectedPast payerInput paidPosition false - (plan.left.balance false).remaining =
    min (limitAt protectedPast payerInput paidPosition false)
      (demand (jointOffer replies protectedPast payerInput paidPosition) false atBody.stack.balances) at charged
  rw [cap, demand_six, min_self] at charged
  have before : outstanding false atBody.stack.balances = 6 := by
    rw [posted_balances_exact]
    change (if Original.occurrence.key.2.2 = false then Original.balance.remaining else 0) + 0 = 6
    simp only [show Original.occurrence.key.2.2 = false from rfl, if_true, add_zero, Original.balance_six]
  have conservation := plan.conservation false
  change outstanding false plan.after.balances +
    (limitAt protectedPast payerInput paidPosition false - (plan.left.balance false).remaining) =
      outstanding false atBody.stack.balances at conservation
  rw [cap, charged, before] at conservation
  have noneDue : outstanding false plan.after.balances = 0 := by linarith only [conservation]
  have sameOrigins := plan.move.keeps_origins
  rw [posted_balances_exact] at sameOrigins
  have count : plan.after.balances.length = 1 := by simpa using congrArg List.length sameOrigins
  obtain ⟨row, exactRows⟩ := List.length_eq_one_iff.mp count
  rw [exactRows] at sameOrigins noneDue
  have key : row.1 = Original.occurrence := List.singleton_inj.mp sameOrigins
  rcases row with ⟨origin, balance⟩
  change origin = Original.occurrence at key
  subst origin
  have zero : balance.remaining = 0 := by
    simpa only [outstanding, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      show Original.occurrence.key.2.2 = false from rfl, if_true] using noneDue
  have cleared : balance = clearedBalance := by
    cases balance
    cases zero
    rfl
  unfold paidBody
  rw [writeTick_balances, positions_exact, writePositions, writePositions, writePosition_balances]
  change plan.after.balances = _
  rw [exactRows, cleared]

def settledHistory : Original.Word := (protectedPast ++ [payerInput]) ++ [none]

/-- The original material body pays the debt and the original accounting
input consumes its native head. This remains the same full ledger. -/
def settled : State Original.seed Original.community settledHistory :=
  Reparation.Actual.advance paidBody none

abbrev settledCut : C := endAt Original.seed settledHistory

theorem settled_cut_is_the_actual_paid_successor :
    settledCut = endAt physicalCut paidWord := by
  change endAt Original.seed settledHistory = endAt physicalCut paidWord
  unfold settledHistory
  rw [List.append_assoc, endAt_append]
  rfl

theorem settled_ready : Ready settledCut :=
  (congrArg (fun cut : C => Ready cut) settled_cut_is_the_actual_paid_successor).mpr paid_native_ready
theorem settled_review : ReviewAvailable settledCut :=
  (congrArg (fun cut : C => ReviewAvailable cut) settled_cut_is_the_actual_paid_successor).mpr paid_native_review

theorem settled_source : settledCut.native.input = compact := (endAt_input _ _).trans Conflict.Consumers.Evolving.sourceInput
theorem settled_raw : settledCut.raw = Original.snapshot 117 107 :=
  (congrArg (fun cut : C => cut.raw) settled_cut_is_the_actual_paid_successor).trans paid_snapshot

theorem settled_balances : settled.stack.balances = [(Original.occurrence, clearedBalance)] := by
  change (Reparation.Actual.advance (past := protectedPast ++ [payerInput]) paidBody none).stack.balances = _
  rw [written_balances paidBody none]
  have absent : openings Original.seed Original.community (protectedPast ++ [payerInput]) none = [] := by
    unfold openings
    rw [Boundary.Actual.no_material_write_has_no_damage _ _ _ the_return_native_step_has_no_material_item]
    rfl
  rw [absent, List.map_nil, List.append_nil]
  exact (Reparation.Actual.Allocation.no_original_items_keeps_rows
    _ _ _ the_return_native_step_has_no_material_item).1.trans the_paid_body_closes_the_original_six

theorem the_protected_origin_is_actually_settled_in_the_whole_ledger :
    Quantities.Recorded Original.seed settledHistory ∧
      settled.stack.balances = [(Original.occurrence, clearedBalance)] ∧
      settledCut.raw.claims = physicalCut.raw.claims ∧
      Boundary.Actual.damages physicalCut payerInput Original.community = [] := by
  refine ⟨Quantities.record _ _, settled_balances, ?_, the_protected_payment_creates_no_damage⟩
  rw [settled_raw, protected_stock]
  rfl

#print axioms the_protected_origin_is_actually_settled_in_the_whole_ledger

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement
