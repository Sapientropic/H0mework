import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Offer
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Boundary

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Consumers.Evolving (C compact returnAt)
open Quantities.Execution
open Reparation Reparation.Actual
open Reparation.Actual.Allocation (Position originalItem itemPositions)
open ExposureGuard
open Original.Replay (stopCut stop_source stop_ready stop_review stop_raw)
open private keysAt original_key from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence

noncomputable section

abbrev protectedPast := protectedCut.history
abbrev physicalCut := endAt Original.seed protectedPast
abbrev payerInput : Reparation.Actual.Input Bool Bool Bool Unit Unit := some (.primitive (returnAt 6))
abbrev paidWord : Original.Word := primitiveScript [returnAt 6]

theorem protected_source : physicalCut.native.input = compact :=
  (congrArg (fun cut : C => cut.native.input) protected_cut_is_the_literal_original_successor).trans stop_source

theorem protected_stock : physicalCut.raw = Original.snapshot 111 113 :=
  (congrArg (fun cut : C => cut.raw) protected_cut_is_the_literal_original_successor).trans
    (stop_raw.trans Original.cut_raw)

private theorem ready : Ready physicalCut :=
  (congrArg (fun cut : C => Ready cut) protected_cut_is_the_literal_original_successor).mpr stop_ready

private theorem review : ReviewAvailable physicalCut :=
  (congrArg (fun cut : C => ReviewAvailable cut) protected_cut_is_the_literal_original_successor).mpr stop_review

private theorem original_authority :
    physicalCut.native.input.law.Valid physicalCut.raw (returnAt 6) := by
  rw [protected_source, protected_stock]
  decide +kernel

private theorem physical_authority :
    (Physical.Public.interpreter physicalCut.native.input).Valid physicalCut.raw (returnAt 6) :=
  PublicFunction.valid_physical _ _ _ original_authority

private theorem primitive_paid :
    Trace physicalCut [returnAt 6] (endAt physicalCut paidWord) ∧
      Ready (endAt physicalCut paidWord) ∧ ReviewAvailable (endAt physicalCut paidWord) := by
  apply pay_checked_primitives physicalCut [returnAt 6] 0 ready review
  · intro request member
    rw [List.mem_singleton.mp member]
    rfl
  · intro item member
    change item ∈ [⟨0, physicalCut.raw, returnAt 6⟩] at member
    rw [List.mem_singleton.mp member]
    exact physical_authority

theorem the_protected_debtor_pays_a_real_original_primitive :
    Trace physicalCut [returnAt 6] (endAt physicalCut paidWord) := primitive_paid.1

theorem paid_native_ready : Ready (endAt physicalCut paidWord) := primitive_paid.2.1

theorem paid_native_review : ReviewAvailable (endAt physicalCut paidWord) := primitive_paid.2.2

theorem the_return_native_step_has_no_material_item :
    Boundary.Actual.items (endAt Original.seed (protectedPast ++ [payerInput])) none = [] := by
  have work := the_actual_body_must_consume_its_original_native_head physicalCut (returnAt 6)
    ready review rfl physical_authority
  rw [endAt_append]
  exact Reparation.Transport.native_step_has_no_material_items none work

theorem paid_snapshot : (endAt physicalCut paidWord).raw = Original.snapshot 117 107 := by
  rw [the_protected_debtor_pays_a_real_original_primitive.raw_is_the_complete_original_execution 0,
    protected_source, protected_stock]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · funext instrument debtor creditor
    cases instrument
    cases debtor <;> cases creditor <;> decide +kernel
  · exact Subsingleton.elim _ _
  · decide +kernel
  · decide +kernel

private theorem original_items_at (cut : C) (ready : Ready cut) (review : ReviewAvailable cut)
    (legal : (Physical.Public.interpreter cut.native.input).Valid cut.raw (returnAt 6)) :
    Boundary.Actual.items cut payerInput = [⟨0, cut.raw, returnAt 6⟩] :=
  (the_selected_primitive_is_paid_by_the_original_root (queued cut (returnAt 6)) (returnAt 6)
    ready (the_available_review_forwards_the_actual_requested_primitive _ _ review) rfl legal).2.2

theorem actual_payment_items :
    Boundary.Actual.items physicalCut payerInput = [⟨0, physicalCut.raw, returnAt 6⟩] :=
  original_items_at physicalCut ready review physical_authority

def paidPosition : Position Original.seed protectedPast payerInput :=
  ⟨0, by
    change 0 < (Boundary.Actual.items physicalCut payerInput).length
    rw [actual_payment_items]
    exact Nat.zero_lt_one⟩

theorem one_position (position : Position Original.seed protectedPast payerInput) :
    position = paidPosition := by
  apply Fin.ext
  have width : (Boundary.Actual.items physicalCut payerInput).length = 1 :=
    congrArg List.length actual_payment_items
  have small := position.isLt.trans_eq width
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ small)

theorem item_at_paid_position (position : Position Original.seed protectedPast payerInput) :
    originalItem Original.seed protectedPast payerInput position = ⟨0, physicalCut.raw, returnAt 6⟩ :=
  List.mem_singleton.mp ((congrArg (fun rows =>
    originalItem Original.seed protectedPast payerInput position ∈ rows) actual_payment_items).mp
      (List.getElem_mem _))

theorem the_protected_payment_creates_no_damage :
    Boundary.Actual.damages physicalCut payerInput Original.community = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro damage _
  have item : damage.item = ⟨0, physicalCut.raw, returnAt 6⟩ := item_at_paid_position damage.position
  have keys := original_key damage
  unfold keysAt at keys
  rw [item] at keys
  change damage.key ∈ ((Physical.Public.interpreter physicalCut.native.input).actualDebit
    physicalCut.raw (returnAt 6)).map (fun entry => (entry.1.1, (returnAt 6).signer, entry.1.2)) at keys
  rw [protected_source, protected_stock] at keys
  have keysExact : ((Physical.Public.interpreter compact).actualDebit (Original.snapshot 111 113)
      (returnAt 6)).map (fun entry => (entry.1.1, (returnAt 6).signer, entry.1.2)) =
        [(true, true, false)] := by decide +kernel
  rw [keysExact] at keys
  have foreign := damage.actual_foreign_debit.1.1
  rw [List.mem_singleton.mp keys] at foreign
  exact foreign rfl

private def debtorChooses (item : Original.Item) : Bool :=
  match item.request.operation with
  | .transfer payer payee goods =>
      decide (item.request.signer = true ∧ payer = true ∧ payee = false ∧ goods = [(false, 6)])
  | _ => false

private def victimAccepts (item : Original.Item) : Bool :=
  match item.request.operation with
  | .transfer payer payee goods => decide (payer = true ∧ payee = false ∧ goods = [(false, 6)])
  | _ => false

/-- These are the two original personal lanes on the actual protected
payment position. A later occurrence needs a new pair of replies. -/
def replies : OwnerAnswers Original.seed := fun past input position bearer =>
  if past.length = protectedPast.length ∧ position.val = 0 then
    let item := originalItem Original.seed past input position
    match bearer with
    | true => debtorChooses item
    | false => victimAccepts item
  else false

theorem the_protected_payment_has_each_original_reply
    (position : Position Original.seed protectedPast payerInput) (bearer : Bool) :
    replies protectedPast payerInput position bearer = true := by
  have atZero : position.val = 0 := congrArg Fin.val (one_position position)
  unfold replies
  rw [if_pos ⟨rfl, atZero⟩, item_at_paid_position]
  cases bearer <;> decide +kernel

theorem the_protected_payment_is_lawfully_forwarded :
    Admitted protectedCut.roster replies protectedPast payerInput ∧
      (protectedCut.verdict replies (damageGate Original.community) openProbe payerInput).emitted = [payerInput] := by
  have authorized : Admitted protectedCut.roster replies protectedPast payerInput := by
    constructor
    · intro item listed
      change item ∈ Boundary.Actual.items physicalCut payerInput at listed
      rw [actual_payment_items] at listed
      rw [List.mem_singleton.mp listed]
      exact original_authority
    · intro position question _ _
      exact the_protected_payment_has_each_original_reply position question.1
  refine ⟨authorized, ?_⟩
  unfold Visit.verdict
  exact the_original_gate_keeps_every_safe_admissible_input
    (community := Original.community) (check := openProbe) authorized the_protected_payment_creates_no_damage rfl

#print axioms paid_snapshot
#print axioms the_protected_payment_is_lawfully_forwarded

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement
