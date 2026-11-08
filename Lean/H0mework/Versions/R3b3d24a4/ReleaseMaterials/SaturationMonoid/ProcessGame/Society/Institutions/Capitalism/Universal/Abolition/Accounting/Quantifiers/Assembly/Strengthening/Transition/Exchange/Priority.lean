import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Slot
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Capacity
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Allocation.Exact

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open ResponsibilityLifecycle Source.Program PublicFunction.Repayment
open Abolition.Root Abolition.Root.Registered Abolition.Root.Epoch
open Innovation.Contribution.Pricing.Root.Runtime
open Quantities.Exit.Redemption (sourceLaw request)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "P" => Plan Party Good Port Technology Instrument
local notation "Pos" => Position Party Instrument

/-- Only preceding original slots at the same settlement address can
consume the quota before this particular old obligation. -/
def priorityBefore (source : C) (position : Pos) (index : Nat) : ℚ :=
  Allocation.prefixCapacity source.native.input source.native.depth source.native.count
    (nativeAccount source) 0 index position.instrument position.debtor position.creditor

theorem priorityBefore_nonnegative (source : C) (position : Pos) (index : Nat) :
    0 ≤ priorityBefore source position index :=
  Allocation.prefixCapacity_nonnegative _ _ _ _ 0 index _ _ _

theorem the_settlement_decreases_the_exact_original_slot_after_its_priority
    {source : C} {position : Pos} {plan : P} {quantity : ℚ} {index : Nat}
    (payment : FundedPayment source position plan quantity) (named : NamesOpenSlot source position index) :
    principalAt (finalAt source position plan quantity) index position.creditor =
      principalAt source index position.creditor - min (principalAt source index position.creditor)
        (max 0 (quantity - priorityBefore source position index)) := by
  let cut := plan.exchanged source
  let settle := request (sourceLaw cut) position quantity
  let body := afterBody cut settle
  let target := finalAt source position plan quantity
  have valid : (sourceLaw cut).Valid cut.raw settle := payment.settles.safe.2.1
  obtain ⟨item, identity, interpreter, consumed⟩ :=
    the_paid_primitive_has_one_literal_native_consumer cut settle
      payment.received.ready payment.received.review rfl valid
  have operation : (item.instruction _ _ _).request.operation =
      .settle position.instrument position.debtor position.creditor quantity :=
    congrArg (fun (entry : ExecutionItem Party Good Port Technology Instrument) => entry.request.operation) identity
  have admitted : (item.interpreter _ _ _).Valid (item.instruction _ _ _).before (item.instruction _ _ _).request := by
    rw [interpreter, identity]
    exact valid
  have kept := (the_paid_body_keeps_the_native_account cut settle payment.received.ready).trans
    (a_paid_exchange_keeps_the_whole_original_native_debt_account payment.received)
  obtain ⟨input, depth, count⟩ :=
    Quantities.Execution.the_actual_script_keeps_the_original_reader_indices source plan.script
  have parameters := (queued cut settle).advance_parameters
  have bodyInput : body.native.input = source.native.input := parameters.1.trans input
  have bodyDepth : body.native.depth = source.native.depth := parameters.2.1.trans depth
  have bodyCount : body.native.count = source.native.count := parameters.2.2.1.trans count
  have originalBalance : principalAt body index position.creditor = principalAt source index position.creditor :=
    read_native_same (nativeAccount source) (nativeAccount body) bodyInput bodyDepth bodyCount kept
      (fun input depth count account =>
        Allocation.balanceAt input depth count account index position.creditor)
  have originalPriority : priorityBefore body position index = priorityBefore source position index :=
    read_native_same (nativeAccount source) (nativeAccount body) bodyInput bodyDepth bodyCount kept
      (fun input depth count account =>
        Allocation.prefixCapacity input depth count account 0 index position.instrument position.debtor position.creditor)
  have originalAddress : (slotAt body index).map (slotAddress body) =
      (slotAt source index).map (slotAddress source) :=
    read_native_same (nativeAccount source) (nativeAccount body) bodyInput bodyDepth bodyCount kept
      (fun input depth count account => account.current.slots[index]?.map (fun slot =>
        let claim := Finance.slotClaim input depth count slot
        (claim.instrument _ _ _, claim.debtor _ _ _)))
  obtain ⟨slot, present, address⟩ := Option.map_eq_some_iff.mp (originalAddress.trans named.1)
  cases slot with
  | terminal archive =>
    have positive : 0 < principalAt body index position.creditor := originalBalance.symm ▸ named.2
    simp [principalAt, present, Finance.slotBalance] at positive
  | live obligation =>
    have coordinates : obligation.content.instrument _ _ _ = position.instrument ∧
        obligation.content.debtor _ _ _ = position.debtor :=
      ⟨congrArg Prod.fst address, congrArg Prod.snd address⟩
    obtain ⟨targetInput, targetDepth, targetCount⟩ :=
      Quantities.Execution.the_actual_script_keeps_the_original_reader_indices source
        (fullScript source position plan quantity)
    have account := (nativeAccount_heq_of_eq
      (finalAt_is_the_original_native_redemption source position plan quantity)).trans consumed
    have paidBalance : principalAt target index position.creditor =
        Allocation.balanceAt body.native.input body.native.depth body.native.count
          ((Finance.consume _ _ _ item (nativeAccount body)).next _ _ _) index position.creditor :=
      read_native_same ((Finance.consume _ _ _ item (nativeAccount body)).next _ _ _) (nativeAccount target)
        (targetInput.trans bodyInput.symm) (targetDepth.trans bodyDepth.symm) (targetCount.trans bodyCount.symm)
        account (fun input depth count state => Allocation.balanceAt input depth count state index position.creditor)
    rw [paidBalance, Allocation.the_literal_native_payment_reduces_the_named_old_slot_by_its_exact_share
      _ _ _ item position.instrument position.debtor position.creditor quantity operation admitted
      (nativeAccount body) index obligation present coordinates]
    change principalAt body index position.creditor - min (principalAt body index position.creditor)
      (max 0 (quantity - priorityBefore body position index)) = _
    rw [originalBalance, originalPriority]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
