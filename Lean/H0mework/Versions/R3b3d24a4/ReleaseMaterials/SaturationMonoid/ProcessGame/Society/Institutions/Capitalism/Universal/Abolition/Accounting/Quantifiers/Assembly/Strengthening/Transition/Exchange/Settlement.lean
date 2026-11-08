import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Review
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Priority
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open Source.Program PublicFunction.Repayment Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "P" => Plan Party Good Port Technology Instrument
local notation "Pos" => Position Party Instrument

def ReachesSlot (source : C) (position : Pos) (plan : P) (quantity : ℚ) (index : Nat) : Prop :=
  principalAt (finalAt source position plan quantity) index position.creditor <
    principalAt source index position.creditor

instance (source : C) (position : Pos) (plan : P) (quantity : ℚ) (index : Nat) :
    Decidable (ReachesSlot source position plan quantity index) := by
  unfold ReachesSlot
  infer_instance

def principalPaid (source : C) (position : Pos) (plan : P) (quantity : ℚ) (index : Nat) : ℚ :=
  principalAt source index position.creditor -
    principalAt (finalAt source position plan quantity) index position.creditor

theorem the_named_slot_is_reached_iff_its_original_priority_is_covered
    {source : C} {position : Pos} {plan : P} {quantity : ℚ} {index : Nat}
    (payment : FundedPayment source position plan quantity) (named : NamesOpenSlot source position index) :
    ReachesSlot source position plan quantity index ↔ priorityBefore source position index < quantity := by
  unfold ReachesSlot
  rw [the_settlement_decreases_the_exact_original_slot_after_its_priority payment named]
  constructor
  · intro strict
    by_contra! blocked
    simp [max_eq_left (sub_nonpos.mpr blocked), min_eq_right named.2.le] at strict
  · intro funded
    have positive : 0 < min (principalAt source index position.creditor)
        (max 0 (quantity - priorityBefore source position index)) :=
      lt_min named.2 ((sub_pos.mpr funded).trans_le (le_max_right _ _))
    linarith

theorem the_old_principal_reduction_is_the_exact_post_priority_share
    {source : C} {position : Pos} {plan : P} {quantity : ℚ} {index : Nat}
    (payment : FundedPayment source position plan quantity) (named : NamesOpenSlot source position index) :
    principalPaid source position plan quantity index = min (principalAt source index position.creditor)
      (max 0 (quantity - priorityBefore source position index)) := by
  unfold principalPaid
  rw [the_settlement_decreases_the_exact_original_slot_after_its_priority payment named]
  ring

/-- The raw material payment and the allocation to the named original slot
are distinct checks. Other obligations at this address keep native priority. -/
structure Settled (source : C) (position : Pos) (plan : P) (index : Nat) : Prop where
  named : NamesOpenSlot source position index
  payment : FundedPayment source position plan (upper source position plan)
  review : NativeReviewed source position plan (upper source position plan) index
  exchangeAccount : HEq (nativeAccount (plan.exchanged source)) (nativeAccount source)
  principal : 0 < principalPaid source position plan (upper source position plan) index
  principalExact : principalPaid source position plan (upper source position plan) index =
    min (principalAt source index position.creditor)
      (max 0 (upper source position plan - priorityBefore source position index))
  rawBalance : balance position (finalAt source position plan (upper source position plan)).raw =
    balance position source.raw - upper source position plan
  native : NativeReconciled source position plan (upper source position plan)
  whole : Quantities.Recorded source (fullScript source position plan (upper source position plan))

theorem pay_original_slot (source : C) (position : Pos) (plan : P) (index : Nat)
    (named : NamesOpenSlot source position index) (delivered : Delivered source position plan)
    (distinct : position.debtor ≠ position.creditor) (rate : 0 < oldRate source position)
    (positive : 0 < upper source position plan) (inside : lower source position plan ≤ upper source position plan)
    (routed : ReachesSlot source position plan (upper source position plan) index) :
    Settled source position plan index := by
  have payment := (the_maximum_funded_payment_is_attained source position plan delivered distinct rate positive inside).1
  have exactPaid := the_actual_exchange_and_redemption_close_the_whole_original_ledger payment
  exact ⟨named, payment, the_original_family_reviews_the_paid_head_at_the_named_slot payment named,
    a_paid_exchange_keeps_the_whole_original_native_debt_account delivered,
    sub_pos.mpr routed, the_old_principal_reduction_is_the_exact_post_priority_share payment named,
    exactPaid.2.2, the_whole_funded_principal_is_consumed_on_its_original_native_address payment,
    exactPaid.1⟩

theorem Settled.maximizes_the_named_old_principal
    {source : C} {position : Pos} {plan : P} {index : Nat}
    (settlement : Settled source position plan index) (quantity : ℚ)
    (alternative : FundedPayment source position plan quantity) :
    principalPaid source position plan quantity index ≤ principalPaid source position plan (upper source position plan) index := by
  rw [the_old_principal_reduction_is_the_exact_post_priority_share alternative settlement.named, settlement.principalExact]
  have below := ((the_original_exchange_funded_principal_interval_is_exact _ _ _ settlement.payment.received _).mp
    alternative).2.2.2.2
  exact min_le_min le_rfl (max_le_max le_rfl (sub_le_sub_right below _))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
