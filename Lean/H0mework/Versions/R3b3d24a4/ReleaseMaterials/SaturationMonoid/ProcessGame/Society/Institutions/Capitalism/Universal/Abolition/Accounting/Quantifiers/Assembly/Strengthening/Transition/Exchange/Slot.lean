import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Head

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange

open ResponsibilityLifecycle Source.Program PublicFunction.Repayment
open Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Contribution.Pricing.Root.Runtime
open Quantities.Exit.Redemption (sourceLaw)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "P" => Plan Party Good Port Technology Instrument
local notation "Pos" => Position Party Instrument

abbrev SlotAt (source : C) :=
  ObligationSlot (Epoch.Finance.vocabulary source.native.input source.native.depth source.native.count)

def slotAt (source : C) (index : Nat) : Option (SlotAt source) :=
  (nativeAccount source).current.slots[index]?

def slotAddress (source : C) (slot : SlotAt source) : Instrument × Party :=
  let claim := Epoch.Finance.slotClaim source.native.input source.native.depth source.native.count slot
  (claim.instrument _ _ _, claim.debtor _ _ _)

def principalAt (source : C) (index : Nat) (holder : Party) : ℚ :=
  ((slotAt source index).map (fun slot =>
    Epoch.Finance.slotBalance source.native.input source.native.depth source.native.count slot holder)).getD 0

def NamesOpenSlot (source : C) (position : Pos) (index : Nat) : Prop :=
  (slotAt source index).map (slotAddress source) = some (position.instrument, position.debtor) ∧
    0 < principalAt source index position.creditor

instance (source : C) (position : Pos) (index : Nat) : Decidable (NamesOpenSlot source position index) := by
  unfold NamesOpenSlot
  infer_instance

theorem a_paid_exchange_keeps_the_whole_original_native_debt_account
    {source : C} {position : Pos} {plan : P} (paid : Delivered source position plan) :
    HEq (nativeAccount (plan.exchanged source)) (nativeAccount source) := by
  obtain ⟨_, _, _, _, offerConsents, offerTransfer⟩ := paid.offer.1
  obtain ⟨_, _, deliveryConsents, deliveryTransfer⟩ := paid.delivery.1
  have start : Ready source ∧ ReviewAvailable source := by
    have trace := paid.trace
    cases trace with
    | cons _ _ _ _ ready review _ _ _ => exact ⟨ready, review⟩
  have first := two_actual_root_steps_pay_and_consume_the_generated_primitive
    source plan.offer start.1 start.2 offerConsents paid.offer.2.1
  have firstReview := afterNative_keeps_the_available_review source plan.offer
    start.1 start.2 offerConsents paid.offer.2.1
  have same := afterNative_keeps_the_same_original_input source plan.offer
  have deliveryValid : (sourceLaw (plan.middle source)).Valid (plan.middle source).raw plan.delivery := by
    rw [show sourceLaw (plan.middle source) = sourceLaw source from
      congrArg Abolition.Root.Registered.Physical.Public.interpreter same]
    exact paid.delivery.2.1
  exact (nativeAccount_heq_of_eq (plan.exchanged_eq source)).trans
    ((a_paid_transfer_keeps_the_literal_native_debt_account _ _ first.1 firstReview
      deliveryConsents deliveryValid _ _ _ deliveryTransfer).trans
    (a_paid_transfer_keeps_the_literal_native_debt_account _ _ start.1 start.2
      offerConsents paid.offer.2.1 _ _ _ offerTransfer))

theorem read_native_same {Value : Type}
    {oldInput newInput : ProgrammeSource.Input Party Good Port Technology Instrument}
    {oldDepth newDepth oldCount newCount : Nat}
    (old : (Epoch.Finance.process oldInput oldDepth oldCount).GeneratedState)
    (new : (Epoch.Finance.process newInput newDepth newCount).GeneratedState)
    (sameInput : newInput = oldInput) (sameDepth : newDepth = oldDepth) (sameCount : newCount = oldCount)
    (sameAccount : HEq new old)
    (read : ∀ (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat),
      (Epoch.Finance.process input depth count).GeneratedState → Value) :
    read newInput newDepth newCount new = read oldInput oldDepth oldCount old := by
  subst newInput newDepth newCount
  rw [eq_of_heq sameAccount]

theorem the_exchange_preserves_every_old_slot_balance_at_its_original_address
    {source : C} {position : Pos} {plan : P} (paid : Delivered source position plan)
    (index : Nat) (holder : Party) :
    principalAt (plan.exchanged source) index holder = principalAt source index holder := by
  obtain ⟨input, depth, count⟩ :=
    Quantities.Execution.the_actual_script_keeps_the_original_reader_indices source plan.script
  exact read_native_same (nativeAccount source) (nativeAccount (plan.exchanged source))
    input depth count (a_paid_exchange_keeps_the_whole_original_native_debt_account paid)
    (fun input depth count account => (account.current.slots[index]?.map (fun slot =>
      Epoch.Finance.slotBalance input depth count slot holder)).getD 0)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange
