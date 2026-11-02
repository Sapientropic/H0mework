import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.PaymentStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Good : Type} [DecidableEq Good]
  (source : ProgrammeSource.Input Party Good Bool Nat Unit) (depth count : Nat)

private theorem the_original_holder_two_slot_does_not_fund_a_holder_one_payment
    (origin : Epoch.Finance.ActualItem source depth count)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (index : Fin state.current.slots.length)
    (old : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (present : state.current.slots.get index = .live old)
    (receipt : Epoch.Finance.Review source depth count old.content)
    (read : Epoch.Finance.readReview source depth count old.content origin = some receipt)
    (available : ℚ) (nonnegative : 0 ≤ available)
    (kind : receipt.kind = .payment 1) (original : old.residual = Finsupp.single 2 1) :
    (nativeAt source depth count origin state index available nonnegative).after.current.slots = state.current.slots ∧
      (nativeAt source depth count origin state index available nonnegative).remaining = available := by
  apply the_original_zero_use_step_keeps_every_slot_and_the_same_quota source depth count
    origin state index old present receipt read available nonnegative 1 kind
  · change min (min available receipt.quantity) (old.residual (receipt.fromHolder source depth count)) = 0
    have zero : old.residual (receipt.fromHolder source depth count) = 0 := by
      simp [original,Epoch.Finance.Review.fromHolder,kind]
    rw [zero]
    exact min_eq_right (le_min nonnegative (receipt.quantity_nonnegative source depth count))
  · rw [original]
    simp

theorem the_original_failure_coverage_pays_its_risk_without_touching_the_two_prior_slots
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (old loan risk : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (slots : state.current.slots = [.live old,.live loan,.live risk])
    (oldDebtor : old.content.debtor source depth count = 0)
    (loanDebtor : loan.content.debtor source depth count = 0)
    (riskDebtor : risk.content.debtor source depth count = 1)
    (riskBalance : risk.residual = Finsupp.single 0 1)
    (origin : Epoch.Finance.ActualItem source depth count)
    (operation : (origin.instruction source depth count).request.operation = .settle () 1 0 1)
    (accepted : (origin.interpreter source depth count).Valid (origin.instruction source depth count).before
      (origin.instruction source depth count).request)
    (movement : Epoch.Finance.Movement source depth count origin) (amount : movement.quantity = 1) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary source depth count),
      (Epoch.Finance.allocate source depth count origin movement state).after.current.slots =
        [.live old,.live loan,.terminal archive] ∧ archive.obligation = risk := by
  have oldRead := an_actual_payment_skips_a_different_original_debtor source depth count old.content origin 1 0 1
    (by rw [oldDebtor]; decide +kernel) operation accepted
  have loanRead := an_actual_payment_skips_a_different_original_debtor source depth count loan.content origin 1 0 1
    (by rw [loanDebtor]; decide +kernel) operation accepted
  obtain ⟨receipt,riskRead,kind,quantity⟩ :=
    an_actual_payment_reviews_the_same_original_debtor source depth count risk.content origin 1 0 1 riskDebtor operation accepted
  let first := nativeAt source depth count origin state 0 movement.quantity (movement.quantity_nonnegative source depth count)
  have firstStep := nativeAt_none source depth count origin state
    ⟨0,by simp [slots]⟩ old (by simp [slots]) oldRead _ (movement.quantity_nonnegative source depth count)
  have firstSlots : first.after.current.slots = [.live old,.live loan,.live risk] :=
    (congrArg (fun value : (Epoch.Finance.process source depth count).GeneratedState => value.current.slots) firstStep.1).trans slots
  have firstAmount : first.remaining = 1 := firstStep.2.trans amount
  let second := nativeAt source depth count origin first.after 1 first.remaining first.remaining_nonnegative
  have secondStep := nativeAt_none source depth count origin first.after
    ⟨1,by simp [firstSlots]⟩ loan (by simp [firstSlots]) loanRead _ first.remaining_nonnegative
  have secondSlots : second.after.current.slots = [.live old,.live loan,.live risk] :=
    (congrArg (fun value : (Epoch.Finance.process source depth count).GeneratedState => value.current.slots) secondStep.1).trans firstSlots
  have secondAmount : second.remaining = 1 := secondStep.2.trans firstAmount
  obtain ⟨archive,paid,original,_,_⟩ :=
    the_original_fully_paid_step_generates_its_exact_archive_and_remaining_quota source depth count origin second.after
      ⟨2,by simp [secondSlots]⟩ risk (by simp [secondSlots]) receipt riskRead _ second.remaining_nonnegative
      0 1 kind riskBalance (by rw [secondAmount]) (by rw [quantity])
  have split := the_original_three_slot_allocation_is_three_original_steps source depth count origin movement state (by simp [slots])
  refine ⟨archive,?_,original⟩
  exact (congrArg (fun value : (Epoch.Finance.process source depth count).GeneratedState => value.current.slots) split.1).trans
    (by simpa only [secondSlots,List.set_cons_succ,List.set_cons_zero] using paid)

theorem the_original_success_premium_pays_its_risk_without_touching_the_old_slot_or_loan_archive
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (old risk : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (loan : TerminalArchive (Epoch.Finance.vocabulary source depth count)) (quantity : ℚ)
    (slots : state.current.slots = [.live old,.terminal loan,.live risk])
    (oldDebtor : old.content.debtor source depth count = 0)
    (oldBalance : old.residual = Finsupp.single 2 1)
    (riskDebtor : risk.content.debtor source depth count = 0)
    (riskBalance : risk.residual = Finsupp.single 1 quantity)
    (origin : Epoch.Finance.ActualItem source depth count)
    (operation : (origin.instruction source depth count).request.operation = .settle () 0 1 quantity)
    (accepted : (origin.interpreter source depth count).Valid (origin.instruction source depth count).before
      (origin.instruction source depth count).request)
    (movement : Epoch.Finance.Movement source depth count origin) (amount : movement.quantity = quantity) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary source depth count),
      (Epoch.Finance.allocate source depth count origin movement state).after.current.slots =
        [.live old,.terminal loan,.terminal archive] ∧ archive.obligation = risk := by
  obtain ⟨oldReceipt,oldRead,oldKind,_⟩ :=
    an_actual_payment_reviews_the_same_original_debtor source depth count old.content origin 0 1 quantity oldDebtor operation accepted
  obtain ⟨receipt,riskRead,kind,sourceQuantity⟩ :=
    an_actual_payment_reviews_the_same_original_debtor source depth count risk.content origin 0 1 quantity riskDebtor operation accepted
  let first := nativeAt source depth count origin state 0 movement.quantity (movement.quantity_nonnegative source depth count)
  have firstStep := the_original_holder_two_slot_does_not_fund_a_holder_one_payment source depth count origin state
    ⟨0,by simp [slots]⟩ old (by simp [slots]) oldReceipt oldRead _ (movement.quantity_nonnegative source depth count) oldKind oldBalance
  have firstSlots : first.after.current.slots = [.live old,.terminal loan,.live risk] := firstStep.1.trans slots
  have firstAmount : first.remaining = quantity := firstStep.2.trans amount
  let second := nativeAt source depth count origin first.after 1 first.remaining first.remaining_nonnegative
  have secondStep := nativeAt_terminal source depth count origin first.after
    ⟨1,by simp [firstSlots]⟩ loan (by simp [firstSlots]) _ first.remaining_nonnegative
  have secondSlots : second.after.current.slots = [.live old,.terminal loan,.live risk] :=
    (congrArg (fun value : (Epoch.Finance.process source depth count).GeneratedState => value.current.slots) secondStep.1).trans firstSlots
  have secondAmount : second.remaining = quantity := secondStep.2.trans firstAmount
  obtain ⟨archive,paid,original,_,_⟩ :=
    the_original_fully_paid_step_generates_its_exact_archive_and_remaining_quota source depth count origin second.after
      ⟨2,by simp [secondSlots]⟩ risk (by simp [secondSlots]) receipt riskRead _ second.remaining_nonnegative
      1 quantity kind riskBalance (by rw [secondAmount]) (by rw [sourceQuantity])
  have split := the_original_three_slot_allocation_is_three_original_steps source depth count origin movement state (by simp [slots])
  refine ⟨archive,?_,original⟩
  exact (congrArg (fun value : (Epoch.Finance.process source depth count).GeneratedState => value.current.slots) split.1).trans
    (by simpa only [secondSlots,List.set_cons_succ,List.set_cons_zero] using paid)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement
