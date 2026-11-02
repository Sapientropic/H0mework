import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement.PaymentStep

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Source.Program

noncomputable section

section Zero
variable {Party Good : Type} [DecidableEq Party] [DecidableEq Good]
  (source : ProgrammeSource.Input Party Good Bool Nat Unit) (depth count : Nat)

theorem the_original_zero_quota_keeps_every_nonzero_slot
    (origin : Epoch.Finance.ActualItem source depth count)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (index : Fin state.current.slots.length) (debtor holder : Party) (quantity : ℚ)
    (operation : (origin.instruction source depth count).request.operation = .settle () debtor holder quantity)
    (accepted : (origin.interpreter source depth count).Valid (origin.instruction source depth count).before
      (origin.instruction source depth count).request)
    (available : ℚ) (nonnegative : 0 ≤ available) (empty : available = 0)
    (nonzero : ∀ obligation, state.current.slots.get index = .live obligation → obligation.residual ≠ 0) :
    (nativeAt source depth count origin state index available nonnegative).after.current.slots = state.current.slots ∧
      (nativeAt source depth count origin state index available nonnegative).remaining = 0 := by
  subst available
  cases observed : state.current.slots.get index with
  | terminal archive =>
      have kept := nativeAt_terminal source depth count origin state index archive observed 0 nonnegative
      exact ⟨congrArg (fun current => current.current.slots) kept.1,kept.2⟩
  | live obligation =>
      by_cases same : obligation.content.debtor source depth count = debtor
      · obtain ⟨receipt,read,kind,_⟩ := an_actual_payment_reviews_the_same_original_debtor
          source depth count obligation.content origin debtor holder quantity same operation accepted
        have unused : receipt.allocated source depth count obligation.residual (min 0 receipt.quantity) = 0 := by
          unfold Epoch.Finance.Review.allocated
          rw [min_eq_left (receipt.quantity_nonnegative source depth count)]
          exact min_eq_left ((Epoch.Finance.live_sound source depth count state index obligation observed).2 _)
        exact the_original_zero_use_step_keeps_every_slot_and_the_same_quota source depth count
          origin state index obligation observed receipt read 0 nonnegative holder kind unused (nonzero obligation observed)
      · have read := an_actual_payment_skips_a_different_original_debtor source depth count
          obligation.content origin debtor holder quantity (Ne.symm same) operation accepted
        have kept := nativeAt_none source depth count origin state index obligation observed read 0 nonnegative
        exact ⟨congrArg (fun current => current.current.slots) kept.1,kept.2⟩
end Zero

variable {Good : Type} [DecidableEq Good]
  (source : ProgrammeSource.Input (Fin 3) Good Bool Nat Unit) (depth count : Nat)

theorem the_original_principal_payment_archives_the_loan_and_preserves_its_other_slots
    (origin : Epoch.Finance.ActualItem source depth count)
    (movement : Epoch.Finance.Movement source depth count origin)
    (state : (Epoch.Finance.process source depth count).GeneratedState)
    (old loan : AdmittedObligation (Epoch.Finance.vocabulary source depth count))
    (tail : ObligationSlot (Epoch.Finance.vocabulary source depth count))
    (slots : state.current.slots = [.live old,.live loan,tail])
    (oldDebtor : old.content.debtor source depth count = 0)
    (oldBalance : old.residual = Finsupp.single 2 1)
    (loanDebtor : loan.content.debtor source depth count = 0)
    (loanBalance : loan.residual = Finsupp.single 1 3)
    (tailNonzero : ∀ obligation, tail = .live obligation → obligation.residual ≠ 0)
    (operation : (origin.instruction source depth count).request.operation = .settle () 0 1 3)
    (accepted : (origin.interpreter source depth count).Valid (origin.instruction source depth count).before
      (origin.instruction source depth count).request)
    (quantity : movement.quantity = 3) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary source depth count),
      (Epoch.Finance.allocate source depth count origin movement state).after.current.slots =
        [.live old,.terminal archive,tail] ∧ archive.obligation = loan := by
  let first := nativeAt source depth count origin state 0 movement.quantity (movement.quantity_nonnegative source depth count)
  let firstIndex : Fin state.current.slots.length := ⟨0,by simp only [slots,List.length_cons,List.length_nil]; omega⟩
  have oldPresent : state.current.slots.get firstIndex = .live old := by
    simp only [List.get_eq_getElem,firstIndex,slots,List.getElem_cons_zero]
  obtain ⟨oldReceipt,oldRead,oldKind,oldAmount⟩ := an_actual_payment_reviews_the_same_original_debtor
    source depth count old.content origin 0 1 3 oldDebtor operation accepted
  have unused : oldReceipt.allocated source depth count old.residual (min movement.quantity oldReceipt.quantity) = 0 := by
    simp only [Epoch.Finance.Review.allocated,Epoch.Finance.Review.fromHolder,oldKind,oldBalance,quantity,oldAmount]
    norm_num [Finsupp.single_apply,show (2 : Fin 3) ≠ 1 by decide]
  have firstKept : first.after.current.slots = state.current.slots ∧ first.remaining = movement.quantity :=
    the_original_zero_use_step_keeps_every_slot_and_the_same_quota source depth count origin state
      firstIndex old oldPresent oldReceipt oldRead movement.quantity (movement.quantity_nonnegative source depth count)
      1 oldKind unused (by rw [oldBalance]; simp)
  let second := nativeAt source depth count origin first.after 1 first.remaining first.remaining_nonnegative
  let secondIndex : Fin first.after.current.slots.length := ⟨1,by simp only [firstKept.1,slots,List.length_cons,List.length_nil]; omega⟩
  have loanPresent : first.after.current.slots.get secondIndex = .live loan := by
    simp only [List.get_eq_getElem,secondIndex,firstKept.1,slots,List.getElem_cons_succ,List.getElem_cons_zero]
  obtain ⟨loanReceipt,loanRead,loanKind,loanAmount⟩ := an_actual_payment_reviews_the_same_original_debtor
    source depth count loan.content origin 0 1 3 loanDebtor operation accepted
  obtain ⟨archive,loanSlots,original,remainder,_⟩ :=
    the_original_fully_paid_step_generates_its_exact_archive_and_remaining_quota source depth count origin first.after
      secondIndex loan loanPresent loanReceipt loanRead first.remaining first.remaining_nonnegative
      1 3 loanKind loanBalance (by rw [firstKept.2,quantity]) (by rw [loanAmount])
  have secondSlots : second.after.current.slots = [.live old,.terminal archive,tail] := by
    refine loanSlots.trans ?_
    change first.after.current.slots.set 1 (.terminal archive) = _
    rw [firstKept.1,slots]
    rfl
  have exhausted : second.remaining = 0 := by
    rw [remainder,firstKept.2,quantity]
    norm_num
  let third := nativeAt source depth count origin second.after 2 second.remaining second.remaining_nonnegative
  let thirdIndex : Fin second.after.current.slots.length := ⟨2,by simp only [secondSlots,List.length_cons,List.length_nil]; omega⟩
  have tailPresent : second.after.current.slots.get thirdIndex = tail := by
    simp only [List.get_eq_getElem,thirdIndex,secondSlots,List.getElem_cons_succ,List.getElem_cons_zero]
  have lastKept : third.after.current.slots = second.after.current.slots :=
    (the_original_zero_quota_keeps_every_nonzero_slot source depth count origin second.after thirdIndex 0 1 3
      operation accepted second.remaining second.remaining_nonnegative exhausted
      (fun obligation present => tailNonzero obligation (tailPresent.symm.trans present))).1
  have allSteps := the_original_three_slot_allocation_is_three_original_steps source depth count origin movement state
    (by rw [slots]; rfl)
  refine ⟨archive,?_,original⟩
  exact (congrArg (fun current => current.current.slots) allSteps.1).trans (lastKept.trans secondSlots)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement
