import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program

noncomputable section

variable {Party Good : Type} [DecidableEq Party] [DecidableEq Good]
  (source : ProgrammeSource.Input Party Good Bool Nat Unit) (depth count : Nat)

theorem an_actual_payment_generates_its_original_movement
    (item : Epoch.Finance.ActualItem source depth count) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction source depth count).request.operation = .settle () debtor holder quantity)
    (accepted : (item.interpreter source depth count).Valid (item.instruction source depth count).before
      (item.instruction source depth count).request) :
    ∃ movement : Epoch.Finance.Movement source depth count item,
      Epoch.Finance.readMovement source depth count item = some movement ∧
      movement.kind = .payment ∧ movement.debtor = debtor ∧ movement.sender = holder ∧
      movement.quantity = quantity := by
  unfold Epoch.Finance.readMovement
  rw [dif_pos accepted]
  split
  · rename_i _ _ _ _ observed
    cases operation.symm.trans observed
    exact ⟨_,rfl,rfl,rfl,rfl,rfl⟩
  · rename_i _ _ _ _ _ observed
    cases operation.symm.trans observed
  · rename_i notPayment _
    exact False.elim (notPayment () debtor holder quantity operation)

theorem an_actual_payment_cannot_generate_a_new_claim
    (item : Epoch.Finance.ActualItem source depth count) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction source depth count).request.operation = .settle () debtor holder quantity) :
    Epoch.Finance.readNewClaim source depth count item = none := by
  unfold Epoch.Finance.readNewClaim
  split
  · rename_i _ _ _ _ observed
    cases operation.symm.trans observed
  · rfl

theorem the_actual_payment_uses_only_its_source_allocation
    (item : Epoch.Finance.ActualItem source depth count) (debtor holder : Party) (quantity : ℚ)
    (operation : (item.instruction source depth count).request.operation = .settle () debtor holder quantity)
    (accepted : (item.interpreter source depth count).Valid (item.instruction source depth count).before
      (item.instruction source depth count).request)
    (before : (Epoch.Finance.process source depth count).GeneratedState) :
    ∃ movement : Epoch.Finance.Movement source depth count item,
      Epoch.Finance.readMovement source depth count item = some movement ∧
      movement.kind = .payment ∧ movement.debtor = debtor ∧ movement.sender = holder ∧
      movement.quantity = quantity ∧
      (Epoch.Finance.consume source depth count item before).next source depth count =
        (Epoch.Finance.allocate source depth count item movement before).after := by
  obtain ⟨movement,returned,kind,actor,receiver,amount⟩ :=
    an_actual_payment_generates_its_original_movement source depth count item debtor holder quantity operation accepted
  refine ⟨movement,returned,kind,actor,receiver,amount,?_⟩
  unfold Epoch.Finance.consume
  rw [dif_neg (not_not_intro accepted)]
  split
  · rename_i claim issued
    have absent := an_actual_payment_cannot_generate_a_new_claim source depth count item debtor holder quantity operation
    cases absent.symm.trans issued
  · split
    · rename_i actual found
      cases Option.some.inj (found.symm.trans returned)
      rfl
    · rename_i absent
      cases absent.symm.trans returned

theorem an_actual_payment_reviews_the_same_original_debtor
    (claim : Epoch.Finance.Claim source depth count) (item : Epoch.Finance.ActualItem source depth count)
    (debtor holder : Party) (quantity : ℚ)
    (sameDebtor : claim.debtor source depth count = debtor)
    (operation : (item.instruction source depth count).request.operation = .settle () debtor holder quantity)
    (accepted : (item.interpreter source depth count).Valid (item.instruction source depth count).before
      (item.instruction source depth count).request) :
    ∃ receipt, Epoch.Finance.readReview source depth count claim item = some receipt ∧
      receipt.kind = .payment holder ∧ receipt.quantity = quantity := by
  unfold Epoch.Finance.readReview
  rw [dif_pos accepted]
  split <;> rename_i observed
  all_goals cases (operation.symm.trans observed)
  split
  · split
    · exact ⟨_,rfl,rfl,rfl⟩
    · rename_i different
      exact (different sameDebtor.symm).elim
  · rename_i different
    exact (different (Subsingleton.elim _ _)).elim

theorem an_actual_payment_skips_a_different_original_debtor
    (claim : Epoch.Finance.Claim source depth count) (item : Epoch.Finance.ActualItem source depth count)
    (debtor holder : Party) (quantity : ℚ)
    (differentDebtor : debtor ≠ claim.debtor source depth count)
    (operation : (item.instruction source depth count).request.operation = .settle () debtor holder quantity)
    (accepted : (item.interpreter source depth count).Valid (item.instruction source depth count).before
      (item.instruction source depth count).request) :
    Epoch.Finance.readReview source depth count claim item = none := by
  unfold Epoch.Finance.readReview
  rw [dif_pos accepted]
  split <;> rename_i observed
  all_goals cases (operation.symm.trans observed)
  split
  · rfl
  · rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Native.Settlement
