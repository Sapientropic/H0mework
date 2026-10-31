import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Review

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

theorem an_actual_matching_payment_generates_its_original_review
    (claim : Epoch.Finance.Claim input depth count) (item : Epoch.Finance.ActualItem input depth count)
    (holder : Party) (quantity : ℚ)
    (operation : (item.instruction input depth count).request.operation =
      .settle (claim.instrument input depth count) (claim.debtor input depth count) holder quantity)
    (accepted : (item.interpreter input depth count).Valid (item.instruction input depth count).before
      (item.instruction input depth count).request) :
    ∃ receipt, Epoch.Finance.readReview input depth count claim item = some receipt ∧
      receipt.origin = item ∧ receipt.kind = .payment holder ∧ receipt.quantity = quantity := by
  unfold Epoch.Finance.readReview
  rw [dif_pos accepted]
  split <;> rename_i observed
  all_goals cases (operation.symm.trans observed)
  split
  · split
    · exact ⟨_,rfl,rfl,rfl,rfl⟩
    · contradiction
  · contradiction

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] in
theorem paying_the_single_original_share_clears_its_balance (holder : Party) (quantity : ℚ) :
    Financial.pay input (Finsupp.single holder quantity) holder quantity = 0 := by
  apply Finsupp.ext
  intro actor
  rw [Financial.pay_apply,Finsupp.single_apply,Finsupp.zero_apply]
  by_cases same : actor = holder
  · subst actor
    simp
  · simp only [if_neg same,if_neg (Ne.symm same),sub_zero]

theorem the_full_original_review_clears_the_single_share
    {claim : Epoch.Finance.Claim input depth count} (receipt : Epoch.Finance.Review input depth count claim)
    (holder : Party) (quantity : ℚ) (payment : receipt.kind = .payment holder) :
    receipt.after input depth count (Finsupp.single holder quantity) quantity = 0 := by
  unfold Epoch.Finance.Review.after Epoch.Finance.Review.allocated Epoch.Finance.Review.fromHolder
  rw [payment,Finsupp.single_eq_same,min_self]
  exact paying_the_single_original_share_clears_its_balance input holder quantity

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement
