import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.Completed

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers

open Innovation.Contribution.Pricing.Consumers.Actual (task)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)

noncomputable section

def originalAmounts : Set EReal :=
  Bounds.Compiled.values lifeSource (compile lifeSource position) (inspectPlan lifeSource position [] task) principal

theorem every_strict_positive_limit_has_an_original_paid_exit_grant (limit : EReal)
    (positive : 0 < limit) :
    ∃ plan, Completed lifeSource position [] task plan ∧ principal plan < limit := by
  obtain ⟨quantity, pos, small⟩ :=
    EReal.exists_rat_btwn_of_lt (lt_min positive (show (0 : EReal) < 1 from zero_lt_one))
  have amountPositive : 0 < quantity := Rat.cast_pos.mp (EReal.coe_lt_coe_iff.mp pos)
  have realSmall : (quantity : ℝ) < 1 := EReal.coe_lt_coe_iff.mp
    (by simpa only [EReal.coe_one] using (lt_min_iff.mp small).2)
  have atMostOne : quantity ≤ 1 := by exact_mod_cast realSmall.le
  exact ⟨proposal quantity, every_positive_small_grant_executes_and_leaves_an_actual_exit_service
    quantity amountPositive atMostOne, (lt_min_iff.mp small).1⟩

private theorem actual_amounts_are_strictly_positive (amount : EReal) (actual : amount ∈ originalAmounts) :
    0 < amount := by
  obtain ⟨plan, paid, rfl⟩ := (exact_joint_grant_domain lifeSource position [] task amount).mp actual
  exact EReal.coe_lt_coe_iff.mpr (Rat.cast_pos.mpr paid.eligible.positive)

theorem the_full_original_grant_infimum_is_zero_without_a_zero_payment_receipt :
    sInf originalAmounts = 0 ∧ 0 ∉ originalAmounts ∧
      ∀ limit, 0 < limit → ∃ plan, Completed lifeSource position [] task plan ∧ principal plan < limit := by
  refine ⟨?_, fun impossible => (lt_irrefl _ (actual_amounts_are_strictly_positive 0 impossible)), ?_⟩
  · apply le_antisymm
    · apply le_of_not_gt
      intro positive
      obtain ⟨plan, actual, cheaper⟩ :=
        every_strict_positive_limit_has_an_original_paid_exit_grant _ positive
      have listed : principal plan ∈ originalAmounts :=
        (exact_joint_grant_domain lifeSource position [] task _).mpr ⟨plan, actual, rfl⟩
      exact (not_lt_of_ge (sInf_le listed)) cheaper
    · exact le_sInf (fun amount listed => (actual_amounts_are_strictly_positive amount listed).le)
  · exact every_strict_positive_limit_has_an_original_paid_exit_grant

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers
