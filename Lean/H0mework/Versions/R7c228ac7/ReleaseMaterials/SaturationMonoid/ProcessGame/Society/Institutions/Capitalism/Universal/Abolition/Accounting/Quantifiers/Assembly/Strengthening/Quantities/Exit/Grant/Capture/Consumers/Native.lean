import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture.Contract
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.Completed

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction.Repayment
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (life task source_ready source_review the_repair_really_funds_both_original_lives)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers
  (position proposal pay_from_the_existing_source every_positive_small_grant_executes_and_leaves_an_actual_exit_service)
open Redemption (sourceLaw unit)

noncomputable section

def charge : Request Bool Bool Bool Unit Unit :=
  ⟨false, [], false, [], .transfer false true [(true, 1)]⟩

/-- The charge policy is installed before the grant on the same physical
current and native account. The grant's temporary reader is separate. -/
def chargedSource := lifeSource.requery (fun _ _ => .primitive charge)

private def paidAmount := proposal 1

private theorem charged_grant_is_actually_paid :
    PaidAt (funded chargedSource paidAmount) position paidAmount.quantity := by
  have original := pay_from_the_existing_source 1 (by norm_num) (by norm_num)
  apply paid_grant_is_the_literal_original_issue_and_redemption
  · exact source_ready
  · exact source_review
  · exact original.qualified

private theorem the_after_grant_exposure_executes_the_old_charge :
    exposureScript chargedSource position paidAmount 1 = [some (.primitive charge)] := by
  unfold exposureScript
  simp only [Execution.originalResponses, List.nil_append]
  rw [Execution.a_constant_original_reader_does_not_repeat_a_temporary_submission
    chargedSource _ (.primitive charge) rfl]

private theorem original_food_available :
    (redeemed chargedSource position paidAmount).raw.stock false true = 1 := by
  have distinct : true ≠ unit (sourceLaw (funded chargedSource paidAmount)) position := by
    change true ≠ unit (sourceLaw lifeSource) position
    rw [SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.original_unit]
    decide
  rw [the_paid_grant_preserves_every_other_material_unit chargedSource position paidAmount charged_grant_is_actually_paid
    false true distinct]
  exact the_repair_really_funds_both_original_lives.1

private theorem the_material_charge_is_admitted
    (law : RawLaw Bool Bool Bool Unit Unit) (current : RawCurrent Bool Bool Unit Unit)
    (policy : law.operationAllowed current charge = true)
    (ports : ∀ port, law.allowed current.technology port false = true)
    (available : 1 ≤ current.stock false true) : law.Valid current charge := by
  refine ⟨⟨trivial, policy⟩, fun port _ => Or.inl (ports port), trivial, ?_, ?_, ?_⟩
  · simp [charge, RawLaw.debit, locate, NonnegativeBundle]
  · simp [charge, RawLaw.credit, locate, NonnegativeBundle]
  · simpa [charge, RawLaw.debit, locate, flowAt, amount] using available

private theorem the_old_charge_is_a_real_authorized_debit :
    (sourceLaw (redeemed chargedSource position paidAmount)).Valid
      (redeemed chargedSource position paidAmount).raw charge :=
  the_material_charge_is_admitted _ _ rfl (fun _ => rfl) (original_food_available.symm ▸ le_rfl)

private theorem the_paid_charge_deducts_one_food
    (law : RawLaw Bool Bool Bool Unit Unit) (current : RawCurrent Bool Bool Unit Unit)
    (paid : law.Valid current charge) :
    (law.step current charge).stock false true = current.stock false true - 1 := by
  rw [RawLaw.step, if_pos paid]
  simp [charge, RawLaw.paidStep, RawLaw.debit, RawLaw.credit, locate, flowAt, amount]

private theorem the_food_action_requires_one_real_unit (law : RawLaw Bool Bool Bool Unit Unit)
    (current : RawCurrent Bool Bool Unit Unit) (accepted : law.Valid current (life false)) :
    1 ≤ current.stock false true := by
  have debit : law.debit current (life false) = [((false, true), 1)] := rfl
  have sufficient := accepted.2.2.2.2.2 ((false, true), (1 : ℚ)) (debit.symm ▸ List.mem_cons_self)
  rw [debit] at sufficient
  have cost : flowAt ([((false, true), 1)] : List ((Bool × Bool) × ℚ)) false true = 1 := by decide +kernel
  exact cost ▸ sufficient

theorem the_same_paid_amount_can_lose_the_original_food_continuation :
    chargedSource.raw = lifeSource.raw ∧
      Completed lifeSource position [] task paidAmount ∧
      PaidAt (funded chargedSource paidAmount) position paidAmount.quantity ∧
      (exposed chargedSource position paidAmount 1).raw.stock false true = 0 ∧
      ¬ (sourceLaw (exposed chargedSource position paidAmount 1)).Valid
        (exposed chargedSource position paidAmount 1).raw (life false) ∧
      Recorded chargedSource (compile chargedSource position (expand chargedSource position 1 paidAmount)) := by
  have initial := every_positive_small_grant_executes_and_leaves_an_actual_exit_service 1 (by norm_num) (by norm_num)
  have actual := the_original_root_executes_the_generated_request
    (redeemed chargedSource position paidAmount) charge charged_grant_is_actually_paid.ready
    charged_grant_is_actually_paid.available rfl the_old_charge_is_a_real_authorized_debit
  have zero : (exposed chargedSource position paidAmount 1).raw.stock false true = 0 := by
    unfold exposed
    rw [the_after_grant_exposure_executes_the_old_charge]
    change (afterBody (redeemed chargedSource position paidAmount) charge).raw.stock false true = 0
    exact (congrArg (fun state : RawCurrent Bool Bool Unit Unit => state.stock false true) actual.1).trans
      ((the_paid_charge_deducts_one_food _ _ the_old_charge_is_a_real_authorized_debit).trans
        (original_food_available.symm ▸ sub_self (1 : ℚ)))
  refine ⟨rfl, initial, charged_grant_is_actually_paid, zero, ?_, record chargedSource _⟩
  intro accepted
  have needed := the_food_action_requires_one_real_unit _ _ accepted
  rw [zero] at needed
  norm_num at needed

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture.Consumers
