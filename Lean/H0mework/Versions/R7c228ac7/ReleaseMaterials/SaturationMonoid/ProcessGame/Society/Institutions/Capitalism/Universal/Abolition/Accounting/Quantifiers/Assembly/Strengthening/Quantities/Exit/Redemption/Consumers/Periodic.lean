import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Consumers.UBI
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.UBI.Execution
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Consumers.Periodic

open Source.Program PublicFunction.Repayment
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Instances.UBI (law state body actual_next time_independent consume program currentAt_exact
  periodic_grant_has_actual_purchasing_power)

noncomputable section

abbrev occurrence (period : Nat) := ProgrammeHistory.visitAt originalInput (period + 1)

def before (period : Nat) := ProgrammeSource.rawCurrent originalInput (occurrence period).current

theorem every_renewal_uses_the_original_root_word (period : Nat) :
    ProgrammeSource.rawEvent originalInput (occurrence period).current = body := by
  change ProgrammeSource.rawEvent originalInput
    (ProgrammeSource.next originalInput (ProgrammeHistory.visitAt originalInput period).current) = body
  cases (ProgrammeHistory.visitAt originalInput period).current <;> rfl

theorem every_actual_cut_has_the_source_generated_time_and_stock (period : Nat) :
    before period = state ((period : ℚ) + 1) (period + 1) := by
  induction period with
  | zero => rfl
  | succ period prior =>
    change ProgrammeSource.rawCurrent originalInput (ProgrammeSource.next originalInput (occurrence period).current) = _
    rw [ProgrammeSource.actual_raw_next, every_renewal_uses_the_original_root_word]
    change law.next (before period) body = _
    rw [prior, actual_next, Nat.cast_succ]

def atRedemption (period : Nat) :=
  (law.execute (before period) 0 (List.take 2 (ProgrammeSource.rawEvent originalInput (occurrence period).current))).final

private theorem atRedemption_retimes_the_original_credit (period : Nat) :
    atRedemption period = redemptionCut.retime ((period : ℚ) + 1) (period + 1) := by
  have original : before period = originalNeedCut.retime ((period : ℚ) + 1) (period + 1) := by
    rw [every_actual_cut_has_the_source_generated_time_and_stock]
    rfl
  unfold atRedemption
  rw [every_renewal_uses_the_original_root_word, original, law.execute_retime time_independent]
  rfl

private theorem safe_amount_is_time_independent (period : Nat) (quantity : ℚ) :
    Safe law (before period) (atRedemption period) position quantity ↔
      Safe law originalNeedCut redemptionCut position quantity := by
  rw [atRedemption_retimes_the_original_credit]
  unfold Safe
  rw [law.valid_retime time_independent, law.step_retime time_independent]
  rfl

theorem each_original_paid_renewal_has_the_same_tight_usable_amount
    (period : Nat) :
    (law.rawItems (before period) (ProgrammeSource.rawEvent originalInput (occurrence period).current))[2]? =
        some ⟨2, atRedemption period, request law position 1⟩ ∧
      Safe law (before period) (atRedemption period) position 1 ∧
      (∀ quantity, Safe law (before period) (atRedemption period) position quantity ↔ quantity = 1) ∧
      (type_of% (ProgrammeHistory.execution_face_shares_whole_ledger_and_next originalInput (period + 1))) := by
  have original := the_actual_ubi_leg_attains_the_source_bounds
  have safe := (safe_amount_is_time_independent period 1).mpr original.2.2.1
  refine ⟨?_, safe, fun quantity => ⟨fun accepted => original.2.2.2 quantity
    ((safe_amount_is_time_independent period quantity).mp accepted), fun exactAmount => exactAmount.symm ▸ safe⟩,
    ProgrammeHistory.execution_face_shares_whole_ledger_and_next originalInput (period + 1)⟩
  unfold atRedemption
  rw [every_renewal_uses_the_original_root_word]
  rfl

theorem every_renewal_pays_the_original_independent_living_service (period : Nat) :
    ∃ item ∈ law.rawItems (before period) (ProgrammeSource.rawEvent originalInput (occurrence period).current),
      item.request = consume ∧ law.Valid item.before item.request ∧
      item.request.consents = [] ∧ flowAt (law.actualDebit item.before item.request) true () = 1 := by
  have literal : before period = program.currentAt (period + 1) := by
    rw [every_actual_cut_has_the_source_generated_time_and_stock, currentAt_exact, Nat.cast_succ]
  rw [literal, every_renewal_uses_the_original_root_word]
  obtain ⟨item, present, same, paid, debit⟩ := (periodic_grant_has_actual_purchasing_power (period + 1)).2.2
  exact ⟨item, present, same, paid, same.symm ▸ rfl, debit⟩

theorem the_registered_ubi_payments_cross_every_actual_time_horizon (horizon : ℚ) :
    ∃ period, horizon < (before period).clock ∧
      Safe law (before period) (atRedemption period) position 1 := by
  obtain ⟨period, beyond⟩ := exists_nat_gt horizon
  refine ⟨period, ?_, (each_original_paid_renewal_has_the_same_tight_usable_amount period).2.1⟩
  rw [every_actual_cut_has_the_source_generated_time_and_stock]
  change horizon < (period : ℚ) + 1
  linarith

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Redemption.Consumers.Periodic
