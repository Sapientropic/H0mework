import H0mework.Realization.Relaxation.P226
import H0mework.Realization.Residual.P498

/-!
# Proposition 499: inverse branch is outside the runtime-safe rate domain

P498 bundled the energy-language projection guardrail: forward positive
saturation has finite accounting, while H¹/Hamiltonian divergence belongs to
the one-sided inverse branch and requires producer certificates.

This file adds the missing runtime-domain statement.  For every genuine
runtime saturation rate `0 < sigma < 1`, its noisy-OR inverse is a legitimate
field inverse but not a legitimate anti-nag/runtime rate:

* `satOrFieldInv sigma < 0`;
* therefore `¬ ValidRate (satOrFieldInv sigma)`;
* applying that inverse rate to the zero state immediately leaves the safe
  interval `[0,1]`.

Thus inverse-branch growth is a controlled algebraic projection, not an
ordinary runtime salience update.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

/-! ## Inverse rates are not runtime-valid rates -/

/-- THEOREM 1: the noisy-OR inverse of a genuine runtime rate lies outside
the runtime-safe interval `[0,1]`. -/
theorem satOrFieldInv_not_validRate_of_mem_Ioo
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    ¬ ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma) := by
  intro hvalid
  have hneg : SatOrFieldAlgebra.satOrFieldInv sigma < 0 :=
    satOrFieldInv_neg_of_mem_Ioo hpos hlt
  exact (not_le_of_gt hneg) hvalid.1

/-- THEOREM 2: the sampled inverse branch is outside the runtime-safe rate
domain whenever the sampled scale is positive. -/
theorem sampled_satOrFieldInv_not_validRate_of_mul_pos
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    ¬ ValidRate
      (SatOrFieldAlgebra.satOrFieldInv (realDecayRate lambda step)) := by
  exact satOrFieldInv_not_validRate_of_mem_Ioo
    (realDecayRate_pos_of_mul_pos hpos)
    (realDecayRate_lt_one lambda step)

/-! ## A one-step inverse bump leaves the safe state interval -/

/-- THEOREM 3: from the zero state, one inverse bump is exactly the inverse
rate itself. -/
theorem bumpSatField_zero_inverse_rate_eq_inv_rate
    (sigma : ℝ) :
    bumpSatField 0 (SatOrFieldAlgebra.satOrFieldInv sigma) =
      SatOrFieldAlgebra.satOrFieldInv sigma := by
  unfold bumpSatField
  ring

/-- THEOREM 4: applying the inverse rate of a genuine runtime rate to the zero
state immediately produces a negative scalar. -/
theorem bumpSatField_zero_inverse_rate_neg_of_mem_Ioo
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    bumpSatField 0 (SatOrFieldAlgebra.satOrFieldInv sigma) < 0 := by
  rw [bumpSatField_zero_inverse_rate_eq_inv_rate]
  exact satOrFieldInv_neg_of_mem_Ioo hpos hlt

/-- THEOREM 5: hence the one-step inverse bump from zero is not in the safe
state interval `[0,1]`. -/
theorem bumpSatField_zero_inverse_rate_not_mem_Icc_of_mem_Ioo
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    ¬ bumpSatField 0 (SatOrFieldAlgebra.satOrFieldInv sigma) ∈
      Set.Icc (0 : ℝ) 1 := by
  intro hmem
  have hneg :=
    bumpSatField_zero_inverse_rate_neg_of_mem_Ioo hpos hlt
  exact (not_le_of_gt hneg) hmem.1

/-- THEOREM 6: the sampled inverse bump from zero also leaves `[0,1]` whenever
the sampled scale is positive. -/
theorem sampled_inverse_bump_from_zero_not_mem_Icc_of_mul_pos
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    ¬ bumpSatField 0
        (SatOrFieldAlgebra.satOrFieldInv (realDecayRate lambda step)) ∈
      Set.Icc (0 : ℝ) 1 := by
  exact bumpSatField_zero_inverse_rate_not_mem_Icc_of_mem_Ioo
    (realDecayRate_pos_of_mul_pos hpos)
    (realDecayRate_lt_one lambda step)

/-! ## Bundled receipt -/

/-- Compact receipt separating field inverse algebra from runtime-safe
anti-nag rates. -/
structure InverseBranchOutsideRuntimeSafeDomainReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  inverse_not_valid :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      ¬ ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)
  sampled_inverse_not_valid :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      ¬ ValidRate
        (SatOrFieldAlgebra.satOrFieldInv (realDecayRate lambda step))
  inverse_zero_step_negative :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      bumpSatField 0 (SatOrFieldAlgebra.satOrFieldInv sigma) < 0
  inverse_zero_step_not_safe :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      ¬ bumpSatField 0 (SatOrFieldAlgebra.satOrFieldInv sigma) ∈
        Set.Icc (0 : ℝ) 1
  sampled_inverse_zero_step_not_safe :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      ¬ bumpSatField 0
          (SatOrFieldAlgebra.satOrFieldInv (realDecayRate lambda step)) ∈
        Set.Icc (0 : ℝ) 1
  energy_language_guardrail :
    EnergyLanguageProjectionGuardrailReceipt.{u, v} E

/-- THEOREM 7: the inverse branch is outside the runtime-safe rate domain. -/
theorem inverseBranchOutsideRuntimeSafeDomainReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    InverseBranchOutsideRuntimeSafeDomainReceipt.{u, v} E where
  inverse_not_valid := fun _ hpos hlt =>
    satOrFieldInv_not_validRate_of_mem_Ioo hpos hlt
  sampled_inverse_not_valid := fun _ _ hpos =>
    sampled_satOrFieldInv_not_validRate_of_mul_pos hpos
  inverse_zero_step_negative := fun _ hpos hlt =>
    bumpSatField_zero_inverse_rate_neg_of_mem_Ioo hpos hlt
  inverse_zero_step_not_safe := fun _ hpos hlt =>
    bumpSatField_zero_inverse_rate_not_mem_Icc_of_mem_Ioo hpos hlt
  sampled_inverse_zero_step_not_safe := fun _ _ hpos =>
    sampled_inverse_bump_from_zero_not_mem_Icc_of_mul_pos hpos
  energy_language_guardrail :=
    energyLanguageProjectionGuardrailReceipt.{u, v} E

end AffineRelaxation
end SaturationMonoid
