import H0mework.Realization.Residual.P479
import H0mework.Quantum.Generator.P489

/-!
# Proposition 490: finite forward accounting versus inverse-scale blow-up

The prose around the saturation carrier often uses the vivid phrase “an
arbitrarily small rate can exhaust all headroom over infinitely many steps.”
P479 proves the exact theorem behind that phrase:

`∑' n, σ(1-σ)^n = 1` for `0 < σ < 1`.

This file records the guardrail that belongs next to it.  Forward positive
saturation does **not** diverge to infinity; its cumulative accounting tends to
one.  Divergence enters only through the explicit noisy-OR inverse branch, or
through a producer certificate that identifies the sampled inverse-carrier
scale with a Hamiltonian scale.

Boundary: this is still carrier algebra.  It does not identify physical
energy, mass, or consciousness without a separate producer/interpretation
certificate.
-/

noncomputable section

open Filter
open scoped BigOperators

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Forward positive saturation is finite, not divergent -/

/-- THEOREM 1: positive non-absorbing forward saturation has infinite-series
total exactly equal to one unit of headroom. -/
theorem forward_saturation_tsum_eq_one
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    (∑' n : ℕ, saturationIncrement sigma n) = 1 :=
  tsum_saturationIncrement_eq_one hpos hlt

/-- THEOREM 2: positive non-absorbing forward cumulative saturation does not
tend to infinity.  Its limit is the finite value `1`. -/
theorem not_tendsto_forward_cumulativeSaturationIncrement_atTop
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    ¬ Tendsto (fun N : ℕ => cumulativeSaturationIncrement sigma N)
        atTop atTop := by
  intro htop
  have hlim := tendsto_cumulativeSaturationIncrement_one hpos hlt
  have hsmall :
      ∀ᶠ N in atTop, cumulativeSaturationIncrement sigma N < 2 := by
    exact hlim.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have hbig :
      ∀ᶠ N in atTop, 2 ≤ cumulativeSaturationIncrement sigma N := by
    exact (Filter.tendsto_atTop.mp htop) 2
  have hfalse : ∀ᶠ _N in atTop, False :=
    (hsmall.and hbig).mono (by
      intro N h
      exact (not_lt_of_ge h.2) h.1)
  exact hfalse.exists.elim (by
    intro _ h
    exact h)

/-! ## Inverse branch is the divergent coordinate -/

/-- THEOREM 3: the noisy-OR inverse branch has divergent keep powers. -/
theorem inverse_branch_keep_pow_tendsto_atTop
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    Tendsto
      (fun N : ℕ =>
        (SatOrFieldAlgebra.keep
          (SatOrFieldAlgebra.satOrFieldInv sigma)) ^ N)
      atTop atTop :=
  tendsto_inverse_keep_pow_atTop hpos hlt

/-- THEOREM 4: complement-then-inverse has exact reciprocal keep coordinate. -/
theorem complement_inverse_keep_eq_inv
    {sigma : ℝ} (hσ : sigma ≠ 0) :
    SatOrFieldAlgebra.keep
        (SatOrFieldAlgebra.satOrFieldInv (complement sigma)) =
      sigma⁻¹ :=
  keep_satOrFieldInv_complement_eq_inv hσ

/-- THEOREM 5: the sampled inverse carrier scale has its exact exponential
growth closed form. -/
theorem sampled_inverse_carrier_scale_closed_form
    (lambda step : ℝ) (N : ℕ) :
    sampledInverseCarrierScale lambda step N =
      (realDecayResidual lambda ((N : ℝ) * step))⁻¹ :=
  sampledInverseCarrierScale_eq_exp_growth lambda step N

/-- THEOREM 6: positive sampled scale makes the sampled inverse carrier scale
diverge. -/
theorem sampled_inverse_carrier_scale_tendsto_atTop
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    Tendsto (sampledInverseCarrierScale lambda step) atTop atTop :=
  tendsto_sampledInverseCarrierScale_atTop hpos

/-! ## Producer gate for Hamiltonian readings -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- THEOREM 7: a Stone-side Hamiltonian reading of sampled inverse growth is
available only through the explicit producer certificate from P489. -/
theorem sampled_inverse_stone_hamiltonian_reading_from_producer
    {lambda step : ℝ}
    (C : SampledInverseStoneUnboundedHamiltonianProducer E lambda step) :
    CarrierProducedStoneUnboundedHamiltonianReceipt E lambda step C :=
  carrierProducedStoneUnboundedHamiltonianReceipt C

/-! ## Bundled boundary receipt -/

/-- A compact guardrail receipt:

* forward positive saturation sums to one and does not diverge;
* inverse coordinates do diverge;
* sampled inverse carrier scale has the exponential closed form;
* Hamiltonian readings must pass through the producer gate.
-/
structure SaturationCarrierEnergyBoundaryReceipt : Prop where
  forward_total_one :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      (∑' n : ℕ, saturationIncrement sigma n) = 1
  forward_not_atTop :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      ¬ Tendsto (fun N : ℕ => cumulativeSaturationIncrement sigma N)
        atTop atTop
  inverse_keep_diverges :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      Tendsto
        (fun N : ℕ =>
          (SatOrFieldAlgebra.keep
            (SatOrFieldAlgebra.satOrFieldInv sigma)) ^ N)
        atTop atTop
  complement_inverse_keep :
    ∀ sigma : ℝ, sigma ≠ 0 ->
      SatOrFieldAlgebra.keep
          (SatOrFieldAlgebra.satOrFieldInv (complement sigma)) =
        sigma⁻¹
  sampled_inverse_closed_form :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      sampledInverseCarrierScale lambda step N =
        (realDecayResidual lambda ((N : ℝ) * step))⁻¹
  sampled_inverse_diverges :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      Tendsto (sampledInverseCarrierScale lambda step) atTop atTop

/-- THEOREM 8: the saturation carrier energy-accounting boundary receipt. -/
theorem saturationCarrierEnergyBoundaryReceipt :
    SaturationCarrierEnergyBoundaryReceipt where
  forward_total_one := fun _ hpos hlt =>
    forward_saturation_tsum_eq_one hpos hlt
  forward_not_atTop := fun _ hpos hlt =>
    not_tendsto_forward_cumulativeSaturationIncrement_atTop hpos hlt
  inverse_keep_diverges := fun _ hpos hlt =>
    inverse_branch_keep_pow_tendsto_atTop hpos hlt
  complement_inverse_keep := fun _ hσ =>
    complement_inverse_keep_eq_inv hσ
  sampled_inverse_closed_form := fun _ _ N =>
    sampled_inverse_carrier_scale_closed_form _ _ N
  sampled_inverse_diverges := fun _ _ hpos =>
    sampled_inverse_carrier_scale_tendsto_atTop hpos

end AffineRelaxation
end SaturationMonoid
