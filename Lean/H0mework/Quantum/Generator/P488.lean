import H0mework.Quantum.Generator.P487

/-!
# Proposition 488: operator-norm growth for carrier-produced Hamiltonians

P487 proves that a sampled inverse-carrier coefficient can faithfully produce
a bounded self-adjoint Hamiltonian sequence

`H_N = (scale N : ℂ) • H₀`.

This file adds the operator-norm consequence.  If the supplied base Hamiltonian
is nonzero, then the scalar coefficient's divergence transfers to the bounded
operator norm:

`‖H_N‖ -> ∞`.

Boundary: this is still a bounded-operator theorem relative to a supplied
nonzero base Hamiltonian.  It does not construct the base Hamiltonian and does
not identify an empirical energy scale without the producer certificate.
-/

noncomputable section

open Filter

namespace SaturationMonoid
namespace AffineRelaxation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Positivity and norm closed form -/

/-- THEOREM 1: every sampled inverse-carrier scale in a bounded Hamiltonian
producer is positive. -/
theorem SampledInverseBoundedHamiltonianProducer.scale_pos
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    0 < C.scale N := by
  rw [C.scale_eq_exp_growth N]
  exact inv_pos.mpr (Real.exp_pos _)

/-- THEOREM 2: the produced Hamiltonian norm is exactly the carrier scale
times the base Hamiltonian norm. -/
theorem SampledInverseBoundedHamiltonianProducer.hamiltonian_norm_eq_scale_mul_base_norm
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    ‖C.hamiltonian N‖ = C.scale N * ‖C.baseHamiltonian‖ := by
  rw [C.hamiltonian_scale N, norm_smul]
  simp [abs_of_pos (C.scale_pos N)]

/-- THEOREM 3: equivalently, the produced Hamiltonian norm has the reciprocal
continuous-residual closed form. -/
theorem SampledInverseBoundedHamiltonianProducer.hamiltonian_norm_eq_exp_growth
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (N : ℕ) :
    ‖C.hamiltonian N‖ =
      (realDecayResidual lambda ((N : ℝ) * step))⁻¹ *
        ‖C.baseHamiltonian‖ := by
  rw [C.hamiltonian_norm_eq_scale_mul_base_norm N, C.scale_eq_exp_growth N]

/-! ## Norm divergence -/

/-- THEOREM 4: if the base Hamiltonian is nonzero, positive sampled inverse
scale makes the produced bounded-operator norms diverge. -/
theorem SampledInverseBoundedHamiltonianProducer.hamiltonian_norm_tendsto_atTop
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (hbase : C.baseHamiltonian ≠ 0)
    (hpos : 0 < lambda * step) :
    Tendsto (fun N : ℕ => ‖C.hamiltonian N‖) atTop atTop := by
  have hnorm_pos : 0 < ‖C.baseHamiltonian‖ := norm_pos_iff.mpr hbase
  have hscale : Tendsto C.scale atTop atTop :=
    C.scale_tendsto_atTop hpos
  have hprod :
      Tendsto (fun N : ℕ => C.scale N * ‖C.baseHamiltonian‖)
        atTop atTop :=
    Filter.Tendsto.atTop_mul_const hnorm_pos hscale
  convert hprod using 1
  ext N
  exact C.hamiltonian_norm_eq_scale_mul_base_norm N

/-! ## Bundled receipt -/

/-- A compact norm-growth receipt for nonzero carrier-produced bounded
Hamiltonians. -/
structure CarrierProducedBoundedHamiltonianNormGrowthReceipt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (lambda step : ℝ)
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (hbase : C.baseHamiltonian ≠ 0) : Prop where
  scale_positive :
    ∀ N : ℕ, 0 < C.scale N
  norm_closed_form :
    ∀ N : ℕ,
      ‖C.hamiltonian N‖ =
        (realDecayResidual lambda ((N : ℝ) * step))⁻¹ *
          ‖C.baseHamiltonian‖
  coefficient_diverges :
    0 < lambda * step -> Tendsto C.scale atTop atTop
  operator_norm_diverges :
    0 < lambda * step ->
      Tendsto (fun N : ℕ => ‖C.hamiltonian N‖) atTop atTop

/-- THEOREM 5: a nonzero faithful sampled inverse bounded-Hamiltonian
producer supplies the operator-norm growth receipt. -/
theorem carrierProducedBoundedHamiltonianNormGrowthReceipt
    {lambda step : ℝ}
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (hbase : C.baseHamiltonian ≠ 0) :
    CarrierProducedBoundedHamiltonianNormGrowthReceipt E lambda step C hbase where
  scale_positive := C.scale_pos
  norm_closed_form := C.hamiltonian_norm_eq_exp_growth
  coefficient_diverges := fun hpos => C.scale_tendsto_atTop hpos
  operator_norm_diverges := fun hpos =>
    C.hamiltonian_norm_tendsto_atTop hbase hpos

end AffineRelaxation
end SaturationMonoid
