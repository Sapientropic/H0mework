import H0mework.Quantum.Generator.P488
import H0mework.Realization.Residual.P496

/-!
# Proposition 497: H¹ residual flow as bounded-Hamiltonian norm scale

P496 proves that a time-indexed H¹ residual family and a Hamiltonian-scale
producer agree when both are faithfully produced by the same sampled inverse
carrier.  P488 proves that a bounded Hamiltonian producer has operator norm

`‖H_N‖ = scale_N * ‖H₀‖`.

This file composes those two facts.  Under the two producer certificates, the
H¹ residual is the exact scalar coefficient of the bounded Hamiltonian, and
the operator norm is the H¹ residual times the supplied base Hamiltonian norm.
If the sampled scale is positive and the base Hamiltonian is nonzero, the
operator norm diverges.

Boundary: this is still a certified producer theorem.  It does not construct
the base Hamiltonian or assert that an arbitrary H¹ residual is physical
energy.  It says exactly when the two readings are the same carrier-produced
scale.
-/

noncomputable section

open Filter

namespace SaturationMonoid
namespace AffineRelaxation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-! ## Scalar equality between bounded Hamiltonian and H¹ residual flow -/

/-- THEOREM 1: a bounded-Hamiltonian producer and an H¹ residual family
producer using the same carrier have the same scalar coefficient at every
sampled step. -/
theorem sampledInverseBoundedHamiltonianScale_eq_h1ResidualFamily
    {lambda step : ℝ}
    (H : SampledInverseBoundedHamiltonianProducer E lambda step)
    (R : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    H.scale N = _root_.threeAgentRingResidual (R.phase N) :=
  sampledInverseHamiltonianScale_eq_h1ResidualFamily
    H.toScalarScaleProducer R N

/-- THEOREM 2: the operator norm of a carrier-produced bounded Hamiltonian is
the carrier-produced H¹ residual times the supplied base-Hamiltonian norm. -/
theorem sampledInverseBoundedHamiltonian_norm_eq_h1Residual_mul_base_norm
    {lambda step : ℝ}
    (H : SampledInverseBoundedHamiltonianProducer E lambda step)
    (R : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    ‖H.hamiltonian N‖ =
      _root_.threeAgentRingResidual (R.phase N) * ‖H.baseHamiltonian‖ := by
  rw [H.hamiltonian_norm_eq_scale_mul_base_norm N]
  rw [sampledInverseBoundedHamiltonianScale_eq_h1ResidualFamily H R N]

/-- THEOREM 3: equivalently, the operator norm has the reciprocal
zero-target-keep closed form after substituting the H¹ residual family. -/
theorem sampledInverseBoundedHamiltonian_norm_eq_h1Residual_exp_growth
    {lambda step : ℝ}
    (H : SampledInverseBoundedHamiltonianProducer E lambda step)
    (R : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    ‖H.hamiltonian N‖ =
      (realDecayResidual lambda ((N : ℝ) * step))⁻¹ *
        ‖H.baseHamiltonian‖ := by
  rw [sampledInverseBoundedHamiltonian_norm_eq_h1Residual_mul_base_norm H R N]
  rw [R.residual_eq_exp_growth N]

/-! ## Divergence transport -/

/-- THEOREM 4: if the sampled scale is positive, the H¹ residual family itself
diverges.  This re-exposes the P496 result at the bounded-Hamiltonian bridge
layer. -/
theorem h1ResidualFamily_tendsto_atTop_of_boundedBridge
    {lambda step : ℝ}
    (R : SampledInverseH1ResidualFamilyProducer lambda step)
    (hpos : 0 < lambda * step) :
    Tendsto (fun N : ℕ => _root_.threeAgentRingResidual (R.phase N))
      atTop atTop :=
  R.residual_tendsto_atTop hpos

/-- THEOREM 5: if the sampled scale is positive and the supplied base
Hamiltonian is nonzero, the produced operator norm diverges. -/
theorem sampledInverseBoundedHamiltonian_norm_tendsto_atTop_of_h1ResidualFamily
    {lambda step : ℝ}
    (H : SampledInverseBoundedHamiltonianProducer E lambda step)
    (_R : SampledInverseH1ResidualFamilyProducer lambda step)
    (hbase : H.baseHamiltonian ≠ 0)
    (hpos : 0 < lambda * step) :
    Tendsto (fun N : ℕ => ‖H.hamiltonian N‖) atTop atTop :=
  H.hamiltonian_norm_tendsto_atTop hbase hpos

/-! ## Receipt -/

/-- Compact receipt for the bounded-Hamiltonian / H¹ residual-flow bridge. -/
structure CarrierProducedH1BoundedHamiltonianNormBridgeReceipt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  scale_eq_residual :
    ∀ lambda step : ℝ,
      ∀ H : SampledInverseBoundedHamiltonianProducer E lambda step,
      ∀ R : SampledInverseH1ResidualFamilyProducer lambda step,
      ∀ N : ℕ,
        H.scale N = _root_.threeAgentRingResidual (R.phase N)
  norm_eq_residual_mul_base_norm :
    ∀ lambda step : ℝ,
      ∀ H : SampledInverseBoundedHamiltonianProducer E lambda step,
      ∀ R : SampledInverseH1ResidualFamilyProducer lambda step,
      ∀ N : ℕ,
        ‖H.hamiltonian N‖ =
          _root_.threeAgentRingResidual (R.phase N) *
            ‖H.baseHamiltonian‖
  norm_eq_exp_growth :
    ∀ lambda step : ℝ,
      ∀ H : SampledInverseBoundedHamiltonianProducer E lambda step,
      ∀ _R : SampledInverseH1ResidualFamilyProducer lambda step,
      ∀ N : ℕ,
        ‖H.hamiltonian N‖ =
          (realDecayResidual lambda ((N : ℝ) * step))⁻¹ *
            ‖H.baseHamiltonian‖
  residual_diverges :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      ∀ R : SampledInverseH1ResidualFamilyProducer lambda step,
        Tendsto (fun N : ℕ => _root_.threeAgentRingResidual (R.phase N))
          atTop atTop
  operator_norm_diverges :
    ∀ lambda step : ℝ,
      ∀ H : SampledInverseBoundedHamiltonianProducer E lambda step,
      ∀ _R : SampledInverseH1ResidualFamilyProducer lambda step,
        H.baseHamiltonian ≠ 0 ->
        0 < lambda * step ->
          Tendsto (fun N : ℕ => ‖H.hamiltonian N‖) atTop atTop

/-- THEOREM 6: the bounded-Hamiltonian / H¹ residual-flow bridge receipt. -/
theorem carrierProducedH1BoundedHamiltonianNormBridgeReceipt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    CarrierProducedH1BoundedHamiltonianNormBridgeReceipt E where
  scale_eq_residual := fun _ _ H R N =>
    sampledInverseBoundedHamiltonianScale_eq_h1ResidualFamily H R N
  norm_eq_residual_mul_base_norm := fun _ _ H R N =>
    sampledInverseBoundedHamiltonian_norm_eq_h1Residual_mul_base_norm H R N
  norm_eq_exp_growth := fun _ _ H R N =>
    sampledInverseBoundedHamiltonian_norm_eq_h1Residual_exp_growth H R N
  residual_diverges := fun _ _ hpos R =>
    h1ResidualFamily_tendsto_atTop_of_boundedBridge R hpos
  operator_norm_diverges := fun _ _ H _R hbase hpos =>
    sampledInverseBoundedHamiltonian_norm_tendsto_atTop_of_h1ResidualFamily
      H _R hbase hpos

end AffineRelaxation
end SaturationMonoid
