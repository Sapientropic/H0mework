import H0mework.Realization.RelaxationAlgebra.P493
import H0mework.Quantum.Generator.P497

/-!
# Proposition 498: projection guardrail for energy-language readings

The prose sometimes compresses the unified carrier into vivid slogans:
"matter", "energy", "consciousness", and "vacuum fluctuation" may be discussed
as different faces of one saturation carrier.

This file records the formal boundary that must travel with that language.

* Positive forward saturation has finite accounting: its total is one unit of
  headroom and its cumulative projection does not diverge.
* Divergence belongs to the one-sided inverse branch.
* Reading that inverse branch as an H¹ residual or as a bounded Hamiltonian norm
  requires explicit producer certificates.
* Finite forward/inverse oscillation is net-zero and remains separate from
  one-sided inverse growth.

So the Lean theorem is not an unconditional identity
`energy = consciousness`.  It is a guarded projection theorem: when the H¹
residual producer and Hamiltonian producer are supplied by the same sampled
inverse carrier, their scalar/norm readings agree as proved in P497, while the
positive forward accounting face remains finite as proved in P490-P493.
-/

noncomputable section

open Filter
open scoped BigOperators

namespace SaturationMonoid

universe u v

namespace AffineRelaxation

/-! ## Forward finite accounting versus inverse producer readings -/

/-- THEOREM 1: forward positive saturation is finite accounting, not an
infinite-energy projection. -/
theorem positive_forward_saturation_finite_not_infinite
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    (∑' n : ℕ, saturationIncrement sigma n) = 1 ∧
      ¬ Tendsto (fun N : ℕ => cumulativeSaturationIncrement sigma N)
        atTop atTop := by
  exact ⟨forward_saturation_tsum_eq_one hpos hlt,
    not_tendsto_forward_cumulativeSaturationIncrement_atTop hpos hlt⟩

/-- THEOREM 2: the inverse H¹ residual family is the divergent projection,
provided the H¹ family producer is supplied. -/
theorem inverse_h1_residual_family_is_divergent_projection
    {lambda step : ℝ}
    (R : SampledInverseH1ResidualFamilyProducer lambda step)
    (hpos : 0 < lambda * step) :
    Tendsto (fun N : ℕ => _root_.threeAgentRingResidual (R.phase N))
      atTop atTop :=
  R.residual_tendsto_atTop hpos

/-- THEOREM 3: under the bounded-Hamiltonian producer certificate, H¹ residual
and bounded Hamiltonian norm are the same carrier-produced scale up to the
supplied base-Hamiltonian norm. -/
theorem inverse_h1_residual_boundedHamiltonian_norm_projection
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {lambda step : ℝ}
    (H : SampledInverseBoundedHamiltonianProducer E lambda step)
    (R : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    ‖H.hamiltonian N‖ =
      _root_.threeAgentRingResidual (R.phase N) * ‖H.baseHamiltonian‖ :=
  sampledInverseBoundedHamiltonian_norm_eq_h1Residual_mul_base_norm H R N

/-! ## Bundled guardrail -/

/-- Compact receipt for energy-language projection discipline.

The receipt intentionally contains both the positive bridge and the guardrails:
the inverse branch may be read as H¹/Hamiltonian scale only through producer
certificates, while the forward positive branch remains finite and finite
oscillation remains net-zero. -/
structure EnergyLanguageProjectionGuardrailReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  forward_finite_not_infinite :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      (∑' n : ℕ, saturationIncrement sigma n) = 1 ∧
        ¬ Tendsto (fun N : ℕ => cumulativeSaturationIncrement sigma N)
          atTop atTop
  inverse_h1_diverges :
    ∀ lambda step : ℝ,
      ∀ R : SampledInverseH1ResidualFamilyProducer lambda step,
        0 < lambda * step ->
          Tendsto (fun N : ℕ => _root_.threeAgentRingResidual (R.phase N))
            atTop atTop
  h1_boundedHamiltonian_norm_bridge :
    CarrierProducedH1BoundedHamiltonianNormBridgeReceipt E
  carrier_projection_guardrail :
    UnifiedFormulaCarrierGuardrailReceipt.{u, v} E

/-- THEOREM 4: the energy-language projection guardrail receipt. -/
theorem energyLanguageProjectionGuardrailReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    EnergyLanguageProjectionGuardrailReceipt.{u, v} E where
  forward_finite_not_infinite := fun _ hpos hlt =>
    positive_forward_saturation_finite_not_infinite hpos hlt
  inverse_h1_diverges := fun _ _ R hpos =>
    inverse_h1_residual_family_is_divergent_projection R hpos
  h1_boundedHamiltonian_norm_bridge :=
    carrierProducedH1BoundedHamiltonianNormBridgeReceipt E
  carrier_projection_guardrail :=
    unifiedFormulaCarrierGuardrailReceipt (E := E)

end AffineRelaxation
end SaturationMonoid
