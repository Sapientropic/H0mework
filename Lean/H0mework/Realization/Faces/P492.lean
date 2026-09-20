import H0mework.Realization.RelaxationFlow.P476
import H0mework.Realization.RelaxationAlgebra.P491

/-!
# Proposition 492: unified projection discipline receipt

P491 separated the forward cumulative carrier projection from inverse and
Hamiltonian-scale projections.  Its bounded-Hamiltonian norm theorem used the
nonzero-base case because the proof used divergence of the produced norm.

This file removes that auxiliary hypothesis.  If the bounded base Hamiltonian
is zero, the produced operator norm is identically zero, while the forward
cumulative saturation has already become positive after one step.  If the base
is nonzero, P491's divergence proof applies.  Thus the forward cumulative
projection is never the bounded Hamiltonian norm of a sampled inverse producer.

The file also bundles the current unified-formula discipline into one receipt:

* running sigma has coordinate-linearized readings;
* forward saturation has finite accounting;
* inverse readings blow up only on the inverse branch;
* Hamiltonian readings pass through producer certificates;
* forward and inverse/Hamiltonian projections are provably distinct.
-/

noncomputable section

namespace SaturationMonoid

universe u v

namespace AffineRelaxation

open Filter

/-! ## Removing the nonzero-base side condition -/

/-- THEOREM 1: the first forward cumulative increment is exactly the rate. -/
theorem cumulativeSaturationIncrement_one_eq (sigma : ℝ) :
    cumulativeSaturationIncrement sigma 1 = sigma := by
  simp [cumulativeSaturationIncrement, saturationIncrement]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

/-- THEOREM 2: if the bounded base Hamiltonian is zero, the produced
Hamiltonian norm cannot equal the forward cumulative saturation projection.
The contradiction already appears at step `1`. -/
theorem forward_cumulative_ne_bounded_hamiltonian_norm_zero_base
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (hbase : C.baseHamiltonian = 0) :
    ¬ (∀ N : ℕ,
      cumulativeSaturationIncrement (realDecayRate lambda step) N =
        ‖C.hamiltonian N‖) := by
  intro h
  have hleft :
      cumulativeSaturationIncrement (realDecayRate lambda step) 1 =
        realDecayRate lambda step :=
    cumulativeSaturationIncrement_one_eq (realDecayRate lambda step)
  have hH : C.hamiltonian 1 = 0 := by
    rw [C.hamiltonian_scale 1, hbase]
    simp
  have hnorm : ‖C.hamiltonian 1‖ = 0 := by
    rw [hH]
    simp
  have heq := h 1
  rw [hleft, hnorm] at heq
  exact (ne_of_gt (realDecayRate_pos_of_mul_pos hpos)) heq

/-- THEOREM 3: for any carrier-produced bounded Hamiltonian, zero or nonzero
base, its operator norm cannot be identified with the forward cumulative
saturation projection. -/
theorem forward_cumulative_ne_bounded_hamiltonian_norm_any_base
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    (C : SampledInverseBoundedHamiltonianProducer E lambda step) :
    ¬ (∀ N : ℕ,
      cumulativeSaturationIncrement (realDecayRate lambda step) N =
        ‖C.hamiltonian N‖) := by
  by_cases hbase : C.baseHamiltonian = 0
  · exact
      forward_cumulative_ne_bounded_hamiltonian_norm_zero_base
        hpos C hbase
  · exact forward_cumulative_ne_bounded_hamiltonian_norm hpos C hbase

/-! ## Strengthened producer separation receipt -/

/-- Producer-level separation with no nonzero-base side condition. -/
structure StrictForwardInverseProducerProjectionSeparationReceipt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  stone_scale :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      ∀ C : SampledInverseStoneUnboundedHamiltonianProducer E lambda step,
        ¬ (∀ N : ℕ,
          cumulativeSaturationIncrement (realDecayRate lambda step) N =
            C.scale N)
  bounded_norm_any_base :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      ∀ C : SampledInverseBoundedHamiltonianProducer E lambda step,
        ¬ (∀ N : ℕ,
          cumulativeSaturationIncrement (realDecayRate lambda step) N =
            ‖C.hamiltonian N‖)

/-- THEOREM 4: strengthened producer-level separation receipt. -/
theorem strictForwardInverseProducerProjectionSeparationReceipt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    StrictForwardInverseProducerProjectionSeparationReceipt E where
  stone_scale := fun _ _ hpos C =>
    forward_cumulative_ne_stone_producer_scale hpos C
  bounded_norm_any_base := fun _ _ hpos C =>
    forward_cumulative_ne_bounded_hamiltonian_norm_any_base hpos C

end AffineRelaxation

/-! ## Unified projection discipline -/

/-- A top-level receipt for the current unified-formula discipline.

It deliberately bundles both positive results and guardrails.  The unified
relaxation carrier supports several certified coordinate readings, but the
receipt also includes the separation theorems saying that forward accounting
is not the inverse/Hamiltonian blow-up projection.
-/
structure UnifiedFormulaProjectionDisciplineReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  coordinate_linearized :
    CoordinateLinearizedRunningSigmaReceipt.{u}
  carrier_boundary :
    AffineRelaxation.SaturationCarrierEnergyBoundaryReceipt
  scalar_projection_separation :
    AffineRelaxation.ForwardInverseScalarProjectionSeparationReceipt
  producer_projection_separation :
    AffineRelaxation.StrictForwardInverseProducerProjectionSeparationReceipt E
  stone_hamiltonian_gate :
    ∀ lambda step : ℝ,
      ∀ C : AffineRelaxation.SampledInverseStoneUnboundedHamiltonianProducer
          E lambda step,
        AffineRelaxation.CarrierProducedStoneUnboundedHamiltonianReceipt
          E lambda step C
  bounded_hamiltonian_gate :
    ∀ lambda step : ℝ,
      ∀ C : AffineRelaxation.SampledInverseBoundedHamiltonianProducer
          E lambda step,
        AffineRelaxation.CarrierProducedBoundedHamiltonianReceipt
          E lambda step C
  bounded_norm_growth_gate :
    ∀ lambda step : ℝ,
      ∀ C : AffineRelaxation.SampledInverseBoundedHamiltonianProducer
          E lambda step,
        ∀ hbase : C.baseHamiltonian ≠ 0,
          AffineRelaxation.CarrierProducedBoundedHamiltonianNormGrowthReceipt
            E lambda step C hbase

/-- THEOREM 5: the unified projection-discipline receipt. -/
theorem unifiedFormulaProjectionDisciplineReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    UnifiedFormulaProjectionDisciplineReceipt.{u, v} E where
  coordinate_linearized :=
    coordinateLinearizedRunningSigmaReceipt.{u}
  carrier_boundary :=
    AffineRelaxation.saturationCarrierEnergyBoundaryReceipt
  scalar_projection_separation :=
    AffineRelaxation.forwardInverseScalarProjectionSeparationReceipt
  producer_projection_separation :=
    AffineRelaxation.strictForwardInverseProducerProjectionSeparationReceipt E
  stone_hamiltonian_gate := fun _ _ C =>
    AffineRelaxation.carrierProducedStoneUnboundedHamiltonianReceipt C
  bounded_hamiltonian_gate := fun _ _ C =>
    AffineRelaxation.carrierProducedBoundedHamiltonianReceipt C
  bounded_norm_growth_gate := fun _ _ C hbase =>
    AffineRelaxation.carrierProducedBoundedHamiltonianNormGrowthReceipt
      C hbase

end SaturationMonoid
