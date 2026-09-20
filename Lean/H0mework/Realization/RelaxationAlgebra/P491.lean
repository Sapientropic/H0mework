import H0mework.Realization.RelaxationAlgebra.P490

/-!
# Proposition 491: forward/inverse projection separation

P490 records the accounting boundary:

* forward positive saturation has finite total accounting and does not tend to
  infinity;
* inverse carrier coordinates do tend to infinity;
* Hamiltonian readings of inverse growth require explicit producer
  certificates.

This file turns that boundary into a separation theorem.  The forward
cumulative saturation projection cannot be identified with the inverse
blow-up projection, nor with a sampled inverse Hamiltonian scale, nor with the
norm of a nonzero carrier-produced bounded Hamiltonian.

This is the formal guardrail behind the prose discipline: several readings may
share the same saturation carrier, but they are not interchangeable without an
explicit bridge, and in the forward-vs-inverse case Lean proves they are
actually distinct.
-/

noncomputable section

open Filter

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Scalar carrier separation -/

/-- THEOREM 1: forward cumulative saturation cannot be the same sequence as
inverse-branch keep powers.  The former does not tend to infinity; the latter
does. -/
theorem forward_cumulative_ne_inverse_keep_pow
    {sigma : ℝ} (hpos : 0 < sigma) (hlt : sigma < 1) :
    ¬ (∀ N : ℕ,
      cumulativeSaturationIncrement sigma N =
        (SatOrFieldAlgebra.keep
          (SatOrFieldAlgebra.satOrFieldInv sigma)) ^ N) := by
  intro h
  have hnot :=
    not_tendsto_forward_cumulativeSaturationIncrement_atTop hpos hlt
  have hinv := inverse_branch_keep_pow_tendsto_atTop hpos hlt
  have hforward :
      Tendsto (fun N : ℕ => cumulativeSaturationIncrement sigma N)
        atTop atTop := by
    convert hinv using 1
    ext N
    exact h N
  exact hnot hforward

/-- THEOREM 2: with the sampled continuous-rate choice
`sigma = realDecayRate lambda step`, the forward cumulative projection cannot
be the sampled inverse carrier scale. -/
theorem forward_cumulative_realDecayRate_ne_sampledInverseCarrierScale
    {lambda step : ℝ} (hpos : 0 < lambda * step) :
    ¬ (∀ N : ℕ,
      cumulativeSaturationIncrement (realDecayRate lambda step) N =
        sampledInverseCarrierScale lambda step N) := by
  intro h
  have hrpos : 0 < realDecayRate lambda step :=
    realDecayRate_pos_of_mul_pos hpos
  have hrlt : realDecayRate lambda step < 1 :=
    realDecayRate_lt_one lambda step
  have hnot :=
    not_tendsto_forward_cumulativeSaturationIncrement_atTop hrpos hrlt
  have hinv := sampled_inverse_carrier_scale_tendsto_atTop hpos
  have hforward :
      Tendsto
        (fun N : ℕ =>
          cumulativeSaturationIncrement (realDecayRate lambda step) N)
        atTop atTop := by
    convert hinv using 1
    ext N
    exact h N
  exact hnot hforward

/-! ## Producer-level separation -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- THEOREM 3: a carrier-produced Stone-side Hamiltonian scale is the inverse
projection, not the forward cumulative projection. -/
theorem forward_cumulative_ne_stone_producer_scale
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    (C : SampledInverseStoneUnboundedHamiltonianProducer E lambda step) :
    ¬ (∀ N : ℕ,
      cumulativeSaturationIncrement (realDecayRate lambda step) N =
        C.scale N) := by
  intro h
  have hrpos : 0 < realDecayRate lambda step :=
    realDecayRate_pos_of_mul_pos hpos
  have hrlt : realDecayRate lambda step < 1 :=
    realDecayRate_lt_one lambda step
  have hnot :=
    not_tendsto_forward_cumulativeSaturationIncrement_atTop hrpos hrlt
  have hscale := C.scale_tendsto_atTop hpos
  have hforward :
      Tendsto
        (fun N : ℕ =>
          cumulativeSaturationIncrement (realDecayRate lambda step) N)
        atTop atTop := by
    convert hscale using 1
    ext N
    exact h N
  exact hnot hforward

variable [CompleteSpace E]

/-- THEOREM 4: if the supplied bounded base Hamiltonian is nonzero, the
operator norm of a carrier-produced bounded Hamiltonian also cannot be the
forward cumulative saturation projection. -/
theorem forward_cumulative_ne_bounded_hamiltonian_norm
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    (C : SampledInverseBoundedHamiltonianProducer E lambda step)
    (hbase : C.baseHamiltonian ≠ 0) :
    ¬ (∀ N : ℕ,
      cumulativeSaturationIncrement (realDecayRate lambda step) N =
        ‖C.hamiltonian N‖) := by
  intro h
  have hrpos : 0 < realDecayRate lambda step :=
    realDecayRate_pos_of_mul_pos hpos
  have hrlt : realDecayRate lambda step < 1 :=
    realDecayRate_lt_one lambda step
  have hnot :=
    not_tendsto_forward_cumulativeSaturationIncrement_atTop hrpos hrlt
  have hnorm := C.hamiltonian_norm_tendsto_atTop hbase hpos
  have hforward :
      Tendsto
        (fun N : ℕ =>
          cumulativeSaturationIncrement (realDecayRate lambda step) N)
        atTop atTop := by
    convert hnorm using 1
    ext N
    exact h N
  exact hnot hforward

/-! ## Bundled receipts -/

/-- Scalar separation receipt for the two carrier projections. -/
structure ForwardInverseScalarProjectionSeparationReceipt : Prop where
  inverse_keep_pow :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      ¬ (∀ N : ℕ,
        cumulativeSaturationIncrement sigma N =
          (SatOrFieldAlgebra.keep
            (SatOrFieldAlgebra.satOrFieldInv sigma)) ^ N)
  sampled_inverse :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      ¬ (∀ N : ℕ,
        cumulativeSaturationIncrement (realDecayRate lambda step) N =
          sampledInverseCarrierScale lambda step N)

/-- THEOREM 5: scalar forward/inverse projection separation receipt. -/
theorem forwardInverseScalarProjectionSeparationReceipt :
    ForwardInverseScalarProjectionSeparationReceipt where
  inverse_keep_pow := fun _ hpos hlt =>
    forward_cumulative_ne_inverse_keep_pow hpos hlt
  sampled_inverse := fun _ _ hpos =>
    forward_cumulative_realDecayRate_ne_sampledInverseCarrierScale hpos

/-- Producer-level separation receipt. -/
structure ForwardInverseProducerProjectionSeparationReceipt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  stone_scale :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      ∀ C : SampledInverseStoneUnboundedHamiltonianProducer E lambda step,
        ¬ (∀ N : ℕ,
          cumulativeSaturationIncrement (realDecayRate lambda step) N =
            C.scale N)
  bounded_norm :
    ∀ lambda step : ℝ, 0 < lambda * step ->
      ∀ C : SampledInverseBoundedHamiltonianProducer E lambda step,
        C.baseHamiltonian ≠ 0 ->
          ¬ (∀ N : ℕ,
            cumulativeSaturationIncrement (realDecayRate lambda step) N =
              ‖C.hamiltonian N‖)

/-- THEOREM 6: producer-level forward/inverse projection separation receipt. -/
theorem forwardInverseProducerProjectionSeparationReceipt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    ForwardInverseProducerProjectionSeparationReceipt E where
  stone_scale := fun _ _ hpos C =>
    forward_cumulative_ne_stone_producer_scale hpos C
  bounded_norm := fun _ _ hpos C hbase =>
    forward_cumulative_ne_bounded_hamiltonian_norm hpos C hbase

end AffineRelaxation
end SaturationMonoid
