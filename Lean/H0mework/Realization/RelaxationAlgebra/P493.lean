import H0mework.Realization.Faces.P492

/-!
# Proposition 493: oscillation is not inverse-branch blow-up

P484 proves that finite sampled forward/inverse oscillations are exactly net
zero on the scalar carrier.  P490-P492 prove that the one-sided inverse branch
is the divergent projection, and that Hamiltonian readings of that projection
must pass through producer certificates.

This file closes a common projection slip: a finite forward/inverse oscillation
is not the same object as one-sided inverse growth.  Starting from `0`, every
finite alternating pair still has headroom `1`; under positive sampled scale,
the one-sided inverse branch has headroom strictly larger than `1` after every
positive number of steps.

Boundary: this is scalar carrier algebra plus the existing producer discipline.
It does not identify oscillation, vacuum, energy, matter, or consciousness
without a separate interpretation/producer certificate.
-/

noncomputable section

namespace SaturationMonoid

universe u v

namespace AffineRelaxation

/-! ## Sampled oscillation operators -/

/-- A sampled forward-then-inverse adjacent pair. -/
def sampledRateInversePair (lambda step : ℝ) : ℝ → ℝ :=
  fun h : ℝ =>
    bumpSatField
      (bumpSatField h (realDecayRate lambda step))
      (SatOrFieldAlgebra.satOrFieldInv (realDecayRate lambda step))

/-- A sampled inverse-then-forward adjacent pair. -/
def sampledInverseRatePair (lambda step : ℝ) : ℝ → ℝ :=
  fun h : ℝ =>
    bumpSatField
      (bumpSatField h
        (SatOrFieldAlgebra.satOrFieldInv (realDecayRate lambda step)))
      (realDecayRate lambda step)

/-- THEOREM 1: every finite sampled forward/inverse oscillation fixes the
zero state. -/
theorem sampledRateInversePair_iterate_zero_state
    (lambda step : ℝ) (N : ℕ) :
    (sampledRateInversePair lambda step)^[N] 0 = 0 := by
  unfold sampledRateInversePair
  exact bumpSatField_iterate_sampled_rate_inv_pair_cancel 0 lambda step N

/-- THEOREM 2: every finite sampled inverse/forward oscillation also fixes the
zero state. -/
theorem sampledInverseRatePair_iterate_zero_state
    (lambda step : ℝ) (N : ℕ) :
    (sampledInverseRatePair lambda step)^[N] 0 = 0 := by
  unfold sampledInverseRatePair
  exact bumpSatField_iterate_sampled_inv_rate_pair_cancel 0 lambda step N

/-- THEOREM 3: the headroom of a finite sampled forward/inverse oscillation
from zero is always exactly one. -/
theorem sampledRateInversePair_iterate_zero_headroom_eq_one
    (lambda step : ℝ) (N : ℕ) :
    (1 : ℝ) - (sampledRateInversePair lambda step)^[N] 0 = 1 := by
  rw [sampledRateInversePair_iterate_zero_state lambda step N]
  ring

/-- THEOREM 4: the headroom of a finite sampled inverse/forward oscillation
from zero is always exactly one. -/
theorem sampledInverseRatePair_iterate_zero_headroom_eq_one
    (lambda step : ℝ) (N : ℕ) :
    (1 : ℝ) - (sampledInverseRatePair lambda step)^[N] 0 = 1 := by
  rw [sampledInverseRatePair_iterate_zero_state lambda step N]
  ring

/-! ## One-sided inverse branch strictly separates -/

/-- THEOREM 5: under positive sampled scale, the one-sided inverse carrier
scale is already larger than one after every positive number of steps. -/
theorem one_lt_sampledInverseCarrierScale_of_pos_steps
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N) :
    1 < sampledInverseCarrierScale lambda step N := by
  rw [sampledInverseCarrierScale_eq_exp_growth lambda step N]
  unfold realDecayResidual
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have htotal : 0 < lambda * ((N : ℝ) * step) := by
    have hmul : 0 < (N : ℝ) * (lambda * step) :=
      mul_pos hNreal hpos
    nlinarith
  have hneg : (-lambda) * ((N : ℝ) * step) < 0 := by
    nlinarith
  have hexp_lt_one :
      Real.exp ((-lambda) * ((N : ℝ) * step)) < 1 :=
    Real.exp_lt_one_iff.mpr hneg
  exact (one_lt_inv₀ (Real.exp_pos _)).mpr hexp_lt_one

/-- THEOREM 6: finite sampled forward/inverse oscillation headroom is not the
one-sided inverse branch scale at any positive step. -/
theorem sampledRateInversePair_headroom_ne_inverse_scale
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N) :
    (1 : ℝ) - (sampledRateInversePair lambda step)^[N] 0 ≠
      sampledInverseCarrierScale lambda step N := by
  rw [sampledRateInversePair_iterate_zero_headroom_eq_one lambda step N]
  exact ne_of_lt (one_lt_sampledInverseCarrierScale_of_pos_steps hpos hN)

/-- THEOREM 7: finite sampled inverse/forward oscillation headroom is also not
the one-sided inverse branch scale at any positive step. -/
theorem sampledInverseRatePair_headroom_ne_inverse_scale
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N) :
    (1 : ℝ) - (sampledInverseRatePair lambda step)^[N] 0 ≠
      sampledInverseCarrierScale lambda step N := by
  rw [sampledInverseRatePair_iterate_zero_headroom_eq_one lambda step N]
  exact ne_of_lt (one_lt_sampledInverseCarrierScale_of_pos_steps hpos hN)

/-! ## Bundled oscillation guardrail -/

/-- A compact receipt separating finite net-zero oscillation from one-sided
inverse-branch growth. -/
structure OscillationInverseBranchSeparationReceipt : Prop where
  rate_inverse_zero_state :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      (sampledRateInversePair lambda step)^[N] 0 = 0
  inverse_rate_zero_state :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      (sampledInverseRatePair lambda step)^[N] 0 = 0
  rate_inverse_headroom_one :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      (1 : ℝ) - (sampledRateInversePair lambda step)^[N] 0 = 1
  inverse_rate_headroom_one :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      (1 : ℝ) - (sampledInverseRatePair lambda step)^[N] 0 = 1
  inverse_scale_gt_one :
    ∀ lambda step : ℝ, 0 < lambda * step -> ∀ N : ℕ, 0 < N ->
      1 < sampledInverseCarrierScale lambda step N
  rate_inverse_not_inverse_branch :
    ∀ lambda step : ℝ, 0 < lambda * step -> ∀ N : ℕ, 0 < N ->
      (1 : ℝ) - (sampledRateInversePair lambda step)^[N] 0 ≠
        sampledInverseCarrierScale lambda step N
  inverse_rate_not_inverse_branch :
    ∀ lambda step : ℝ, 0 < lambda * step -> ∀ N : ℕ, 0 < N ->
      (1 : ℝ) - (sampledInverseRatePair lambda step)^[N] 0 ≠
        sampledInverseCarrierScale lambda step N
  finite_net_zero :
    FiniteSampledOscillationNetZeroReceipt

/-- THEOREM 8: the oscillation-vs-inverse-branch separation receipt. -/
theorem oscillationInverseBranchSeparationReceipt :
    OscillationInverseBranchSeparationReceipt where
  rate_inverse_zero_state :=
    sampledRateInversePair_iterate_zero_state
  inverse_rate_zero_state :=
    sampledInverseRatePair_iterate_zero_state
  rate_inverse_headroom_one :=
    sampledRateInversePair_iterate_zero_headroom_eq_one
  inverse_rate_headroom_one :=
    sampledInverseRatePair_iterate_zero_headroom_eq_one
  inverse_scale_gt_one := fun _ _ hpos _ hN =>
    one_lt_sampledInverseCarrierScale_of_pos_steps hpos hN
  rate_inverse_not_inverse_branch := fun _ _ hpos _ hN =>
    sampledRateInversePair_headroom_ne_inverse_scale hpos hN
  inverse_rate_not_inverse_branch := fun _ _ hpos _ hN =>
    sampledInverseRatePair_headroom_ne_inverse_scale hpos hN
  finite_net_zero :=
    finiteSampledOscillationNetZeroReceipt

end AffineRelaxation

/-! ## Top-level carrier guardrail -/

/-- A stronger top-level receipt: the unified formula admits multiple certified
coordinate readings, but forward accounting, one-sided inverse growth, finite
oscillation, and Hamiltonian producer readings remain separated by explicit
gates. -/
structure UnifiedFormulaCarrierGuardrailReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  projection_discipline :
    UnifiedFormulaProjectionDisciplineReceipt.{u, v} E
  oscillation_inverse_separation :
    AffineRelaxation.OscillationInverseBranchSeparationReceipt

/-- THEOREM 9: the stronger carrier guardrail receipt. -/
theorem unifiedFormulaCarrierGuardrailReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    UnifiedFormulaCarrierGuardrailReceipt.{u, v} E where
  projection_discipline :=
    unifiedFormulaProjectionDisciplineReceipt (E := E)
  oscillation_inverse_separation :=
    AffineRelaxation.oscillationInverseBranchSeparationReceipt

end SaturationMonoid
