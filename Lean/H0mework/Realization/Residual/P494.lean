import H0mework.Physics.SourceContracts.P468
import H0mework.Realization.RelaxationAlgebra.P493

/-!
# Proposition 494: zero-target keep and inverse branch are reciprocal projections

P467/P468 prove that an apparent `Target=1` salience bump is the complement of
a zero-target keep/headroom flow.  P493 proves that one-sided inverse-branch
growth is not the same projection as finite net-zero oscillation.

This file connects those two guardrails.  The sampled inverse carrier scale is
the reciprocal of the zero-target keep flow from `1`, equivalently the
reciprocal of the forward zero-origin bump orbit's remaining headroom.
Therefore, under positive sampled scale and a positive number of steps, the
forward keep projection lies in `(0,1)` while the inverse projection lies above
`1`.

Boundary: this is still scalar carrier algebra.  It proves the reciprocal
projection relation and the non-equality guardrail; it does not identify either
projection with physical energy, mass, vacuum, or consciousness without a
separate producer certificate.
-/

noncomputable section

namespace SaturationMonoid

universe u v

namespace AffineRelaxation

/-! ## Zero-target keep as the forward projection -/

/-- THEOREM 1: zero-target real relaxation from the unit keep coordinate is
exactly the continuous residual. -/
theorem zeroTarget_keep_flow_from_one_eq_residual
    (lambda t : ℝ) :
    realDecayRelaxFlow (0 : ℝ) lambda t 1 =
      realDecayResidual lambda t := by
  rw [realDecayRelaxFlow_eq_closed]
  ring

/-- THEOREM 2: the forward zero-origin salience orbit's remaining headroom is
the same zero-target keep flow. -/
theorem forward_zero_origin_headroom_eq_zeroTarget_keep_flow
    (lambda step : ℝ) (N : ℕ) :
    (1 : ℝ) -
        (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 =
      realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 := by
  simpa using
    _root_.SaturationMonoid.StandardModelConstraint.complement_bumpSatField_iterate_realDecayRate_eq_zeroTarget_flow_keep
      0 lambda step N

/-! ## The inverse branch is the reciprocal projection -/

/-- THEOREM 3: the sampled inverse carrier scale is the reciprocal of the
zero-target keep flow. -/
theorem sampledInverseCarrierScale_eq_zeroTarget_keep_inv
    (lambda step : ℝ) (N : ℕ) :
    sampledInverseCarrierScale lambda step N =
      (realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1)⁻¹ := by
  rw [sampledInverseCarrierScale_eq_exp_growth]
  rw [zeroTarget_keep_flow_from_one_eq_residual]

/-- THEOREM 4: the zero-target keep projection and the sampled inverse branch
multiply to one. -/
theorem zeroTarget_keep_mul_sampledInverseCarrierScale_eq_one
    (lambda step : ℝ) (N : ℕ) :
    realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 *
        sampledInverseCarrierScale lambda step N =
      1 := by
  rw [zeroTarget_keep_flow_from_one_eq_residual]
  rw [sampledInverseCarrierScale_eq_exp_growth]
  have hresne : realDecayResidual lambda ((N : ℝ) * step) ≠ 0 := by
    unfold realDecayResidual
    exact (Real.exp_pos _).ne'
  simpa using mul_inv_cancel₀ hresne

/-- THEOREM 5: equivalently, the sampled inverse carrier scale is the
reciprocal of the forward zero-origin orbit's remaining headroom. -/
theorem sampledInverseCarrierScale_eq_forward_zero_origin_headroom_inv
    (lambda step : ℝ) (N : ℕ) :
    sampledInverseCarrierScale lambda step N =
      ((1 : ℝ) -
        (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0)⁻¹ := by
  rw [forward_zero_origin_headroom_eq_zeroTarget_keep_flow]
  exact sampledInverseCarrierScale_eq_zeroTarget_keep_inv lambda step N

/-- THEOREM 6: the forward zero-origin headroom and the sampled inverse scale
multiply to one. -/
theorem forward_zero_origin_headroom_mul_inverse_scale_eq_one
    (lambda step : ℝ) (N : ℕ) :
    ((1 : ℝ) -
        (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0) *
        sampledInverseCarrierScale lambda step N =
      1 := by
  rw [forward_zero_origin_headroom_eq_zeroTarget_keep_flow]
  exact zeroTarget_keep_mul_sampledInverseCarrierScale_eq_one lambda step N

/-! ## Positive sampled steps strictly separate the projections -/

/-- THEOREM 7: after a positive number of positive sampled steps, the
zero-target keep projection lies strictly between zero and one. -/
theorem zeroTarget_keep_flow_from_one_mem_Ioo_of_pos_steps
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N) :
    realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 ∈
      Set.Ioo (0 : ℝ) 1 := by
  rw [zeroTarget_keep_flow_from_one_eq_residual]
  constructor
  · unfold realDecayResidual
    exact Real.exp_pos _
  · unfold realDecayResidual
    have hNreal : 0 < (N : ℝ) := by
      exact_mod_cast hN
    have hneg : (-lambda) * ((N : ℝ) * step) < 0 := by
      nlinarith
    exact Real.exp_lt_one_iff.mpr hneg

/-- THEOREM 8: after a positive number of positive sampled steps, the forward
zero-origin headroom also lies strictly between zero and one. -/
theorem forward_zero_origin_headroom_mem_Ioo_of_pos_steps
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N) :
    (1 : ℝ) -
        (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 ∈
      Set.Ioo (0 : ℝ) 1 := by
  rw [forward_zero_origin_headroom_eq_zeroTarget_keep_flow]
  exact zeroTarget_keep_flow_from_one_mem_Ioo_of_pos_steps hpos hN

/-- THEOREM 9: the zero-target keep projection is not the inverse branch at
any positive sampled step. -/
theorem zeroTarget_keep_flow_ne_sampledInverseCarrierScale_of_pos_steps
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N) :
    realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 ≠
      sampledInverseCarrierScale lambda step N := by
  have hkeep_lt :
      realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 < 1 :=
    (zeroTarget_keep_flow_from_one_mem_Ioo_of_pos_steps hpos hN).2
  have hinv_gt : 1 < sampledInverseCarrierScale lambda step N :=
    one_lt_sampledInverseCarrierScale_of_pos_steps hpos hN
  exact ne_of_lt (lt_trans hkeep_lt hinv_gt)

/-- THEOREM 10: the forward zero-origin headroom is not the inverse branch at
any positive sampled step. -/
theorem forward_zero_origin_headroom_ne_sampledInverseCarrierScale_of_pos_steps
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N) :
    (1 : ℝ) -
        (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 ≠
      sampledInverseCarrierScale lambda step N := by
  rw [forward_zero_origin_headroom_eq_zeroTarget_keep_flow]
  exact zeroTarget_keep_flow_ne_sampledInverseCarrierScale_of_pos_steps hpos hN

/-! ## Bundled receipt -/

/-- A compact receipt: the forward keep projection is the zero-target face of
the sampled bump orbit, and the inverse branch is its reciprocal, not the same
projection. -/
structure ZeroTargetKeepInverseProjectionReceipt : Prop where
  keep_flow_residual :
    ∀ lambda t : ℝ,
      realDecayRelaxFlow (0 : ℝ) lambda t 1 =
        realDecayResidual lambda t
  forward_headroom_is_keep_flow :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      (1 : ℝ) -
          (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 =
        realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1
  inverse_is_keep_reciprocal :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      sampledInverseCarrierScale lambda step N =
        (realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1)⁻¹
  keep_times_inverse :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 *
          sampledInverseCarrierScale lambda step N =
        1
  forward_headroom_times_inverse :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      ((1 : ℝ) -
          (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0) *
          sampledInverseCarrierScale lambda step N =
        1
  keep_in_unit_interval :
    ∀ lambda step : ℝ, 0 < lambda * step -> ∀ N : ℕ, 0 < N ->
      realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 ∈
        Set.Ioo (0 : ℝ) 1
  keep_not_inverse :
    ∀ lambda step : ℝ, 0 < lambda * step -> ∀ N : ℕ, 0 < N ->
      realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 ≠
        sampledInverseCarrierScale lambda step N

/-- THEOREM 11: the zero-target keep / inverse-branch reciprocal receipt. -/
theorem zeroTargetKeepInverseProjectionReceipt :
    ZeroTargetKeepInverseProjectionReceipt where
  keep_flow_residual :=
    zeroTarget_keep_flow_from_one_eq_residual
  forward_headroom_is_keep_flow :=
    forward_zero_origin_headroom_eq_zeroTarget_keep_flow
  inverse_is_keep_reciprocal :=
    sampledInverseCarrierScale_eq_zeroTarget_keep_inv
  keep_times_inverse :=
    zeroTarget_keep_mul_sampledInverseCarrierScale_eq_one
  forward_headroom_times_inverse :=
    forward_zero_origin_headroom_mul_inverse_scale_eq_one
  keep_in_unit_interval := fun _ _ hpos _ hN =>
    zeroTarget_keep_flow_from_one_mem_Ioo_of_pos_steps hpos hN
  keep_not_inverse := fun _ _ hpos _ hN =>
    zeroTarget_keep_flow_ne_sampledInverseCarrierScale_of_pos_steps hpos hN

end AffineRelaxation

/-! ## Top-level zero-target guardrail -/

/-- A top-level receipt combining the single zero-target reading with the
projection guardrails through the keep/inverse reciprocal law. -/
structure UnifiedFormulaZeroTargetGuardrailReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  single_zero_target :
    StandardModelConstraint.SingleZeroTargetRelaxationReceipt ℝ
  rate_complement_zero_target :
    StandardModelConstraint.RateComplementSampledZeroTargetFlowReceipt
  keep_inverse_projection :
    AffineRelaxation.ZeroTargetKeepInverseProjectionReceipt
  carrier_guardrail :
    UnifiedFormulaCarrierGuardrailReceipt.{u, v} E

/-- THEOREM 12: the unified formula zero-target guardrail receipt. -/
theorem unifiedFormulaZeroTargetGuardrailReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    UnifiedFormulaZeroTargetGuardrailReceipt.{u, v} E where
  single_zero_target :=
    StandardModelConstraint.singleZeroTargetRelaxationReceipt ℝ
  rate_complement_zero_target :=
    StandardModelConstraint.rateComplementSampledZeroTargetFlowReceipt
  keep_inverse_projection :=
    AffineRelaxation.zeroTargetKeepInverseProjectionReceipt
  carrier_guardrail :=
    unifiedFormulaCarrierGuardrailReceipt.{u, v} (E := E)

end SaturationMonoid
