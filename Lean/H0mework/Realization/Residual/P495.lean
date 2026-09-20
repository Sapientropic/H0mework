import H0mework.Realization.CyclicMemory.P117
import H0mework.Realization.Residual.P494

/-!
# Proposition 495: carrier-produced H¹ residual gate

P486-P490 introduced the producer gate for reading the sampled inverse carrier
scale as a Hamiltonian scale.  P116-P117 separately proved that a nonzero
three-agent ring residual gives a genuine H¹ obstruction.

This file adds the analogous producer gate for H¹ readings.  A cyclic
obstruction is carrier-produced only when a phase cochain is supplied together
with a faithful law identifying its three-ring residual with the sampled
inverse carrier scale.  Under that certificate, the residual is nonzero, gives
H¹, is the reciprocal of the zero-target keep projection, and shares the same
scale as any Hamiltonian producer using the same carrier.

Boundary: this is a bridge theorem for certified projections.  It does not
assert that arbitrary psychological, neural, physical, or metaphysical
quantities are H¹ residuals.  Those readings still need the producer
certificate supplied here.
-/

noncomputable section

namespace SaturationMonoid

universe u v

namespace AffineRelaxation

/-! ## H¹ residual producer -/

/-- A three-agent phase cochain whose selected ring residual is faithfully
identified with the sampled inverse carrier scale at one sampled step.

The phase data is intentionally explicit.  Without this certificate, the
carrier scale and H¹ residual live on different projections and must not be
silently identified. -/
structure SampledInverseH1ResidualProducer
    (lambda step : ℝ) (N : ℕ) where
  phase : _root_.ThreeCycleTime -> _root_.ThreeCycleTime -> ℝ
  residual_eq_carrier :
    _root_.threeAgentRingResidual phase =
      sampledInverseCarrierScale lambda step N

/-- THEOREM 1: the sampled inverse carrier scale is never zero. -/
theorem sampledInverseCarrierScale_ne_zero
    (lambda step : ℝ) (N : ℕ) :
    sampledInverseCarrierScale lambda step N ≠ 0 := by
  rw [sampledInverseCarrierScale_eq_exp_growth]
  exact inv_ne_zero (Real.exp_pos _).ne'

/-- THEOREM 2: every faithful H¹ residual producer has nonzero residual. -/
theorem SampledInverseH1ResidualProducer.residual_ne_zero
    {lambda step : ℝ} {N : ℕ}
    (C : SampledInverseH1ResidualProducer lambda step N) :
    _root_.threeAgentRingResidual C.phase ≠ 0 := by
  rw [C.residual_eq_carrier]
  exact sampledInverseCarrierScale_ne_zero lambda step N

/-- THEOREM 3: every faithful H¹ residual producer gives a genuine H¹
obstruction. -/
theorem SampledInverseH1ResidualProducer.h1Obstruction
    {lambda step : ℝ} {N : ℕ}
    (C : SampledInverseH1ResidualProducer lambda step N) :
    _root_.CechAdditiveCover.H1Obstruction
      (_root_.identityPairZeroTripleCover _root_.ThreeCycleTime ℝ)
      C.phase :=
  _root_.threeAgentRingResidual_nonzero_h1 C.phase C.residual_ne_zero

/-! ## Reciprocal zero-target keep projection -/

/-- THEOREM 4: a carrier-produced H¹ residual is the reciprocal of the
zero-target keep flow. -/
theorem SampledInverseH1ResidualProducer.residual_eq_zeroTarget_keep_inv
    {lambda step : ℝ} {N : ℕ}
    (C : SampledInverseH1ResidualProducer lambda step N) :
    _root_.threeAgentRingResidual C.phase =
      (realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1)⁻¹ := by
  rw [C.residual_eq_carrier]
  exact sampledInverseCarrierScale_eq_zeroTarget_keep_inv lambda step N

/-- THEOREM 5: the zero-target keep projection times a carrier-produced H¹
residual is one. -/
theorem SampledInverseH1ResidualProducer.zeroTarget_keep_mul_residual
    {lambda step : ℝ} {N : ℕ}
    (C : SampledInverseH1ResidualProducer lambda step N) :
    realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 *
        _root_.threeAgentRingResidual C.phase =
      1 := by
  rw [C.residual_eq_carrier]
  exact zeroTarget_keep_mul_sampledInverseCarrierScale_eq_one lambda step N

/-- THEOREM 6: under positive sampled steps, the forward zero-origin headroom
projection is not the carrier-produced H¹ residual. -/
theorem SampledInverseH1ResidualProducer.forward_headroom_ne_residual
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N)
    (C : SampledInverseH1ResidualProducer lambda step N) :
    (1 : ℝ) -
        (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 ≠
      _root_.threeAgentRingResidual C.phase := by
  rw [C.residual_eq_carrier]
  exact forward_zero_origin_headroom_ne_sampledInverseCarrierScale_of_pos_steps
    hpos hN

/-! ## Shared carrier scale with Hamiltonian producers -/

/-- THEOREM 7: when a Hamiltonian-scale producer and an H¹ residual producer
use the same sampled inverse carrier, their produced scalar values agree. -/
theorem sampledInverseHamiltonianScale_eq_h1Residual
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {lambda step : ℝ} {N : ℕ}
    (H : SampledInverseHamiltonianScaleProducer E lambda step)
    (R : SampledInverseH1ResidualProducer lambda step N) :
    H.scale N = _root_.threeAgentRingResidual R.phase := by
  rw [H.carrier_scale N]
  exact R.residual_eq_carrier.symm

/-! ## Receipts -/

/-- The reusable H¹ residual producer gate. -/
structure CarrierProducedH1ResidualReceipt : Prop where
  carrier_nonzero :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      sampledInverseCarrierScale lambda step N ≠ 0
  residual_nonzero :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      ∀ C : SampledInverseH1ResidualProducer lambda step N,
        _root_.threeAgentRingResidual C.phase ≠ 0
  h1_from_producer :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      ∀ C : SampledInverseH1ResidualProducer lambda step N,
        _root_.CechAdditiveCover.H1Obstruction
          (_root_.identityPairZeroTripleCover _root_.ThreeCycleTime ℝ)
          C.phase
  residual_is_keep_reciprocal :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      ∀ C : SampledInverseH1ResidualProducer lambda step N,
        _root_.threeAgentRingResidual C.phase =
          (realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1)⁻¹
  keep_times_residual :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      ∀ C : SampledInverseH1ResidualProducer lambda step N,
        realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 *
            _root_.threeAgentRingResidual C.phase =
          1
  forward_headroom_not_residual :
    ∀ lambda step : ℝ, 0 < lambda * step -> ∀ N : ℕ, 0 < N ->
      ∀ C : SampledInverseH1ResidualProducer lambda step N,
        (1 : ℝ) -
            (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 ≠
          _root_.threeAgentRingResidual C.phase

/-- THEOREM 8: the carrier-produced H¹ residual receipt. -/
theorem carrierProducedH1ResidualReceipt :
    CarrierProducedH1ResidualReceipt where
  carrier_nonzero := sampledInverseCarrierScale_ne_zero
  residual_nonzero := fun _ _ _ C => C.residual_ne_zero
  h1_from_producer := fun _ _ _ C => C.h1Obstruction
  residual_is_keep_reciprocal := fun _ _ _ C =>
    C.residual_eq_zeroTarget_keep_inv
  keep_times_residual := fun _ _ _ C =>
    C.zeroTarget_keep_mul_residual
  forward_headroom_not_residual := fun _ _ hpos _ hN C =>
    C.forward_headroom_ne_residual hpos hN

end AffineRelaxation

/-! ## Top-level producer bridge -/

/-- A top-level bridge receipt saying that Hamiltonian and H¹ readings of the
sampled inverse carrier are both producer-gated and agree only when both
producers identify their output with the same carrier scale. -/
structure UnifiedFormulaProducerBridgeReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : Prop where
  zero_target_guardrail :
    UnifiedFormulaZeroTargetGuardrailReceipt.{u, v} E
  h1_residual_gate :
    AffineRelaxation.CarrierProducedH1ResidualReceipt
  hamiltonian_scale_gate :
    ∀ lambda step : ℝ,
      ∀ H : AffineRelaxation.SampledInverseHamiltonianScaleProducer
          E lambda step,
        AffineRelaxation.CarrierProducedHamiltonianScaleReceipt
          E lambda step H
  shared_scale_when_both_produced :
    ∀ lambda step : ℝ, ∀ N : ℕ,
      ∀ H : AffineRelaxation.SampledInverseHamiltonianScaleProducer
          E lambda step,
      ∀ R : AffineRelaxation.SampledInverseH1ResidualProducer
          lambda step N,
        H.scale N = _root_.threeAgentRingResidual R.phase

/-- THEOREM 9: the unified producer bridge receipt. -/
theorem unifiedFormulaProducerBridgeReceipt
    (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    UnifiedFormulaProducerBridgeReceipt.{u, v} E where
  zero_target_guardrail :=
    unifiedFormulaZeroTargetGuardrailReceipt.{u, v} (E := E)
  h1_residual_gate :=
    AffineRelaxation.carrierProducedH1ResidualReceipt
  hamiltonian_scale_gate := fun _ _ H =>
    AffineRelaxation.carrierProducedHamiltonianScaleReceipt H
  shared_scale_when_both_produced := fun _ _ _ H R =>
    AffineRelaxation.sampledInverseHamiltonianScale_eq_h1Residual H R

end SaturationMonoid
