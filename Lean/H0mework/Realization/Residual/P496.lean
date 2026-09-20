import H0mework.Realization.Residual.P495

/-!
# Proposition 496: time-indexed carrier-produced H¹ residual flow

P495 gates a single H¹ residual reading of the sampled inverse carrier.  This
file lifts the gate to a time-indexed family: a phase cochain at every sampled
step whose three-ring residual is exactly the sampled inverse carrier scale at
that step.

With that family certificate, the H¹ residual sequence inherits the carrier's
closed form, divergence under positive sampled scale, per-step H¹ obstruction,
and agreement with any Hamiltonian-scale producer using the same carrier.

Boundary: this is a certified projection theorem.  It does not identify
arbitrary physical, psychological, or metaphysical quantities with H¹ residuals
unless the family producer certificate is supplied.
-/

noncomputable section

open Filter

namespace SaturationMonoid

universe u

namespace AffineRelaxation

/-- A phase-cochain family whose selected three-ring residual is the sampled
inverse carrier scale at every sampled step. -/
structure SampledInverseH1ResidualFamilyProducer
    (lambda step : ℝ) where
  phase : ℕ -> _root_.ThreeCycleTime -> _root_.ThreeCycleTime -> ℝ
  residual_eq_carrier :
    ∀ N : ℕ,
      _root_.threeAgentRingResidual (phase N) =
        sampledInverseCarrierScale lambda step N

/-- THEOREM 1: a family producer restricts to the one-step producer from P495
at every sampled step. -/
def SampledInverseH1ResidualFamilyProducer.at
    {lambda step : ℝ}
    (C : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    SampledInverseH1ResidualProducer lambda step N where
  phase := C.phase N
  residual_eq_carrier := C.residual_eq_carrier N

/-- THEOREM 2: every step of a faithful family has nonzero residual. -/
theorem SampledInverseH1ResidualFamilyProducer.residual_ne_zero
    {lambda step : ℝ}
    (C : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    _root_.threeAgentRingResidual (C.phase N) ≠ 0 :=
  (C.at N).residual_ne_zero

/-- THEOREM 3: every step of a faithful family gives a genuine H¹
obstruction. -/
theorem SampledInverseH1ResidualFamilyProducer.h1Obstruction
    {lambda step : ℝ}
    (C : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    _root_.CechAdditiveCover.H1Obstruction
      (_root_.identityPairZeroTripleCover _root_.ThreeCycleTime ℝ)
      (C.phase N) :=
  (C.at N).h1Obstruction

/-- THEOREM 4: the family residual has the same reciprocal exponential closed
form as the inverse carrier. -/
theorem SampledInverseH1ResidualFamilyProducer.residual_eq_exp_growth
    {lambda step : ℝ}
    (C : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    _root_.threeAgentRingResidual (C.phase N) =
      (realDecayResidual lambda ((N : ℝ) * step))⁻¹ := by
  rw [C.residual_eq_carrier N]
  exact sampledInverseCarrierScale_eq_exp_growth lambda step N

/-- THEOREM 5: under positive sampled scale, the carrier-produced H¹ residual
sequence diverges to infinity. -/
theorem SampledInverseH1ResidualFamilyProducer.residual_tendsto_atTop
    {lambda step : ℝ}
    (C : SampledInverseH1ResidualFamilyProducer lambda step)
    (hpos : 0 < lambda * step) :
    Tendsto (fun N : ℕ => _root_.threeAgentRingResidual (C.phase N))
      atTop atTop := by
  have hfun :
      (fun N : ℕ => _root_.threeAgentRingResidual (C.phase N)) =
        sampledInverseCarrierScale lambda step := by
    funext N
    exact C.residual_eq_carrier N
  rw [hfun]
  exact tendsto_sampledInverseCarrierScale_atTop hpos

/-- THEOREM 6: at every sampled step, the zero-target keep projection times
the family residual is one. -/
theorem SampledInverseH1ResidualFamilyProducer.zeroTarget_keep_mul_residual
    {lambda step : ℝ}
    (C : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    realDecayRelaxFlow (0 : ℝ) lambda ((N : ℝ) * step) 1 *
        _root_.threeAgentRingResidual (C.phase N) =
      1 :=
  (C.at N).zeroTarget_keep_mul_residual

/-- THEOREM 7: under positive sampled steps, the forward zero-origin headroom
projection is not the family residual. -/
theorem SampledInverseH1ResidualFamilyProducer.forward_headroom_ne_residual
    {lambda step : ℝ} (hpos : 0 < lambda * step)
    {N : ℕ} (hN : 0 < N)
    (C : SampledInverseH1ResidualFamilyProducer lambda step) :
    (1 : ℝ) -
        (fun z : ℝ => bumpSatField z (realDecayRate lambda step))^[N] 0 ≠
      _root_.threeAgentRingResidual (C.phase N) :=
  (C.at N).forward_headroom_ne_residual hpos hN

/-- THEOREM 8: a Hamiltonian-scale producer and an H¹ residual family producer
using the same carrier agree at every sampled step. -/
theorem sampledInverseHamiltonianScale_eq_h1ResidualFamily
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {lambda step : ℝ}
    (H : SampledInverseHamiltonianScaleProducer E lambda step)
    (R : SampledInverseH1ResidualFamilyProducer lambda step)
    (N : ℕ) :
    H.scale N = _root_.threeAgentRingResidual (R.phase N) :=
  sampledInverseHamiltonianScale_eq_h1Residual H (R.at N)

end AffineRelaxation
end SaturationMonoid
