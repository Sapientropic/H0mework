/-
  Proposition 472: one-loop gauge running is affine in inverse-coupling
  coordinates.

  P451-P462 prove the saturation-side one-loop step law

      sigma' - sigma = -b0 * sigma^2

  where the Standard-Model carrier fixes `b0` for `SU(3)`, `SU(2)`, and
  `U(1)`.  P471 connected Yukawa slots to the zero-target exponential sampled
  flow.  Gauge running has a different but equally rigid linearizing
  coordinate: inverse coupling.

  The continuous one-loop equation `d sigma / dt = -b0 sigma^2` has solution

      sigma(t) = sigma0 / (1 + b0 * sigma0 * t),

  and therefore

      1 / sigma(t) = 1 / sigma0 + b0 * t.

  This file proves the algebraic spine of that fact and specializes it to the
  carrier-fixed Standard-Model `b0` values.

  Boundary: this is the one-loop closed-form coordinate theorem.  It does not
  add thresholds, two- or three-loop corrections, or derive the universal QFT
  one-loop weights; those boundaries are exactly the ones recorded in P464.
  Lean's field division is totalized, so the reciprocal identity is stated in
  algebraic form with `sigma0 ≠ 0`; physical use should still avoid Landau-pole
  denominators when interpreting the flow as a smooth trajectory.
-/

import H0mework.Physics.YukawaSources.P471
import H0mework.Physics.RepresentationSources.P462

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

noncomputable section

/-! ## Generic one-loop inverse-coupling flow -/

/-- The closed-form one-loop running-sigma flow for coefficient `b0`.

It is the rational solution of the one-loop shape, not the exponential
zero-target flow used by Yukawa residual powers. -/
def oneLoopSigmaFlow (b0 sigma0 t : ℝ) : ℝ :=
  sigma0 / (1 + b0 * sigma0 * t)

/-- THEOREM 1: the one-loop flow starts at the supplied coupling. -/
theorem oneLoopSigmaFlow_zero (b0 sigma0 : ℝ) :
    oneLoopSigmaFlow b0 sigma0 0 = sigma0 := by
  unfold oneLoopSigmaFlow
  ring

/-- THEOREM 2: the one-loop flow is the reciprocal of an affine inverse-
coupling coordinate. -/
theorem oneLoopSigmaFlow_eq_inverse_affine
    (b0 sigma0 t : ℝ) (hsigma : sigma0 ≠ 0) :
    oneLoopSigmaFlow b0 sigma0 t =
      (1 : ℝ) / ((1 : ℝ) / sigma0 + b0 * t) := by
  unfold oneLoopSigmaFlow
  field_simp [hsigma]

/-- THEOREM 3: inverse coupling evolves linearly with slope `b0`. -/
theorem oneLoopSigmaFlow_inverse_linear
    (b0 sigma0 t : ℝ) (hsigma : sigma0 ≠ 0) :
    (1 : ℝ) / oneLoopSigmaFlow b0 sigma0 t =
      (1 : ℝ) / sigma0 + b0 * t := by
  unfold oneLoopSigmaFlow
  field_simp [hsigma]

/-- THEOREM 4: an exact finite step can be written as a quadratic beta-shaped
increment times the endpoint flow.  For small `dt`, this is the Euler
one-loop increment `-b0 * sigma0^2 * dt` to first order. -/
theorem oneLoopSigmaFlow_step_delta_eq
    (b0 sigma0 dt : ℝ)
    (hden : 1 + b0 * sigma0 * dt ≠ 0) :
    oneLoopSigmaFlow b0 sigma0 dt - sigma0 =
      -(b0 * dt) * sigma0 * oneLoopSigmaFlow b0 sigma0 dt := by
  unfold oneLoopSigmaFlow
  have hden' : 1 + sigma0 * b0 * dt ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hden
  apply mul_left_cancel₀ hden'
  field_simp [hden, hden']
  ring

/-! ## Carrier and Standard-Model specializations -/

namespace OneLoopCarrier

/-- The one-loop rational flow selected by a scalar one-loop carrier. -/
def sigmaFlow (C : OneLoopCarrier) (sigma0 t : ℝ) : ℝ :=
  oneLoopSigmaFlow C.b0 sigma0 t

/-- THEOREM 5: a scalar carrier's inverse coupling is affine with slope
`C.b0`. -/
theorem sigmaFlow_inverse_linear
    (C : OneLoopCarrier) (sigma0 t : ℝ) (hsigma : sigma0 ≠ 0) :
    (1 : ℝ) / C.sigmaFlow sigma0 t =
      (1 : ℝ) / sigma0 + C.b0 * t := by
  exact oneLoopSigmaFlow_inverse_linear C.b0 sigma0 t hsigma

/-- THEOREM 6: the carrier flow has the exact finite-step quadratic delta
form. -/
theorem sigmaFlow_step_delta_eq
    (C : OneLoopCarrier) (sigma0 dt : ℝ)
    (hden : 1 + C.b0 * sigma0 * dt ≠ 0) :
    C.sigmaFlow sigma0 dt - sigma0 =
      -(C.b0 * dt) * sigma0 * C.sigmaFlow sigma0 dt := by
  exact oneLoopSigmaFlow_step_delta_eq C.b0 sigma0 dt hden

end OneLoopCarrier

/-- The Standard-Model one-loop rational flow for a gauge factor. -/
def standardModelOneLoopSigmaFlow
    (G : StandardModelGaugeFactor) (sigma0 t : ℝ) : ℝ :=
  (standardModelOneLoopCarrier G).sigmaFlow sigma0 t

/-- THEOREM 7: every Standard-Model gauge factor has inverse-coupling affine
running with slope fixed by the carrier-selected asymptotic `b0`. -/
theorem standardModelOneLoopSigmaFlow_inverse_linear
    (G : StandardModelGaugeFactor) (sigma0 t : ℝ)
    (hsigma : sigma0 ≠ 0) :
    (1 : ℝ) / standardModelOneLoopSigmaFlow G sigma0 t =
      (1 : ℝ) / sigma0 + (standardModelAsymptoticB0 G : ℝ) * t := by
  exact
    OneLoopCarrier.sigmaFlow_inverse_linear
      (standardModelOneLoopCarrier G) sigma0 t hsigma

/-- THEOREM 8: color/QCD inverse coupling has slope `7`. -/
theorem color_oneLoopSigmaFlow_inverse_linear
    (sigma0 t : ℝ) (hsigma : sigma0 ≠ 0) :
    (1 : ℝ) / standardModelOneLoopSigmaFlow .colorSU3 sigma0 t =
      (1 : ℝ) / sigma0 + (7 : ℝ) * t := by
  rw [standardModelOneLoopSigmaFlow_inverse_linear
    .colorSU3 sigma0 t hsigma]
  rw [standardModelAsymptoticB0, qcdSixFlavor_asymptoticB0]
  norm_num

/-- THEOREM 9: weak-sector inverse coupling has slope `19/6`. -/
theorem weak_oneLoopSigmaFlow_inverse_linear
    (sigma0 t : ℝ) (hsigma : sigma0 ≠ 0) :
    (1 : ℝ) / standardModelOneLoopSigmaFlow .weakSU2 sigma0 t =
      (1 : ℝ) / sigma0 + ((19 : ℝ) / 6) * t := by
  rw [standardModelOneLoopSigmaFlow_inverse_linear
    .weakSU2 sigma0 t hsigma]
  rw [standardModelAsymptoticB0, weakStandardModel_asymptoticB0]
  norm_num

/-- THEOREM 10: hypercharge inverse coupling has slope `-41/6` in the
asymptotic/residual convention. -/
theorem hypercharge_oneLoopSigmaFlow_inverse_linear
    (sigma0 t : ℝ) (hsigma : sigma0 ≠ 0) :
    (1 : ℝ) / standardModelOneLoopSigmaFlow .hyperchargeU1 sigma0 t =
      (1 : ℝ) / sigma0 - ((41 : ℝ) / 6) * t := by
  rw [standardModelOneLoopSigmaFlow_inverse_linear
    .hyperchargeU1 sigma0 t hsigma]
  rw [standardModelAsymptoticB0, hyperchargeStandardModel_asymptoticB0]
  ring

/-! ## Bundled receipt -/

/-- A reusable receipt for the one-loop inverse-coupling linearization. -/
structure OneLoopInverseCouplingAffineReceipt : Prop where
  flow_zero :
    ∀ b0 sigma0 : ℝ, oneLoopSigmaFlow b0 sigma0 0 = sigma0
  inverse_affine :
    ∀ b0 sigma0 t : ℝ, sigma0 ≠ 0 ->
      oneLoopSigmaFlow b0 sigma0 t =
        (1 : ℝ) / ((1 : ℝ) / sigma0 + b0 * t)
  inverse_linear :
    ∀ b0 sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / oneLoopSigmaFlow b0 sigma0 t =
        (1 : ℝ) / sigma0 + b0 * t
  carrier_inverse_linear :
    ∀ C : OneLoopCarrier, ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / C.sigmaFlow sigma0 t =
        (1 : ℝ) / sigma0 + C.b0 * t
  standard_model_inverse_linear :
    ∀ G : StandardModelGaugeFactor, ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / standardModelOneLoopSigmaFlow G sigma0 t =
        (1 : ℝ) / sigma0 + (standardModelAsymptoticB0 G : ℝ) * t
  color_slope :
    ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / standardModelOneLoopSigmaFlow .colorSU3 sigma0 t =
        (1 : ℝ) / sigma0 + (7 : ℝ) * t
  weak_slope :
    ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / standardModelOneLoopSigmaFlow .weakSU2 sigma0 t =
        (1 : ℝ) / sigma0 + ((19 : ℝ) / 6) * t
  hypercharge_slope :
    ∀ sigma0 t : ℝ, sigma0 ≠ 0 ->
      (1 : ℝ) / standardModelOneLoopSigmaFlow .hyperchargeU1 sigma0 t =
        (1 : ℝ) / sigma0 - ((41 : ℝ) / 6) * t

/-- THEOREM 11: the one-loop inverse-coupling affine receipt. -/
theorem oneLoopInverseCouplingAffineReceipt :
    OneLoopInverseCouplingAffineReceipt where
  flow_zero := oneLoopSigmaFlow_zero
  inverse_affine := oneLoopSigmaFlow_eq_inverse_affine
  inverse_linear := oneLoopSigmaFlow_inverse_linear
  carrier_inverse_linear := OneLoopCarrier.sigmaFlow_inverse_linear
  standard_model_inverse_linear :=
    standardModelOneLoopSigmaFlow_inverse_linear
  color_slope := color_oneLoopSigmaFlow_inverse_linear
  weak_slope := weak_oneLoopSigmaFlow_inverse_linear
  hypercharge_slope := hypercharge_oneLoopSigmaFlow_inverse_linear

end

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
