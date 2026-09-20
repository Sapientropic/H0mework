/-
  Proposition 473: the one-loop inverse-coupling flow is a genuine local
  semigroup action away from poles.

  P472 proved the closed form

      sigma(t) = sigma0 / (1 + b0 * sigma0 * t)

  and the linearizing coordinate

      1 / sigma(t) = 1 / sigma0 + b0 * t.

  This file proves the missing flow law: running for time `t` and then for
  time `s` is the same as running once for time `t + s`, provided the starting
  coupling and the relevant denominators are nonzero.  In inverse-coupling
  coordinates the result is just translation by `b0 * t`.

  Boundary: the theorem is intentionally local.  Lean's division on fields is
  totalized, while the physical one-loop trajectory is only interpreted on
  non-pole patches.  The explicit denominator hypotheses mark exactly that
  patch condition.
-/

import H0mework.Physics.RepresentationSources.P472

namespace SaturationMonoid
namespace StandardModelConstraint
namespace RunningSigmaBeta

noncomputable section

/-! ## Generic one-loop flow law -/

/-- THEOREM 1: away from a pole, a nonzero initial coupling remains nonzero
under one-loop flow. -/
theorem oneLoopSigmaFlow_ne_zero
    (b0 sigma0 t : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden : 1 + b0 * sigma0 * t ≠ 0) :
    oneLoopSigmaFlow b0 sigma0 t ≠ 0 := by
  unfold oneLoopSigmaFlow
  exact div_ne_zero hsigma hden

/-- THEOREM 2: if the first patch and the combined patch avoid poles, the
intermediate patch also avoids its pole. -/
theorem oneLoopSigmaFlow_intermediate_den_ne_zero
    (b0 sigma0 t s : ℝ)
    (hden_t : 1 + b0 * sigma0 * t ≠ 0)
    (hden_ts : 1 + b0 * sigma0 * (t + s) ≠ 0) :
    1 + b0 * oneLoopSigmaFlow b0 sigma0 t * s ≠ 0 := by
  intro hinner
  unfold oneLoopSigmaFlow at hinner
  have hmul :
      (1 + b0 * (sigma0 / (1 + b0 * sigma0 * t)) * s) *
          (1 + b0 * sigma0 * t) = 0 := by
    rw [hinner]
    ring
  have hcombined_zero : 1 + b0 * sigma0 * (t + s) = 0 := by
    field_simp [hden_t] at hmul
    linear_combination hmul
  exact hden_ts hcombined_zero

/-- THEOREM 3: the one-loop flow composes by addition of the flow parameter.
In inverse-coupling coordinates this is ordinary translation. -/
theorem oneLoopSigmaFlow_add
    (b0 sigma0 t s : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden_t : 1 + b0 * sigma0 * t ≠ 0)
    (hden_ts : 1 + b0 * sigma0 * (t + s) ≠ 0) :
    oneLoopSigmaFlow b0 (oneLoopSigmaFlow b0 sigma0 t) s =
      oneLoopSigmaFlow b0 sigma0 (t + s) := by
  have _hinner :
      1 + b0 * oneLoopSigmaFlow b0 sigma0 t * s ≠ 0 :=
    oneLoopSigmaFlow_intermediate_den_ne_zero
      b0 sigma0 t s hden_t hden_ts
  have hflow_t :
      oneLoopSigmaFlow b0 sigma0 t ≠ 0 :=
    oneLoopSigmaFlow_ne_zero b0 sigma0 t hsigma hden_t
  apply eq_of_one_div_eq_one_div
  calc
    (1 : ℝ) / oneLoopSigmaFlow b0 (oneLoopSigmaFlow b0 sigma0 t) s
        = (1 : ℝ) / oneLoopSigmaFlow b0 sigma0 t + b0 * s := by
          exact oneLoopSigmaFlow_inverse_linear
            b0 (oneLoopSigmaFlow b0 sigma0 t) s hflow_t
    _ = ((1 : ℝ) / sigma0 + b0 * t) + b0 * s := by
          rw [oneLoopSigmaFlow_inverse_linear b0 sigma0 t hsigma]
    _ = (1 : ℝ) / sigma0 + b0 * (t + s) := by
          ring
    _ = (1 : ℝ) / oneLoopSigmaFlow b0 sigma0 (t + s) := by
          rw [oneLoopSigmaFlow_inverse_linear b0 sigma0 (t + s) hsigma]

/-! ## Carrier and Standard-Model specializations -/

namespace OneLoopCarrier

/-- THEOREM 4: scalar carrier one-loop flow composes by addition of the flow
parameter on every non-pole patch. -/
theorem sigmaFlow_add
    (C : OneLoopCarrier) (sigma0 t s : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden_t : 1 + C.b0 * sigma0 * t ≠ 0)
    (hden_ts : 1 + C.b0 * sigma0 * (t + s) ≠ 0) :
    C.sigmaFlow (C.sigmaFlow sigma0 t) s =
      C.sigmaFlow sigma0 (t + s) := by
  exact oneLoopSigmaFlow_add C.b0 sigma0 t s hsigma hden_t hden_ts

/-- THEOREM 5: scalar carrier one-loop flow preserves nonzero couplings on
non-pole patches. -/
theorem sigmaFlow_ne_zero
    (C : OneLoopCarrier) (sigma0 t : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden : 1 + C.b0 * sigma0 * t ≠ 0) :
    C.sigmaFlow sigma0 t ≠ 0 := by
  exact oneLoopSigmaFlow_ne_zero C.b0 sigma0 t hsigma hden

end OneLoopCarrier

/-- THEOREM 6: every Standard-Model one-loop gauge factor has the same local
flow law, with slope fixed by the carrier-selected `b0`. -/
theorem standardModelOneLoopSigmaFlow_add
    (G : StandardModelGaugeFactor) (sigma0 t s : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden_t :
      1 + (standardModelAsymptoticB0 G : ℝ) * sigma0 * t ≠ 0)
    (hden_ts :
      1 + (standardModelAsymptoticB0 G : ℝ) * sigma0 * (t + s) ≠ 0) :
    standardModelOneLoopSigmaFlow G
        (standardModelOneLoopSigmaFlow G sigma0 t) s =
      standardModelOneLoopSigmaFlow G sigma0 (t + s) := by
  exact
    OneLoopCarrier.sigmaFlow_add
      (standardModelOneLoopCarrier G) sigma0 t s hsigma hden_t hden_ts

/-- THEOREM 7: color/QCD one-loop flow composes with slope `7`. -/
theorem color_oneLoopSigmaFlow_add
    (sigma0 t s : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden_t : 1 + (7 : ℝ) * sigma0 * t ≠ 0)
    (hden_ts : 1 + (7 : ℝ) * sigma0 * (t + s) ≠ 0) :
    standardModelOneLoopSigmaFlow .colorSU3
        (standardModelOneLoopSigmaFlow .colorSU3 sigma0 t) s =
      standardModelOneLoopSigmaFlow .colorSU3 sigma0 (t + s) := by
  exact
    standardModelOneLoopSigmaFlow_add
      .colorSU3 sigma0 t s hsigma
      (by
        simpa [standardModelAsymptoticB0, qcdSixFlavor_asymptoticB0]
          using hden_t)
      (by
        simpa [standardModelAsymptoticB0, qcdSixFlavor_asymptoticB0]
          using hden_ts)

/-- THEOREM 8: weak-sector one-loop flow composes with slope `19/6`. -/
theorem weak_oneLoopSigmaFlow_add
    (sigma0 t s : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden_t : 1 + ((19 : ℝ) / 6) * sigma0 * t ≠ 0)
    (hden_ts : 1 + ((19 : ℝ) / 6) * sigma0 * (t + s) ≠ 0) :
    standardModelOneLoopSigmaFlow .weakSU2
        (standardModelOneLoopSigmaFlow .weakSU2 sigma0 t) s =
      standardModelOneLoopSigmaFlow .weakSU2 sigma0 (t + s) := by
  exact
    standardModelOneLoopSigmaFlow_add
      .weakSU2 sigma0 t s hsigma
      (by
        simpa [standardModelAsymptoticB0, weakStandardModel_asymptoticB0]
          using hden_t)
      (by
        simpa [standardModelAsymptoticB0, weakStandardModel_asymptoticB0]
          using hden_ts)

/-- THEOREM 9: hypercharge one-loop flow composes with slope `-41/6` in the
asymptotic/residual convention. -/
theorem hypercharge_oneLoopSigmaFlow_add
    (sigma0 t s : ℝ)
    (hsigma : sigma0 ≠ 0)
    (hden_t : 1 - ((41 : ℝ) / 6) * sigma0 * t ≠ 0)
    (hden_ts : 1 - ((41 : ℝ) / 6) * sigma0 * (t + s) ≠ 0) :
    standardModelOneLoopSigmaFlow .hyperchargeU1
        (standardModelOneLoopSigmaFlow .hyperchargeU1 sigma0 t) s =
      standardModelOneLoopSigmaFlow .hyperchargeU1 sigma0 (t + s) := by
  exact
    standardModelOneLoopSigmaFlow_add
      .hyperchargeU1 sigma0 t s hsigma
      (by
        simpa [standardModelAsymptoticB0, hyperchargeStandardModel_asymptoticB0,
          sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hden_t)
      (by
        simpa [standardModelAsymptoticB0, hyperchargeStandardModel_asymptoticB0,
          sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hden_ts)

/-! ## Bundled receipt -/

/-- A reusable receipt that the one-loop inverse-coupling law is a local
semigroup action by parameter addition. -/
structure OneLoopSigmaFlowSemigroupReceipt : Prop where
  nonzero_preserved :
    ∀ b0 sigma0 t : ℝ, sigma0 ≠ 0 ->
      1 + b0 * sigma0 * t ≠ 0 ->
      oneLoopSigmaFlow b0 sigma0 t ≠ 0
  intermediate_patch :
    ∀ b0 sigma0 t s : ℝ,
      1 + b0 * sigma0 * t ≠ 0 ->
      1 + b0 * sigma0 * (t + s) ≠ 0 ->
      1 + b0 * oneLoopSigmaFlow b0 sigma0 t * s ≠ 0
  flow_add :
    ∀ b0 sigma0 t s : ℝ, sigma0 ≠ 0 ->
      1 + b0 * sigma0 * t ≠ 0 ->
      1 + b0 * sigma0 * (t + s) ≠ 0 ->
      oneLoopSigmaFlow b0 (oneLoopSigmaFlow b0 sigma0 t) s =
        oneLoopSigmaFlow b0 sigma0 (t + s)
  carrier_flow_add :
    ∀ C : OneLoopCarrier, ∀ sigma0 t s : ℝ, sigma0 ≠ 0 ->
      1 + C.b0 * sigma0 * t ≠ 0 ->
      1 + C.b0 * sigma0 * (t + s) ≠ 0 ->
      C.sigmaFlow (C.sigmaFlow sigma0 t) s =
        C.sigmaFlow sigma0 (t + s)
  standard_model_flow_add :
    ∀ G : StandardModelGaugeFactor, ∀ sigma0 t s : ℝ, sigma0 ≠ 0 ->
      1 + (standardModelAsymptoticB0 G : ℝ) * sigma0 * t ≠ 0 ->
      1 + (standardModelAsymptoticB0 G : ℝ) * sigma0 * (t + s) ≠ 0 ->
      standardModelOneLoopSigmaFlow G
          (standardModelOneLoopSigmaFlow G sigma0 t) s =
        standardModelOneLoopSigmaFlow G sigma0 (t + s)
  color_flow_add :
    ∀ sigma0 t s : ℝ, sigma0 ≠ 0 ->
      1 + (7 : ℝ) * sigma0 * t ≠ 0 ->
      1 + (7 : ℝ) * sigma0 * (t + s) ≠ 0 ->
      standardModelOneLoopSigmaFlow .colorSU3
          (standardModelOneLoopSigmaFlow .colorSU3 sigma0 t) s =
        standardModelOneLoopSigmaFlow .colorSU3 sigma0 (t + s)
  weak_flow_add :
    ∀ sigma0 t s : ℝ, sigma0 ≠ 0 ->
      1 + ((19 : ℝ) / 6) * sigma0 * t ≠ 0 ->
      1 + ((19 : ℝ) / 6) * sigma0 * (t + s) ≠ 0 ->
      standardModelOneLoopSigmaFlow .weakSU2
          (standardModelOneLoopSigmaFlow .weakSU2 sigma0 t) s =
        standardModelOneLoopSigmaFlow .weakSU2 sigma0 (t + s)
  hypercharge_flow_add :
    ∀ sigma0 t s : ℝ, sigma0 ≠ 0 ->
      1 - ((41 : ℝ) / 6) * sigma0 * t ≠ 0 ->
      1 - ((41 : ℝ) / 6) * sigma0 * (t + s) ≠ 0 ->
      standardModelOneLoopSigmaFlow .hyperchargeU1
          (standardModelOneLoopSigmaFlow .hyperchargeU1 sigma0 t) s =
        standardModelOneLoopSigmaFlow .hyperchargeU1 sigma0 (t + s)

/-- THEOREM 10: the one-loop local semigroup receipt. -/
theorem oneLoopSigmaFlowSemigroupReceipt :
    OneLoopSigmaFlowSemigroupReceipt where
  nonzero_preserved := oneLoopSigmaFlow_ne_zero
  intermediate_patch := oneLoopSigmaFlow_intermediate_den_ne_zero
  flow_add := oneLoopSigmaFlow_add
  carrier_flow_add := OneLoopCarrier.sigmaFlow_add
  standard_model_flow_add := standardModelOneLoopSigmaFlow_add
  color_flow_add := color_oneLoopSigmaFlow_add
  weak_flow_add := weak_oneLoopSigmaFlow_add
  hypercharge_flow_add := hypercharge_oneLoopSigmaFlow_add

end

end RunningSigmaBeta
end StandardModelConstraint
end SaturationMonoid
