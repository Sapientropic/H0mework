import H0mework.Realization.RelaxationAlgebra.P717

/-!
# Proposition 718: the target-general affine relaxation law is unique

P717 proves that the target-one saturation face is forced: the only biaffine
target-one update satisfying the structural endpoint/complement laws is
`bumpSatField`.

This file lifts the uniqueness statement back to the full target-general
equation.  The residual law

`target - f target sigma x = (1-sigma) • (target-x)`

forces `f = relaxModule` over arbitrary module carriers.  On the real scalar
carrier, the weaker-looking target/rate affine endpoint laws already solve the
coefficients and force the same equation.
-/

noncomputable section

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

/-! ## Residual uniqueness over arbitrary module carriers -/

/-- THEOREM 1: over any module carrier, the target residual law uniquely
determines the affine relaxation update. -/
theorem relaxModule_unique_of_target_residual_law
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : ∀ target : E, ∀ sigma : K, ∀ x : E,
      target - f target sigma x = (1 - sigma) • (target - x)) :
    ∀ target : E, ∀ sigma : K, ∀ x : E,
      f target sigma x = relaxModule target sigma x := by
  intro target sigma x
  have hleft :
      target - f target sigma x =
        target - relaxModule target sigma x := by
    rw [hres, target_sub_relaxModule]
  exact sub_right_inj.mp hleft

/-! ## Scalar target/rate affine endpoint laws force relaxTo -/

/-- A real scalar update is target/rate affine when it is linear in `x`,
`target`, `sigma*x`, and `sigma*target`. -/
def IsTargetRateAffineUpdate (f : ℝ -> ℝ -> ℝ -> ℝ) : Prop :=
  ∃ A B C D : ℝ, ∀ target sigma x : ℝ,
    f target sigma x =
      A * x + B * target + C * (sigma * x) + D * (sigma * target)

/-- THEOREM 2: the scalar residual law uniquely determines `relaxTo`. -/
theorem relaxTo_unique_of_target_residual_law
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hres : ∀ target sigma x : ℝ,
      target - f target sigma x = (1 - sigma) * (target - x)) :
    ∀ target sigma x : ℝ, f target sigma x = relaxTo target sigma x := by
  intro target sigma x
  have hres' := hres target sigma x
  unfold relaxTo
  nlinarith

/-- THEOREM 3: a target/rate affine scalar update with the two endpoint laws
`sigma=0` as identity and `sigma=1` as direct hit is exactly `relaxTo`. -/
theorem relaxTo_unique_of_target_rate_affine_endpoint_laws
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target) :
    ∀ target sigma x : ℝ, f target sigma x = relaxTo target sigma x := by
  rcases hlin with ⟨A, B, C, D, hpoly⟩
  have hA : A = 1 := by
    have hpolyA : f 0 0 1 = A := by
      simpa using hpoly 0 0 1
    have hzeroA : f 0 0 1 = 1 := hzero 0 1
    rw [← hpolyA, hzeroA]
  have hB : B = 0 := by
    have hpolyB : f 1 0 0 = B := by
      simpa using hpoly 1 0 0
    have hzeroB : f 1 0 0 = 0 := hzero 1 0
    rw [← hpolyB, hzeroB]
  have hC : C = -1 := by
    have hpolyC : f 0 1 1 = A + C := by
      have h := hpoly 0 1 1
      ring_nf at h ⊢
      exact h
    have honeC : f 0 1 1 = 0 := hone 0 1
    have hAC : A + C = 0 := by
      rw [← hpolyC, honeC]
    rw [hA] at hAC
    nlinarith
  have hD : D = 1 := by
    have hpolyD : f 1 1 0 = B + D := by
      have h := hpoly 1 1 0
      ring_nf at h ⊢
      exact h
    have honeD : f 1 1 0 = 1 := hone 1 0
    have hBD : B + D = 1 := by
      rw [← hpolyD, honeD]
    rw [hB] at hBD
    nlinarith
  intro target sigma x
  rw [hpoly target sigma x, hA, hB, hC, hD]
  unfold relaxTo
  ring

/-- THEOREM 4: the scalar target/rate affine endpoint laws force the residual
law. -/
theorem target_residual_law_of_target_rate_affine_endpoint_laws
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target) :
    ∀ target sigma x : ℝ,
      target - f target sigma x = (1 - sigma) * (target - x) := by
  intro target sigma x
  rw [relaxTo_unique_of_target_rate_affine_endpoint_laws f hlin hzero hone]
  exact target_sub_relaxTo target sigma x

/-- THEOREM 5: the forced target-general scalar update specializes at
`target=1` to `bumpSatField`. -/
theorem target_one_unique_update_is_bumpSat
    (f : ℝ -> ℝ -> ℝ -> ℝ)
    (hlin : IsTargetRateAffineUpdate f)
    (hzero : ∀ target x : ℝ, f target 0 x = x)
    (hone : ∀ target x : ℝ, f target 1 x = target) :
    ∀ h sigma : ℝ, f 1 sigma h = bumpSatField h sigma := by
  intro h sigma
  rw [relaxTo_unique_of_target_rate_affine_endpoint_laws f hlin hzero hone]
  exact relaxTo_one_eq_bumpSatField sigma h

/-! ## Convex closure of the forced scalar law -/

/-- THEOREM 6: the unique target-general scalar update is closed on every
runtime interval. -/
theorem relaxTo_unique_interval_closure
    (lo hi target sigma x : ℝ)
    (hx0 : lo <= x) (hx1 : x <= hi)
    (ht0 : lo <= target) (ht1 : target <= hi)
    (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    lo <= relaxTo target sigma x ∧ relaxTo target sigma x <= hi :=
  relaxTo_mem_Icc lo hi target sigma x hx0 hx1 ht0 ht1 hs0 hs1

/-! ## Certificate -/

/-- P718 certificate: the target-general affine relaxation equation is the
unique update compatible with residual accounting and scalar target/rate
affine endpoint laws. -/
structure UnifiedAffineRelaxationUniquenessCertificate : Prop where
  module_residual_unique :
    ∀ {K E : Type*} [Field K] [AddCommGroup E] [Module K E],
      ∀ f : E -> K -> E -> E,
        (∀ target : E, ∀ sigma : K, ∀ x : E,
          target - f target sigma x = (1 - sigma) • (target - x)) ->
        ∀ target : E, ∀ sigma : K, ∀ x : E,
          f target sigma x = relaxModule target sigma x
  scalar_residual_unique :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      (∀ target sigma x : ℝ,
        target - f target sigma x = (1 - sigma) * (target - x)) ->
      ∀ target sigma x : ℝ, f target sigma x = relaxTo target sigma x
  scalar_endpoint_unique :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      ∀ target sigma x : ℝ, f target sigma x = relaxTo target sigma x
  scalar_endpoint_residual_law :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      ∀ target sigma x : ℝ,
        target - f target sigma x = (1 - sigma) * (target - x)
  target_one_is_bumpSat :
    ∀ f : ℝ -> ℝ -> ℝ -> ℝ,
      IsTargetRateAffineUpdate f ->
      (∀ target x : ℝ, f target 0 x = x) ->
      (∀ target x : ℝ, f target 1 x = target) ->
      ∀ h sigma : ℝ, f 1 sigma h = bumpSatField h sigma
  interval_closure :
    ∀ lo hi target sigma x : ℝ,
      lo <= x -> x <= hi ->
      lo <= target -> target <= hi ->
      0 <= sigma -> sigma <= 1 ->
      lo <= relaxTo target sigma x ∧ relaxTo target sigma x <= hi

/-- THEOREM 7: the real/module affine relaxation carrier supplies the P718
target-general uniqueness certificate. -/
theorem unifiedAffineRelaxationUniquenessCertificate :
    UnifiedAffineRelaxationUniquenessCertificate where
  module_residual_unique := relaxModule_unique_of_target_residual_law
  scalar_residual_unique := relaxTo_unique_of_target_residual_law
  scalar_endpoint_unique := relaxTo_unique_of_target_rate_affine_endpoint_laws
  scalar_endpoint_residual_law :=
    target_residual_law_of_target_rate_affine_endpoint_laws
  target_one_is_bumpSat := target_one_unique_update_is_bumpSat
  interval_closure := relaxTo_unique_interval_closure

end AffineRelaxation
end SaturationMonoid
