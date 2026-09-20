import H0mework.Realization.Residual.P719

/-!
# Proposition 720: residual accounting uniquely induces cross-target geometry

P719 proves that residual accounting forces the same-target noisy-OR action.

This file closes the complementary cross-target face.  Any update family
`f target sigma x` satisfying target residual accounting is forced to have the
same raw cross-target commutator as `relaxModule`, and the same positive
translation-transport law that conjugates one target chart to another.  Thus
cross-target obstruction and target transport are not auxiliary choices; they
are the unique geometry induced by the residual accounting law.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Forced cross-target obstruction -/

/-- THEOREM 1: any residual-accounted update family has the forced
cross-target commutator. -/
theorem residualLaw_cross_target_commutator
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target1 target2 x : E) (sigma1 sigma2 : K) :
    f target2 sigma2 (f target1 sigma1 x) -
        f target1 sigma1 (f target2 sigma2 x) =
      (sigma1 * sigma2) • (target2 - target1) := by
  have hf := residualLaw_unique_step f hres
  rw [hf target1 sigma1 x, hf target2 sigma2 (relaxModule target1 sigma1 x),
    hf target2 sigma2 x, hf target1 sigma1 (relaxModule target2 sigma2 x)]
  exact relaxModule_cross_target_commutator target1 target2 x sigma1 sigma2

/-! ## Forced target transport -/

/-- THEOREM 2: translation by `target₂-target₁` is the forced conjugacy
between residual-accounted target charts. -/
theorem residualLaw_transport_conjugate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target1 target2 x : E) (sigma : K) :
    translateModule (target2 - target1)
        (f target1 sigma
          (translateModule (target1 - target2) x)) =
      f target2 sigma x := by
  have hf := residualLaw_unique_step f hres
  rw [hf target1 sigma (translateModule (target1 - target2) x),
    hf target2 sigma x]
  exact relaxModule_transport_conjugate target1 target2 x sigma

/-- THEOREM 3: after target transport, residual-accounted same-target steps
compose by the forced noisy-OR rate. -/
theorem residualLaw_transport_compose
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (target1 target2 x : E) (sigma1 sigma2 : K) :
    translateModule (target2 - target1)
        (f target1 sigma2
          (f target1 sigma1
            (translateModule (target1 - target2) x))) =
      f target2 (satOrField sigma1 sigma2) x := by
  have hf := residualLaw_unique_step f hres
  rw [hf target1 sigma1 (translateModule (target1 - target2) x),
    hf target1 sigma2
      (relaxModule target1 sigma1 (translateModule (target1 - target2) x)),
    hf target2 (satOrField sigma1 sigma2) x]
  exact relaxModule_transport_compose target1 target2 x sigma1 sigma2

/-- THEOREM 4: direct relaxation toward a target is forced to equal
transported relaxation from any source chart. -/
theorem residualLaw_transport_then_direct
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : E -> K -> E -> E)
    (hres : TargetResidualLaw f)
    (sourceTarget target x : E) (sigma : K) :
    f target sigma x =
      translateModule (target - sourceTarget)
        (f sourceTarget sigma
          (translateModule (sourceTarget - target) x)) := by
  have hf := residualLaw_unique_step f hres
  rw [hf target sigma x,
    hf sourceTarget sigma (translateModule (sourceTarget - target) x)]
  exact relaxModule_transport_then_direct sourceTarget target x sigma

/-! ## Certificate -/

/-- P720 certificate: residual accounting uniquely induces the raw
cross-target commutator and the positive affine transport law. -/
structure ResidualAccountedCrossTargetGeometryCertificate
    (K E : Type*) [Field K] [AddCommGroup E] [Module K E] : Prop where
  cross_target_commutator_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target1 target2 x : E, ∀ sigma1 sigma2 : K,
        f target2 sigma2 (f target1 sigma1 x) -
            f target1 sigma1 (f target2 sigma2 x) =
          (sigma1 * sigma2) • (target2 - target1)
  transport_conjugates_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target1 target2 x : E, ∀ sigma : K,
        translateModule (target2 - target1)
            (f target1 sigma
              (translateModule (target1 - target2) x)) =
          f target2 sigma x
  noisy_or_after_transport_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ target1 target2 x : E, ∀ sigma1 sigma2 : K,
        translateModule (target2 - target1)
            (f target1 sigma2
              (f target1 sigma1
                (translateModule (target1 - target2) x))) =
          f target2 (satOrField sigma1 sigma2) x
  transported_direct_unique :
    ∀ f : E -> K -> E -> E,
      TargetResidualLaw f ->
      ∀ sourceTarget target x : E, ∀ sigma : K,
        f target sigma x =
          translateModule (target - sourceTarget)
            (f sourceTarget sigma
              (translateModule (sourceTarget - target) x))

/-- THEOREM 5: residual accounting supplies the unique cross-target geometry
certificate. -/
theorem residualAccountedCrossTargetGeometryCertificate
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] :
    ResidualAccountedCrossTargetGeometryCertificate K E where
  cross_target_commutator_unique := residualLaw_cross_target_commutator
  transport_conjugates_unique := residualLaw_transport_conjugate
  noisy_or_after_transport_unique := residualLaw_transport_compose
  transported_direct_unique := residualLaw_transport_then_direct

end AffineRelaxation
end SaturationMonoid
