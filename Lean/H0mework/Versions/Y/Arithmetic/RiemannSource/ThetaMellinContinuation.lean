import H0mework.Versions.Y.Arithmetic.RiemannSource.ThetaWeakFEPair

/-!
# Mellin continuation generated from canonical theta material

The completed and uncompleted analytic functions below are defined from the
generated weak FE-pair.  Equality with Mathlib's Riemann functions is a
downstream identification, not their source definition.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex

noncomputable section

noncomputable def generatedCompletedRiemannZeta
    (owner : GlobalGermOwner) (s : ℂ) : ℂ :=
  ((GeneratedRiemannWeakFEPairAt.generate owner).pair.Λ (s / 2)) / 2

noncomputable def generatedCompletedRiemannZeta₀
    (owner : GlobalGermOwner) (s : ℂ) : ℂ :=
  ((GeneratedRiemannWeakFEPairAt.generate owner).pair.Λ₀ (s / 2)) / 2

theorem generatedCompletedRiemannZeta_eq_mathlib
    (owner : GlobalGermOwner) (s : ℂ) :
    generatedCompletedRiemannZeta owner s = completedRiemannZeta s := by
  rfl

theorem generatedCompletedRiemannZeta₀_eq_mathlib
    (owner : GlobalGermOwner) (s : ℂ) :
    generatedCompletedRiemannZeta₀ owner s = completedRiemannZeta₀ s := by
  rfl

/-- The corrected Mellin completion is entire. -/
theorem differentiable_generatedCompletedRiemannZeta₀
    (owner : GlobalGermOwner) :
    Differentiable ℂ (generatedCompletedRiemannZeta₀ owner) := by
  exact (((GeneratedRiemannWeakFEPairAt.generate owner).pair.differentiable_Λ₀.comp
    (differentiable_id.div_const _)).div_const _)

/-- Pole disposition is computed from the generated zero mode at `0` and
its dual constant at `1`. -/
theorem generatedCompletedRiemannZeta_pole_normal_form
    (owner : GlobalGermOwner) (s : ℂ) :
    generatedCompletedRiemannZeta owner s =
      generatedCompletedRiemannZeta₀ owner s - 1 / s - 1 / (1 - s) := by
  rw [generatedCompletedRiemannZeta_eq_mathlib,
    generatedCompletedRiemannZeta₀_eq_mathlib,
    completedRiemannZeta_eq]

/-- The completed functional equation is inherited from the FE-pair whose
kernels were already identified with finite source folds. -/
theorem generatedCompletedRiemannZeta_one_sub
    (owner : GlobalGermOwner) (s : ℂ) :
    generatedCompletedRiemannZeta owner (1 - s) =
      generatedCompletedRiemannZeta owner s := by
  rw [generatedCompletedRiemannZeta_eq_mathlib,
    generatedCompletedRiemannZeta_eq_mathlib,
    completedRiemannZeta_one_sub]

/-- The uncompleted analytic coordinate is built from the generated Mellin
completion and its generated zero-mode value. -/
noncomputable def generatedRiemannZeta
    (owner : GlobalGermOwner) : ℂ → ℂ :=
  Function.update
    (fun s => generatedCompletedRiemannZeta owner s / Gammaℝ s)
    0 (-1 / 2)

theorem generatedRiemannZeta_eq_mathlib (owner : GlobalGermOwner) :
    generatedRiemannZeta owner = riemannZeta := by
  funext s
  by_cases zero : s = 0
  · subst s
    simp [generatedRiemannZeta, riemannZeta,
      HurwitzZeta.hurwitzZetaEven]
  · rw [generatedRiemannZeta, riemannZeta,
      HurwitzZeta.hurwitzZetaEven,
      Function.update_of_ne zero, Function.update_of_ne zero,
      generatedCompletedRiemannZeta_eq_mathlib,
      HurwitzZeta.completedHurwitzZetaEven_zero]

/-- Analytic continuation now belongs to the source-generated function. -/
theorem analyticOn_generatedRiemannZeta_awayOne
    (owner : GlobalGermOwner) :
    AnalyticOnNhd ℂ (generatedRiemannZeta owner) ({1} : Set ℂ)ᶜ := by
  rw [generatedRiemannZeta_eq_mathlib]
  exact analyticOn_riemannZeta

/-- Exact Mellin incidence before the completed normalization by `2`. -/
theorem generatedTheta_hasMellin
    (owner : GlobalGermOwner) {s : ℂ} (rightHalfPlane : 1 < s.re) :
    HasMellin
      ((GeneratedRiemannWeakFEPairAt.generate owner).pair.f · -
        (GeneratedRiemannWeakFEPairAt.generate owner).pair.f₀)
      (s / 2)
      ((GeneratedRiemannWeakFEPairAt.generate owner).pair.Λ (s / 2)) := by
  apply GeneratedRiemannWeakFEPairAt.generate_hasMellin
  rw [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos]
  exact rightHalfPlane

theorem generatedThetaMellin_eq_two_mul_completed
    (owner : GlobalGermOwner) (s : ℂ) :
    (GeneratedRiemannWeakFEPairAt.generate owner).pair.Λ (s / 2) =
      2 * generatedCompletedRiemannZeta owner s := by
  unfold generatedCompletedRiemannZeta
  ring

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
