import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import H0mework.Arithmetic.Muntz.CoPoissonMuntzStripReadback
import H0mework.Arithmetic.Muntz.CoPoissonMuntzDirichletSeed

/-!
# General co-Poisson--Müntz value factorization

Clearing the common pole at one extends the Dirichlet seed across the whole
positive half-plane.  The actual scale remainder and square-root quarter
chart therefore factor through the same zeta occurrence and the arbitrary
Schwartz even-source Mellin transform.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex FourierTransform MeasureTheory Set Filter Asymptotics
open ClozelEndpointSourceEffect
open scoped SchwartzMap RealInnerProductSpace Topology

noncomputable section

private def coPoissonMuntzOnePoleCleared
    (P : WeakFEPair ℂ) (s : ℂ) : ℂ :=
  (s - 1) * P.Λ₀ s - ((s - 1) / s) * P.f₀ + P.ε * P.g₀

private theorem coPoissonMuntzOnePoleCleared_eq
    (P : WeakFEPair ℂ) (weightOne : P.k = 1)
    {s : ℂ} (notOne : s ≠ 1) :
    coPoissonMuntzOnePoleCleared P s = (s - 1) * P.Λ s := by
  unfold coPoissonMuntzOnePoleCleared WeakFEPair.Λ
  rw [weightOne]
  simp only [ofReal_one, smul_eq_mul]
  field_simp [notOne]
  ring

private theorem coPoissonMuntzOnePoleCleared_analyticOn
    (P : WeakFEPair ℂ) :
    AnalyticOnNhd ℂ (coPoissonMuntzOnePoleCleared P)
      {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s positive
    unfold coPoissonMuntzOnePoleCleared
    have notZero : s ≠ 0 := by
      intro zero
      subst s
      norm_num at positive
    have subDifferentiable :
        DifferentiableAt ℂ (fun w : ℂ => w - 1) s :=
      differentiableAt_id.sub (differentiableAt_const (1 : ℂ))
    have quotientDifferentiable :
        DifferentiableAt ℂ (fun w : ℂ => (w - 1) / w) s :=
      subDifferentiable.div differentiableAt_id notZero
    exact (((subDifferentiable.mul
      (P.differentiable_Λ₀ s)).sub
        (quotientDifferentiable.mul_const P.f₀)).add
          (differentiableAt_const (P.ε * P.g₀))).differentiableWithinAt
  · exact isOpen_lt continuous_const continuous_re

private theorem coPoissonMuntzRightHalfPlane_isPreconnected :
    IsPreconnected {s : ℂ | 0 < s.re} := by
  exact ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm).isPreconnected

theorem coPoissonMuntzWeakFEPair_lambda_factorization
    (test : SchwartzMap ℝ ℂ) {s : ℂ}
    (positive : 0 < s.re) (belowOne : s.re < 1) :
    (coPoissonMuntzWeakFEPair test).Λ s =
      riemannZeta s * coPoissonMuntzEvenSourceMellin test s := by
  let P := coPoissonMuntzWeakFEPair test
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  let leftCleared : ℂ → ℂ := coPoissonMuntzOnePoleCleared P
  let rightCleared : ℂ → ℂ := fun w =>
    riemannZeta₁ w * coPoissonMuntzEvenSourceMellin test w
  have leftAnalytic : AnalyticOnNhd ℂ leftCleared U := by
    exact coPoissonMuntzOnePoleCleared_analyticOn P
  have rightAnalytic : AnalyticOnNhd ℂ rightCleared U := by
    apply DifferentiableOn.analyticOnNhd
    · intro w hw
      exact (differentiable_riemannZeta₁.differentiableAt.mul
        (coPoissonMuntzEvenSourceMellin_differentiableAt test w hw)).differentiableWithinAt
    · exact isOpen_lt continuous_const continuous_re
  have seedCleared : ∀ w : ℂ, 1 < w.re →
      leftCleared w = rightCleared w := by
    intro w hw
    have notOne : w ≠ 1 := by
      intro equality
      subst w
      norm_num at hw
    rw [show leftCleared w = (w - 1) * P.Λ w by
      exact coPoissonMuntzOnePoleCleared_eq P rfl notOne]
    rw [coPoissonMuntzWeakFEPair_lambda_dirichletSeed test w hw]
    unfold rightCleared
    rw [riemannZeta_eq_inv_sub_mul notOne]
    field_simp [notOne]
  have globalCleared : Set.EqOn leftCleared rightCleared U := by
    apply leftAnalytic.eqOn_of_preconnected_of_eventuallyEq
      rightAnalytic coPoissonMuntzRightHalfPlane_isPreconnected
      (z₀ := (2 : ℂ))
    · norm_num [U]
    · exact eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by norm_num : 1 < (2 : ℂ).re))
        (fun w hw => seedCleared w hw)
  have notOne : s ≠ 1 := by
    intro equality
    subst s
    norm_num at belowOne
  have atS := globalCleared (show s ∈ U by exact positive)
  have leftAtS : leftCleared s = (s - 1) * P.Λ s :=
    coPoissonMuntzOnePoleCleared_eq P rfl notOne
  have rightAtS : rightCleared s =
      (s - 1) * (riemannZeta s * coPoissonMuntzEvenSourceMellin test s) := by
    unfold rightCleared
    rw [riemannZeta_eq_inv_sub_mul notOne]
    field_simp [notOne]
  rw [leftAtS, rightAtS] at atS
  exact mul_left_cancel₀ (sub_ne_zero.mpr notOne) atS

theorem coPoissonMuntzScaleRemainder_mellin_factorization
    (test : SchwartzMap ℝ ℂ) {s : ℂ}
    (positive : 0 < s.re) (belowOne : s.re < 1) :
    mellin (coPoissonMuntzScaleRemainder test) s =
      riemannZeta s * coPoissonMuntzEvenSourceMellin test s := by
  rw [coPoissonMuntzScaleRemainder_mellin_eq_weakFEPair
    test s positive belowOne]
  exact coPoissonMuntzWeakFEPair_lambda_factorization
    test positive belowOne

def coPoissonQuarterMuntzSourceMellin
    (test : SchwartzMap ℝ ℂ) (z : ℂ) : ℂ :=
  2 * coPoissonMuntzEvenSourceMellin test (2 * z)

theorem positiveMellinExtension_coPoissonQuarterMellinMap_mellin_eq
    (test : SchwartzMap ℝ ℂ) (z : ℂ) :
    mellin (positiveMellinExtension (coPoissonQuarterMellinMap test)) z =
      2 * mellin (coPoissonMuntzScaleRemainder test) (2 * z) := by
  rw [positiveMellinExtension_quarter_eq_scaleRemainder_rpow]
  rw [mellin_comp_rpow]
  norm_num [smul_eq_mul]
  congr 2
  field_simp

theorem positiveMellinExtension_coPoissonQuarterMellinMap_factorization
    (test : SchwartzMap ℝ ℂ) {z : ℂ}
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    mellin (positiveMellinExtension (coPoissonQuarterMellinMap test)) z =
      riemannZeta (2 * z) * coPoissonQuarterMuntzSourceMellin test z := by
  rw [positiveMellinExtension_coPoissonQuarterMellinMap_mellin_eq]
  rw [coPoissonMuntzScaleRemainder_mellin_factorization test
    (by norm_num [Complex.mul_re]; linarith)
    (by norm_num [Complex.mul_re]; linarith)]
  unfold coPoissonQuarterMuntzSourceMellin
  ring

theorem quarterMellinL2Functional_coPoissonQuarterMellinConvergentMap
    (test : SchwartzMap ℝ ℂ) (z : ℂ)
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    quarterMellinL2Functional z
        (coPoissonQuarterMellinConvergentMap
          z positive belowHalf test) =
      riemannZeta (2 * z) * coPoissonQuarterMuntzSourceMellin test z := by
  exact positiveMellinExtension_coPoissonQuarterMellinMap_factorization
    test positive belowHalf

theorem quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0) :
    (quarterMellinL2Functional z).comp
      (coPoissonQuarterMellinConvergentMap z positive belowHalf) = 0 := by
  ext test
  change quarterMellinL2Functional z
      (coPoissonQuarterMellinConvergentMap
        z positive belowHalf test) = 0
  rw [quarterMellinL2Functional_coPoissonQuarterMellinConvergentMap,
    zero, zero_mul]


end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
