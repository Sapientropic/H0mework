import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.GeneratorStrong

/-! The same isometric dilation generates the two-parameter Gram identity and its Fourier-fixed real diagonal. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem strong_pair {x y vx vy : BurnolL2}
    (xs : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) x) vx 0)
    (ys : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) y) vy 0) :
    inner ℂ x vy + inner ℂ vx y = 0 := by
  have actual := xs.inner ℂ ys
  have constant : (fun h : ℝ => inner ℂ
      (burnolMultiplicativeDilation (-h / 2) x)
      (burnolMultiplicativeDilation (-h / 2) y)) = fun _ => inner ℂ x y :=
    funext fun h => (burnolMultiplicativeDilation (-h / 2)).inner_map_map x y
  change HasDerivAt (fun h : ℝ => inner ℂ
    (burnolMultiplicativeDilation (-h / 2) x) (burnolMultiplicativeDilation (-h / 2) y)) _ 0 at actual
  rw [constant] at actual
  have zero := actual.unique (hasDerivAt_const (0 : ℝ) (inner ℂ x y))
  simpa only [neg_zero, zero_div, burnolMultiplicativeDilation_zero] using zero

theorem burnolDirectRightResolvent_gram (z w : ℂ)
    (zr : 1 / 4 < z.re) (wr : 1 / 4 < w.re) (value : BurnolL2) :
    inner ℂ value (burnolDirectRightResolvent z value) +
      star (inner ℂ value (burnolDirectRightResolvent w value)) =
    -(z + star w - 1 / 2) *
      inner ℂ (burnolDirectRightResolvent w value) (burnolDirectRightResolvent z value) := by
  let x := burnolDirectRightResolvent w value
  let y := burnolDirectRightResolvent z value
  have zero := strong_pair
    (burnolDirectRightResolventOrbit_hasDerivAt w wr value)
    (burnolDirectRightResolventOrbit_hasDerivAt z zr value)
  change inner ℂ x ((z - 1 / 4) • y + value) +
    inner ℂ ((w - 1 / 4) • x + value) y = 0 at zero
  rw [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right] at zero
  change inner ℂ value y + star (inner ℂ value x) =
    -(z + star w - 1 / 2) * inner ℂ x y
  simp only [Complex.star_def, map_sub, map_div₀, map_one, map_ofNat] at zero ⊢
  rw [inner_conj_symm x value]
  linear_combination zero

theorem burnolDirectRightResolvent_realDiagonal (r : ℝ) (rr : 1 / 4 < r) (value : BurnolL2)
    (fixed : fourierL2 value = value) :
    inner ℂ value (burnolDirectRightResolvent (r : ℂ) value) =
      -((r : ℂ) - 1 / 4) * (‖burnolDirectRightResolvent (r : ℂ) value‖ : ℂ) ^ 2 := by
  let d := burnolDirectRightResolvent (r : ℂ) value
  have strong := burnolDirectRightResolventOrbit_hasDerivAt (r : ℂ) rr value
  have dual := burnolFourierOrbit_hasDerivAt _ _ strong
  have trace := strong_pair dual strong
  change inner ℂ (fourierL2 d) (((r : ℂ) - 1 / 4) • d + value) +
    inner ℂ (-fourierL2 (((r : ℂ) - 1 / 4) • d + value)) d = 0 at trace
  simp only [map_add, map_smul, inner_add_right, inner_add_left, inner_neg_left,
    inner_smul_right, inner_smul_left, fixed] at trace
  have scalar : (starRingEnd ℂ) ((r : ℂ) - 1 / 4) = (r : ℂ) - 1 / 4 := by
    simp only [map_sub, map_div₀, map_ofNat, map_one, Complex.conj_ofReal]
  have pairing : inner ℂ (fourierL2 d) value = inner ℂ d value := by
    have same := fourierL2.inner_map_map d value
    rwa [fixed] at same
  rw [scalar, pairing] at trace
  have symmetric : inner ℂ value d = star (inner ℂ value d) := by
    rw [Complex.star_def, inner_conj_symm d value]
    linear_combination -trace
  have gram := burnolDirectRightResolvent_gram (r : ℂ) (r : ℂ) rr rr value
  change inner ℂ value d + star (inner ℂ value d) =
    -((r : ℂ) + star (r : ℂ) - 1 / 2) * inner ℂ d d at gram
  rw [← symmetric, inner_self_eq_norm_sq_to_K] at gram
  simp only [Complex.star_def, Complex.conj_ofReal] at gram
  change inner ℂ value d = -((r : ℂ) - 1 / 4) * (‖d‖ : ℂ) ^ 2
  linear_combination (1 / 2 : ℂ) * gram

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
