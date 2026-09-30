import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.ProjectedSourceCompact
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The original compact source generates a signed Euler current and both Green boundary terms. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
theorem burnolFirstSourceCoefficient_euler (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    (t : ℂ) * burnolFirstSourceCoefficientSlope coordinate source t =
      (coordinate.value - 1) * burnolFirstSourceCoefficient coordinate source t +
        4 * source.1 t := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have power₁ : (t : ℂ) * (t : ℂ) ^ (coordinate.value - 2) =
      (t : ℂ) ^ (coordinate.value - 1) := by
    nth_rw 1 [← Complex.cpow_one (t : ℂ)]
    rw [← Complex.cpow_add _ _ nonzero]
    congr 1
    ring
  have power₂ : (t : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
      (t : ℂ) ^ (-coordinate.value) = 1 := by
    nth_rw 1 [← Complex.cpow_one (t : ℂ)]
    rw [← Complex.cpow_add _ _ nonzero,
      ← Complex.cpow_add _ _ nonzero]
    convert Complex.cpow_zero (t : ℂ) using 2
    ring
  unfold burnolFirstSourceCoefficientSlope burnolFirstSourceCoefficient burnolFirstSourceDensity
  rw [max_eq_right (show (1 / 8 : ℝ) ≤ t by linarith [inside.1])]
  calc
    _ = -(2 : ℂ) * (coordinate.value - 1) *
        ((t : ℂ) * (t : ℂ) ^ (coordinate.value - 2)) *
          (∫ u : ℝ in t..4, burnolFirstSourceDensity coordinate source u) +
        4 * ((t : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
          (t : ℂ) ^ (-coordinate.value)) * source.1 t := by
            dsimp only [burnolFirstSourceDensity]
            ring
    _ = _ := by
      rw [power₁, power₂]
      dsimp only [burnolFirstSourceDensity]
      ring

theorem burnolFirstSourceCoefficient_outer (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    burnolFirstSourceCoefficient coordinate source 4 = 0 := by
  simp [burnolFirstSourceCoefficient]

theorem burnolCompactSourceGreen_flux (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    HasDerivAt (fun u : ℝ => u * ‖burnolFirstSourceCoefficient coordinate source u‖ ^ 2)
      ((2 * coordinate.value.re - 1) * ‖burnolFirstSourceCoefficient coordinate source t‖ ^ 2 +
        8 * (star (burnolFirstSourceCoefficient coordinate source t) * source.1 t).re) t := by
  let f := burnolFirstSourceCoefficient coordinate source t
  let d := burnolFirstSourceCoefficientSlope coordinate source t
  have law := burnolFirstSourceCoefficient_euler coordinate source inside
  have flux := (hasDerivAt_id t).mul
    (burnolFirstSourceCoefficient_hasDerivAt coordinate source inside).norm_sq
  convert! flux using 1
  simp only [id, one_mul]
  change (2 * coordinate.value.re - 1) * ‖f‖ ^ 2 + 8 * (star f * source.1 t).re =
    ‖f‖ ^ 2 + t * (2 * inner ℝ f d)
  change (t : ℂ) * d = (coordinate.value - 1) * f + 4 * source.1 t at law
  have re := congrArg Complex.re law
  have im := congrArg Complex.im law
  norm_num [Complex.mul_re, Complex.mul_im] at re im
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  linear_combination -2 * f.re * re - 2 * f.im * im

theorem burnolCompactSourceGreen_identity (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    let f := burnolFirstSourceCoefficient coordinate source;
    -8 * (∫ t : ℝ in (1 / 4 : ℝ)..4, (star (f t) * source.1 t).re) =
      (2 * coordinate.value.re - 1) * (∫ t : ℝ in (1 / 4 : ℝ)..4, ‖f t‖ ^ 2) +
        (1 / 4 : ℝ) * ‖f (1 / 4)‖ ^ 2 := by
  let f := burnolFirstSourceCoefficient coordinate source
  have regular : Continuous f := burnolFirstSourceCoefficient_continuous coordinate source
  have energyInt : IntervalIntegrable (fun t : ℝ => ‖f t‖ ^ 2) volume (1 / 4) 4 :=
    (regular.norm.pow 2).intervalIntegrable (μ := volume) (1 / 4 : ℝ) 4
  have couplingInt : IntervalIntegrable (fun t : ℝ => (star (f t) * source.1 t).re)
      volume (1 / 4) 4 := (Complex.continuous_re.comp
    (regular.star.mul source.1.continuous)).intervalIntegrable
    (μ := volume) (1 / 4 : ℝ) 4
  have current := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 / 4 : ℝ)) (b := (4 : ℝ))
    (fun t inside => burnolCompactSourceGreen_flux coordinate source
      (by simpa only [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 4)] using inside))
    ((energyInt.const_mul _).add (couplingInt.const_mul 8))
  change (∫ t : ℝ in (1 / 4 : ℝ)..4,
      (2 * coordinate.value.re - 1) * ‖f t‖ ^ 2 +
        8 * (star (f t) * source.1 t).re) =
      4 * ‖f 4‖ ^ 2 - (1 / 4 : ℝ) * ‖f (1 / 4)‖ ^ 2 at current
  rw [intervalIntegral.integral_add (energyInt.const_mul (2 * coordinate.value.re - 1))
      (couplingInt.const_mul 8),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at current
  have outer : f 4 = 0 := burnolFirstSourceCoefficient_outer coordinate source
  rw [outer, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at current
  change -8 * (∫ t : ℝ in (1 / 4 : ℝ)..4, (star (f t) * source.1 t).re) = _
  linarith

theorem burnolCompactSourceGreen_endpoint (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    burnolFirstSourceCoefficient coordinate source (1 / 4) =
      -(2 : ℂ) * ((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) *
        burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source) := by
  rw [burnolFirstSourceCoefficient_raw coordinate source (by constructor <;> norm_num),
    burnolFirstSource_rawInner coordinate.value source (by norm_num) le_rfl,
    burnolPaResolventSourceCoefficient_compact]
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
