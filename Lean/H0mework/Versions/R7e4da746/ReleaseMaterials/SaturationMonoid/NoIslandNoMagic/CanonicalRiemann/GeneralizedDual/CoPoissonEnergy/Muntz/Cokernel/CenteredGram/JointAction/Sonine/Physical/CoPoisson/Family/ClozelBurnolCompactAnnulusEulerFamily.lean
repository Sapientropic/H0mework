import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusAdditiveFamily
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import H0mework.Arithmetic.Tempered.RealStructure
import H0mework.Versions.R7e4da746.Arithmetic.RieszEuler.Weak

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CompactSourceEuler
open Complex MeasureTheory Set Filter
open scoped SchwartzMap Topology
noncomputable section

private def weighted (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) test

private theorem weighted_apply (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    weighted test x = (x : ℂ) * test x := by
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  exact SchwartzMap.smulLeftCLM_apply_apply growth test x

/-- The original normalized-dilation generator on the raw source. -/
def rawEuler (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (1 / 2 : ℂ) • test + weighted (SchwartzMap.derivCLM ℂ ℂ test)

theorem rawEuler_apply (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    rawEuler test x = (1 / 2 : ℂ) * test x + (x : ℂ) * deriv test x := by
  simp only [rawEuler, add_apply, smul_apply, smul_eq_mul, weighted_apply,
    SchwartzMap.derivCLM_apply]

private theorem derivative_zero_on (source : burnolCompactAnnulusSource)
    (s : Set ℝ) (unique : UniqueDiffOn ℝ s) (zero : ∀ x ∈ s, source.1 x = 0)
    {x : ℝ} (inside : x ∈ s) : deriv source.1 x = 0 := by
  have constant : HasDerivWithinAt (fun _ : ℝ => (0 : ℂ)) 0 s x :=
    hasDerivWithinAt_const x s 0
  have generated : HasDerivWithinAt source.1 0 s x :=
    constant.congr_of_mem zero inside
  exact UniqueDiffWithinAt.eq_deriv s (unique x inside)
    (source.1.hasDerivAt x).hasDerivWithinAt generated

private theorem derivative_inner (source : burnolCompactAnnulusSource)
    {x : ℝ} (inside : |x| ≤ (1 / 4 : ℝ)) : deriv source.1 x = 0 := by
  exact derivative_zero_on source (Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ))
    (uniqueDiffOn_Icc (by norm_num))
    (fun y hy => source.2.2.1 y (abs_le.mpr hy)) (abs_le.mp inside)

private theorem derivative_outer (source : burnolCompactAnnulusSource)
    {x : ℝ} (outside : (4 : ℝ) ≤ |x|) : deriv source.1 x = 0 := by
  rcases le_or_gt 0 x with nonnegative | negative
  · exact derivative_zero_on source (Ici (4 : ℝ)) (uniqueDiffOn_Ici 4)
      (fun y hy => source.2.2.2 y (hy.trans (le_abs_self y)))
      (by simpa only [mem_Ici, abs_of_nonneg nonnegative] using outside)
  · exact derivative_zero_on source (Iic (-4 : ℝ)) (uniqueDiffOn_Iic (-4))
      (fun y hy => source.2.2.2 y (by
        change y ≤ -4 at hy
        rw [abs_of_neg (by linarith)]
        linarith))
      (by change x ≤ -4; rw [abs_of_neg negative] at outside; linarith)

private theorem derivative_neg (source : burnolCompactAnnulusSource) (x : ℝ) :
    deriv source.1 (-x) = -deriv source.1 x := by
  have reflected := (source.1.hasDerivAt (-x)).scomp x (hasDerivAt_neg x)
  have same : (fun y : ℝ => source.1 (-y)) = source.1 :=
    funext source.2.1
  change HasDerivAt (fun y : ℝ => source.1 (-y))
    ((-1 : ℝ) • deriv source.1 (-x)) x at reflected
  rw [same] at reflected
  have equal := reflected.unique (source.1.hasDerivAt x)
  simp only [neg_smul, one_smul] at equal
  exact neg_eq_iff_eq_neg.mp equal

def sourceEuler (source : burnolCompactAnnulusSource) : burnolCompactAnnulusSource :=
  ⟨rawEuler source.1, (fun x => by
      rw [rawEuler_apply, rawEuler_apply, source.2.1, derivative_neg]
      push_cast
      ring),
    (fun x inside => by rw [rawEuler_apply, source.2.2.1 x inside,
      derivative_inner source inside]; ring),
    (fun x outside => by rw [rawEuler_apply, source.2.2.2 x outside,
      derivative_outer source outside]; ring)⟩

theorem normalization (source : burnolCompactAnnulusSource) :
    burnolCompactAdditiveNormalization (sourceEuler source) =
      -(1 / 2 : ℂ) * burnolCompactAdditiveNormalization source := by
  have weightedInt (test : SchwartzMap ℝ ℂ) :
      Integrable (fun x : ℝ => (x : ℂ) * test x) := by
    exact ((weighted test).integrable (μ := volume)).congr
      (ae_of_all volume (weighted_apply test))
  have original (x : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    exact Complex.ofRealCLM.hasDerivAt
  have parts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => original x) (fun x _ => source.1.hasDerivAt x)
    (by simpa only [SchwartzMap.derivCLM_apply, Pi.mul_def] using
      weightedInt (SchwartzMap.derivCLM ℂ ℂ source.1))
    (by simpa only [Pi.mul_def, one_mul] using (source.1.integrable (μ := volume)))
    (weightedInt source.1)
  change (1 / 2 : ℂ) * (∫ x : ℝ, rawEuler source.1 x) = _
  simp_rw [rawEuler_apply]
  rw [integral_add ((source.1.integrable (μ := volume)).const_mul _)
    (by simpa only [SchwartzMap.derivCLM_apply, Pi.mul_def] using
      weightedInt (SchwartzMap.derivCLM ℂ ℂ source.1)), integral_const_mul]
  simp only [one_mul] at parts
  rw [parts]
  unfold burnolCompactAdditiveNormalization
  ring

/-- The actual arithmetic source sum is locally a fixed finite sum. -/
theorem locally_finite (source : burnolCompactAnnulusSource) (x : ℝ) :
    let N := ⌊4 * (|x| + 1)⌋₊ + 1
    ∀ᶠ y : ℝ in 𝓝 x,
      burnolCompactAdditiveCoSum source y =
        (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ)⁻¹ *
          burnolCompactAdditiveSource source (y / (n + 1 : ℕ))) -
        burnolCompactAdditiveNormalization source := by
  let N : ℕ := ⌊4 * (|x| + 1)⌋₊ + 1
  change ∀ᶠ y : ℝ in 𝓝 x, _
  have neighborhood : ∀ᶠ y : ℝ in 𝓝 x, |y| < |x| + 1 :=
    (isOpen_lt continuous_abs (continuous_const : Continuous (fun _ : ℝ => |x| + 1))).mem_nhds
      (show |x| < |x| + 1 by linarith)
  filter_upwards [neighborhood] with y hy
  unfold burnolCompactAdditiveCoSum
  congr 1
  apply tsum_eq_sum
  intro n outside
  have index : N ≤ n := by simpa [N] using outside
  have bound : 4 * (|x| + 1) < (N : ℝ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (4 * (|x| + 1))
  have cast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast index
  rw [burnolCompactAdditiveSource_zero_of_abs_le_quarter]
  · exact mul_zero _
  · rw [abs_div, abs_of_pos (show (0 : ℝ) < (n + 1 : ℕ) by positivity)]
    apply (div_le_iff₀ (show (0 : ℝ) < (n + 1 : ℕ) by positivity)).mpr
    push_cast
    linarith

private def term (source : burnolCompactAnnulusSource) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ)⁻¹ * source.1 (((n + 1 : ℕ) : ℝ) * x⁻¹)

private theorem term_derivative (source : burnolCompactAnnulusSource)
    (n : ℕ) {x : ℝ} (nonzero : x ≠ 0) :
    HasDerivAt (term source n)
      (-((term (sourceEuler source) n x + (1 / 2 : ℂ) * term source n x) /
        (x : ℂ))) x := by
  have inverse := (Complex.ofRealCLM.hasDerivAt (x := x)).inv
    (Complex.ofReal_ne_zero.mpr nonzero)
  have argument := (hasDerivAt_inv nonzero).const_mul (((n + 1 : ℕ) : ℝ))
  have action := inverse.mul ((source.1.hasDerivAt _).scomp x argument)
  convert! action using 1
  change -( ((x : ℂ)⁻¹ * rawEuler source.1 (((n + 1 : ℕ) : ℝ) * x⁻¹) +
      (1 / 2 : ℂ) * ((x : ℂ)⁻¹ * source.1 (((n + 1 : ℕ) : ℝ) * x⁻¹))) /
      (x : ℂ)) = _
  rw [rawEuler_apply]
  simp only [Complex.real_smul, Complex.ofRealCLM_apply,
    Pi.inv_apply, Function.comp_apply]
  push_cast
  field_simp [nonzero]
  ring

/-- The compensated arithmetic sum carries the opposite source Euler action. -/
theorem positive_derivative (source : burnolCompactAnnulusSource)
    {x : ℝ} (positive : 0 < x) :
    HasDerivAt (burnolCompactAdditiveCoSum source)
      (-((burnolCompactAdditiveCoSum (sourceEuler source) x +
        (1 / 2 : ℂ) * burnolCompactAdditiveCoSum source x) / (x : ℂ))) x := by
  let N : ℕ := ⌊4 * (|x| + 1)⌋₊ + 1
  have finite (seed : burnolCompactAnnulusSource) :
      burnolCompactAdditiveCoSum seed =ᶠ[𝓝 x]
        (fun y => (∑ n ∈ Finset.range N, term seed n y) -
          burnolCompactAdditiveNormalization seed) := by
    filter_upwards [locally_finite seed x, Ioi_mem_nhds positive] with y actual hy
    rw [actual]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact burnolCompactAdditiveSource_div_nat seed hy n
  have derivative := (HasDerivAt.fun_sum (u := Finset.range N)
    (fun n _ => term_derivative source n positive.ne')).sub_const
      (burnolCompactAdditiveNormalization source)
  have generated := derivative.congr_of_eventuallyEq (finite source)
  apply generated.congr_deriv
  rw [(finite source).eq_of_nhds, (finite (sourceEuler source)).eq_of_nhds,
    normalization]
  simp only [Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring

theorem arithmetic_derivative (source : burnolCompactAnnulusSource) (x : ℝ) :
    HasDerivAt (burnolCompactAdditiveCoSum source)
      (-((burnolCompactAdditiveCoSum (sourceEuler source) x +
        (1 / 2 : ℂ) * burnolCompactAdditiveCoSum source x) / (x : ℂ))) x := by
  rcases lt_trichotomy 0 x with positive | zero | negative
  · exact positive_derivative source positive
  · subst x
    have localConstant : burnolCompactAdditiveCoSum source =ᶠ[𝓝 (0 : ℝ)]
        (fun _ => -burnolCompactAdditiveNormalization source) := by
      have small : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), |y| < (1 / 4 : ℝ) :=
        (isOpen_lt continuous_abs (continuous_const : Continuous (fun _ : ℝ => (1 / 4 : ℝ)))).mem_nhds
          (by norm_num)
      filter_upwards [small] with y hy
      exact burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter source hy.le
    simpa only [Complex.ofReal_zero, div_zero, neg_zero] using
      (hasDerivAt_const (0 : ℝ) (-burnolCompactAdditiveNormalization source)).congr_of_eventuallyEq
        localConstant
  · have reflected := (positive_derivative source (neg_pos.mpr negative)).scomp x (hasDerivAt_neg x)
    have same : (fun y : ℝ => burnolCompactAdditiveCoSum source (-y)) =
        burnolCompactAdditiveCoSum source :=
      funext (burnolCompactAdditiveCoSum_even source)
    change HasDerivAt (fun y : ℝ => burnolCompactAdditiveCoSum source (-y)) _ x at reflected
    rw [same] at reflected
    convert! reflected using 1
    simp only [neg_smul, one_smul, burnolCompactAdditiveCoSum_even,
      Complex.ofReal_neg, div_neg, neg_neg]

theorem arithmetic_euler (source : burnolCompactAnnulusSource) (x : ℝ) :
    (x : ℂ) * deriv (burnolCompactAdditiveCoSum source) x +
      (1 / 2 : ℂ) * burnolCompactAdditiveCoSum source x =
        -burnolCompactAdditiveCoSum (sourceEuler source) x := by
  by_cases zero : x = 0
  · subst x
    rw [burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
      source (by norm_num),
      burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
      (sourceEuler source) (by norm_num), normalization]
    simp
  · rw [(arithmetic_derivative source x).deriv]
    field_simp [Complex.ofReal_ne_zero.mpr zero]
    ring

def sourceStar (source : burnolCompactAnnulusSource) : burnolCompactAnnulusSource :=
  ⟨schwartzConjugation source.1,
    (fun x => by simp only [schwartzConjugation_apply, source.2.1]),
    (fun x inside => by simp only [schwartzConjugation_apply, source.2.2.1 x inside, star_zero]),
    (fun x outside => by simp only [schwartzConjugation_apply, source.2.2.2 x outside, star_zero])⟩

theorem normalization_star (source : burnolCompactAnnulusSource) :
    burnolCompactAdditiveNormalization (sourceStar source) =
      star (burnolCompactAdditiveNormalization source) := by
  unfold burnolCompactAdditiveNormalization
  change (1 / 2 : ℂ) * (∫ x : ℝ, star (source.1 x)) = star _
  have integralStar : (∫ x : ℝ, star (source.1 x)) = star (∫ x : ℝ, source.1 x) :=
    integral_conj
  rw [integralStar, star_mul]
  norm_num
  ring

theorem additiveSource_star (source : burnolCompactAnnulusSource) (x : ℝ) :
    burnolCompactAdditiveSource (sourceStar source) x =
      star (burnolCompactAdditiveSource source x) := by
  by_cases zero : x = 0
  · simp [burnolCompactAdditiveSource, zero]
  · simp only [burnolCompactAdditiveSource, zero, ↓reduceIte,
      sourceStar, schwartzConjugation_apply, star_mul, star_inv₀, Complex.star_def,
      Complex.conj_ofReal]
    ring

theorem coSum_star (source : burnolCompactAnnulusSource) (x : ℝ) :
    burnolCompactAdditiveCoSum (sourceStar source) x =
      star (burnolCompactAdditiveCoSum source x) := by
  unfold burnolCompactAdditiveCoSum
  rw [star_sub, tsum_star, normalization_star]
  congr 1
  apply tsum_congr
  intro n
  rw [additiveSource_star, star_mul, star_inv₀]
  simp only [star_natCast]
  ring

/-- The same raw arithmetic action realizes the source Euler law as a
full tempered-distribution equation. -/
theorem tempered_euler (source : burnolCompactAnnulusSource) :
    OriginalRieszSource.GapEuler.euler
      (burnolCompactAdditiveL2 source : TemperedDistribution ℝ ℂ) =
        -(burnolCompactAdditiveL2 (sourceEuler source) : TemperedDistribution ℝ ℂ) := by
  ext test
  let f := burnolCompactAdditiveCoSum source
  let g := burnolCompactAdditiveCoSum (sourceEuler source)
  have fLp : MemLp f 2 volume := burnolCompactAdditiveCoSum_memLp_full source
  have gLp : MemLp g 2 volume := burnolCompactAdditiveCoSum_memLp_full (sourceEuler source)
  have testLp : MemLp (test : ℝ → ℂ) 2 volume := test.memLp 2 volume
  have weightedLp (test : SchwartzMap ℝ ℂ) :
      MemLp (fun x : ℝ => (x : ℂ) * test x) 2 volume :=
    ((weighted test).memLp 2 volume).ae_eq (ae_of_all volume (weighted_apply test))
  have dtestLp : MemLp (fun x : ℝ => (x : ℂ) * deriv test x) 2 volume := by
    simpa only [SchwartzMap.derivCLM_apply] using
      weightedLp (SchwartzMap.derivCLM ℂ ℂ test)
  have firstInt := testLp.integrable_mul fLp
  have nextInt := testLp.integrable_mul gLp
  have slopeInt := dtestLp.integrable_mul fLp
  have actionInt : Integrable (fun x : ℝ => (x : ℂ) * test x * deriv f x) := by
    apply (nextInt.neg.sub (firstInt.const_mul (1 / 2 : ℂ))).congr
    filter_upwards with x
    have actual := arithmetic_euler source x
    change (x : ℂ) * deriv f x + (1 / 2 : ℂ) * f x = -g x at actual
    change -(test x * g x) - (1 / 2 : ℂ) * (test x * f x) =
      (x : ℂ) * test x * deriv f x
    linear_combination -(test x) * actual
  have differentiatedInt : Integrable
      (fun x : ℝ => (test x + (x : ℂ) * deriv test x) * f x) := by
    simpa only [Pi.add_def, Pi.mul_def, add_mul] using firstInt.add slopeInt
  have originalInt : Integrable (fun x : ℝ => (x : ℂ) * test x * f x) :=
    (weightedLp test).integrable_mul fLp
  have weightedDerivative (x : ℝ) :
      HasDerivAt (fun y : ℝ => (y : ℂ) * test y)
        (test x + (x : ℂ) * deriv test x) x := by
    convert! Complex.ofRealCLM.hasDerivAt.mul (test.hasDerivAt x) using 1
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
  have parts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => weightedDerivative x)
    (fun x _ => (arithmetic_derivative source x).differentiableAt.hasDerivAt)
    (by simpa only [Pi.mul_def] using actionInt)
    (by simpa only [Pi.mul_def] using differentiatedInt)
    (by simpa only [Pi.mul_def] using originalInt)
  have actionRead :
      (∫ x : ℝ, (x : ℂ) * test x * deriv f x) =
        -(∫ x : ℝ, test x * g x) - (1 / 2 : ℂ) * (∫ x : ℝ, test x * f x) := by
    have same : (fun x : ℝ => (x : ℂ) * test x * deriv f x) =
        (fun x => -(test x * g x) - (1 / 2 : ℂ) * (test x * f x)) := by
      funext x
      have actual := arithmetic_euler source x
      change (x : ℂ) * deriv f x + (1 / 2 : ℂ) * f x = -g x at actual
      linear_combination (test x) * actual
    rw [same]
    calc
      _ = (∫ x : ℝ, -(test x * g x)) -
          (∫ x : ℝ, (1 / 2 : ℂ) * (test x * f x)) :=
        integral_sub nextInt.neg (firstInt.const_mul _)
      _ = _ := by rw [integral_neg, integral_const_mul]
  have differentiatedRead :
      (∫ x : ℝ, (test x + (x : ℂ) * deriv test x) * f x) =
        (∫ x : ℝ, test x * f x) + (∫ x : ℝ, (x : ℂ) * deriv test x * f x) := by
    simp_rw [add_mul]
    exact integral_add firstInt slopeInt
  change (∫ x : ℝ, (x : ℂ) * test x * deriv f x) =
    -(∫ x : ℝ, (test x + (x : ℂ) * deriv test x) * f x) at parts
  rw [actionRead, differentiatedRead] at parts
  have rawRead (seed : burnolCompactAnnulusSource) (test : SchwartzMap ℝ ℂ) :
      (burnolCompactAdditiveL2 seed : TemperedDistribution ℝ ℂ) test =
        ∫ x : ℝ, test x * burnolCompactAdditiveCoSum seed x := by
    rw [Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [burnolCompactAdditiveL2_coeFn seed] with x actual
    rw [actual]
    rfl
  rw [OriginalRieszSource.Dilation.euler_test, rawRead, rawRead, neg_apply, rawRead]
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [SchwartzMap.smulLeftCLM_apply_apply growth,
    SchwartzMap.derivCLM_apply, smul_eq_mul]
  change -(1 / 2 : ℂ) * (∫ x : ℝ, test x * f x) -
    (∫ x : ℝ, (x : ℂ) * deriv test x * f x) = -(∫ x : ℝ, test x * g x)
  linear_combination -parts

end
end CompactSourceEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
