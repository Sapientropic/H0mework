import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import H0mework.Arithmetic.Mellin.QuarterEnergy
import H0mework.Arithmetic.CoPoisson.PositiveDecay

/-!
# Two-sided co-Poisson quarter-energy carrier

Fourier reflection transports the public positive-end decay to the negative
end.  The resulting `exp (-|x| / 2)` majorant constructs a genuine `Lp ℂ 2`
value for every actual Schwartz test and bundles the construction linearly.
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

open Complex FourierTransform MeasureTheory Filter
open ClozelEndpointSourceEffect
open scoped SchwartzMap RealInnerProductSpace ENNReal

noncomputable section

private theorem complexExp_cpow_half (x : ℝ) :
    (Real.exp x : ℂ) ^ (1 / 2 : ℂ) = (Real.exp (x / 2) : ℂ) := by
  calc
    _ = ((Real.exp x ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      symm
      convert Complex.ofReal_cpow (Real.exp_pos x).le (1 / 2 : ℝ) using 1
      all_goals norm_num
    _ = _ := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
      congr 1
      ring

theorem coPoissonLogOrbitMap_measurable (test : SchwartzMap ℝ ℂ) :
    Measurable (coPoissonLogOrbitMap test) := by
  rw [show coPoissonLogOrbitMap test = fun x : ℝ =>
      (Real.exp x : ℂ) ^ (1 / 2 : ℂ) *
        ((∑' n : {n : ℤ // n ≠ 0}, test (Real.exp x * (n.1 : ℝ))) -
          Real.exp (-x) • ∫ y : ℝ, test y) by
    funext x
    exact coPoissonLogOrbitMap_nonzero_formula test x]
  have hweight : Continuous (fun x : ℝ =>
      (Real.exp x : ℂ) ^ (1 / 2 : ℂ)) := by
    simp_rw [complexExp_cpow_half]
    fun_prop
  have hsummand : ∀ n : {n : ℤ // n ≠ 0},
      Measurable (fun x : ℝ => test (Real.exp x * (n.1 : ℝ))) := by
    intro n
    exact (test.continuous.comp
      (Real.continuous_exp.mul continuous_const)).measurable
  have hsum : Measurable (fun x : ℝ =>
      ∑' n : {n : ℤ // n ≠ 0}, test (Real.exp x * (n.1 : ℝ))) :=
    Measurable.tsum hsummand
  have hintegral : Continuous (fun x : ℝ =>
      Real.exp (-x) • ∫ y : ℝ, test y) := by fun_prop
  exact hweight.measurable.mul (hsum.sub hintegral.measurable)

def coPoissonTwoSidedBound (test : SchwartzMap ℝ ℂ) : ℝ :=
  max (coPoissonPositiveBound test)
    (coPoissonPositiveBound (FourierTransform.fourier test))

theorem coPoissonTwoSidedBound_nonneg (test : SchwartzMap ℝ ℂ) :
    0 ≤ coPoissonTwoSidedBound test :=
  (coPoissonPositiveBound_nonneg test).trans (le_max_left _ _)

theorem coPoissonLogOrbitMap_norm_le_two_sided
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖coPoissonLogOrbitMap test x‖ ≤
      coPoissonTwoSidedBound test * Real.exp (-|x| / 2) := by
  rcases le_total 0 x with hx | hx
  · calc
      _ ≤ coPoissonPositiveBound test * Real.exp (-x / 2) :=
        coPoissonLogOrbitMap_norm_le_positive test hx
      _ ≤ coPoissonTwoSidedBound test * Real.exp (-x / 2) := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ = _ := by rw [abs_of_nonneg hx]
  · have hpositive : 0 ≤ -x := neg_nonneg.mpr hx
    rw [← coPoissonLogOrbitMap_fourier_reflection test x]
    calc
      _ ≤ coPoissonPositiveBound (FourierTransform.fourier test) *
          Real.exp (-(-x) / 2) :=
        coPoissonLogOrbitMap_norm_le_positive
          (FourierTransform.fourier test) hpositive
      _ ≤ coPoissonTwoSidedBound test * Real.exp (-(-x) / 2) := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
      _ = _ := by rw [abs_of_nonpos hx]

private theorem integrable_exp_neg_abs :
    Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)),
    integrableOn_union]
  constructor
  · refine (integrableOn_exp_Iic 0).congr_fun ?_ measurableSet_Iic
    intro x hx
    change x ≤ 0 at hx
    simp [abs_of_nonpos hx]
  · refine (integrableOn_exp_neg_Ioi 0).congr_fun ?_ measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    simp [abs_of_pos hx]

private theorem coPoissonLogOrbitMap_sq_norm_le
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖coPoissonLogOrbitMap test x‖ ^ 2 ≤
      coPoissonTwoSidedBound test ^ 2 * Real.exp (-|x|) := by
  have hnorm := coPoissonLogOrbitMap_norm_le_two_sided test x
  have hright : 0 ≤ coPoissonTwoSidedBound test * Real.exp (-|x| / 2) :=
    mul_nonneg (coPoissonTwoSidedBound_nonneg test) (Real.exp_pos _).le
  calc
    _ ≤ (coPoissonTwoSidedBound test * Real.exp (-|x| / 2)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hright).2 hnorm
    _ = _ := by
      rw [mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Every actual Schwartz test has a two-sided logarithmic co-Poisson
`L²` orbit. -/
theorem coPoissonLogOrbitMap_memLp (test : SchwartzMap ℝ ℂ) :
    MemLp (coPoissonLogOrbitMap test) (2 : ℝ≥0∞)
      (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (coPoissonLogOrbitMap test)
      (volume : Measure ℝ) :=
    (coPoissonLogOrbitMap_measurable test).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have hdom : Integrable (fun x : ℝ =>
      coPoissonTwoSidedBound test ^ 2 * Real.exp (-|x|)) :=
    integrable_exp_neg_abs.const_mul _
  apply hdom.mono'
  · exact (hmeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
      coPoissonLogOrbitMap_sq_norm_le test x

/-- Source-owned linear realization in the quarter-energy carrier. -/
def coPoissonLogOrbitEnergyMap :
    SchwartzMap ℝ ℂ →ₗ[ℂ] PositiveMellinQuarterEnergy where
  toFun test := (coPoissonLogOrbitMap_memLp test).toLp
  map_add' left right := by
    simpa only [map_add] using
      MemLp.toLp_add (coPoissonLogOrbitMap_memLp left)
        (coPoissonLogOrbitMap_memLp right)
  map_smul' coefficient test := by
    simpa only [map_smul, RingHom.id_apply] using
      MemLp.toLp_const_smul coefficient (coPoissonLogOrbitMap_memLp test)

theorem coPoissonLogOrbitEnergyMap_coeFn (test : SchwartzMap ℝ ℂ) :
    (coPoissonLogOrbitEnergyMap test : ℝ → ℂ) =ᵐ[(volume : Measure ℝ)]
      coPoissonLogOrbitMap test :=
  MemLp.coeFn_toLp (coPoissonLogOrbitMap_memLp test)

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
