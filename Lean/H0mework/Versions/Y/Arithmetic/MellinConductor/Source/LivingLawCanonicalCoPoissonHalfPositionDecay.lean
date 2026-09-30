import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import H0mework.Versions.Y.Arithmetic.MellinConductor.HalfPositionDomain
import H0mework.Arithmetic.CoPoisson.MellinConvergence

/-!
# Co-Poisson decay enters the maximal half-position domain

The existing two-sided exponential bound remains square-integrable after
multiplication by the Quarter-Mellin coordinate `x/2`.  Hence every actual
co-Poisson relation test lands in the maximal half-position domain; no domain
membership is supplied by the caller.
-/

set_option autoImplicit false
namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor
namespace HalfPositionSource

open Complex MeasureTheory Set
open HalfPositionDomain
open scoped ENNReal SchwartzMap

noncomputable section

private theorem integrableOn_sq_mul_exp_neg_half_Ioi :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-x / 2)) (Ioi 0) := by
  have source := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (2 : ℝ)) (p := (1 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  refine source.congr_fun ?_ measurableSet_Ioi
  intro x hx
  change x ^ (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (1 : ℝ)) =
    x ^ (2 : Nat) * Real.exp (-x / 2)
  rw [Real.rpow_two, Real.rpow_one]
  rw [show -(1 / 2 : ℝ) * x = -x / 2 by ring]

private theorem integrable_abs_sq_mul_exp_neg_half :
    Integrable (fun x : ℝ => |x| ^ 2 * Real.exp (-|x| / 2)) := by
  rw [← integrableOn_univ,
    ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have sourceIci : IntegrableOn
        (fun x : ℝ => x ^ 2 * Real.exp (-x / 2)) (Ici 0) :=
      Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
        integrableOn_sq_mul_exp_neg_half_Ioi
    have reflected : IntegrableOn
        (fun x : ℝ => (-x) ^ 2 * Real.exp (-(-x) / 2)) (Iic 0) :=
      IntegrableOn.comp_neg_Iic
        (G := ℝ) (F := ℝ) (μ := volume) (c := (0 : ℝ))
        (f := fun x : ℝ => x ^ 2 * Real.exp (-x / 2))
        (by simpa only [neg_zero] using sourceIci)
    refine reflected.congr_fun ?_ measurableSet_Iic
    intro x hx
    change (-x) ^ 2 * Real.exp (-(-x) / 2) =
      |x| ^ 2 * Real.exp (-|x| / 2)
    rw [abs_of_nonpos hx]
  · refine integrableOn_sq_mul_exp_neg_half_Ioi.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change x ^ 2 * Real.exp (-x / 2) =
      |x| ^ 2 * Real.exp (-|x| / 2)
    rw [abs_of_pos (show 0 < x from hx)]

def coPoissonQuarterLogState (test : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fun x => coPoissonLogOrbitMap test (x / 2)

def coPoissonQuarterHalfPositionState
    (test : SchwartzMap ℝ ℂ) : ℝ → ℂ :=
  fun x => ((x / 2 : ℝ) : ℂ) * coPoissonQuarterLogState test x

private theorem coPoissonQuarterHalfPositionState_measurable
    (test : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (coPoissonQuarterHalfPositionState test)
      (volume : Measure ℝ) := by
  apply Measurable.aestronglyMeasurable
  apply Measurable.mul
  · fun_prop
  · exact (coPoissonLogOrbitMap_measurable test).comp (by fun_prop)

private theorem coPoissonQuarterHalfPositionState_norm_le
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖coPoissonQuarterHalfPositionState test x‖ ≤
      (coPoissonTwoSidedBound test * |x| / 2) *
        Real.exp (-|x| / 4) := by
  have orbitBound := coPoissonLogOrbitMap_norm_le_two_sided test (x / 2)
  have absHalf : |x / 2| = |x| / 2 := by
    rw [abs_div]
    norm_num
  rw [absHalf] at orbitBound
  change ‖((x / 2 : ℝ) : ℂ) * coPoissonLogOrbitMap test (x / 2)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, absHalf]
  calc
    |x| / 2 * ‖coPoissonLogOrbitMap test (x / 2)‖ ≤
        |x| / 2 *
          (coPoissonTwoSidedBound test * Real.exp (-(|x| / 2) / 2)) :=
      mul_le_mul_of_nonneg_left orbitBound (by positivity)
    _ = _ := by ring_nf

private theorem coPoissonQuarterHalfPositionState_sq_norm_le
    (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖coPoissonQuarterHalfPositionState test x‖ ^ 2 ≤
      (coPoissonTwoSidedBound test / 2) ^ 2 *
        (|x| ^ 2 * Real.exp (-|x| / 2)) := by
  have bound := coPoissonQuarterHalfPositionState_norm_le test x
  have rightNonnegative :
      0 ≤ (coPoissonTwoSidedBound test * |x| / 2) *
        Real.exp (-|x| / 4) := by
    apply mul_nonneg
    · exact div_nonneg
        (mul_nonneg (coPoissonTwoSidedBound_nonneg test) (abs_nonneg x))
        (by norm_num)
    · exact (Real.exp_pos _).le
  calc
    _ ≤ ((coPoissonTwoSidedBound test * |x| / 2) *
          Real.exp (-|x| / 4)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) rightNonnegative).2 bound
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf

theorem coPoissonQuarterHalfPositionState_memLp
    (test : SchwartzMap ℝ ℂ) :
    MemLp (coPoissonQuarterHalfPositionState test)
      (2 : ℝ≥0∞) (volume : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq_norm
    (coPoissonQuarterHalfPositionState_measurable test)).2
  have dominating := integrable_abs_sq_mul_exp_neg_half.const_mul
    ((coPoissonTwoSidedBound test / 2) ^ 2)
  apply dominating.mono'
  · have normMeasurable :=
      (coPoissonQuarterHalfPositionState_measurable test).norm
    exact (normMeasurable.aemeasurable.pow_const 2).aestronglyMeasurable
  · filter_upwards with x
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
      coPoissonQuarterHalfPositionState_sq_norm_le test x

theorem coPoissonQuarterFeature_coeFn
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    (quarterMellinL2Feature z
        (coPoissonQuarterMellinConvergentMap
          z positive belowHalf test) : ℝ → ℂ) =ᵐ[volume]
      coPoissonQuarterLogState test := by
  let value := coPoissonQuarterMellinConvergentMap
    z positive belowHalf test
  have toLpAE := value.2.1.coeFn_toLp
  filter_upwards [toLpAE] with x atPoint
  change quarterMellinL2Feature z value x = _
  rw [show quarterMellinL2Feature z value x =
      positiveMellinLogQuarterTransform value.1 x by exact atPoint]
  exact positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap test x

theorem coPoissonQuarterFeature_mem_halfPositionOperator_domain
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    quarterMellinL2Feature z
        (coPoissonQuarterMellinConvergentMap
          z positive belowHalf test) ∈
      HalfPositionOperator.domain := by
  rw [mem_halfPositionOperator_domain_iff]
  apply (memLp_congr_ae ?_).mpr
    (coPoissonQuarterHalfPositionState_memLp test)
  filter_upwards [coPoissonQuarterFeature_coeFn
    z positive belowHalf test] with x atPoint
  rw [atPoint]
  rfl

end
end HalfPositionSource
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
