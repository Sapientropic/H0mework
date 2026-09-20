import H0mework.Arithmetic.CoPoisson.QuarterChart
import H0mework.Arithmetic.Mellin.QuarterTest

/-!
# Mellin convergence of the square-root co-Poisson quarter chart

The existing chart identifies the quarter-log transform of an actual
Schwartz orbit with `x ↦ coPoissonLogOrbitMap test (x / 2)`.  Its two-sided
decay makes the Mellin integrand integrable exactly throughout
`0 < re z < 1/2`.  This file packages that source theorem as a linear map to
the existing quarter-`L²` Mellin test carrier and records complementary
Fourier/Tate naturality.  It proves no Mellin value identity or zero.
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

open Complex MeasureTheory Set
open ClozelEndpointSourceEffect
open scoped SchwartzMap ENNReal

noncomputable section

def coPoissonQuarterMellinLogIntegrand
    (z : ℂ) (test : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  (Real.exp x : ℂ) ^ (z - (1 / 4 : ℂ)) *
    coPoissonLogOrbitMap test (x / 2)

private theorem mellinConvergent_of_logQuarter_integrable
    (z : ℂ) (f : ClozelPositiveMellinFunction)
    (logIntegrable : Integrable (fun x : ℝ =>
      (Real.exp x : ℂ) ^ (z - (1 / 4 : ℂ)) *
        positiveMellinLogQuarterTransform f x)) :
    MellinConvergent (positiveMellinExtension f) z := by
  let weighted : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (z - 1) • positiveMellinExtension f t
  have changeVariables :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      (fun _ _ _ _ equality => Real.exp_injective equality)
      weighted
  rw [Set.image_univ, Real.range_exp] at changeVariables
  unfold MellinConvergent
  change IntegrableOn weighted (Ioi 0)
  apply changeVariables.mpr
  rw [integrableOn_univ]
  apply logIntegrable.congr
  filter_upwards with x
  unfold weighted
  simp only [abs_of_pos (Real.exp_pos x),
    positiveMellinLogQuarterTransform, positiveMellinExtension,
    LinearMap.coe_mk, AddHom.coe_mk, dif_pos (Real.exp_pos x),
    real_smul, smul_eq_mul]
  have baseNe : (Real.exp x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)
  have quarterWeight :
      (Real.exp (x / 4) : ℂ) =
        (Real.exp x : ℂ) ^ (1 / 4 : ℂ) := by
    calc
      _ = ((Real.exp x ^ (1 / 4 : ℝ) : ℝ) : ℂ) := by
        congr 1
        rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
        congr 1
        ring
      _ = _ := by
        convert Complex.ofReal_cpow (Real.exp_pos x).le (1 / 4 : ℝ)
          using 1
        all_goals norm_num
  have leftWeight :
      (Real.exp x : ℂ) ^ (z - (1 / 4 : ℂ)) *
          (Real.exp (x / 4) : ℂ) =
        (Real.exp x : ℂ) ^ z := by
    rw [quarterWeight, ← Complex.cpow_add _ _ baseNe]
    congr 2
    ring
  have rightWeight :
      (Real.exp x : ℂ) * (Real.exp x : ℂ) ^ (z - 1) =
        (Real.exp x : ℂ) ^ z := by
    calc
      _ = (Real.exp x : ℂ) ^ (1 : ℂ) *
          (Real.exp x : ℂ) ^ (z - 1) := by
        rw [Complex.cpow_one]
      _ = (Real.exp x : ℂ) ^ ((1 : ℂ) + (z - 1)) := by
        rw [Complex.cpow_add _ _ baseNe]
      _ = _ := by congr 2; ring
  change (Real.exp x : ℂ) ^ (z - (1 / 4 : ℂ)) *
      ((Real.exp (x / 4) : ℂ) * f ⟨Real.exp x, Real.exp_pos x⟩) =
    (Real.exp x : ℂ) * ((Real.exp x : ℂ) ^ (z - 1) *
      f ⟨Real.exp x, Real.exp_pos x⟩)
  calc
    _ = ((Real.exp x : ℂ) ^ (z - (1 / 4 : ℂ)) *
        (Real.exp (x / 4) : ℂ)) *
      f ⟨Real.exp x, Real.exp_pos x⟩ := by rw [mul_assoc]
    _ = (Real.exp x : ℂ) ^ z *
      f ⟨Real.exp x, Real.exp_pos x⟩ := by rw [leftWeight]
    _ = ((Real.exp x : ℂ) * (Real.exp x : ℂ) ^ (z - 1)) *
      f ⟨Real.exp x, Real.exp_pos x⟩ := by rw [rightWeight]
    _ = _ := by rw [mul_assoc]

private theorem coPoissonQuarterMellinLogIntegrand_aestronglyMeasurable
    (z : ℂ) (test : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (coPoissonQuarterMellinLogIntegrand z test)
      (volume : Measure ℝ) := by
  unfold coPoissonQuarterMellinLogIntegrand
  apply Measurable.aestronglyMeasurable
  apply Measurable.mul
  · apply Continuous.measurable
    apply Continuous.cpow (by fun_prop) continuous_const
    intro x
    exact Complex.ofReal_mem_slitPlane.2 (Real.exp_pos x)
  · exact (coPoissonLogOrbitMap_measurable test).comp (by fun_prop)

private theorem norm_coPoissonQuarterMellinLogIntegrand_le_of_nonpos
    (z : ℂ) (test : SchwartzMap ℝ ℂ) {x : ℝ} (hx : x ≤ 0) :
    ‖coPoissonQuarterMellinLogIntegrand z test x‖ ≤
      coPoissonTwoSidedBound test * Real.exp (z.re * x) := by
  unfold coPoissonQuarterMellinLogIntegrand
  rw [norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos x)]
  have orbitBound := coPoissonLogOrbitMap_norm_le_two_sided test (x / 2)
  calc
    Real.exp x ^ (z - (1 / 4 : ℂ)).re *
        ‖coPoissonLogOrbitMap test (x / 2)‖ ≤
      Real.exp x ^ (z - (1 / 4 : ℂ)).re *
        (coPoissonTwoSidedBound test *
          Real.exp (-|x / 2| / 2)) := by
      exact mul_le_mul_of_nonneg_left orbitBound
        (Real.rpow_nonneg (Real.exp_pos x).le _)
    _ = coPoissonTwoSidedBound test * Real.exp (z.re * x) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp,
        abs_of_nonpos (by linarith : x / 2 ≤ 0)]
      calc
        Real.exp (x * (z - (1 / 4 : ℂ)).re) *
            (coPoissonTwoSidedBound test *
              Real.exp (- -(x / 2) / 2)) =
          coPoissonTwoSidedBound test *
            (Real.exp (x * (z - (1 / 4 : ℂ)).re) *
              Real.exp (- -(x / 2) / 2)) := by ring
        _ = coPoissonTwoSidedBound test *
            Real.exp (x * (z - (1 / 4 : ℂ)).re +
              (- -(x / 2) / 2)) := by rw [Real.exp_add]
        _ = _ := by
          congr 2
          norm_num [Complex.div_re]
          ring

private theorem norm_coPoissonQuarterMellinLogIntegrand_le_of_nonneg
    (z : ℂ) (test : SchwartzMap ℝ ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖coPoissonQuarterMellinLogIntegrand z test x‖ ≤
      coPoissonTwoSidedBound test *
        Real.exp ((z.re - 1 / 2) * x) := by
  unfold coPoissonQuarterMellinLogIntegrand
  rw [norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (Real.exp_pos x)]
  have orbitBound := coPoissonLogOrbitMap_norm_le_two_sided test (x / 2)
  calc
    Real.exp x ^ (z - (1 / 4 : ℂ)).re *
        ‖coPoissonLogOrbitMap test (x / 2)‖ ≤
      Real.exp x ^ (z - (1 / 4 : ℂ)).re *
        (coPoissonTwoSidedBound test *
          Real.exp (-|x / 2| / 2)) := by
      exact mul_le_mul_of_nonneg_left orbitBound
        (Real.rpow_nonneg (Real.exp_pos x).le _)
    _ = coPoissonTwoSidedBound test *
        Real.exp ((z.re - 1 / 2) * x) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp,
        abs_of_nonneg (by linarith : 0 ≤ x / 2)]
      calc
        Real.exp (x * (z - (1 / 4 : ℂ)).re) *
            (coPoissonTwoSidedBound test *
              Real.exp (-(x / 2) / 2)) =
          coPoissonTwoSidedBound test *
            (Real.exp (x * (z - (1 / 4 : ℂ)).re) *
              Real.exp (-(x / 2) / 2)) := by ring
        _ = coPoissonTwoSidedBound test *
            Real.exp (x * (z - (1 / 4 : ℂ)).re +
              (-(x / 2) / 2)) := by rw [Real.exp_add]
        _ = _ := by
          congr 2
          norm_num [Complex.div_re]
          ring

theorem coPoissonQuarterMellinLogIntegrand_integrable
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    Integrable (coPoissonQuarterMellinLogIntegrand z test) := by
  rw [← integrableOn_univ,
    ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have dominating : IntegrableOn (fun x : ℝ =>
        coPoissonTwoSidedBound test * Real.exp (z.re * x))
        (Iic 0) :=
      (integrableOn_exp_mul_Iic positive 0).const_mul _
    apply dominating.mono'
    · exact (coPoissonQuarterMellinLogIntegrand_aestronglyMeasurable
        z test).mono_measure Measure.restrict_le_self
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      have bound :=
        norm_coPoissonQuarterMellinLogIntegrand_le_of_nonpos
          z test hx
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (coPoissonTwoSidedBound_nonneg test)
          (Real.exp_pos _).le)] using bound
  · have exponentNegative : z.re - 1 / 2 < 0 := by linarith
    have dominating : IntegrableOn (fun x : ℝ =>
        coPoissonTwoSidedBound test *
          Real.exp ((z.re - 1 / 2) * x)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi exponentNegative 0).const_mul _
    apply dominating.mono'
    · exact (coPoissonQuarterMellinLogIntegrand_aestronglyMeasurable
        z test).mono_measure Measure.restrict_le_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have bound :=
        norm_coPoissonQuarterMellinLogIntegrand_le_of_nonneg
          z test hx.le
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (coPoissonTwoSidedBound_nonneg test)
          (Real.exp_pos _).le)] using bound

theorem positiveMellinExtension_coPoissonQuarterMellinMap_mellinConvergent
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    MellinConvergent
      (positiveMellinExtension (coPoissonQuarterMellinMap test)) z := by
  apply mellinConvergent_of_logQuarter_integrable
  apply (coPoissonQuarterMellinLogIntegrand_integrable
    z positive belowHalf test).congr
  filter_upwards with x
  rw [positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap]
  rfl

/-- The actual square-root co-Poisson chart lands linearly in the existing
quarter-`L²` Mellin test carrier throughout the complementary strip. -/
def coPoissonQuarterMellinConvergentMap
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] QuarterMellinL2Test z where
  toFun test :=
    ⟨coPoissonQuarterMellinMap test,
      ⟨coPoissonQuarterMellinMap_mem_quarterL2 test,
        positiveMellinExtension_coPoissonQuarterMellinMap_mellinConvergent
          z positive belowHalf test⟩⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add coPoissonQuarterMellinMap left right
  map_smul' coefficient test := by
    apply Subtype.ext
    exact map_smul coPoissonQuarterMellinMap coefficient test

@[simp]
theorem coPoissonQuarterMellinConvergentMap_value
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    (coPoissonQuarterMellinConvergentMap
      z positive belowHalf test).1 = coPoissonQuarterMellinMap test :=
  rfl

/-- Fourier/Tate naturality keeps the same actual source while switching to
the complementary Mellin parameter. -/
theorem coPoissonQuarterMellinConvergentMap_fourier_tate
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    (coPoissonQuarterMellinConvergentMap z positive belowHalf
      (FourierTransform.fourier test)).1 =
      positiveTateInvolution
        ((coPoissonQuarterMellinConvergentMap
          ((1 / 2 : ℂ) - z)
          (by norm_num [Complex.div_re]; linarith)
          (by norm_num [Complex.div_re]; linarith) test).1) := by
  exact coPoissonQuarterMellinMap_fourier_tate test

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
