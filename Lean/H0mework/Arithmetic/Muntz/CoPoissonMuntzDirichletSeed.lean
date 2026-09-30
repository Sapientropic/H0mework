import H0mework.Arithmetic.Muntz.CoPoissonMuntzWeakFEPair
import H0mework.Arithmetic.Muntz.CoPoissonMuntzDirichletSource

/-!
# Dirichlet seed for the arbitrary-Schwartz co-Poisson--Müntz formula

Absolute convergence on `re s > 1` justifies exchange of the positive
integer sum and Mellin integral.  Dilation then factors the theta Mellin
value as the source-owned Riemann zeta function times the even source Mellin
transform.
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

theorem coPoissonMuntzThetaNonzero_mellin_eq_zeta_mul_evenSourceMellin
    (test : SchwartzMap ℝ ℂ) (s : ℂ) (one_lt : 1 < s.re) :
    mellin (coPoissonMuntzThetaNonzero test) s =
      riemannZeta s * coPoissonMuntzEvenSourceMellin test s := by
  let term : ℕ → ℝ → ℂ := fun n t =>
    (t : ℂ) ^ (s - 1) * coPoissonMuntzEvenSource test
      (((n + 1 : ℕ) : ℝ) * t)
  have sourceConvergent := coPoissonMuntzEvenSource_mellinConvergent
    test s (zero_lt_one.trans one_lt)
  have termIntegrable (n : ℕ) : Integrable (term n)
      (volume.restrict (Ioi 0)) := by
    have scalePositive : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    have scaledConvergent := (MellinConvergent.comp_mul_left
      (f := coPoissonMuntzEvenSource test) (s := s)
      scalePositive).2 sourceConvergent
    change IntegrableOn (term n) (Ioi 0)
    simpa only [MellinConvergent, term, smul_eq_mul] using scaledConvergent
  let baseNormIntegral : ℝ :=
    ∫ t : ℝ in Ioi 0,
      ‖(t : ℂ) ^ (s - 1) * coPoissonMuntzEvenSource test t‖
  have coefficientSummable : Summable (fun n : ℕ =>
      ((((n + 1 : ℕ) : ℝ)) ^ (-s.re))) := by
    have source := (Real.summable_one_div_nat_add_rpow 1 s.re).2 one_lt
    refine source.congr ?_
    intro n
    rw [Real.rpow_neg (by positivity)]
    simp only [one_div]
    congr 2
    norm_num
    positivity
  have normIntegralSummable : Summable (fun n : ℕ =>
      ∫ t : ℝ, ‖term n t‖ ∂(volume.restrict (Ioi 0))) := by
    refine (coefficientSummable.mul_right baseNormIntegral).congr ?_
    intro n
    rw [show (∫ t : ℝ, ‖term n t‖ ∂(volume.restrict (Ioi 0))) =
        ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) *
          coPoissonMuntzEvenSource test
            ((((n + 1 : ℕ) : ℝ)) * t)‖ by rfl]
    exact (integral_norm_mellin_comp_mul_left
      (coPoissonMuntzEvenSource test) s
      (scale := (((n + 1 : ℕ) : ℝ))) (by positivity)).symm
  have interchange := integral_tsum_of_summable_integral_norm
    termIntegrable normIntegralSummable
  have pointwise (t : ℝ) (positive : t ∈ Ioi (0 : ℝ)) :
      (t : ℂ) ^ (s - 1) * coPoissonMuntzThetaNonzero test t =
        ∑' n : ℕ, term n t := by
    rw [coPoissonMuntzThetaNonzero_eq_positive_tsum test positive.ne']
    rw [tsum_mul_left]
  have mellinAsSum : mellin (coPoissonMuntzThetaNonzero test) s =
      ∑' n : ℕ, ∫ t : ℝ, term n t ∂(volume.restrict (Ioi 0)) := by
    unfold mellin
    simp only [smul_eq_mul]
    rw [interchange]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positive
    exact pointwise t positive
  rw [mellinAsSum]
  have termIntegral (n : ℕ) :
      (∫ t : ℝ, term n t ∂(volume.restrict (Ioi 0))) =
        ((((n + 1 : ℕ) : ℂ)) ^ (-s)) *
          coPoissonMuntzEvenSourceMellin test s := by
    change mellin (fun t : ℝ => coPoissonMuntzEvenSource test
      ((((n + 1 : ℕ) : ℝ)) * t)) s = _
    rw [mellin_comp_mul_left]
    rfl
    positivity
  rw [show (∑' n : ℕ,
      ∫ t : ℝ, term n t ∂(volume.restrict (Ioi 0))) =
      ∑' n : ℕ, ((((n + 1 : ℕ) : ℂ)) ^ (-s)) *
        coPoissonMuntzEvenSourceMellin test s by
    apply tsum_congr
    exact termIntegral]
  have complexCoefficientSummable : Summable (fun n : ℕ =>
      ((((n + 1 : ℕ) : ℂ)) ^ s)⁻¹) := by
    have source := Complex.summable_one_div_nat_cpow.mpr one_lt
    refine (source.comp_injective Nat.succ_injective).congr ?_
    intro n
    simp only [Function.comp_apply, one_div]
  simp_rw [Complex.cpow_neg]
  rw [complexCoefficientSummable.tsum_mul_right]
  have coefficientValue :
      (∑' n : ℕ, ((((n + 1 : ℕ) : ℂ)) ^ s)⁻¹) =
        riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow one_lt]
    apply tsum_congr
    intro n
    simp only [one_div]
    congr 2
    norm_num
  rw [coefficientValue]

theorem coPoissonMuntzWeakFEPair_lambda_dirichletSeed
    (test : SchwartzMap ℝ ℂ) (s : ℂ) (one_lt : 1 < s.re) :
    (coPoissonMuntzWeakFEPair test).Λ s =
      riemannZeta s * coPoissonMuntzEvenSourceMellin test s := by
  let P := coPoissonMuntzWeakFEPair test
  have source := P.hasMellin one_lt
  have functionEq : (P.f · - P.f₀) =
      coPoissonMuntzThetaNonzero test := by
    funext scale
    simp only [P, coPoissonMuntzWeakFEPair,
      coPoissonMuntzTheta, add_sub_cancel_right]
  rw [functionEq] at source
  rw [← source.2]
  exact coPoissonMuntzThetaNonzero_mellin_eq_zeta_mul_evenSourceMellin
    test s one_lt


end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
