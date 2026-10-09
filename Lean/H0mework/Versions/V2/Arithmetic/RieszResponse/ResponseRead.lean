import H0mework.Versions.V2.Arithmetic.RieszEuler.Weak
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteResponse

open Complex MeasureTheory
open scoped InnerProductSpace SchwartzMap
open OriginalRieszSource
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

private theorem distribution_read (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    (value : TemperedDistribution ℝ ℂ) test =
      inner ℂ (star (test.toLp 2 volume)) value := by
  rw [L2.inner_def, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (test.toLp 2 volume), test.coeFn_toLp 2 volume]
    with x hstar htest
  rw [hstar, Pi.star_apply, htest]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_star, smul_eq_mul]
  exact mul_comm _ _

theorem original_read (value : BurnolL2) (test : SchwartzMap ℝ ℂ) (h : ℝ) :
    (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) test =
      (value : TemperedDistribution ℝ ℂ)
        (coPoissonSchwartzEnergyTranslation (-h) test) := by
  rw [distribution_read, distribution_read]
  symm
  rw [← coPoissonSchwartzEnergyTranslationEquiv_apply,
    ← burnolMultiplicativeDilation_schwartz, burnolMultiplicativeDilation_star,
    (burnolMultiplicativeDilation (-h)).inner_map_eq_flip,
    ← burnolMultiplicativeDilation_neg_eq_symm (-h), neg_neg]

private def eulerCotest (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  -(1 / 2 : ℂ) • test -
    SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
      (SchwartzMap.derivCLM ℂ ℂ test)

private theorem eulerCotest_apply (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    eulerCotest test x = -(1 / 2 : ℂ) * test x - (x : ℂ) * deriv test x := by
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [eulerCotest, sub_apply, smul_apply, SchwartzMap.smulLeftCLM_apply growth,
    SchwartzMap.derivCLM_apply, smul_eq_mul]

private theorem eulerCotest_read (value : TemperedDistribution ℝ ℂ)
    (test : SchwartzMap ℝ ℂ) : GapEuler.euler value test = value (eulerCotest test) := by
  rw [Dilation.euler_test]
  simp only [eulerCotest, map_sub, map_smul, smul_eq_mul]

private theorem eulerCotest_action (test : SchwartzMap ℝ ℂ) (h : ℝ) :
    coPoissonSchwartzEnergyTranslation h (eulerCotest test) =
      eulerCotest (coPoissonSchwartzEnergyTranslation h test) := by
  ext x
  have derivative := (test.hasDerivAt (Real.exp h * x)).scomp x
    ((hasDerivAt_id x).const_mul (Real.exp h))
  have normalized := derivative.const_mul ((Real.exp h : ℂ) ^ (1 / 2 : ℂ))
  have sourceDerivative : deriv (coPoissonSchwartzEnergyTranslation h test) x =
      (Real.exp h : ℂ) ^ (1 / 2 : ℂ) *
        ((Real.exp h : ℂ) * deriv test (Real.exp h * x)) := by
    change deriv (fun y : ℝ => (Real.exp h : ℂ) ^ (1 / 2 : ℂ) *
      test (Real.exp h * y)) x = _
    exact (by simpa only [Complex.real_smul, id_eq, Function.comp_apply, mul_one]
      using normalized.deriv)
  rw [eulerCotest_apply, sourceDerivative]
  change (Real.exp h : ℂ) ^ (1 / 2 : ℂ) *
      eulerCotest test (Real.exp h * x) = _
  rw [eulerCotest_apply]
  change _ = -(1 / 2 : ℂ) *
    ((Real.exp h : ℂ) ^ (1 / 2 : ℂ) * test (Real.exp h * x)) - _
  push_cast
  ring

theorem original_euler_action (value : BurnolL2) (test : SchwartzMap ℝ ℂ) (h : ℝ) :
    GapEuler.euler (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) test =
      GapEuler.euler (value : TemperedDistribution ℝ ℂ)
        (coPoissonSchwartzEnergyTranslation (-h) test) := by
  rw [eulerCotest_read, original_read, eulerCotest_action, ← eulerCotest_read]

end
end OriginalRieszFiniteResponse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
