import H0mework.Versions.Y.Arithmetic.RieszEuler.GapEulerSource
import H0mework.Versions.Y.Arithmetic.MellinProjection.FourierSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.GapEuler

open Complex FourierTransform LineDeriv
open scoped FourierTransform
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

private theorem schwartz_position_derivative (test : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) test) =
    test + SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
      (SchwartzMap.derivCLM ℂ ℂ test) := by
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  ext x
  have generated := (Complex.ofRealCLM.hasDerivAt (x := x)).mul (test.hasDerivAt x)
  change deriv (fun y : ℝ => (SchwartzMap.smulLeftCLM ℂ (fun t : ℝ => (t : ℂ)) test) y) x = _
  simp only [SchwartzMap.smulLeftCLM_apply growth, smul_eq_mul, add_apply, SchwartzMap.derivCLM_apply]
  exact (by simpa only [Pi.mul_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    using generated.deriv)

theorem derivative_position (value : TemperedDistribution ℝ ℂ) :
    TemperedDistribution.derivCLM ℂ (position value) =
      position (TemperedDistribution.derivCLM ℂ value) + value := by
  ext test
  simp only [position, TemperedDistribution.derivCLM_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, schwartz_position_derivative,
    map_neg, map_add, neg_add, add_apply]
  abel

theorem derivative_fourier (value : TemperedDistribution ℝ ℂ) :
    TemperedDistribution.derivCLM ℂ (𝓕 value) =
      (-(2 * (Real.pi : ℂ) * Complex.I)) • 𝓕 (position value) := by
  have source := TemperedDistribution.lineDerivOp_fourier_eq value (1 : ℝ)
  rw [← burnolTemperedDerivative_eq_lineOne] at source
  simpa only [Real.inner_apply, mul_one, position, FourierSMul.fourier_smul] using source

theorem fourier_derivative (value : TemperedDistribution ℝ ℂ) :
    𝓕 (TemperedDistribution.derivCLM ℂ value) =
      (2 * (Real.pi : ℂ) * Complex.I) • position (𝓕 value) := by
  have source := TemperedDistribution.fourier_lineDerivOp_eq value (1 : ℝ)
  rw [← burnolTemperedDerivative_eq_lineOne] at source
  simpa only [Real.inner_apply, mul_one, position] using source

theorem euler_fourier (value : TemperedDistribution ℝ ℂ) :
    euler (𝓕 value) = -𝓕 (euler value) := by
  have source := fourier_derivative (position value)
  rw [derivative_position, FourierAdd.fourier_add] at source
  unfold euler
  simp only [add_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, derivative_fourier, map_smul,
    FourierAdd.fourier_add, FourierSMul.fourier_smul]
  calc
    _ = -((2 * (Real.pi : ℂ) * Complex.I) • position (𝓕 (position value))) +
        (1 / 2 : ℂ) • 𝓕 value := by module
    _ = -(𝓕 (position (TemperedDistribution.derivCLM ℂ value)) + 𝓕 value) +
        (1 / 2 : ℂ) • 𝓕 value := by rw [← source]
    _ = _ := by module

end
end OriginalRieszSource.GapEuler
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
