import H0mework.Arithmetic.Mellin.PositiveDomain
import H0mework.Arithmetic.Tempered.Remainder

/-!
# Variable co-Poisson orbit of the Clozel remainder

Positive scaling of Schwartz tests is constructed directly.  Change of
variables proves the scale/inverse-scale Fourier square, and the actual
self-Fourier remainder then gives an unconditional Tate law for the
half-weighted co-Poisson orbit.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelEndpointSourceEffect

open Complex FourierTransform MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

def realScaleEquiv (scale : ℝ) (nonzero : scale ≠ 0) :
    ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 scale nonzero)

def scaledSchwartzTest (scale : ℝ) (nonzero : scale ≠ 0)
    (test : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (realScaleEquiv scale nonzero) test

@[simp] theorem scaledSchwartzTest_apply
    (scale : ℝ) (nonzero : scale ≠ 0)
    (test : 𝓢(ℝ, ℂ)) (x : ℝ) :
    scaledSchwartzTest scale nonzero test x = test (scale * x) := by
  rfl

def coPoissonOrbitValue (scale : ℝ) (positive : 0 < scale)
    (test : 𝓢(ℝ, ℂ)) : ℂ :=
  (scale : ℂ) ^ (1 / 2 : ℂ) *
    clozelTemperedRemainder
      (scaledSchwartzTest scale positive.ne' test)

def coPoissonOrbitMap :
    𝓢(ℝ, ℂ) →ₗ[ℂ] (PositiveMellinReal → ℂ) where
  toFun test scale := coPoissonOrbitValue scale.1 scale.2 test
  map_add' left right := by
    funext scale
    unfold coPoissonOrbitValue scaledSchwartzTest
    rw [map_add, map_add]
    simp only [Pi.add_apply]
    ring
  map_smul' coefficient test := by
    funext scale
    unfold coPoissonOrbitValue scaledSchwartzTest
    rw [map_smul, map_smul]
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem clozelTemperedRemainder_fourier_test (test : 𝓢(ℝ, ℂ)) :
    clozelTemperedRemainder (𝓕 test) =
      clozelTemperedRemainder test := by
  have fixed := congrArg
    (fun distribution : ComplexTempered => distribution test)
    fourier_clozelTemperedRemainder
  simpa only [TemperedDistribution.fourier_apply] using fixed

theorem scaledSchwartzTest_fourier_apply
    (scale frequency : ℝ) (positive : 0 < scale)
    (test : 𝓢(ℝ, ℂ)) :
    𝓕 (scaledSchwartzTest scale positive.ne' test) frequency =
      (scale⁻¹ : ℝ) • 𝓕 test (frequency / scale) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  let integrand : ℝ → ℂ := fun y =>
    𝐞 (-(y * (frequency / scale))) • test y
  have changeVariables :=
    Measure.integral_comp_smul (volume : Measure ℝ) integrand scale
  have changeVariables' :
      (∫ x : ℝ, integrand (scale • x)) =
        (scale⁻¹ : ℝ) • ∫ y : ℝ, integrand y := by
    simpa only [Module.finrank_self, pow_one,
      abs_of_pos (inv_pos.mpr positive)] using changeVariables
  rw [← changeVariables']
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [integrand]
  rw [scaledSchwartzTest_apply]
  congr 2
  simp only [smul_eq_mul]
  field_simp [positive.ne']

theorem scaledSchwartzTest_fourier
    (scale : ℝ) (positive : 0 < scale)
    (test : 𝓢(ℝ, ℂ)) :
    𝓕 (scaledSchwartzTest scale positive.ne' test) =
      (scale⁻¹ : ℂ) •
        scaledSchwartzTest scale⁻¹ (inv_ne_zero positive.ne') (𝓕 test) := by
  ext frequency
  rw [scaledSchwartzTest_fourier_apply scale frequency positive test]
  dsimp [scaledSchwartzTest, realScaleEquiv]
  change ((scale⁻¹ : ℝ) : ℂ) * 𝓕 test (frequency / scale) =
    (scale : ℂ)⁻¹ * 𝓕 test (scale⁻¹ * frequency)
  rw [show (scale : ℂ)⁻¹ = ((scale⁻¹ : ℝ) : ℂ) by norm_num]
  congr 2
  field_simp [positive.ne']

theorem coPoissonOrbitValue_tate
    (scale : ℝ) (positive : 0 < scale)
    (test : 𝓢(ℝ, ℂ)) :
    coPoissonOrbitValue scale positive test =
      coPoissonOrbitValue scale⁻¹ (inv_pos.mpr positive) (𝓕 test) := by
  unfold coPoissonOrbitValue
  rw [← clozelTemperedRemainder_fourier_test
      (scaledSchwartzTest scale positive.ne' test),
    scaledSchwartzTest_fourier scale positive test]
  rw [map_smul]
  simp only [smul_eq_mul]
  have scaleCNe : (scale : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr positive.ne'
  have halfProduct :
      (scale : ℂ) ^ (1 / 2 : ℂ) * (scale⁻¹ : ℂ) =
        ((scale⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [show (scale⁻¹ : ℂ) = (scale : ℂ)⁻¹ by norm_num]
    have invAsCpow :
        (scale : ℂ)⁻¹ = (scale : ℂ) ^ (-(1 : ℂ)) := by
      rw [Complex.cpow_neg, Complex.cpow_one]
    rw [invAsCpow, ← Complex.cpow_add _ _ scaleCNe]
    rw [show (1 / 2 : ℂ) + -(1 : ℂ) = -(1 / 2 : ℂ) by norm_num]
    rw [show (((scale⁻¹ : ℝ) : ℂ)) = (scale : ℂ)⁻¹ by norm_num]
    rw [Complex.inv_cpow_ofReal_nonneg positive.le,
      Complex.cpow_neg]
  rw [← mul_assoc, halfProduct]

theorem coPoissonOrbitMap_tate
    (test : 𝓢(ℝ, ℂ)) (scale : PositiveMellinReal) :
    coPoissonOrbitMap test scale =
      coPoissonOrbitMap (𝓕 test)
        ⟨scale.1⁻¹, inv_pos.mpr scale.2⟩ :=
  coPoissonOrbitValue_tate scale.1 scale.2 test

end

end ClozelEndpointSourceEffect
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
