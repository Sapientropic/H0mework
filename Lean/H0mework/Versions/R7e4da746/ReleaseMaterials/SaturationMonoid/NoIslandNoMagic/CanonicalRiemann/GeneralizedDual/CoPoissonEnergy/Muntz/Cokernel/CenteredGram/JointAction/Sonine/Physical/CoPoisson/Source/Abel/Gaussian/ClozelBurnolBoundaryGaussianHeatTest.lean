import H0mework.Arithmetic.BurnolMellin.GaussianHeatPair
import H0mework.Versions.R7e4da746.Arithmetic.MuntzAction.GaussianCoPoissonRelation

/-! The Fourier dual Gaussian test, with both source zero modes retained. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform Filter MeasureTheory Set Asymptotics
open ClozelEndpointSourceEffect
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

private theorem clozelGaussianSchwartz_eq_burnolRaw (x : ℝ) :
    clozelGaussianSchwartz x = burnolGaussianRaw 1 x := by
  rw [clozelGaussianSchwartz_apply, burnolGaussianRaw]
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  ring_nf

private theorem fourier_clozelGaussianSchwartz_eq_burnolRaw (x : ℝ) :
    FourierTransform.fourier clozelGaussianSchwartz x = burnolGaussianRaw 1 x := by
  rw [SchwartzMap.fourier_coe]
  have raw : (clozelGaussianSchwartz : ℝ → ℂ) = burnolGaussianRaw 1 := by
    funext y
    exact clozelGaussianSchwartz_eq_burnolRaw y
  rw [raw, fourier_burnolGaussianRaw (by norm_num)]
  simp [burnolGaussianReciprocalScale]

def burnolBoundaryGaussianHeatTest (scale : ℝ) (positive : 0 < scale) :
    SchwartzMap ℝ ℂ :=
  let a := (Real.sqrt scale)⁻¹
  (a : ℂ) • scaledSchwartzTest a
    (inv_ne_zero (Real.sqrt_pos.2 positive).ne') clozelGaussianSchwartz

theorem fourier_burnolBoundaryGaussianHeatTest
    (scale : ℝ) (positive : 0 < scale) (x : ℝ) :
    FourierTransform.fourier (burnolBoundaryGaussianHeatTest scale positive) x =
      burnolGaussianRaw scale x := by
  let r := Real.sqrt scale
  have rpos : 0 < r := Real.sqrt_pos.2 positive
  have apos : 0 < r⁻¹ := inv_pos.mpr rpos
  dsimp only [burnolBoundaryGaussianHeatTest]
  change (SchwartzMap.fourierTransformCLM ℂ
    (((r⁻¹ : ℝ) : ℂ) • scaledSchwartzTest r⁻¹ (inv_ne_zero rpos.ne')
      clozelGaussianSchwartz)) x = _
  rw [map_smul]
  simp only [smul_apply, SchwartzMap.fourierTransformCLM_apply]
  rw [scaledSchwartzTest_fourier_apply r⁻¹ x apos clozelGaussianSchwartz,
    fourier_clozelGaussianSchwartz_eq_burnolRaw]
  have coefficient : (((r⁻¹ : ℝ) : ℂ) * (((r⁻¹)⁻¹ : ℝ) : ℂ)) = 1 := by
    push_cast
    field_simp [rpos.ne']
  simp only [smul_eq_mul, real_smul]
  rw [← mul_assoc, coefficient, one_mul]
  unfold burnolGaussianRaw
  congr 1
  push_cast
  have square : r ^ 2 = scale := Real.sq_sqrt positive.le
  have squareC : (r : ℂ) ^ 2 = (scale : ℂ) := by exact_mod_cast square
  rw [div_inv_eq_mul, mul_pow, squareC]
  ring_nf

@[simp] theorem burnolBoundaryGaussianHeatTest_zero
    (scale : ℝ) (positive : 0 < scale) :
    burnolBoundaryGaussianHeatTest scale positive 0 = ((Real.sqrt scale)⁻¹ : ℝ) := by
  simp [burnolBoundaryGaussianHeatTest, scaledSchwartzTest_apply,
    clozelGaussianSchwartz_apply]

@[simp] theorem fourier_burnolBoundaryGaussianHeatTest_zero
    (scale : ℝ) (positive : 0 < scale) :
    FourierTransform.fourier (burnolBoundaryGaussianHeatTest scale positive) 0 = 1 := by
  rw [fourier_burnolBoundaryGaussianHeatTest scale positive]
  simp [burnolGaussianRaw]

private theorem fourier_zero_eq_integral (test : SchwartzMap ℝ ℂ) :
    FourierTransform.fourier test 0 = ∫ x : ℝ, test x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
  simp

private theorem burnolBoundaryGaussianHeatTest_integral
    (scale : ℝ) (positive : 0 < scale) :
    (∫ x : ℝ, burnolBoundaryGaussianHeatTest scale positive x) = 1 := by
  rw [← fourier_zero_eq_integral]
  exact fourier_burnolBoundaryGaussianHeatTest_zero scale positive

theorem coPoissonMuntzScaleRemainder_burnolBoundaryGaussianHeatTest
    (scale : ℝ) (positive : 0 < scale) {u : ℝ} (positiveU : 0 < u) :
    coPoissonMuntzScaleRemainder (burnolBoundaryGaussianHeatTest scale positive) u =
      (((Real.sqrt scale)⁻¹ : ℝ) : ℂ) *
        coPoissonMuntzScaleRemainder clozelGaussianSchwartz
          ((Real.sqrt scale)⁻¹ * u) := by
  let a := (Real.sqrt scale)⁻¹
  have positiveA : 0 < a := inv_pos.mpr (Real.sqrt_pos.2 positive)
  have nested : scaledSchwartzTest u positiveU.ne'
      (burnolBoundaryGaussianHeatTest scale positive) =
      (a : ℂ) • scaledSchwartzTest (a * u) (mul_ne_zero positiveA.ne' positiveU.ne')
        clozelGaussianSchwartz := by
    apply SchwartzMap.ext
    intro x
    simp only [burnolBoundaryGaussianHeatTest, scaledSchwartzTest_apply, smul_apply]
    congr 1
    dsimp only [a]
    ring_nf
  unfold coPoissonMuntzScaleRemainder
  rw [dif_pos positiveU, nested, map_smul]
  rw [dif_pos (mul_pos positiveA positiveU)]
  rfl

theorem burnolBoundaryGaussianHeatTest_thetaBracket_eq_remainder
    (scale : ℝ) (positive : 0 < scale) {u : ℝ} (positiveU : 0 < u) :
    coPoissonMuntzTheta (burnolBoundaryGaussianHeatTest scale positive) u - (u : ℂ)⁻¹ =
      (((Real.sqrt scale)⁻¹ : ℝ) : ℂ) *
        (coPoissonMuntzScaleRemainder clozelGaussianSchwartz
          ((Real.sqrt scale)⁻¹ * u) + 1) := by
  have remainder := coPoissonMuntzScaleRemainder_eq
    (burnolBoundaryGaussianHeatTest scale positive) positiveU
  rw [burnolBoundaryGaussianHeatTest_integral] at remainder
  have inverseCast : ((u⁻¹ : ℝ) : ℂ) = (u : ℂ)⁻¹ := by norm_cast
  have remainder' :
      coPoissonMuntzThetaNonzero (burnolBoundaryGaussianHeatTest scale positive) u -
          (u : ℂ)⁻¹ =
        coPoissonMuntzScaleRemainder (burnolBoundaryGaussianHeatTest scale positive) u := by
    calc
      _ = coPoissonMuntzThetaNonzero (burnolBoundaryGaussianHeatTest scale positive) u -
          ((u⁻¹ : ℝ) : ℂ) := by rw [inverseCast]
      _ = coPoissonMuntzThetaNonzero (burnolBoundaryGaussianHeatTest scale positive) u -
          u⁻¹ • (1 : ℂ) := by simp [real_smul]
      _ = _ := remainder.symm
  rw [coPoissonMuntzTheta, burnolBoundaryGaussianHeatTest_zero]
  calc
    _ = (coPoissonMuntzThetaNonzero (burnolBoundaryGaussianHeatTest scale positive) u -
          (u : ℂ)⁻¹) + (((Real.sqrt scale)⁻¹ : ℝ) : ℂ) := by ring_nf
    _ = coPoissonMuntzScaleRemainder (burnolBoundaryGaussianHeatTest scale positive) u +
          (((Real.sqrt scale)⁻¹ : ℝ) : ℂ) := by rw [remainder']
    _ = _ := by
      rw [coPoissonMuntzScaleRemainder_burnolBoundaryGaussianHeatTest
        scale positive positiveU]
      ring_nf

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
