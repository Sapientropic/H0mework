import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Clozel centered scaling on tempered distributions

On `𝓢'(ℝ, ℂ)`, let `A u = x * ∂u + (1 / 2) * u`.  Mathlib's
distributional derivative and Fourier conventions give the exact identity
`A (𝓕 u) = -𝓕 (A u)`.  The intermediate calculation retains both `2πi`
and the dimension-one product-rule correction.

This is an operator identity.  It does not assert that `u`, `A u`, or either
side of the identity vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open FourierTransform LineDeriv
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

abbrev ComplexTempered := 𝓢'(ℝ, ℂ)

def position (u : ComplexTempered) : ComplexTempered :=
  TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) u

def centeredScalingGenerator (u : ComplexTempered) : ComplexTempered :=
  position (∂_{(1 : ℝ)} u) + (1 / 2 : ℂ) • u

theorem schwartz_position_lineDeriv (φ : 𝓢(ℝ, ℂ)) :
    ∂_{(1 : ℝ)}
        ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))) φ) =
      (SchwartzMap.smulLeftCLM ℂ
          (fun x : ℝ => (x : ℂ))) (∂_{(1 : ℝ)} φ) + φ := by
  have coordinateGrowth :
      (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by
    fun_prop
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change (fderiv ℝ (fun y : ℝ =>
      ((SchwartzMap.smulLeftCLM ℂ
        (fun z : ℝ => (z : ℂ))) φ) y) x) 1 = _
  have functionEquality :
      (fun y : ℝ => ((SchwartzMap.smulLeftCLM ℂ
        (fun z : ℝ => (z : ℂ))) φ) y) =
      (fun y : ℝ => (y : ℂ) * φ y) := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply coordinateGrowth]
    rfl
  rw [functionEquality]
  have derivative :
      fderiv ℝ (fun y : ℝ => (y : ℂ) * φ y) x =
        (x : ℂ) • fderiv ℝ (fun y : ℝ => φ y) x +
          φ x • Complex.ofRealCLM := by
    have generated :=
      ((Complex.ofRealCLM.hasFDerivAt (x := x)).mul
        φ.differentiable.differentiableAt.hasFDerivAt).fderiv
    change fderiv ℝ (fun y : ℝ => (y : ℂ) * φ y) x =
      Complex.ofRealCLM x • fderiv ℝ (fun y : ℝ => φ y) x +
        φ x • Complex.ofRealCLM at generated
    simpa only [Complex.ofRealCLM_apply] using generated
  rw [derivative]
  simp [SchwartzMap.smulLeftCLM_apply_apply coordinateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem lineDeriv_position (u : ComplexTempered) :
    ∂_{(1 : ℝ)} (position u) =
      position (∂_{(1 : ℝ)} u) + u := by
  ext φ
  simp [position]
  rw [schwartz_position_lineDeriv]
  simp

def fourierDerivativeConstant : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I

theorem fourierDerivativeConstant_ne_zero :
    fourierDerivativeConstant ≠ 0 := by
  unfold fourierDerivativeConstant
  exact mul_ne_zero
    (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

theorem lineDeriv_fourier_eq_neg_constant_fourier_position
    (u : ComplexTempered) :
    ∂_{(1 : ℝ)} (𝓕 u) =
      -(fourierDerivativeConstant • 𝓕 (position u)) := by
  unfold fourierDerivativeConstant
  simpa [position] using
    TemperedDistribution.lineDerivOp_fourier_eq u (1 : ℝ)

theorem fourier_lineDeriv_eq_constant_position_fourier
    (u : ComplexTempered) :
    𝓕 (∂_{(1 : ℝ)} u) =
      fourierDerivativeConstant • position (𝓕 u) := by
  unfold fourierDerivativeConstant
  simpa [position] using
    TemperedDistribution.fourier_lineDerivOp_eq u (1 : ℝ)

theorem position_lineDeriv_fourier_add_fourier
    (u : ComplexTempered) :
    position (∂_{(1 : ℝ)} (𝓕 u)) + 𝓕 u =
      -(𝓕 (position (∂_{(1 : ℝ)} u))) := by
  have generated :=
    lineDeriv_fourier_eq_neg_constant_fourier_position
      (∂_{(1 : ℝ)} u)
  rw [fourier_lineDeriv_eq_constant_position_fourier u] at generated
  change ∂_{(1 : ℝ)}
      (fourierDerivativeConstant • position (𝓕 u)) =
    -(fourierDerivativeConstant •
      𝓕 (position (∂_{(1 : ℝ)} u))) at generated
  rw [lineDerivOp_smul, lineDeriv_position, smul_add] at generated
  apply smul_right_injective ComplexTempered
    fourierDerivativeConstant_ne_zero
  change fourierDerivativeConstant •
      (position (∂_{(1 : ℝ)} (𝓕 u)) + 𝓕 u) =
    fourierDerivativeConstant •
      (-(𝓕 (position (∂_{(1 : ℝ)} u))))
  rw [smul_add, smul_neg]
  exact generated

theorem centeredScalingGenerator_fourier
    (u : ComplexTempered) :
    centeredScalingGenerator (𝓕 u) =
      -(𝓕 (centeredScalingGenerator u)) := by
  unfold centeredScalingGenerator
  have fourierAdd := fourier_add
    (position (∂_{(1 : ℝ)} u)) ((1 / 2 : ℂ) • u)
  rw [fourierAdd]
  have fourierHalf := fourier_smul (1 / 2 : ℂ) u
  rw [fourierHalf]
  let current : ComplexTempered :=
    position (∂_{(1 : ℝ)} (𝓕 u))
  let transformed : ComplexTempered := 𝓕 u
  let partner : ComplexTempered :=
    𝓕 (position (∂_{(1 : ℝ)} u))
  let half : ComplexTempered := (1 / 2 : ℂ) • transformed
  change current + half = -(partner + half)
  have generated : current + transformed = -partner := by
    exact position_lineDeriv_fourier_add_fourier u
  have split : transformed = half + half := by
    dsimp [half]
    calc
      transformed = (1 : ℂ) • transformed :=
        (one_smul ℂ transformed).symm
      _ = ((1 / 2 : ℂ) + (1 / 2 : ℂ)) • transformed := by
        norm_num
      _ = (1 / 2 : ℂ) • transformed +
          (1 / 2 : ℂ) • transformed :=
        add_smul (1 / 2 : ℂ) (1 / 2 : ℂ) transformed
  rw [split] at generated
  have zero : (current + (half + half)) + partner = 0 :=
    eq_neg_iff_add_eq_zero.mp generated
  apply eq_neg_of_add_eq_zero_left
  calc
    (current + half) + (partner + half) =
        (current + (half + half)) + partner := by
      abel
    _ = 0 := zero

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
