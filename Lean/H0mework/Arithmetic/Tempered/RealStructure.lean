import H0mework.Arithmetic.Tempered.Scaling

/-!
# Real structure of the Clozel tempered scaling generator

Conjugating both a Schwartz test function and the resulting scalar defines a
complex-linear conjugate tempered distribution.  This involution commutes
with the real coordinate multiplier, the real directional derivative, and
the centered scaling generator.

These commuting laws preserve real distributions; they do not imply that a
distribution or its centered scaling derivative vanishes.
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
open scoped SchwartzMap

noncomputable section

def schwartzConjugation :
    𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

@[simp] theorem schwartzConjugation_apply
    (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzConjugation φ x = star (φ x) := by
  simp [schwartzConjugation, SchwartzMap.postcompCLM_apply]

@[simp] theorem schwartzConjugation_smul
    (c : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    schwartzConjugation (c • φ) =
      star c • schwartzConjugation φ := by
  ext x
  simp

@[simp] theorem schwartzConjugation_involutive
    (φ : 𝓢(ℝ, ℂ)) :
    schwartzConjugation (schwartzConjugation φ) = φ := by
  ext x
  simp

theorem schwartzConjugation_lineDeriv
    (φ : 𝓢(ℝ, ℂ)) :
    schwartzConjugation (∂_{(1 : ℝ)} φ) =
      ∂_{(1 : ℝ)} (schwartzConjugation φ) := by
  ext x
  simp only [schwartzConjugation_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change star ((fderiv ℝ (fun y : ℝ => φ y) x) 1) =
    (fderiv ℝ (fun y : ℝ => schwartzConjugation φ y) x) 1
  have functionEquality :
      (fun y : ℝ => schwartzConjugation φ y) =
        (fun y : ℝ => Complex.conjCLE (φ y)) := by
    funext y
    simp
  rw [functionEquality]
  have generated :=
    (((Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp x
      φ.differentiable.differentiableAt.hasFDerivAt).fderiv)
  have applied := congrArg (fun L : ℝ →L[ℝ] ℂ => L 1) generated
  simpa [Function.comp_def] using applied.symm

theorem schwartzConjugation_position
    (φ : 𝓢(ℝ, ℂ)) :
    schwartzConjugation
        ((SchwartzMap.smulLeftCLM ℂ
          (fun x : ℝ => (x : ℂ))) φ) =
      (SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => (x : ℂ))) (schwartzConjugation φ) := by
  have coordinateGrowth :
      (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by
    fun_prop
  ext x
  rw [schwartzConjugation_apply,
    SchwartzMap.smulLeftCLM_apply_apply coordinateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply coordinateGrowth,
    schwartzConjugation_apply]
  simp

def conjugateFunctional (u : ComplexTempered) :
    𝓢(ℝ, ℂ) →L[ℂ] ℂ where
  toFun φ := star (u (schwartzConjugation φ))
  map_add' left right := by simp
  map_smul' c φ := by
    rw [schwartzConjugation_smul]
    simp
  cont := Complex.continuous_conj.comp
    (u.cont.comp schwartzConjugation.cont)

def realConjugation (u : ComplexTempered) : ComplexTempered :=
  ContinuousLinearMap.toPointwiseConvergenceCLM
    ℂ (RingHom.id ℂ) _ _ (conjugateFunctional u)

@[simp] theorem realConjugation_apply
    (u : ComplexTempered) (φ : 𝓢(ℝ, ℂ)) :
    realConjugation u φ =
      star (u (schwartzConjugation φ)) :=
  rfl

@[simp] theorem realConjugation_add
    (u v : ComplexTempered) :
    realConjugation (u + v) =
      realConjugation u + realConjugation v := by
  ext φ
  simp

@[simp] theorem realConjugation_smul
    (c : ℂ) (u : ComplexTempered) :
    realConjugation (c • u) =
      star c • realConjugation u := by
  ext φ
  simp

@[simp] theorem realConjugation_involutive
    (u : ComplexTempered) :
    realConjugation (realConjugation u) = u := by
  ext φ
  simp only [realConjugation_apply]
  rw [schwartzConjugation_involutive]
  simp

theorem realConjugation_lineDeriv
    (u : ComplexTempered) :
    realConjugation (∂_{(1 : ℝ)} u) =
      ∂_{(1 : ℝ)} (realConjugation u) := by
  ext φ
  simp only [realConjugation_apply,
    TemperedDistribution.lineDerivOp_apply_apply]
  have testEquality :
      schwartzConjugation (-∂_{(1 : ℝ)} φ) =
        -∂_{(1 : ℝ)} (schwartzConjugation φ) := by
    rw [map_neg, schwartzConjugation_lineDeriv]
  rw [testEquality, map_neg]

theorem realConjugation_position
    (u : ComplexTempered) :
    realConjugation (position u) =
      position (realConjugation u) := by
  ext φ
  simp only [realConjugation_apply, position,
    TemperedDistribution.smulLeftCLM_apply_apply]
  rw [schwartzConjugation_position]

theorem realConjugation_centeredScalingGenerator
    (u : ComplexTempered) :
    realConjugation (centeredScalingGenerator u) =
      centeredScalingGenerator (realConjugation u) := by
  unfold centeredScalingGenerator
  rw [realConjugation_add, realConjugation_position,
    realConjugation_lineDeriv, realConjugation_smul]
  norm_num

def IsReal (u : ComplexTempered) : Prop :=
  realConjugation u = u

theorem IsReal.centeredScalingGenerator
    {u : ComplexTempered} (real : IsReal u) :
    IsReal (centeredScalingGenerator u) := by
  unfold IsReal at real ⊢
  rw [realConjugation_centeredScalingGenerator, real]

/-- An actual eigen-equation for `u` transports to the Fourier transform of
its real conjugate with eigenparameter `-conj lambda`.  This theorem neither
generates `u` or its eigen-equation nor asserts that the resulting J-cross
vanishes. -/
theorem centeredScalingGenerator_fourierRealConjugation_eigenpartner
    (u : ComplexTempered) (lambda : ℂ)
    (eigen : centeredScalingGenerator u = lambda • u) :
    centeredScalingGenerator (𝓕 (realConjugation u)) =
      (-star lambda) • 𝓕 (realConjugation u) := by
  calc
    centeredScalingGenerator (𝓕 (realConjugation u)) =
        -(𝓕 (centeredScalingGenerator (realConjugation u))) :=
      centeredScalingGenerator_fourier (realConjugation u)
    _ = -(𝓕 (realConjugation (centeredScalingGenerator u))) := by
      rw [realConjugation_centeredScalingGenerator]
    _ = -(𝓕 (realConjugation (lambda • u))) := by rw [eigen]
    _ = -(𝓕 (star lambda • realConjugation u)) := by
      rw [realConjugation_smul]
    _ = -(star lambda • 𝓕 (realConjugation u)) := by
      rw [fourier_smul]
    _ = (-star lambda) • 𝓕 (realConjugation u) :=
      (neg_smul (star lambda) (𝓕 (realConjugation u))).symm

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
