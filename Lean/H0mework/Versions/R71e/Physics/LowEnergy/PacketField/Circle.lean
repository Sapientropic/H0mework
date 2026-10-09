import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Rotation.Alignment
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! A specified Borel quarter-angle section replaces an unspecified choice of
frame when the actual light field must be integrated over momentum. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open Rotation
noncomputable section

def circleParameter (cosine sine : ℝ) : ℝ :=
  if cosine= -1 then 1 else
    (sine/(2*Real.sqrt ((1+cosine)/2)))/(1+Real.sqrt ((1+cosine)/2))

theorem halfParameter (a b : ℝ) (unit : a^2+b^2=1) (denominator : 1+a≠0) :
    halfCos (b/(1+a))=a ∧ halfSin (b/(1+a))=b := by
  have total : (1+a)^2+b^2≠0 := ne_of_gt
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero denominator) (sq_nonneg b))
  constructor
  · unfold halfCos
    field_simp
    linear_combination -(1+a)*unit
  · unfold halfSin
    field_simp
    linear_combination -b*unit

theorem circleParameter_correct (c s : ℝ) (unit : c^2+s^2=1) :
    circleCos (circleParameter c s)=c ∧ circleSin (circleParameter c s)=s := by
  by_cases endpoint : c= -1
  · have zero : s=0 := by nlinarith [unit]
    norm_num [circleParameter,circleCos,circleSin,halfCos,halfSin,endpoint,zero]
  have positive : 0<1+c := by
    have nonnegative : 0≤1+c := by nlinarith [sq_nonneg (c+1),sq_nonneg s]
    exact lt_of_le_of_ne nonnegative (by intro equal; apply endpoint; linarith)
  let a := Real.sqrt ((1+c)/2)
  let b := s/(2*a)
  have a_positive : 0<a := Real.sqrt_pos.2 (by positivity)
  have a_square : a^2=(1+c)/2 := Real.sq_sqrt (by positivity)
  have b_square : b^2=(1-c)/2 := by
    dsimp [b]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 (mul_ne_zero (by norm_num) a_positive.ne'))).2
    rw [mul_pow,a_square]
    nlinarith [unit]
  obtain ⟨cosine,sine⟩ := halfParameter a b (by linarith) (ne_of_gt (by positivity))
  change circleCos (if c= -1 then 1 else b/(1+a))=c ∧
    circleSin (if c= -1 then 1 else b/(1+a))=s
  rw [if_neg endpoint]
  constructor
  · rw [circleCos,cosine,sine]
    linarith
  · rw [circleSin,cosine,sine]
    dsimp [b]
    field_simp

theorem circleParameter_measurable : Measurable (fun pair : ℝ×ℝ => circleParameter pair.1 pair.2) := by
  unfold circleParameter
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
  fun_prop

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
