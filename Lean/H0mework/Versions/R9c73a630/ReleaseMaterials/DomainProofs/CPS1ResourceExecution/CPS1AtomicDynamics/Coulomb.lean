import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0

namespace CPS1AtomicDynamics.Coulomb
noncomputable section
open scoped RealInnerProductSpace

abbrev Point := EuclideanSpace ℝ (Fin 3)

def pairEnergy (q₁ q₂ : ℝ) (x y : Point) : ℝ := q₁ * q₂ / ‖x-y‖

def pairForce (q₁ q₂ : ℝ) (x y : Point) : Point := (q₁ * q₂ / ‖x-y‖^3) • (x-y)

theorem pair_force_swap (q₁ q₂ : ℝ) (x y : Point) :
    pairForce q₂ q₁ y x = -pairForce q₁ q₂ x y := by
  have difference : y-x = -(x-y) := (neg_sub x y).symm
  simp only [pairForce,difference,norm_neg,mul_comm q₂ q₁,smul_neg]

theorem pair_energy_derivative (q₁ q₂ : ℝ) (x y : Point) (distinct : x ≠ y) :
    HasFDerivAt (fun z => pairEnergy q₁ q₂ z y)
      (-(innerSL ℝ (pairForce q₁ q₂ x y))) x := by
  have displacement : x-y ≠ 0 := sub_ne_zero.mpr distinct
  have radius : ‖x-y‖ ≠ 0 := norm_ne_zero_iff.mpr displacement
  have squared := ((hasFDerivAt_id x).sub_const y).norm_sq
  have root := squared.sqrt (pow_ne_zero 2 radius)
  have normDerivative : HasFDerivAt (fun z : Point => ‖z-y‖)
      (‖x-y‖⁻¹ • innerSL ℝ (x-y)) x := by
    simp only [id_eq,Real.sqrt_sq (norm_nonneg _)] at root
    convert root using 1 <;> first
    | rfl
    | (ext z
       simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_apply,
         two_smul,add_apply,innerSL_apply_apply,smul_eq_mul]
       field_simp
       ring)
  have reciprocal := ((hasDerivAt_inv radius).comp_hasFDerivAt x normDerivative).const_mul (q₁*q₂)
  have derivative : -(innerSL ℝ (pairForce q₁ q₂ x y)) =
      (q₁*q₂) • (-(‖x-y‖^2)⁻¹ • (‖x-y‖⁻¹ • innerSL ℝ (x-y))) := by
    ext z
    simp only [pairForce,neg_apply,smul_apply,
      innerSL_apply_apply,real_inner_smul_left,smul_eq_mul]
    field_simp
  rw [derivative]
  simpa only [pairEnergy,div_eq_mul_inv,Function.comp_apply] using reciprocal

theorem pair_energy_direction (q₁ q₂ : ℝ) (x y direction : Point) (distinct : x ≠ y) :
    fderiv ℝ (fun z => pairEnergy q₁ q₂ z y) x direction =
      -(inner ℝ (pairForce q₁ q₂ x y) direction) := by
  rw [(pair_energy_derivative q₁ q₂ x y distinct).fderiv]
  rfl

def kinetic (mass : ℝ) (momentum : Point) : ℝ := ‖momentum‖^2 / (2*mass)

def nextP (p force : Point) (dt : ℝ) : Point := p + dt • force

def nextR (mass : ℝ) (r p force : Point) (dt : ℝ) : Point :=
  r + (dt/mass) • p + (dt^2/(2*mass)) • force

theorem midpoint_work (mass : ℝ) (positive : 0 < mass) (r p force : Point) (dt : ℝ) :
    kinetic mass (nextP p force dt) - kinetic mass p =
      inner ℝ force (nextR mass r p force dt-r) := by
  have nonzero : mass ≠ 0 := ne_of_gt positive
  simp only [kinetic,nextP,nextR,← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm p force]
  field_simp
  ring

end
end CPS1AtomicDynamics.Coulomb
