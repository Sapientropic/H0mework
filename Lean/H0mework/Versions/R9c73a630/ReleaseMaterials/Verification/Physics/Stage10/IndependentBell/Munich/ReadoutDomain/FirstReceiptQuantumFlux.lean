import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

set_option autoImplicit false

namespace BellFirstReceiptQuantumFlux

def mask (b : Bool) : ℝ := if b then 1 else 0

theorem priority_first (ownAbsent earlier : Bool) :
    mask (ownAbsent && earlier) = mask ownAbsent - mask (ownAbsent && !earlier) := by
  cases ownAbsent <;> cases earlier <;> norm_num [mask]

theorem priority_second (ownAbsent earlier later : Bool) :
    mask (ownAbsent && (!earlier && later)) =
      mask (ownAbsent && !earlier) - mask (ownAbsent && (!earlier && !later)) := by
  cases ownAbsent <;> cases earlier <;> cases later <;> norm_num [mask]

theorem priority_sum (ownAbsent earlier later : Bool) :
    mask (ownAbsent && earlier) + mask (ownAbsent && (!earlier && later)) =
      mask ownAbsent - mask (ownAbsent && (!earlier && !later)) := by
  rw [priority_first, priority_second]
  ring

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem source_quantum_first (J : V →ₗ[ℝ] W) (rho : V) (ownAbsent earlier : Bool) :
    J (mask (ownAbsent && earlier) • rho) =
      J (mask ownAbsent • rho) - J (mask (ownAbsent && !earlier) • rho) := by
  rw [priority_first, sub_smul, map_sub]

theorem source_quantum_second (J : V →ₗ[ℝ] W) (rho : V) (ownAbsent earlier later : Bool) :
    J (mask (ownAbsent && (!earlier && later)) • rho) =
      J (mask (ownAbsent && !earlier) • rho) -
        J (mask (ownAbsent && (!earlier && !later)) • rho) := by
  rw [priority_second, sub_smul, map_sub]

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem original_drift_duality (k e rho : Matrix n n ℂ) :
    Matrix.trace (e * (k*rho + rho*k.conjTranspose)) =
      Matrix.trace ((k.conjTranspose*e + e*k)*rho) := by
  simp only [mul_add, add_mul, Matrix.trace_add]
  rw [← Matrix.mul_assoc e k rho, Matrix.trace_mul_cycle' e rho k.conjTranspose]
  simp only [← Matrix.mul_assoc]
  exact add_comm _ _

omit [DecidableEq n] in
theorem original_recycle_duality (left right e rho : Matrix n n ℂ) :
    Matrix.trace (e * (left*rho*right)) = Matrix.trace ((right*e*left)*rho) := by
  rw [Matrix.trace_mul_cycle' e (left*rho) right]
  simp only [Matrix.mul_assoc]

end BellFirstReceiptQuantumFlux
