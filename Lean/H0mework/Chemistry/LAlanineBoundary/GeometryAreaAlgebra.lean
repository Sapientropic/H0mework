import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace WholeCellBoundaryArea

open Matrix
open scoped Matrix

def axisOrientation (axis : Fin 3) : ℝ := (-1) ^ axis.val

theorem axisOrientation_nonzero (axis : Fin 3) : axisOrientation axis ≠ 0 :=
  pow_ne_zero _ (by norm_num)

/-- Fin.succAbove lists the remaining axes in increasing order, reversing the middle face. -/
theorem adjugate_row_cross (m : Matrix (Fin 3) (Fin 3) ℝ) (axis : Fin 3) :
    m.adjugate axis = axisOrientation axis •
      (m.col (axis.succAbove 0) ⨯₃ m.col (axis.succAbove 1)) := by
  funext j
  rw [adjugate_fin_three, cross_apply]
  fin_cases axis <;> fin_cases j <;>
    simp [axisOrientation, Matrix.col, Fin.succAbove] <;> ring

theorem transverse_dot_adjugate (m : Matrix (Fin 3) (Fin 3) ℝ) (axis : Fin 3) :
    m.col axis ⬝ᵥ m.adjugate axis = m.det := by
  have equality := congrArg (fun a : Matrix (Fin 3) (Fin 3) ℝ => a axis axis) (adjugate_mul m)
  simpa only [mul_apply, dotProduct, Matrix.col, Matrix.transpose_apply, Matrix.smul_apply, one_apply_eq,
    smul_eq_mul, mul_one, mul_comm] using equality

end WholeCellBoundaryArea
