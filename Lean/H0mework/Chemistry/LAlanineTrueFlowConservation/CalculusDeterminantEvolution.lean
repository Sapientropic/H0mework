import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit false

namespace LAlanineTrueFlowConservation

open Matrix
open scoped Matrix

/-- Jacobi's evolution law consumes the actual nine entry derivatives, not an inverse
or a preinstalled determinant evolution. It also applies at closed time endpoints. -/
theorem determinant_evolution
    (J : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (H : Matrix (Fin 3) (Fin 3) ℝ)
    (s : Set ℝ) (t : ℝ)
    (entry : ∀ i j, HasDerivWithinAt (fun u => J u i j) ((H * J t) i j) s t) :
    HasDerivWithinAt (fun u => (J u).det) (H.trace * (J t).det) s t := by
  convert! (((((entry 0 0).mul (entry 1 1)).mul (entry 2 2)).sub
    (((entry 0 0).mul (entry 1 2)).mul (entry 2 1))).sub
    (((entry 0 1).mul (entry 1 0)).mul (entry 2 2))).add
    (((entry 0 1).mul (entry 1 2)).mul (entry 2 0)) |>.add
    (((entry 0 2).mul (entry 1 0)).mul (entry 2 1)) |>.sub
    (((entry 0 2).mul (entry 1 1)).mul (entry 2 0)) using 1
  · funext u
    exact Matrix.det_fin_three _
  · simp only [Pi.mul_apply, Matrix.mul_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_three,
      Matrix.det_fin_three]
    ring

end LAlanineTrueFlowConservation
