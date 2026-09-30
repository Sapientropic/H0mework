import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.UnitaryGroup

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ElectronicFrame.Polar

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isUnit_of_close (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) : IsUnit C := by
  have close' : ‖1 - C‖ < 1 := by simpa only [norm_sub_rev] using close
  simpa using (Units.oneSub (1 - C) close').isUnit

theorem abs_isUnit (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) : IsUnit (CFC.abs C) :=
  (CFC.isUnit_sqrt_iff (star C * C) (star_mul_self_nonneg C)).mpr
    ((isUnit_of_close C close).star.mul (isUnit_of_close C close))

def matrix (C : Matrix ι ι ℂ) : Matrix ι ι ℂ := C * Ring.inverse (CFC.abs C)

theorem matrix_mem_unitary (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    matrix C ∈ Matrix.unitaryGroup ι ℂ := by
  have unit := abs_isUnit C close
  have selfAdjoint : star (CFC.abs C) = CFC.abs C := (CFC.abs_nonneg C).star_eq
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [matrix, star_mul, ← Ring.inverse_star, selfAdjoint]
  calc
    Ring.inverse (CFC.abs C) * star C * (C * Ring.inverse (CFC.abs C)) =
        Ring.inverse (CFC.abs C) * (star C * C) * Ring.inverse (CFC.abs C) := by
      simp only [mul_assoc]
    _ = Ring.inverse (CFC.abs C) * (CFC.abs C * CFC.abs C) * Ring.inverse (CFC.abs C) := by
      rw [CFC.abs_mul_abs]
    _ = 1 := by rw [Ring.inverse_mul_cancel_left _ _ unit, Ring.mul_inverse_cancel _ unit]

def unitary (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) : Matrix.unitaryGroup ι ℂ :=
  ⟨matrix C, matrix_mem_unitary C close⟩

theorem adjoint_mul (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    star (matrix C) * matrix C = 1 := (matrix_mem_unitary C close).1

theorem mul_adjoint (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    matrix C * star (matrix C) = 1 := (matrix_mem_unitary C close).2

theorem factorization (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    matrix C * CFC.abs C = C := Ring.inverse_mul_cancel_right _ _ (abs_isUnit C close)

/-- The finite-frame projection discrepancy remains separate from its unitary factor. -/
def projectionResidual (C : Matrix ι ι ℂ) : Matrix ι ι ℂ := C - matrix C

theorem residual_reconstruction (C : Matrix ι ι ℂ) : matrix C + projectionResidual C = C := by
  simp only [projectionResidual, add_sub_cancel]

theorem residual_factorization (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    projectionResidual C = matrix C * (CFC.abs C - 1) := by
  rw [mul_sub, mul_one, factorization C close, projectionResidual]

theorem residual_norm (C : Matrix ι ι ℂ) (close : ‖C - 1‖ < 1) :
    ‖projectionResidual C‖ = ‖CFC.abs C - 1‖ := by
  rw [residual_factorization C close]
  exact CStarRing.norm_mem_unitary_mul _ (matrix_mem_unitary C close)

end
end LAlanine40K2025.ElectronicFrame.Polar
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
