import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! Universal spatial symbol of a generated four-real-dimensional SU(2) block.
Its identification with the source-adapted basis is checked separately. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.ScalarSymbol
noncomputable section

def quaternionSkew (momentum : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,-momentum 0,-momentum 1,-momentum 2;
    momentum 0,0,momentum 2,-momentum 1;
    momentum 1,-momentum 2,0,momentum 0;
    momentum 2,momentum 1,-momentum 0,0]

def squareMomentum (momentum : Fin 3 → ℂ) : ℂ := ∑ axis, (momentum axis)^2

theorem quaternionSkew_squared (momentum : Fin 3 → ℂ) :
    quaternionSkew momentum*quaternionSkew momentum = -squareMomentum momentum • 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [quaternionSkew, squareMomentum, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
  all_goals ring

def blockSymbol (center amplitude : ℂ) (momentum : Fin 3 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  center • 1+(Complex.I*amplitude) • quaternionSkew momentum

theorem blockSymbol_determinant (center amplitude : ℂ) (momentum : Fin 3 → ℂ) :
    (blockSymbol center amplitude momentum).det =
      (center^2-amplitude^2*squareMomentum momentum)^2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Matrix.det_fin_three]
  norm_num [blockSymbol, quaternionSkew, squareMomentum, Fin.sum_univ_three,
    Matrix.submatrix_apply, Fin.succAbove, Fin.succ, Matrix.one_apply]
  dsimp
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four]
  ring

theorem blockSymbol_product (center amplitude : ℂ) (momentum : Fin 3 → ℂ) :
    blockSymbol center amplitude momentum*blockSymbol center (-amplitude) momentum =
      (center^2-amplitude^2*squareMomentum momentum) • 1 := by
  simp only [blockSymbol, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, quaternionSkew_squared, smul_smul]
  simp only [smul_add, smul_smul]
  have coefficient : (Complex.I*(-amplitude))*(Complex.I*amplitude*(-squareMomentum momentum)) =
      -amplitude^2*squareMomentum momentum := by
    ring_nf
    simp [Complex.I_sq]
  rw [coefficient]
  module

theorem blockSymbol_inverse (center amplitude : ℂ) (momentum : Fin 3 → ℂ)
    (regular : center^2-amplitude^2*squareMomentum momentum ≠ 0) :
    (blockSymbol center amplitude momentum)⁻¹ =
      (center^2-amplitude^2*squareMomentum momentum)⁻¹ • blockSymbol center (-amplitude) momentum := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, blockSymbol_product, smul_smul, inv_mul_cancel₀ regular, one_smul]

end
end SaturationMonoid.PhysicsCore.LowEnergy.ScalarSymbol
