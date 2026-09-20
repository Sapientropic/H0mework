import H0mework.Physics.GaugeSpectrum.Curvature

/-! Nonzero connected curvature responses in the source-generated quantum
state. These are curvature operators on the occupied matter representation. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum

open Matrix DiracCliffordRepresentation
open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open scoped Kronecker

noncomputable section

theorem pauli_hermitian (axis : Fin 3) : (pauli axis).IsHermitian := by
  rw [pauli_explicit]
  ext row column
  fin_cases axis <;> fin_cases row <;> fin_cases column <;>
    simp [Matrix.conjTranspose_apply]

theorem pauli_square (axis : Fin 3) : pauli axis * pauli axis = 1 := by
  rw [pauli_explicit]
  ext row column
  fin_cases axis <;> fin_cases row <;> fin_cases column <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem exchange_hermitian : exchange.IsHermitian := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [exchange, spinFlip, Matrix.conjTranspose_apply]

theorem exchange_square : exchange * exchange = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num +decide [exchange, spinFlip, Matrix.mul_apply, Fin.sum_univ_four]

theorem curvature_hermitian (point : BasePoint) (axis : Fin 3) :
    (curvature point axis).IsHermitian := by
  rw [curvature_normalForm]
  change _ᴴ = _
  simp [Matrix.conjTranspose_smul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, (pauli_hermitian axis).eq]

theorem dualCurvature_hermitian (point : BasePoint) (axis : Fin 3) :
    (dualCurvature point axis).IsHermitian := by
  rw [dualCurvature_normalForm]
  change _ᴴ = _
  simp [Matrix.conjTranspose_smul,
    Matrix.conjTranspose_kronecker, exchange_hermitian.eq, (pauli_hermitian axis).eq]

theorem curvature_square (point : BasePoint) (axis : Fin 3) :
    curvature point axis * curvature point axis = ((curvatureScale : ℂ) ^ 2) • 1 := by
  rw [curvature_normalForm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, pauli_square, Matrix.one_kronecker_one]
  simp [pow_two]

theorem dualCurvature_square (point : BasePoint) (axis : Fin 3) :
    dualCurvature point axis * dualCurvature point axis = ((curvatureScale : ℂ) ^ 2) • 1 := by
  rw [dualCurvature_normalForm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    ← Matrix.mul_kronecker_mul, exchange_square, pauli_square, Matrix.one_kronecker_one]
  simp [pow_two]

theorem curvature_mean (point : BasePoint) (axis : Fin 3) :
    State.evaluation point (curvature point axis) = 0 := by
  rw [curvature_normalForm, map_smul]
  suffices State.evaluation point
      ((1 : Matrix DiracSpinorIndex DiracSpinorIndex ℂ) ⊗ₖ pauli axis) = 0 by simp [this]
  rw [pauli_explicit]
  fin_cases axis <;>
    simp [State.evaluation, State.vectorEvaluation, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two,
      Source.vector, Source.amplitude, spinPairCoefficients]
  ring

theorem dualCurvature_mean (point : BasePoint) (axis : Fin 3) :
    State.evaluation point (dualCurvature point axis) = 0 := by
  rw [dualCurvature_normalForm, map_smul]
  suffices State.evaluation point (exchange ⊗ₖ pauli axis) = 0 by simp [this]
  rw [pauli_explicit]
  fin_cases axis <;>
    simp [State.evaluation, State.vectorEvaluation, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_two, exchange, spinFlip,
      Source.vector, Source.amplitude, spinPairCoefficients]
  ring

def connected (point : BasePoint) (first second : State.Observable) : ℂ :=
  State.evaluation point (star first * second) -
    star (State.evaluation point first) * State.evaluation point second

theorem curvature_variance (point : BasePoint) (axis : Fin 3) :
    connected point (curvature point axis) (curvature point axis) =
      (curvatureScale : ℂ) ^ 2 := by
  simp only [connected, Matrix.star_eq_conjTranspose, (curvature_hermitian point axis).eq,
    curvature_square, map_smul, State.evaluation_one, curvature_mean, star_zero,
    mul_zero, sub_zero, smul_eq_mul, mul_one]

theorem dualCurvature_variance (point : BasePoint) (axis : Fin 3) :
    connected point (dualCurvature point axis) (dualCurvature point axis) =
      (curvatureScale : ℂ) ^ 2 := by
  simp only [connected, Matrix.star_eq_conjTranspose, (dualCurvature_hermitian point axis).eq,
    dualCurvature_square, map_smul, State.evaluation_one, dualCurvature_mean, star_zero,
    mul_zero, sub_zero, smul_eq_mul, mul_one]

theorem dualCurvature_connected_nonzero (point : BasePoint) (axis : Fin 3) :
    connected point (dualCurvature point axis) (dualCurvature point axis) ≠ 0 := by
  rw [dualCurvature_variance]
  exact pow_ne_zero 2 (by exact_mod_cast ne_of_gt curvatureScale_pos)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum
