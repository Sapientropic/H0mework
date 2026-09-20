import H0mework.Physics.Dirac.CoframeSpinRepresentation

/-!
# Orientation of the generated Spin--Lorentz image

The determinant of the actual Lorentz matrix generated from the existing
`SL(2,ℂ)` Spin carrier is derived from its elementary-transvection
decomposition.  This representation theorem is independent of any gravity
root-action formulation and can therefore be consumed by both gravity and
matter density covariance proofs.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSpinLorentzOrientation

open ProofFreeRicherAnholonomicSource
open StageNineCoframeSpinRepresentation
open StageNineGlobalBundle
open StageNineLorentzCoverAndSpinDescent
open StageNinePhysicalBivectorSpinRepresentation
open Matrix
open scoped MatrixGroups ComplexConjugate

noncomputable section

set_option autoImplicit false

def upperLorentzTransvectionMatrix
    (parameter : ℂ) : LorentzianCoframe :=
  let normSquare := parameter.re ^ 2 + parameter.im ^ 2
  !![1 + normSquare / 2, parameter.re, -parameter.im, -normSquare / 2;
     parameter.re, 1, 0, -parameter.re;
     -parameter.im, 0, 1, parameter.im;
     normSquare / 2, parameter.re, -parameter.im, 1 - normSquare / 2]

def lowerLorentzTransvectionMatrix
    (parameter : ℂ) : LorentzianCoframe :=
  let normSquare := parameter.re ^ 2 + parameter.im ^ 2
  !![1 + normSquare / 2, parameter.re, parameter.im, normSquare / 2;
     parameter.re, 1, 0, parameter.re;
     parameter.im, 0, 1, parameter.im;
     -normSquare / 2, -parameter.re, -parameter.im, 1 - normSquare / 2]

theorem spinLorentzMatrix_upper_transvection
    (unequal : (0 : Fin 2) ≠ 1) (parameter : ℂ) :
    spinLorentzMatrix
        (Matrix.SpecialLinearGroup.transvection unequal parameter) =
      upperLorentzTransvectionMatrix parameter := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [spinLorentzMatrix_apply, spinLorentzCover,
      spinLorentzLinearEquiv, spinLorentzLinearMap,
      spinHermitianAction, pauliDecode, pauliEncode,
      Matrix.SpecialLinearGroup.transvection_coe,
      upperLorentzTransvectionMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals ring

theorem spinLorentzMatrix_lower_transvection
    (unequal : (1 : Fin 2) ≠ 0) (parameter : ℂ) :
    spinLorentzMatrix
        (Matrix.SpecialLinearGroup.transvection unequal parameter) =
      lowerLorentzTransvectionMatrix parameter := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [spinLorentzMatrix_apply, spinLorentzCover,
      spinLorentzLinearEquiv, spinLorentzLinearMap,
      spinHermitianAction, pauliDecode, pauliEncode,
      Matrix.SpecialLinearGroup.transvection_coe,
      lowerLorentzTransvectionMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals ring

private theorem upperLorentzTransvectionMatrix_det
    (parameter : ℂ) :
    Matrix.det (upperLorentzTransvectionMatrix parameter) = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [upperLorentzTransvectionMatrix, Fin.sum_univ_four,
    Matrix.det_fin_three, Fin.succAbove]
  ring

private theorem lowerLorentzTransvectionMatrix_det
    (parameter : ℂ) :
    Matrix.det (lowerLorentzTransvectionMatrix parameter) = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [lowerLorentzTransvectionMatrix, Fin.sum_univ_four,
    Matrix.det_fin_three, Fin.succAbove]
  ring

private theorem spinLorentzMatrix_upper_transvection_det
    (unequal : (0 : Fin 2) ≠ 1) (parameter : ℂ) :
    Matrix.det
        (spinLorentzMatrix
          (Matrix.SpecialLinearGroup.transvection unequal parameter)) = 1 := by
  rw [spinLorentzMatrix_upper_transvection]
  exact upperLorentzTransvectionMatrix_det parameter

private theorem spinLorentzMatrix_lower_transvection_det
    (unequal : (1 : Fin 2) ≠ 0) (parameter : ℂ) :
    Matrix.det
        (spinLorentzMatrix
          (Matrix.SpecialLinearGroup.transvection unequal parameter)) = 1 := by
  rw [spinLorentzMatrix_lower_transvection]
  exact lowerLorentzTransvectionMatrix_det parameter

/-- The generated Spin image is orientation preserving.  The determinant is
derived from the actual `SL(2,ℂ)` carrier rather than supplied as a receipt. -/
theorem spinLorentzMatrix_det_eq_one (groupElement : SpinPlus13) :
    Matrix.det (spinLorentzMatrix groupElement) = 1 := by
  induction groupElement using Matrix.SL2.transvection_induction with
  | htransvec row column unequal parameter =>
      fin_cases row <;> fin_cases column
      · exact False.elim (unequal rfl)
      · exact spinLorentzMatrix_upper_transvection_det unequal parameter
      · exact spinLorentzMatrix_lower_transvection_det unequal parameter
      · exact False.elim (unequal rfl)
  | hmul first second firstDet secondDet =>
      rw [map_mul, Matrix.det_mul, firstDet, secondDet, one_mul]

/-- Left transport by the generated Spin--Lorentz image preserves the
coframe determinant exactly. -/
theorem spinLorentzCoframe_det
    (groupElement : SpinPlus13) (coframe : LorentzianCoframe) :
    Matrix.det (spinLorentzCoframeRepresentation groupElement coframe) =
      Matrix.det coframe := by
  change Matrix.det (spinLorentzMatrix groupElement * coframe) =
    Matrix.det coframe
  rw [Matrix.det_mul, spinLorentzMatrix_det_eq_one, one_mul]

end

end SaturationMonoid.PhysicsCore.StageNineSpinLorentzOrientation
