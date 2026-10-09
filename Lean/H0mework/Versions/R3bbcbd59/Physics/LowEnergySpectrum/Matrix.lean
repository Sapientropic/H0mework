import H0mework.Versions.R3bbcbd59.Physics.LowEnergySpectrum.Jacobian
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! Coordinate matrix and spectral factors of the actual constrained derivative. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spectrum
open Evolution Stage9C.Material.SpinPair Polynomial
noncomputable section

def actualJacobian : Matrix (Fin 7) (Fin 7) ℝ :=
  fun row col => fderiv ℝ generator (Evolution.seed 0) (Pi.single col 1) row

theorem actualJacobian_eq : actualJacobian =
    !![0,lapse,0,0,0,0,0;
       -12*lapse,0,0,0,0,0,0;
       0,0,0,1/lapse,0,0,0;
       0,0,(50/3)*lapse,0,0,0,0;
       0,0,0,0,0,lapse,0;
       0,0,0,0,2*lapse,0,0;
       -3*lapse*spinScale,0,(5/2)*lapse,0,0,0,0] := by
  ext row col
  unfold actualJacobian
  rw [generator_fderiv]
  fin_cases row <;> fin_cases col <;> simp [linearResponse]

def geometryBlock : Matrix (Fin 2) (Fin 2) ℝ :=
  actualJacobian.submatrix (fun i => i.castLE (by decide)) (fun i => i.castLE (by decide))
def gaugeBlock : Matrix (Fin 2) (Fin 2) ℝ :=
  actualJacobian.submatrix (fun i => ⟨i.val+2, by omega⟩) (fun i => ⟨i.val+2, by omega⟩)
def radialBlock : Matrix (Fin 2) (Fin 2) ℝ :=
  actualJacobian.submatrix (fun i => ⟨i.val+4, by omega⟩) (fun i => ⟨i.val+4, by omega⟩)

theorem geometryBlock_eq : geometryBlock = !![0,lapse;-12*lapse,0] := by
  rw [geometryBlock, actualJacobian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem gaugeBlock_eq : gaugeBlock = !![0,1/lapse;(50/3)*lapse,0] := by
  rw [gaugeBlock, actualJacobian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem radialBlock_eq : radialBlock = !![0,lapse;2*lapse,0] := by
  rw [radialBlock, actualJacobian_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem geometry_characteristic : geometryBlock.charpoly = X^2 + C (648/125:ℝ) := by
  have determinant : geometryBlock.det = (648/125:ℝ) := by
    rw [geometryBlock_eq, Matrix.det_fin_two]
    simp
    nlinarith [lapse_sq]
  have trace : geometryBlock.trace = 0 := by simp [geometryBlock_eq, Matrix.trace, Fin.sum_univ_two]
  rw [Matrix.charpoly_fin_two, trace, determinant]
  simp

theorem gauge_characteristic : gaugeBlock.charpoly = X^2 - C (50/3:ℝ) := by
  have determinant : gaugeBlock.det = (-50/3:ℝ) := by
    rw [gaugeBlock_eq, Matrix.det_fin_two]
    simp
    field_simp [ne_of_gt lapse_pos]
  have trace : gaugeBlock.trace = 0 := by simp [gaugeBlock_eq, Matrix.trace, Fin.sum_univ_two]
  rw [Matrix.charpoly_fin_two, trace, determinant]
  simp [neg_div, sub_eq_add_neg]

theorem radial_characteristic : radialBlock.charpoly = X^2 - C (108/125:ℝ) := by
  have determinant : radialBlock.det = (-108/125:ℝ) := by
    rw [radialBlock_eq, Matrix.det_fin_two]
    simp
    nlinarith [lapse_sq]
  have trace : radialBlock.trace = 0 := by simp [radialBlock_eq, Matrix.trace, Fin.sum_univ_two]
  rw [Matrix.charpoly_fin_two, trace, determinant]
  simp [neg_div, sub_eq_add_neg]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spectrum
