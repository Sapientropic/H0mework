import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Assembly.Bounds
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Energies
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Cast

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator BigOperators
noncomputable section

def Q : Matrix Basis Basis ℂ := (1/10^15 : ℂ) • Cast.complexMatrix frame
def A : Matrix Basis Basis ℂ := activeMatrix Propagation.Source.electronicSource
def E : Matrix Basis Basis ℂ := Matrix.diagonal (fun i => (energies[i.val]! : ℂ)/10^15)

theorem A_original : A = (1/10^15 : ℂ) • Cast.complexMatrix original := by
  ext i j
  simp only [A,Matrix.smul_apply,smul_eq_mul,Cast.complexMatrix,actual_source,activeMatrix]
  ring

theorem actual_Gram_scaled : star Q*Q = (1/10^30 : ℂ) • Cast.complexMatrix gram := by
  rw [Q,star_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  change ((star (1/10^15 : ℂ))*(1/10^15 : ℂ)) •
    (star (Cast.complexMatrix frame)*Cast.complexMatrix frame) = _
  rw [Matrix.star_eq_conjTranspose,← Cast.complexMatrix_transpose,← Cast.complexMatrix_mul,source_gram]
  norm_num

theorem actual_product_scaled : A*Q = (1/10^30 : ℂ) • Cast.complexMatrix applied := by
  rw [A_original,Q,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← Cast.complexMatrix_mul,source_product]
  norm_num

theorem residual_entry (i j : Basis) : (A*Q-Q*E) i j =
    (Rows.read (Rows.rowAt residualColumns j) i : ℂ)/10^30 := by
  rw [Matrix.sub_apply,actual_product_scaled]
  simp only [Matrix.smul_apply,smul_eq_mul,Cast.complexMatrix,E,Matrix.mul_diagonal,Q]
  have first : i.val < (Rows.rowAt appliedColumns j).length := by rw [appliedColumns_lengths]; exact i.isLt
  have second : i.val < (Rows.rowAt frameColumns j).length := by rw [frameColumns_lengths]; exact i.isLt
  have both : i.val < ((Rows.rowAt appliedColumns j).zip (Rows.rowAt frameColumns j)).length := by
    simp only [List.length_zip]; omega
  have reading : Rows.read (Rows.rowAt residualColumns j) i = applied i j-frame i j*energies[j.val]! := by
    rw [all_eigen_residuals]
    simp [Rows.read,applied,frame,Rows.columnMatrix,getElem!_pos,first,second]
  rw [reading]
  push_cast
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
