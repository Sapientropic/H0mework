import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Commutator

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Interface Powered.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def centeredE : Matrix Basis Basis ℂ := E+(7 : ℂ) • 1

theorem centered_entries_checked : ((energies.map (fun n => n+7*10^15)).map abs).all (· ≤ 12*10^15)=true := by decide +kernel

theorem centered_entry_bound (i : Basis) : |energies[i.val]!+7*10^15| ≤ (12*10^15 : Int) := by
  have paid := all_abs_bound (energies.map (fun n => n+7*10^15)) (by simpa only [List.length_map] using energies_length)
    _ centered_entries_checked i
  have bound : i.val < energies.length := by rw [energies_length]; exact i.isLt
  simpa only [Spectral.Rows.read,getElem!_pos, List.length_map,List.getElem_map,bound] using paid

theorem centered_E_norm : ‖centeredE‖ ≤ 12 := by
  have read : centeredE=Matrix.diagonal (fun i : Basis => ((energies[i.val]!+7*10^15 : Int) : ℂ)/10^15) := by
    ext i j
    simp only [centeredE,E,Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply,Matrix.one_apply,smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  rw [read,Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  have bound : (|energies[i.val]!+7*10^15| : ℝ) ≤ 12*10^15 := by exact_mod_cast centered_entry_bound i
  rw [norm_div,Complex.norm_intCast]
  norm_num at bound ⊢
  linarith

theorem interaction_scalar_zero (c : ℂ) : interaction (c • (1 : Matrix Basis Basis ℂ))=0 := by
  have diff : difference (c • (1 : Matrix Basis Basis ℂ))=0 := by
    simp only [difference,Matrix.kronecker,Matrix.smul_kronecker,Matrix.kronecker_smul,Matrix.one_kronecker_one,sub_self]
  simp only [interaction,transfer,raising,diff,mul_zero,add_zero,smul_zero,Matrix.kronecker,
    Matrix.zero_kronecker,Matrix.conjTranspose_zero]

theorem numeric_interaction_norm : ‖interaction E‖ ≤ 48 := by
  have paid := source_interaction_perturbation E ((-7 : ℂ) • (1 : Matrix Basis Basis ℂ))
  rw [interaction_scalar_zero,sub_zero] at paid
  have delta : E-(-7 : ℂ) • (1 : Matrix Basis Basis ℂ)=centeredE := by
    unfold centeredE
    module
  rw [delta] at paid
  linarith [centered_E_norm]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
