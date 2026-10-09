import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Compression
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.TopEnergy

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Donor Propagation.Interface Load.Source Powered.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def numericDonorEnergy : ℝ := 2*calculatedEnergy calculatedTop+3

theorem numeric_loaded_top_entry (e f : Fin 2) :
    numericLoadHamiltonian (((calculatedTop,calculatedTop),1),e) (((calculatedTop,calculatedTop),1),f) =
      (numericDonorEnergy : ℂ)*(if e=f then 1 else 0)+Powered.Dynamics.controllerHamiltonian 2 e f := by
  have entry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
    (hpc_diagonal_block calculatedEnergy calculatedTop)
  have diagonal : sourcePCH E ((calculatedTop,calculatedTop),1) ((calculatedTop,calculatedTop),1) =
      2*(calculatedEnergy calculatedTop : ℂ)+3 := by
    rw [sourcePCH,recorded_diagonal_source]
    exact entry
  simp only [numericLoadHamiltonian,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
    Matrix.add_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]
  rw [diagonal]
  have interaction : loadInteraction (((calculatedTop,calculatedTop),1),e)
      (((calculatedTop,calculatedTop),1),f) = 0 := by
    simp [loadInteraction,controllerEnvironmentExchange,Matrix.kronecker,Matrix.single]
  rw [interaction]
  simp only [if_true,one_mul,add_zero,numericDonorEnergy,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]

theorem numeric_donor_environment_read (e f : Fin 2) :
    (BodyKernel.slice numericLoadHamiltonian e f*calculatedDonor).trace =
      (numericDonorEnergy : ℂ)*(if e=f then 1 else 0)+Powered.Dynamics.controllerHamiltonian 2 e f := by
  rw [calculatedDonor,BasisInverse.trace_basis]
  exact numeric_loaded_top_entry e f

theorem donor_energy_error : |donorEnergy-numericDonorEnergy| ≤ (44/10^12 : ℝ) := by
  have expression : donorEnergy-numericDonorEnergy =
      2*(Preparation.sourceEnergies originalTop-calculatedEnergy calculatedTop) := by
    unfold donorEnergy numericDonorEnergy
    ring
  rw [expression,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [actual_top_energy_error]

theorem actual_compression_error (e f : Fin 2) :
    ‖(BodyKernel.slice actualHamiltonian e f*actualDonor).trace-
      (BodyKernel.slice numericLoadHamiltonian e f*calculatedDonor).trace‖ ≤ (44/10^12 : ℝ) := by
  rw [actual_donor_environment_read,numeric_donor_environment_read,add_sub_add_right_eq_sub,← sub_mul]
  by_cases same : e=f
  · simp only [if_pos same,mul_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact donor_energy_error
  · norm_num [same]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
