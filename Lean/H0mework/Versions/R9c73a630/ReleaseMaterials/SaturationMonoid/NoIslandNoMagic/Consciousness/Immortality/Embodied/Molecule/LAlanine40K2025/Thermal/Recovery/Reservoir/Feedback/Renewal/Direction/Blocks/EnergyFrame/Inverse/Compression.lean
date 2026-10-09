import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Actual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] Source.donor Powered.Producer.poweredTotalHamiltonian actualDonor actualHamiltonian installedPCFrame installedLoadFrame

def donorEnergy : ℝ := 2*Preparation.sourceEnergies Donor.originalTop+3

theorem original_loaded_top_entry (e f : Fin 2) :
    loadTotalHamiltonian (Spectral.Projection.excitedIndex,e) (Spectral.Projection.excitedIndex,f) =
      (donorEnergy : ℂ)*(if e=f then 1 else 0)+Powered.Dynamics.controllerHamiltonian 2 e f := by
  have entry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1)
    (original_hpc_diagonal_block Donor.originalTop)
  change Powered.Producer.poweredTotalHamiltonian ((Donor.originalTop,Donor.originalTop),1)
      ((Donor.originalTop,Donor.originalTop),1) = 2*(Preparation.sourceEnergies Donor.originalTop : ℂ)+3 at entry
  simp only [loadTotalHamiltonian,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
    Matrix.add_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,Spectral.Projection.excitedIndex,Matrix.one_apply]
  dsimp only [Donor.originalTop] at entry
  rw [entry]
  have interaction : loadInteraction (((Donor.originalTop,Donor.originalTop),1),e)
      (((Donor.originalTop,Donor.originalTop),1),f) = 0 := by
    simp [loadInteraction,controllerEnvironmentExchange,Matrix.kronecker,Matrix.single]
  dsimp only [Donor.originalTop] at interaction
  rw [interaction]
  simp only [if_true,one_mul,add_zero,donorEnergy,Donor.originalTop,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]

theorem original_donor_environment_read (e f : Fin 2) :
    (BodyKernel.slice loadTotalHamiltonian e f*Source.donor).trace =
      (donorEnergy : ℂ)*(if e=f then 1 else 0)+Powered.Dynamics.controllerHamiltonian 2 e f := by
  rw [Spectral.Projection.actual_donor,BasisInverse.trace_basis]
  exact original_loaded_top_entry e f

theorem actual_donor_environment_read (e f : Fin 2) :
    (BodyKernel.slice actualHamiltonian e f*actualDonor).trace =
      (donorEnergy : ℂ)*(if e=f then 1 else 0)+Powered.Dynamics.controllerHamiltonian 2 e f := by
  unfold actualHamiltonian actualDonor installedLoadFrame
  have slice : BodyKernel.slice (Quantum.conjugation (spectatorFrame (κ := Fin 2) installedPCFrame) loadTotalHamiltonian) e f =
      Quantum.conjugation installedPCFrame (BodyKernel.slice loadTotalHamiltonian e f) :=
    BodyKernel.slice_local_conjugation installedPCFrame loadTotalHamiltonian e f
  rw [slice,BasisInverse.conjugation_pair]
  exact original_donor_environment_read e f

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
