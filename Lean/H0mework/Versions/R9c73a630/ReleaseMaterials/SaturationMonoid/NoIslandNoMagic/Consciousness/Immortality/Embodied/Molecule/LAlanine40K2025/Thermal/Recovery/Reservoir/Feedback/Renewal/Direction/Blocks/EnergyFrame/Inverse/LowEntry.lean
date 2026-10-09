import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.LowEnergy

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def lowIndex (i : Basis) : PairController := ((i,i),0)

theorem original_low_load_entry (i : Basis) :
    loadTotalHamiltonian (lowIndex i,0) (lowIndex i,0) = 2*(Preparation.sourceEnergies i : ℂ)+1 := by
  have entry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (original_hpc_diagonal_block i)
  change Powered.Producer.poweredTotalHamiltonian ((i,i),0) ((i,i),0)=2*(Preparation.sourceEnergies i : ℂ)+1 at entry
  simp only [loadTotalHamiltonian,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
    Matrix.add_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,lowIndex,Matrix.one_apply]
  rw [entry]
  norm_num [Powered.Dynamics.controllerHamiltonian,loadInteraction,controllerEnvironmentExchange,Matrix.kronecker,Matrix.single]

theorem original_inverse_low_entry (i : Basis) :
    BasisInverse.bodyInverse Spectral.Projection.excitedIndex (Real.cos BasisInverse.actualAngle)
      (Real.sin BasisInverse.actualAngle) loadTotalHamiltonian (lowIndex i,0) (lowIndex i,0) =
      (2*(Preparation.sourceEnergies i : ℂ)+1-(Real.sin BasisInverse.actualAngle : ℂ)^2*(donorEnergy : ℂ))/
        (Real.cos BasisInverse.actualAngle : ℂ)^2 := by
  have different : lowIndex i ≠ Spectral.Projection.excitedIndex := by
    intro equal
    have h := congrArg Prod.snd equal
    norm_num [lowIndex,Spectral.Projection.excitedIndex] at h
  simp only [BasisInverse.bodyInverse,BasisInverse.inverse,if_neg different,ite_true,
    BodyKernel.slice,Matrix.submatrix_apply]
  rw [original_low_load_entry,original_loaded_top_entry]
  norm_num [Powered.Dynamics.controllerHamiltonian]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
