import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Norm

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def diagonalPCE (a : Basis) (p : Fin 2 × Fin 2) : PairController × Fin 2 := (((a,a),p.1),p.2)
def diagonalLoaded (x : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Powered.Dynamics.totalHamiltonian (diagonalHpc x) 2 controllerEnvironmentExchange

theorem numeric_diagonal_PC (a : Basis) :
    (sourcePCH E).submatrix (fun c : Fin 2 => ((a,a),c)) (fun c : Fin 2 => ((a,a),c))=
      diagonalHpc (Donor.calculatedEnergy a) := by
  rw [source_E_diagonal]
  exact hpc_diagonal_block Donor.calculatedEnergy a

theorem diagonal_CE (a : Basis) :
    loadInteraction.submatrix (diagonalPCE a) (diagonalPCE a)=controllerEnvironmentExchange := by
  ext i j
  simp [loadInteraction,diagonalPCE,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.submatrix_apply]

theorem numeric_diagonal_load (a : Basis) :
    numericLoadHamiltonian.submatrix (diagonalPCE a) (diagonalPCE a)=diagonalLoaded (Donor.calculatedEnergy a) := by
  have hpc := numeric_diagonal_PC a
  have ce := diagonal_CE a
  ext i j
  have hi := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i.1 j.1) hpc
  have ci := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M i j) ce
  simp only [numericLoadHamiltonian,diagonalLoaded,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
    Matrix.submatrix_apply,Matrix.add_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,diagonalPCE,Matrix.one_apply] at hi ci ⊢
  rw [hi,ci]
  simp

theorem diagonal_environment (a : Basis) :
    (Matrix.kronecker (1 : Matrix PairController PairController ℂ) numericEnvironmentRead).submatrix
      (diagonalPCE a) (diagonalPCE a)=Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) numericEnvironmentRead := by
  ext i j
  simp [Matrix.submatrix_apply,diagonalPCE,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.one_apply]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
