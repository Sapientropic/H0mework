import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ReversePC

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Collision Propagation.Interface Load.Source Powered.Source Powered.Dynamics
open scoped Matrix
noncomputable section

def packedBare (x y : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![x+y,0,1,0],![0,x+y+2,0,1],![1,0,x+y,0],![0,1,0,x+y+2]]

def scalarBare (x y : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (packedBare x y).submatrix finProdFinEquiv finProdFinEquiv

theorem source_reverse_split (H : Matrix Basis Basis ℂ) :
    Actions.reversePCH H=(2 : ℂ) • bareHamiltonian (pairHamiltonian H) 2-sourcePCH H := by
  unfold Actions.reversePCH sourcePCH totalHamiltonian
  module

theorem bare_scalar_block (energies : Basis → ℝ) (a b : Basis) (distinct : a ≠ b) :
    (bareHamiltonian (Dynamics.pairH (Matrix.diagonal (fun i => (energies i : ℂ))) 1) 2).submatrix
      (orbitPC a b) (orbitPC a b)=scalarBare (energies a) (energies b) := by
  ext ⟨p,c⟩ ⟨q,d⟩
  fin_cases p <;> fin_cases c <;> fin_cases q <;> fin_cases d <;>
    norm_num [bareHamiltonian,Dynamics.pairH,Dynamics.freePairH,jointHamiltonian,
      Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply,Matrix.one_apply,Powered.Dynamics.controllerHamiltonian,swap_entry,orbitPC,scalarBare,packedBare,
      Matrix.submatrix,finProdFinEquiv,distinct,Ne.symm distinct,smul_eq_mul] <;> ring

theorem original_bare_scalar (a b : Basis) (distinct : a ≠ b) :
    (bareHamiltonian (pairHamiltonian E) 2).submatrix (orbitPC a b) (orbitPC a b)=
      scalarBare (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) := by
  rw [Scaled.Order.source_E_diagonal]
  exact bare_scalar_block Donor.calculatedEnergy a b distinct

theorem reverse_scalar_identity (x y : ℝ) :
    (2 : ℂ) • scalarBare x y-scalarHpc x y=smallControllerSign*scalarHpc x y*smallControllerSign := by
  ext ⟨p,c⟩ ⟨q,d⟩
  fin_cases p <;> fin_cases c <;> fin_cases q <;> fin_cases d <;>
    norm_num [scalarBare,packedBare,scalarHpc,packedHpc,smallControllerSign,controllerSign,
      Matrix.mul_apply,Fin.sum_univ_succ,Fintype.sum_prod_type,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply,Matrix.one_apply,Matrix.submatrix,finProdFinEquiv,Matrix.smul_apply,Matrix.sub_apply,
      smul_eq_mul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div] <;> ring

theorem original_reverse_scalar (a b : Basis) (distinct : a ≠ b) :
    (Actions.reversePCH E).submatrix (orbitPC a b) (orbitPC a b)=
      smallControllerSign*scalarHpc (Donor.calculatedEnergy a) (Donor.calculatedEnergy b)*smallControllerSign := by
  rw [source_reverse_split,Matrix.submatrix_sub,Matrix.submatrix_smul]
  simp only [Pi.sub_apply,Pi.smul_apply]
  rw [original_bare_scalar a b distinct,Scaled.Order.numeric_hpc_block a b distinct,reverse_scalar_identity]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
