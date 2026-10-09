import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def orbitPCE (a b : Basis) (p : (Fin 2 × Fin 2) × Fin 2) : PairController × Fin 2 := (orbitPC a b p.1,p.2)

def smallExchange : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) controllerEnvironmentExchange).submatrix
    (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)) (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2))

def smallLoaded (x y : ℝ) : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ :=
  Powered.Dynamics.totalHamiltonian (scalarHpc x y) 2 smallExchange

theorem orbitPC_injective (a b : Basis) (distinct : a ≠ b) : Function.Injective (orbitPC a b) := by
  intro i j same
  apply (offDiagonalEquiv a b distinct).injective
  exact Subtype.ext same

theorem original_load_interaction_block (a b : Basis) (distinct : a ≠ b) :
    loadInteraction.submatrix (orbitPCE a b) (orbitPCE a b)=smallExchange := by
  ext ⟨⟨p,c⟩,e⟩ ⟨⟨q,d⟩,f⟩
  fin_cases p <;> fin_cases q <;>
    simp [loadInteraction,smallExchange,orbitPCE,orbitPC,Matrix.kronecker,Matrix.kroneckerMap_apply,
      Matrix.submatrix_apply,distinct,Ne.symm distinct]

theorem original_numeric_load_block (a b : Basis) (distinct : a ≠ b) :
    numericLoadHamiltonian.submatrix (orbitPCE a b) (orbitPCE a b)=
      smallLoaded (Donor.calculatedEnergy a) (Donor.calculatedEnergy b) := by
  have hpc := numeric_hpc_block a b distinct
  have v := original_load_interaction_block a b distinct
  ext i j
  have h := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ => M i.1 j.1) hpc
  have vi := congrArg (fun M : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ => M i j) v
  have same : orbitPC a b i.1=orbitPC a b j.1 ↔ i.1=j.1 := (orbitPC_injective a b distinct).eq_iff
  simp only [numericLoadHamiltonian,smallLoaded,Powered.Dynamics.totalHamiltonian,Powered.Dynamics.bareHamiltonian,
    Matrix.submatrix_apply,Matrix.add_apply,Matrix.kronecker,Matrix.kroneckerMap_apply,orbitPCE,Matrix.one_apply] at h vi ⊢
  rw [h,vi,if_congr same rfl rfl]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
