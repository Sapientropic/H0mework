import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.DiagonalAncilla
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Receiver

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def ancillaFrame (B : Matrix κ κ ℂ) (positive : B.PosSemidef) : Matrix.unitaryGroup (ι × κ) ℂ :=
  Load.Quantum.localUnitary (1 : Matrix.unitaryGroup ι ℂ) (star positive.isHermitian.eigenvectorUnitary)

def ancillaReadout (B : Matrix κ κ ℂ) (positive : B.PosSemidef) (O : Matrix (ι × κ) (ι × κ) ℂ) : Matrix ι ι ℂ :=
  diagonalReadout positive.isHermitian.eigenvalues (Quantum.conjugation (ancillaFrame B positive) O)

theorem ancilla_state (B : Matrix κ κ ℂ) (positive : B.PosSemidef) (rho : Matrix ι ι ℂ) :
    Quantum.conjugation (ancillaFrame B positive) (Matrix.kronecker rho B)=
      Matrix.kronecker rho (Matrix.diagonal (fun a => (positive.isHermitian.eigenvalues a : ℂ))) := by
  change Load.Quantum.localConjugation (1 : Matrix.unitaryGroup ι ℂ) (star positive.isHermitian.eigenvectorUnitary) (Matrix.kronecker rho B)=_
  rw [Load.Quantum.localConjugation_tensor]
  have one : Quantum.conjugation (1 : Matrix.unitaryGroup ι ℂ) rho=rho := by
    simp only [Quantum.conjugation_apply,Submonoid.coe_one,star_one,Matrix.one_mul,Matrix.mul_one]
  rw [one]
  change Matrix.kronecker rho (Unitary.conjStarAlgAut ℂ _ (star positive.isHermitian.eigenvectorUnitary) B)=_
  rw [positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
  rfl

theorem ancilla_readout_energy (B : Matrix κ κ ℂ) (positive : B.PosSemidef)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (rho : Matrix ι ι ℂ) :
    energy O (Matrix.kronecker rho B)=energy (ancillaReadout B positive O) rho := by
  have invariant := Work.Capacity.energy_unitary_conjugation O (Matrix.kronecker rho B) (ancillaFrame B positive)
  change energy (Quantum.conjugation (ancillaFrame B positive) O)
    (Quantum.conjugation (ancillaFrame B positive) (Matrix.kronecker rho B))=energy O (Matrix.kronecker rho B) at invariant
  rw [ancilla_state,diagonal_readout_energy] at invariant
  exact invariant.symm

attribute [local irreducible] ancillaFrame

theorem ancilla_readout_norm (B : Matrix κ κ ℂ) (positive : B.PosSemidef) (normalized : B.trace=1)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (hermitian : O.IsHermitian) : ‖ancillaReadout B positive O‖ ≤ ‖O‖ := by
  apply (diagonal_readout_norm positive.isHermitian.eigenvalues positive.eigenvalues_nonneg
    (Thermal.Quantum.eigenvalues_normalized B positive normalized) (Quantum.conjugation (ancillaFrame (ι := ι) B positive) O)
    (conjugation_hermitian (ancillaFrame B positive) O hermitian)).trans
  exact le_of_eq (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ (Matrix (ι × κ) (ι × κ) ℂ) (ancillaFrame (ι := ι) B positive)) O)

theorem ancilla_readout_hermitian (B : Matrix κ κ ℂ) (positive : B.PosSemidef)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (hermitian : O.IsHermitian) : (ancillaReadout B positive O).IsHermitian :=
  diagonal_readout_hermitian positive.isHermitian.eigenvalues _ (conjugation_hermitian (ancillaFrame B positive) O hermitian)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
