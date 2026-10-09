import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared.Corners
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.BinaryPointerDilation

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
open Collision
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pointerReadout (O : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) : Matrix ι ι ℂ := O.submatrix Sum.inl Sum.inl

theorem pointer_readout_norm (O : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hermitian : O.IsHermitian) :
    ‖pointerReadout O‖ ≤ ‖O‖ := principal_norm Sum.inl Sum.inl_injective O hermitian

omit [Fintype ι] [DecidableEq ι] in
theorem pointer_readout_hermitian (O : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hermitian : O.IsHermitian) :
    (pointerReadout O).IsHermitian := hermitian.submatrix Sum.inl

omit [DecidableEq ι] in
theorem pointer_readout_energy (O : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (rho : Matrix ι ι ℂ) :
    energy O (prepared rho)=energy (pointerReadout O) rho := by
  simp [energy,prepared,pointerReadout,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fintype.sum_sum_type]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Prepared
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
