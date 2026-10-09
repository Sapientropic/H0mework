import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor.Projector

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
open Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
theorem basis_tensor (i : ι) (k : κ) :
    Matrix.kronecker (Spectrum.basisPure i) (Spectrum.basisPure k) = Spectrum.basisPure (i,k) := by
  ext a b
  rcases a with ⟨a,c⟩
  rcases b with ⟨b,d⟩
  simp only [Spectrum.basisPure,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.diagonal_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype κ] [DecidableEq κ] in
theorem paired_state_error (P Q : Matrix ι ι ℂ) (first : ‖P‖ ≤ 1) (second : ‖Q‖ ≤ 1) :
    ‖Matrix.kronecker P P-Matrix.kronecker Q Q‖ ≤ 2*‖P-Q‖ := by
  have split : Matrix.kronecker P P-Matrix.kronecker Q Q =
      Matrix.kronecker (P-Q) P+Matrix.kronecker Q (P-Q) := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,Matrix.add_apply]
    ring
  rw [split]
  calc
    _ ≤ ‖Matrix.kronecker (P-Q) P‖+‖Matrix.kronecker Q (P-Q)‖ := norm_add_le _ _
    _ ≤ ‖P-Q‖*‖P‖+‖Q‖*‖P-Q‖ := add_le_add (kronecker_norm_le _ _) (kronecker_norm_le _ _)
    _ ≤ ‖P-Q‖*1+1*‖P-Q‖ := by gcongr
    _ = _ := by ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Donor
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
