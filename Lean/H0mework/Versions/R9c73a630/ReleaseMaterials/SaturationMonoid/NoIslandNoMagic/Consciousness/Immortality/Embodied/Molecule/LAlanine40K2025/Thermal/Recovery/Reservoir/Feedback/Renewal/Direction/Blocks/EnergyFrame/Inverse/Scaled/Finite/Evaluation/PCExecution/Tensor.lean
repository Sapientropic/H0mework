import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution.Bounds

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
open Load.Producer.StrictThermal
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem tensor_change (A C : Matrix ι ι ℂ) (B D : Matrix κ κ ℂ) :
    ‖Matrix.kronecker A B-Matrix.kronecker C D‖ ≤ ‖A-C‖*‖B‖+‖C‖*‖B-D‖ := by
  have split : Matrix.kronecker A B-Matrix.kronecker C D=
      Matrix.kronecker (A-C) B+Matrix.kronecker C (B-D) := by
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,Matrix.add_apply]
    ring
  rw [split]
  exact (norm_add_le _ _).trans (add_le_add (kronecker_norm_le _ _) (kronecker_norm_le _ _))

theorem tensor_left_change (A C : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    ‖Matrix.kronecker A B-Matrix.kronecker C B‖ ≤ ‖A-C‖*‖B‖ := by
  have p := tensor_change A C B B
  simpa only [sub_self,norm_zero,mul_zero,add_zero] using p

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.PCExecution
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
