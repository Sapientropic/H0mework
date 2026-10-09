import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Upper
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Lower

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem original_five_literal_norm : ‖rationalCore‖=
    max (max ‖block0‖ ‖block1‖) (max (max ‖block2‖ ‖block3‖) ‖block4‖) := by
  have d0 := original_rational_diagonal_block (0 : Fin 97)
  have d96 := original_rational_diagonal_block (96 : Fin 97)
  rw [show (0 : Fin 97).castSucc=(0 : Basis) from by decide +kernel] at d0
  rw [show (96 : Fin 97).castSucc=(96 : Basis) from by decide +kernel] at d96
  rw [original_whole_norm_exact]
  unfold wholeNormBound offDiagonalNormBound diagonalNormBound donorNorm
  rw [original_rational_block 0 1 (by decide),original_rational_block 96 97 (by decide),
    d0,d96,source_donor_core,
    source_block0,source_block1,source_block2,source_block3,source_block4]
  simp only [reindex_norm]

theorem original_rational_norm_interval :
    (480362644761/10^10 : ℝ) ≤ ‖rationalCore‖ ∧ ‖rationalCore‖ ≤ (480362644764/10^10 : ℝ) := by
  rw [original_five_literal_norm]
  exact ⟨block0_norm_lower.trans ((le_max_left _ _).trans (le_max_left _ _)),
    max_le (max_le block0_norm_upper block1_norm_upper)
      (max_le (max_le block2_norm_upper block3_norm_upper) block4_norm_upper)⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
