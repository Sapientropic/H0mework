import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.DiagonalNorm
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order.Fibers

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open Propagation.Interface Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

theorem original_whole_norm_upper : ‖rationalCore‖ ≤ wholeNormBound := by
  apply (norm_le_iff_block_norm_le rational_core_preserves wholeNormBound whole_bound_nonnegative).mpr
  intro k
  obtain ⟨⟨a,b⟩,rfl⟩ := Sym2.mk_surjective k
  change ‖restrict pceOrbit s(a,b) rationalCore‖ ≤ wholeNormBound
  rcases lt_trichotomy a b with ordered | same | reverse
  · rw [offDiagonal_fiber_norm a b ordered.ne]
    exact (all_offDiagonal_norm a b ordered).trans (le_max_left _ _)
  · subst b
    rw [diagonal_fiber_norm]
    exact (all_diagonal_norm a).trans (le_max_right _ _)
  · rw [Sym2.eq_swap,offDiagonal_fiber_norm b a reverse.ne]
    exact (all_offDiagonal_norm b a reverse).trans (le_max_left _ _)

theorem original_fiber_norm_lower (k : Sym2 Basis) : ‖restrict pceOrbit k rationalCore‖ ≤ ‖rationalCore‖ := by
  rw [norm_eq_block_norm rational_core_preserves]
  exact norm_le_pi_norm (fun k => restrict pceOrbit k rationalCore) k

theorem original_whole_norm_exact : ‖rationalCore‖=wholeNormBound := by
  apply le_antisymm original_whole_norm_upper
  unfold wholeNormBound offDiagonalNormBound diagonalNormBound donorNorm
  apply max_le
  · apply max_le
    · rw [← offDiagonal_fiber_norm 0 1 (by decide)]
      exact original_fiber_norm_lower _
    · rw [← offDiagonal_fiber_norm 96 97 (by decide)]
      exact original_fiber_norm_lower _
  · apply max_le
    · apply max_le
      · rw [← diagonal_fiber_norm]
        exact original_fiber_norm_lower _
      · rw [← diagonal_fiber_norm]
        exact original_fiber_norm_lower _
    · rw [← diagonal_fiber_norm]
      exact original_fiber_norm_lower _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
