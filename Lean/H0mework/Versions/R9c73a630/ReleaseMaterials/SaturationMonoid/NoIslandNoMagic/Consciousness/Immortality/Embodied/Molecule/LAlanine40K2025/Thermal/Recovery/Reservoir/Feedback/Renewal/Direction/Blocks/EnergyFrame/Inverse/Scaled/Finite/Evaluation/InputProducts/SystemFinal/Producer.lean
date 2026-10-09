import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.SystemFinal.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Matrices
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Rounded

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem system_final_actual_error : ‖system-systemMiddle*star Field.computedSystemWord‖ ≤ (1/10^22 : ℝ) := by
  have checked := checked_product Products.systemMiddleRRows Products.systemMiddleIRows Operands.wordRRows
    (negativeRows Operands.wordIRows) Products.systemRRows Products.systemIRows 1 (10^48)
    Products.systemMiddleRRows_lengths Products.systemMiddleIRows_lengths Operands.wordRRows_lengths
    (negative_lengths _ Operands.wordIRows_length Operands.wordIRows_lengths) Products.system_final_all
  have realColumns : Rows.columnMatrix (n := 98) Operands.wordRRows=wordRe.transpose := by
    change (Rows.rowMatrix (n := 98) Operands.wordRRows).transpose=wordRe.transpose
    rw [Operands.wordRRows_source]
  rw [realColumns,negative_columns _ Operands.wordIRows_length Operands.wordIRows_lengths,Operands.wordIRows_source] at checked
  rw [original_system_word_integer,scaledMatrix_star]
  apply rounded_product_error systemMiddleR systemMiddleI wordRe.transpose (-wordIm.transpose) systemR systemI
    (10^24) (10^48) (10^48) (by norm_num) (by ring) ?_
  simpa only [one_mul,systemMiddleR,systemMiddleI,systemR,systemI] using checked

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
