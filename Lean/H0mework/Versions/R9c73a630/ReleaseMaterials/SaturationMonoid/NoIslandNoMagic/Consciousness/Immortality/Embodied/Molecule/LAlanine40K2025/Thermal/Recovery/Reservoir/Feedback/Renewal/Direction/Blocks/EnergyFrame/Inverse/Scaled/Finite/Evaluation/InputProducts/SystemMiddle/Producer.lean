import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.SystemMiddle.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Matrices
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Rounded

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem system_middle_actual_error : ‖systemMiddle-Field.computedSystemWord*Dense.computedBase‖ ≤ (1/10^22 : ℝ) := by
  have checked := checked_product Operands.wordRRows Operands.wordIRows Dense.densityGramRows zeroColumns
    Products.systemMiddleRRows Products.systemMiddleIRows 1 systemMiddleDenominator
    Operands.wordRRows_lengths Operands.wordIRows_lengths Dense.densityGramRows_lengths zero_column_length
    Products.system_middle_all
  rw [Operands.wordRRows_source,Operands.wordIRows_source,gram_columns,zero_matrix] at checked
  simp only [Matrix.mul_zero,sub_zero,zero_add,one_mul] at checked
  rw [original_system_word_integer,original_base_integer]
  apply rounded_product_error wordRe wordIm Dense.densityGramInt 0 systemMiddleR systemMiddleI
    (10^48) baseDenominator systemMiddleDenominator system_middle_denominator_positive ?_ ?_
  · unfold baseDenominator systemMiddleDenominator
    ring
  · simpa only [Matrix.mul_zero,sub_zero,zero_add,systemMiddleR,systemMiddleI] using checked

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
