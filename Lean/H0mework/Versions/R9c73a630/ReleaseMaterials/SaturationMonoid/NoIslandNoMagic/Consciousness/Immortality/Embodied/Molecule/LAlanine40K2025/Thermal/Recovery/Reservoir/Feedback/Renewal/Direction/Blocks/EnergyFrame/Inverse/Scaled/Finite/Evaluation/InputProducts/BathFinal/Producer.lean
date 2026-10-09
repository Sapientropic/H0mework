import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.BathFinal.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Matrices
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Rounded

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem bath_final_actual_error : ‖bath-bathMiddle*star Field.computedPolynomial‖ ≤ (1/10^22 : ℝ) := by
  have checked := checked_product Products.bathMiddleRRows Products.bathMiddleIRows Operands.fieldRRows
    (negativeRows Operands.fieldIRows) Products.bathRRows Products.bathIRows 1 (10^24)
    Products.bathMiddleRRows_lengths Products.bathMiddleIRows_lengths Operands.fieldRRows_lengths
    (negative_lengths _ Operands.fieldIRows_length Operands.fieldIRows_lengths) Products.bath_final_all
  have realColumns : Rows.columnMatrix (n := 98) Operands.fieldRRows=fieldRe.transpose := by
    change (Rows.rowMatrix (n := 98) Operands.fieldRRows).transpose=fieldRe.transpose
    rw [Operands.fieldRRows_source]
  rw [realColumns,negative_columns _ Operands.fieldIRows_length Operands.fieldIRows_lengths,Operands.fieldIRows_source] at checked
  rw [original_field_values,scaledMatrix_star]
  apply rounded_product_error bathMiddleR bathMiddleI fieldRe.transpose (-fieldIm.transpose) bathR bathI
    (10^24) (10^24) (10^24) (by norm_num) rfl ?_
  simpa only [one_mul,bathMiddleR,bathMiddleI,bathR,bathI] using checked

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
