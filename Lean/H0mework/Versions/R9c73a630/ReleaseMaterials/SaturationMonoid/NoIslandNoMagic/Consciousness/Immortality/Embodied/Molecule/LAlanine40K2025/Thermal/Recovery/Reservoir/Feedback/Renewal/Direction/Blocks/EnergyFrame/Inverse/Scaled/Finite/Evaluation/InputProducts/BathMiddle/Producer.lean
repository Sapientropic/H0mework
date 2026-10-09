import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.BathMiddle.All
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Matrices
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Rounded

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem bath_middle_actual_error : ‖bathMiddle-Field.computedPolynomial*Diagonal.computedGibbs‖ ≤ (1/10^22 : ℝ) := by
  have checked := weighted_product_bound Operands.fieldRRows Operands.fieldIRows
    Products.bathMiddleRRows Products.bathMiddleIRows Products.bath_middle_all
  rw [Operands.fieldRRows_source,Operands.fieldIRows_source] at checked
  rw [original_field_values,original_gibbs_integer]
  apply rounded_product_error fieldRe fieldIm (Matrix.diagonal gibbsInt) 0 bathMiddleR bathMiddleI
    (10^24) gibbsTotal gibbsTotal gibbs_total_positive (by ring) ?_
  simpa only [Matrix.mul_zero,sub_zero,zero_add,bathMiddleR,bathMiddleI] using checked

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
