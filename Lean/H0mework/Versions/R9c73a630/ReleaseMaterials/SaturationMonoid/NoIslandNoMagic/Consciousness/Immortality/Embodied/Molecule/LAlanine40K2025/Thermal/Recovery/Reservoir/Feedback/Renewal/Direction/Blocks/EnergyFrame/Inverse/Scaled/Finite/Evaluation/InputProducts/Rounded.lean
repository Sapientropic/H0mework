import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.ProductAlgebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Residual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators Matrix.Norms.L2Operator
noncomputable section

theorem rounded_product_error (R I A B C D : Matrix Basis Basis Int) (leftScale rightScale denominator : Int)
    (positive : 0 < denominator) (scale : leftScale*rightScale=denominator*10^24)
    (bound : ∀ i j, |(R*A-I*B) i j-denominator*C i j|+|(R*B+I*A) i j-denominator*D i j| ≤ denominator) :
    ‖scaledMatrix C D (10^24)-scaledMatrix R I leftScale*scaledMatrix A B rightScale‖ ≤ (1/10^22 : ℝ) := by
  rw [scaled_product_form,scale]
  have h := complex_product_residual R I A B C D 1 denominator positive
    (by simpa only [one_mul] using bound)
  simpa only [Int.cast_one,one_div,Int.cast_mul,Int.cast_pow,Int.cast_ofNat] using h

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
