import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal.Reuse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalMaterial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
open Propagation.Interface

structure Material (a : Basis) where
  lower : Scalar.QComplex
  centre : Scalar.QComplex
  beta : Scalar.QComplex
  gamma : Scalar.QComplex
  upper : Scalar.QComplex
  lower_error : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (LoadPrimitive.sourceSum a a 1) 1) 14) lower ≤ (1/10^24 : ℚ)
  centre_error : Scalar.distance (LoadPrimitive.sourceCoefficient a a 3 0) centre ≤ (1/10^24 : ℚ)
  beta_error : Scalar.distance (LoadPrimitive.sourceCoefficient a a 3 1) beta ≤ (1/10^30 : ℚ)
  gamma_error : Scalar.distance (LoadPrimitive.sourceCoefficient a a 3 2) gamma ≤ (1/10^30 : ℚ)
  upper_error : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (LoadPrimitive.sourceSum a a 5) 1) 14) upper ≤ (1/10^30 : ℚ)

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
