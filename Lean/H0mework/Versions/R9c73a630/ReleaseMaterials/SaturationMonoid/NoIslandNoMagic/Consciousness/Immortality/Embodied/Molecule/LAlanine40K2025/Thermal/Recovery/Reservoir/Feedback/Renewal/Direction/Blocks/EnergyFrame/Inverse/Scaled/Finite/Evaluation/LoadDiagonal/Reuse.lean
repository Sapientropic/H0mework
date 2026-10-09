import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Reuse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.DiagonalMaterial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
open Propagation.Interface

theorem lower_energy (a : Basis) : LoadPrimitive.sourceSum a a 1=Primitive.diagonalScalarEnergy a 0 := by
  simp only [LoadPrimitive.sourceSum,Primitive.diagonalScalarEnergy,Fin.val_zero,Nat.cast_zero,mul_zero,add_zero]
  ring

theorem centre_energy (a : Basis) : LoadPrimitive.sourceSum a a 3=Primitive.diagonalScalarEnergy a 1 := by
  simp only [LoadPrimitive.sourceSum,Primitive.diagonalScalarEnergy,Fin.val_one,Nat.cast_one,mul_one]
  ring

theorem reuse_lower_error (a : Basis) (M : Primitive.DiagonalMaterial a) :
    Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (LoadPrimitive.sourceSum a a 1) 1) 14) (M 0).one ≤ (1/10^24 : ℚ) := by
  rw [lower_energy]
  exact (M 0).one_error

theorem reuse_centre_error (a : Basis) (M : Primitive.DiagonalMaterial a) :
    Scalar.distance (LoadPrimitive.sourceCoefficient a a 3 0) (M 1).one ≤ (1/10^24 : ℚ) := by
  rw [LoadPrimitive.source_zero_raw,centre_energy]
  exact (M 1).one_error

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadDiagonal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
