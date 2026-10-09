import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.SourceValues
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCMaterial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Propagation.Producer
open scoped Matrix BigOperators

theorem scalar_value_injective : Function.Injective Scalar.value := by
  intro z w same
  apply Prod.ext
  · have h := congrArg Complex.re same
    simp [Scalar.value] at h
    exact_mod_cast h
  · have h := congrArg Complex.im same
    simp [Scalar.value] at h
    exact_mod_cast h

theorem source_zero_raw (a b : Basis) (offset : ℚ) :
    sourceCoefficient a b offset 0=Scalar.polynomial (Primitive.scalarSeed (sourceSum a b offset) 1) 14 :=
  scalar_value_injective (source_zero_scalar a b offset)

theorem source_sum_three (a b : Basis) : sourceSum a b 3=Primitive.scalarEnergy a b 1 := rfl

theorem source_sum_minus_one (a b : Basis) : sourceSum a b (-1)=Primitive.scalarEnergy a b 0 := by
  simp [sourceSum,Primitive.scalarEnergy,sub_eq_add_neg]

theorem reuse_minus_zero_error (a b : Basis) (M : Primitive.PCMaterial a b) :
    Scalar.distance (sourceCoefficient a b 3 0) (M 1).one ≤ (1/10^24 : ℚ) := by
  rw [source_zero_raw,source_sum_three]
  exact (M 1).one_error

theorem reuse_lower_error (a b : Basis) (M : Primitive.PCMaterial a b) :
    Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum a b (-1)) 1) 14) (M 0).one ≤ (1/10^24 : ℚ) := by
  rw [source_sum_minus_one]
  exact (M 0).one_error

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
