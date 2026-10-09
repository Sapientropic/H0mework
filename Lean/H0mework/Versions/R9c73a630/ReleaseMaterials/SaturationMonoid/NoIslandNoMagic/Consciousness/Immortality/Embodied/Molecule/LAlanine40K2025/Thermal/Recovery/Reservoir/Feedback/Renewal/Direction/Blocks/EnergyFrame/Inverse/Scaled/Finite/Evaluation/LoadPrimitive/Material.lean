import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Reuse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.PCMaterial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open Propagation.Interface Propagation.Producer
open scoped Matrix BigOperators

def coefficientBudget (k : Fin 3) : ℚ := if k=0 then 1/10^24 else 1/10^30

structure Material (a b : Basis) where
  plus : Fin 3 → Scalar.QComplex
  minus : Fin 3 → Scalar.QComplex
  upper : Scalar.QComplex
  lower : Scalar.QComplex
  plus_error : ∀ k, Scalar.distance (sourceCoefficient a b 1 k) (plus k) ≤ coefficientBudget k
  minus_error : ∀ k, Scalar.distance (sourceCoefficient a b 3 k) (minus k) ≤ coefficientBudget k
  upper_error : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum a b 5) 1) 14) upper ≤ (1/10^30 : ℚ)
  lower_error : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum a b (-1)) 1) 14) lower ≤ (1/10^24 : ℚ)

theorem scalar_error (z w : Scalar.QComplex) (d : ℚ) (checked : Scalar.distance z w ≤ d) :
    ‖Scalar.value z-Scalar.value w‖ ≤ (d : ℝ) :=
  (Scalar.value_distance z w).trans (Diagonal.rational_order checked)

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
