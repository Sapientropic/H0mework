import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Check
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Word

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators

def WeightedCheck (r i c e : List Int) : Prop :=
  ∀ j : Basis, |Rows.read r j*gibbsInt j-gibbsTotal*Rows.read c j|+
    |Rows.read i j*gibbsInt j-gibbsTotal*Rows.read e j| ≤ gibbsTotal

theorem weighted_product_bound (R I C D : List (List Int))
    (checked : ∀ i : Basis, WeightedCheck (Rows.rowAt R i) (Rows.rowAt I i) (Rows.rowAt C i) (Rows.rowAt D i)) :
    ∀ i j : Basis,
      |((Rows.rowMatrix (n := 98) R)*Matrix.diagonal gibbsInt) i j-gibbsTotal*Rows.rowMatrix (n := 98) C i j|+
      |((Rows.rowMatrix (n := 98) I)*Matrix.diagonal gibbsInt) i j-gibbsTotal*Rows.rowMatrix (n := 98) D i j| ≤ gibbsTotal := by
  intro i j
  simpa only [Matrix.mul_diagonal,Rows.rowMatrix] using checked i j

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
