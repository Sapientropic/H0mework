import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Expansion.Rows1

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
open Propagation.Interface Load.Source Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem ordinary_expanded (x y : ℝ) : ordinaryCore x y=
    (expandedCore x y (sineHat^2) numericDonorEnergy).submatrix tripleIndex tripleIndex := by
  ext ⟨⟨o,c⟩,e⟩ j
  fin_cases o <;> fin_cases c <;> fin_cases e
  · exact expanded_row0 x y j
  · exact expanded_row1 x y j
  · exact expanded_row2 x y j
  · exact expanded_row3 x y j
  · exact expanded_row4 x y j
  · exact expanded_row5 x y j
  · exact expanded_row6 x y j
  · exact expanded_row7 x y j

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
