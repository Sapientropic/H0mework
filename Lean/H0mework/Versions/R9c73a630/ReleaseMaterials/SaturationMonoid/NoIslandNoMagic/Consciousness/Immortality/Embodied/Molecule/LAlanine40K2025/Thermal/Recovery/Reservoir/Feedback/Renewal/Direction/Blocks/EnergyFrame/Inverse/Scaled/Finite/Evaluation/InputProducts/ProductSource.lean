import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Check
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Word

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators

def zeroRow : List Int := List.replicate 98 0
def zeroColumns : List (List Int) := List.replicate 98 zeroRow

theorem zero_column (j : Basis) : Rows.rowAt zeroColumns j=zeroRow := by
  change (List.replicate 98 zeroRow)[j.val]! = zeroRow
  rw [getElem!_pos _ _ (by simpa only [List.length_replicate] using j.isLt),List.getElem_replicate]

theorem zero_row_read (i : Basis) : Rows.read zeroRow i=0 := by
  change (List.replicate 98 (0 : Int))[i.val]! = 0
  rw [getElem!_pos _ _ (by simpa only [List.length_replicate] using i.isLt),List.getElem_replicate]

theorem zero_column_length (j : Basis) : (Rows.rowAt zeroColumns j).length=98 := by
  rw [zero_column]
  rfl

theorem zero_matrix : Rows.columnMatrix (n := 98) zeroColumns=0 := by
  ext i j
  change Rows.read (Rows.rowAt zeroColumns j) i=0
  rw [zero_column,zero_row_read]

theorem gram_columns : Rows.columnMatrix (n := 98) Dense.densityGramRows=Dense.densityGramInt := by
  change Dense.densityGramInt.transpose=Dense.densityGramInt
  rw [← Dense.original_density_full_gram,Matrix.transpose_mul,Matrix.transpose_transpose]

def systemMiddleDenominator : Int := Dense.densitySquaredMass*10^54

theorem system_middle_denominator_positive : 0 < systemMiddleDenominator := by decide +kernel

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
