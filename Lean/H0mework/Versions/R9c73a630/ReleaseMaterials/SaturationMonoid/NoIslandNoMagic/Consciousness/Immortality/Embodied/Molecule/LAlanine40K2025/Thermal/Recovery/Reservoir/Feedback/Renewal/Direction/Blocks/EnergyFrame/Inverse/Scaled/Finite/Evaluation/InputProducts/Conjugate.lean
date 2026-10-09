import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.ProductSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts.Word

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
open Spectral Propagation.Interface
open scoped Matrix BigOperators

def negativeRows (rows : List (List Int)) : List (List Int) := rows.map (fun row => row.map Neg.neg)

theorem negative_row (rows : List (List Int)) (length : rows.length=98) (j : Basis) :
    Rows.rowAt (negativeRows rows) j=(Rows.rowAt rows j).map Neg.neg := by
  have hj : j.val < rows.length := by rw [length]; exact j.isLt
  simp only [Rows.rowAt,negativeRows,getElem!_pos,List.length_map,hj,List.getElem_map]

theorem negative_read (row : List Int) (length : row.length=98) (i : Basis) :
    Rows.read (row.map Neg.neg) i=-Rows.read row i := by
  have hi : i.val < row.length := by rw [length]; exact i.isLt
  simp only [Rows.read,getElem!_pos,List.length_map,hi,List.getElem_map]

theorem negative_lengths (rows : List (List Int)) (length : rows.length=98)
    (lengths : ∀ i : Basis, (Rows.rowAt rows i).length=98) (i : Basis) :
    (Rows.rowAt (negativeRows rows) i).length=98 := by
  rw [negative_row rows length i,List.length_map]
  exact lengths i

theorem negative_columns (rows : List (List Int)) (length : rows.length=98)
    (lengths : ∀ i : Basis, (Rows.rowAt rows i).length=98) :
    Rows.columnMatrix (n := 98) (negativeRows rows)=-(Rows.rowMatrix (n := 98) rows).transpose := by
  ext i j
  change Rows.read (Rows.rowAt (negativeRows rows) j) i=-Rows.read (Rows.rowAt rows j) i
  rw [negative_row rows length j,negative_read _ (lengths j) i]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.InputProducts
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
