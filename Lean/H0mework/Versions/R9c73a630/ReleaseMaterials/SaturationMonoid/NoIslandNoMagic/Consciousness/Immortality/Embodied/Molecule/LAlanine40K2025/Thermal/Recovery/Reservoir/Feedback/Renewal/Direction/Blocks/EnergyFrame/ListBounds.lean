import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows
import Mathlib.Data.List.Zip

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral

variable {n : Nat}

theorem all_abs_bound (row : List Int) (length : row.length = n) (bound : Int)
    (checked : (row.map abs).all (· ≤ bound) = true) (i : Fin n) : |Rows.read row i| ≤ bound := by
  have boundIndex : i.val < row.length := by omega
  have present : row[i.val]! ∈ row := by
    rw [getElem!_pos row i.val boundIndex]
    exact List.getElem_mem boundIndex
  have member : |row[i.val]!| ∈ row.map abs := List.mem_map.mpr ⟨row[i.val]!,present,rfl⟩
  exact of_decide_eq_true (List.all_eq_true.mp checked _ member)

theorem all_difference_bound (row other : List Int) (length : row.length = n) (otherLength : other.length = n)
    (bound : Int) (checked : ((row.zip other).map (fun pair => |pair.1-pair.2|)).all (· ≤ bound) = true)
    (i : Fin n) : |Rows.read row i-Rows.read other i| ≤ bound := by
  have first : i.val < row.length := by omega
  have second : i.val < other.length := by omega
  have both : i.val < (row.zip other).length := by simp only [List.length_zip]; omega
  have entry : (row.zip other)[i.val]! = (row[i.val]!,other[i.val]!) := by
    simp [getElem!_pos,first,second]
  have member : (row[i.val]!,other[i.val]!) ∈ row.zip other := by
    rw [← entry]
    rw [getElem!_pos (row.zip other) i.val both]
    exact List.getElem_mem both
  exact of_decide_eq_true (List.all_eq_true.mp checked _ (List.mem_map.mpr ⟨_,member,rfl⟩))

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
