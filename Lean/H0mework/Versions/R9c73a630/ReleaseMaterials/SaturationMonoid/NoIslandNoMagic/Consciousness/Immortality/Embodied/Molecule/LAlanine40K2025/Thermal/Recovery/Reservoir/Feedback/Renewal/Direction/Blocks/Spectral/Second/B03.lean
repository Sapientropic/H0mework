import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Second
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Vector
import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.B03

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
namespace Second
open Propagation.Interface
open Witness.Second

theorem sourceDeltaRow21 (j : Basis) : sourceRows21[j.val]! =
    Witness.Upper.sourceRows21[j.val]! - (if j = (21 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[21]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow21 (j : Basis) : sourceRows21[j.val]! =
    (if j = (21 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (21 : Basis) j + 1000*Witness.vector[21]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow21, Upper.sourceRow21]
  split_ifs <;> ring

theorem firstColumn21 : firstColumns21 = sourceRows.map (fun row => Rows.dot row basisColumns21) := by rfl

theorem gramRow21 : gramRows21 = firstColumns.map (Rows.dot basisColumns21) := by rfl

theorem dominanceRow21 : 0 < Rows.margin gramRows21 (⟨21, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength21 : sourceRows21.length = 98 := by rfl
theorem basisColumnsLength21 : basisColumns21.length = 98 := by rfl
theorem firstColumnsLength21 : firstColumns21.length = 98 := by rfl
theorem gramRowsLength21 : gramRows21.length = 98 := by rfl

theorem sourceDeltaRow22 (j : Basis) : sourceRows22[j.val]! =
    Witness.Upper.sourceRows22[j.val]! - (if j = (22 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[22]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow22 (j : Basis) : sourceRows22[j.val]! =
    (if j = (22 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (22 : Basis) j + 1000*Witness.vector[22]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow22, Upper.sourceRow22]
  split_ifs <;> ring

theorem firstColumn22 : firstColumns22 = sourceRows.map (fun row => Rows.dot row basisColumns22) := by rfl

theorem gramRow22 : gramRows22 = firstColumns.map (Rows.dot basisColumns22) := by rfl

theorem dominanceRow22 : 0 < Rows.margin gramRows22 (⟨22, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength22 : sourceRows22.length = 98 := by rfl
theorem basisColumnsLength22 : basisColumns22.length = 98 := by rfl
theorem firstColumnsLength22 : firstColumns22.length = 98 := by rfl
theorem gramRowsLength22 : gramRows22.length = 98 := by rfl

theorem sourceDeltaRow23 (j : Basis) : sourceRows23[j.val]! =
    Witness.Upper.sourceRows23[j.val]! - (if j = (23 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[23]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow23 (j : Basis) : sourceRows23[j.val]! =
    (if j = (23 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (23 : Basis) j + 1000*Witness.vector[23]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow23, Upper.sourceRow23]
  split_ifs <;> ring

theorem firstColumn23 : firstColumns23 = sourceRows.map (fun row => Rows.dot row basisColumns23) := by rfl

theorem gramRow23 : gramRows23 = firstColumns.map (Rows.dot basisColumns23) := by rfl

theorem dominanceRow23 : 0 < Rows.margin gramRows23 (⟨23, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength23 : sourceRows23.length = 98 := by rfl
theorem basisColumnsLength23 : basisColumns23.length = 98 := by rfl
theorem firstColumnsLength23 : firstColumns23.length = 98 := by rfl
theorem gramRowsLength23 : gramRows23.length = 98 := by rfl

theorem sourceDeltaRow24 (j : Basis) : sourceRows24[j.val]! =
    Witness.Upper.sourceRows24[j.val]! - (if j = (24 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[24]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow24 (j : Basis) : sourceRows24[j.val]! =
    (if j = (24 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (24 : Basis) j + 1000*Witness.vector[24]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow24, Upper.sourceRow24]
  split_ifs <;> ring

theorem firstColumn24 : firstColumns24 = sourceRows.map (fun row => Rows.dot row basisColumns24) := by rfl

theorem gramRow24 : gramRows24 = firstColumns.map (Rows.dot basisColumns24) := by rfl

theorem dominanceRow24 : 0 < Rows.margin gramRows24 (⟨24, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength24 : sourceRows24.length = 98 := by rfl
theorem basisColumnsLength24 : basisColumns24.length = 98 := by rfl
theorem firstColumnsLength24 : firstColumns24.length = 98 := by rfl
theorem gramRowsLength24 : gramRows24.length = 98 := by rfl

theorem sourceDeltaRow25 (j : Basis) : sourceRows25[j.val]! =
    Witness.Upper.sourceRows25[j.val]! - (if j = (25 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[25]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow25 (j : Basis) : sourceRows25[j.val]! =
    (if j = (25 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (25 : Basis) j + 1000*Witness.vector[25]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow25, Upper.sourceRow25]
  split_ifs <;> ring

theorem firstColumn25 : firstColumns25 = sourceRows.map (fun row => Rows.dot row basisColumns25) := by rfl

theorem gramRow25 : gramRows25 = firstColumns.map (Rows.dot basisColumns25) := by rfl

theorem dominanceRow25 : 0 < Rows.margin gramRows25 (⟨25, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength25 : sourceRows25.length = 98 := by rfl
theorem basisColumnsLength25 : basisColumns25.length = 98 := by rfl
theorem firstColumnsLength25 : firstColumns25.length = 98 := by rfl
theorem gramRowsLength25 : gramRows25.length = 98 := by rfl

theorem sourceDeltaRow26 (j : Basis) : sourceRows26[j.val]! =
    Witness.Upper.sourceRows26[j.val]! - (if j = (26 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[26]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow26 (j : Basis) : sourceRows26[j.val]! =
    (if j = (26 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (26 : Basis) j + 1000*Witness.vector[26]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow26, Upper.sourceRow26]
  split_ifs <;> ring

theorem firstColumn26 : firstColumns26 = sourceRows.map (fun row => Rows.dot row basisColumns26) := by rfl

theorem gramRow26 : gramRows26 = firstColumns.map (Rows.dot basisColumns26) := by rfl

theorem dominanceRow26 : 0 < Rows.margin gramRows26 (⟨26, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength26 : sourceRows26.length = 98 := by rfl
theorem basisColumnsLength26 : basisColumns26.length = 98 := by rfl
theorem firstColumnsLength26 : firstColumns26.length = 98 := by rfl
theorem gramRowsLength26 : gramRows26.length = 98 := by rfl

theorem sourceDeltaRow27 (j : Basis) : sourceRows27[j.val]! =
    Witness.Upper.sourceRows27[j.val]! - (if j = (27 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[27]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow27 (j : Basis) : sourceRows27[j.val]! =
    (if j = (27 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (27 : Basis) j + 1000*Witness.vector[27]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow27, Upper.sourceRow27]
  split_ifs <;> ring

theorem firstColumn27 : firstColumns27 = sourceRows.map (fun row => Rows.dot row basisColumns27) := by rfl

theorem gramRow27 : gramRows27 = firstColumns.map (Rows.dot basisColumns27) := by rfl

theorem dominanceRow27 : 0 < Rows.margin gramRows27 (⟨27, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength27 : sourceRows27.length = 98 := by rfl
theorem basisColumnsLength27 : basisColumns27.length = 98 := by rfl
theorem firstColumnsLength27 : firstColumns27.length = 98 := by rfl
theorem gramRowsLength27 : gramRows27.length = 98 := by rfl

end Second
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
