import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Second
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Vector
import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.B12

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
namespace Second
open Propagation.Interface
open Witness.Second

theorem sourceDeltaRow84 (j : Basis) : sourceRows84[j.val]! =
    Witness.Upper.sourceRows84[j.val]! - (if j = (84 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[84]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow84 (j : Basis) : sourceRows84[j.val]! =
    (if j = (84 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (84 : Basis) j + 1000*Witness.vector[84]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow84, Upper.sourceRow84]
  split_ifs <;> ring

theorem firstColumn84 : firstColumns84 = sourceRows.map (fun row => Rows.dot row basisColumns84) := by rfl

theorem gramRow84 : gramRows84 = firstColumns.map (Rows.dot basisColumns84) := by rfl

theorem dominanceRow84 : 0 < Rows.margin gramRows84 (⟨84, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength84 : sourceRows84.length = 98 := by rfl
theorem basisColumnsLength84 : basisColumns84.length = 98 := by rfl
theorem firstColumnsLength84 : firstColumns84.length = 98 := by rfl
theorem gramRowsLength84 : gramRows84.length = 98 := by rfl

theorem sourceDeltaRow85 (j : Basis) : sourceRows85[j.val]! =
    Witness.Upper.sourceRows85[j.val]! - (if j = (85 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[85]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow85 (j : Basis) : sourceRows85[j.val]! =
    (if j = (85 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (85 : Basis) j + 1000*Witness.vector[85]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow85, Upper.sourceRow85]
  split_ifs <;> ring

theorem firstColumn85 : firstColumns85 = sourceRows.map (fun row => Rows.dot row basisColumns85) := by rfl

theorem gramRow85 : gramRows85 = firstColumns.map (Rows.dot basisColumns85) := by rfl

theorem dominanceRow85 : 0 < Rows.margin gramRows85 (⟨85, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength85 : sourceRows85.length = 98 := by rfl
theorem basisColumnsLength85 : basisColumns85.length = 98 := by rfl
theorem firstColumnsLength85 : firstColumns85.length = 98 := by rfl
theorem gramRowsLength85 : gramRows85.length = 98 := by rfl

theorem sourceDeltaRow86 (j : Basis) : sourceRows86[j.val]! =
    Witness.Upper.sourceRows86[j.val]! - (if j = (86 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[86]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow86 (j : Basis) : sourceRows86[j.val]! =
    (if j = (86 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (86 : Basis) j + 1000*Witness.vector[86]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow86, Upper.sourceRow86]
  split_ifs <;> ring

theorem firstColumn86 : firstColumns86 = sourceRows.map (fun row => Rows.dot row basisColumns86) := by rfl

theorem gramRow86 : gramRows86 = firstColumns.map (Rows.dot basisColumns86) := by rfl

theorem dominanceRow86 : 0 < Rows.margin gramRows86 (⟨86, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength86 : sourceRows86.length = 98 := by rfl
theorem basisColumnsLength86 : basisColumns86.length = 98 := by rfl
theorem firstColumnsLength86 : firstColumns86.length = 98 := by rfl
theorem gramRowsLength86 : gramRows86.length = 98 := by rfl

theorem sourceDeltaRow87 (j : Basis) : sourceRows87[j.val]! =
    Witness.Upper.sourceRows87[j.val]! - (if j = (87 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[87]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow87 (j : Basis) : sourceRows87[j.val]! =
    (if j = (87 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (87 : Basis) j + 1000*Witness.vector[87]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow87, Upper.sourceRow87]
  split_ifs <;> ring

theorem firstColumn87 : firstColumns87 = sourceRows.map (fun row => Rows.dot row basisColumns87) := by rfl

theorem gramRow87 : gramRows87 = firstColumns.map (Rows.dot basisColumns87) := by rfl

theorem dominanceRow87 : 0 < Rows.margin gramRows87 (⟨87, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength87 : sourceRows87.length = 98 := by rfl
theorem basisColumnsLength87 : basisColumns87.length = 98 := by rfl
theorem firstColumnsLength87 : firstColumns87.length = 98 := by rfl
theorem gramRowsLength87 : gramRows87.length = 98 := by rfl

theorem sourceDeltaRow88 (j : Basis) : sourceRows88[j.val]! =
    Witness.Upper.sourceRows88[j.val]! - (if j = (88 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[88]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow88 (j : Basis) : sourceRows88[j.val]! =
    (if j = (88 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (88 : Basis) j + 1000*Witness.vector[88]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow88, Upper.sourceRow88]
  split_ifs <;> ring

theorem firstColumn88 : firstColumns88 = sourceRows.map (fun row => Rows.dot row basisColumns88) := by rfl

theorem gramRow88 : gramRows88 = firstColumns.map (Rows.dot basisColumns88) := by rfl

theorem dominanceRow88 : 0 < Rows.margin gramRows88 (⟨88, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength88 : sourceRows88.length = 98 := by rfl
theorem basisColumnsLength88 : basisColumns88.length = 98 := by rfl
theorem firstColumnsLength88 : firstColumns88.length = 98 := by rfl
theorem gramRowsLength88 : gramRows88.length = 98 := by rfl

theorem sourceDeltaRow89 (j : Basis) : sourceRows89[j.val]! =
    Witness.Upper.sourceRows89[j.val]! - (if j = (89 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[89]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow89 (j : Basis) : sourceRows89[j.val]! =
    (if j = (89 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (89 : Basis) j + 1000*Witness.vector[89]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow89, Upper.sourceRow89]
  split_ifs <;> ring

theorem firstColumn89 : firstColumns89 = sourceRows.map (fun row => Rows.dot row basisColumns89) := by rfl

theorem gramRow89 : gramRows89 = firstColumns.map (Rows.dot basisColumns89) := by rfl

theorem dominanceRow89 : 0 < Rows.margin gramRows89 (⟨89, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength89 : sourceRows89.length = 98 := by rfl
theorem basisColumnsLength89 : basisColumns89.length = 98 := by rfl
theorem firstColumnsLength89 : firstColumns89.length = 98 := by rfl
theorem gramRowsLength89 : gramRows89.length = 98 := by rfl

theorem sourceDeltaRow90 (j : Basis) : sourceRows90[j.val]! =
    Witness.Upper.sourceRows90[j.val]! - (if j = (90 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[90]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow90 (j : Basis) : sourceRows90[j.val]! =
    (if j = (90 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (90 : Basis) j + 1000*Witness.vector[90]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow90, Upper.sourceRow90]
  split_ifs <;> ring

theorem firstColumn90 : firstColumns90 = sourceRows.map (fun row => Rows.dot row basisColumns90) := by rfl

theorem gramRow90 : gramRows90 = firstColumns.map (Rows.dot basisColumns90) := by rfl

theorem dominanceRow90 : 0 < Rows.margin gramRows90 (⟨90, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength90 : sourceRows90.length = 98 := by rfl
theorem basisColumnsLength90 : basisColumns90.length = 98 := by rfl
theorem firstColumnsLength90 : firstColumns90.length = 98 := by rfl
theorem gramRowsLength90 : gramRows90.length = 98 := by rfl

end Second
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
