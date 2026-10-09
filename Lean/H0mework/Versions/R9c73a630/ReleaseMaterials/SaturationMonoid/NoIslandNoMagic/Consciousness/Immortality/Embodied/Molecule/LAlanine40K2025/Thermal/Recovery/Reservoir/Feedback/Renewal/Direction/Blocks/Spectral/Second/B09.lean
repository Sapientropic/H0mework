import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Second
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Vector
import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.B09

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
namespace Second
open Propagation.Interface
open Witness.Second

theorem sourceDeltaRow63 (j : Basis) : sourceRows63[j.val]! =
    Witness.Upper.sourceRows63[j.val]! - (if j = (63 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[63]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow63 (j : Basis) : sourceRows63[j.val]! =
    (if j = (63 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (63 : Basis) j + 1000*Witness.vector[63]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow63, Upper.sourceRow63]
  split_ifs <;> ring

theorem firstColumn63 : firstColumns63 = sourceRows.map (fun row => Rows.dot row basisColumns63) := by rfl

theorem gramRow63 : gramRows63 = firstColumns.map (Rows.dot basisColumns63) := by rfl

theorem dominanceRow63 : 0 < Rows.margin gramRows63 (⟨63, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength63 : sourceRows63.length = 98 := by rfl
theorem basisColumnsLength63 : basisColumns63.length = 98 := by rfl
theorem firstColumnsLength63 : firstColumns63.length = 98 := by rfl
theorem gramRowsLength63 : gramRows63.length = 98 := by rfl

theorem sourceDeltaRow64 (j : Basis) : sourceRows64[j.val]! =
    Witness.Upper.sourceRows64[j.val]! - (if j = (64 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[64]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow64 (j : Basis) : sourceRows64[j.val]! =
    (if j = (64 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (64 : Basis) j + 1000*Witness.vector[64]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow64, Upper.sourceRow64]
  split_ifs <;> ring

theorem firstColumn64 : firstColumns64 = sourceRows.map (fun row => Rows.dot row basisColumns64) := by rfl

theorem gramRow64 : gramRows64 = firstColumns.map (Rows.dot basisColumns64) := by rfl

theorem dominanceRow64 : 0 < Rows.margin gramRows64 (⟨64, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength64 : sourceRows64.length = 98 := by rfl
theorem basisColumnsLength64 : basisColumns64.length = 98 := by rfl
theorem firstColumnsLength64 : firstColumns64.length = 98 := by rfl
theorem gramRowsLength64 : gramRows64.length = 98 := by rfl

theorem sourceDeltaRow65 (j : Basis) : sourceRows65[j.val]! =
    Witness.Upper.sourceRows65[j.val]! - (if j = (65 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[65]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow65 (j : Basis) : sourceRows65[j.val]! =
    (if j = (65 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (65 : Basis) j + 1000*Witness.vector[65]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow65, Upper.sourceRow65]
  split_ifs <;> ring

theorem firstColumn65 : firstColumns65 = sourceRows.map (fun row => Rows.dot row basisColumns65) := by rfl

theorem gramRow65 : gramRows65 = firstColumns.map (Rows.dot basisColumns65) := by rfl

theorem dominanceRow65 : 0 < Rows.margin gramRows65 (⟨65, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength65 : sourceRows65.length = 98 := by rfl
theorem basisColumnsLength65 : basisColumns65.length = 98 := by rfl
theorem firstColumnsLength65 : firstColumns65.length = 98 := by rfl
theorem gramRowsLength65 : gramRows65.length = 98 := by rfl

theorem sourceDeltaRow66 (j : Basis) : sourceRows66[j.val]! =
    Witness.Upper.sourceRows66[j.val]! - (if j = (66 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[66]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow66 (j : Basis) : sourceRows66[j.val]! =
    (if j = (66 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (66 : Basis) j + 1000*Witness.vector[66]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow66, Upper.sourceRow66]
  split_ifs <;> ring

theorem firstColumn66 : firstColumns66 = sourceRows.map (fun row => Rows.dot row basisColumns66) := by rfl

theorem gramRow66 : gramRows66 = firstColumns.map (Rows.dot basisColumns66) := by rfl

theorem dominanceRow66 : 0 < Rows.margin gramRows66 (⟨66, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength66 : sourceRows66.length = 98 := by rfl
theorem basisColumnsLength66 : basisColumns66.length = 98 := by rfl
theorem firstColumnsLength66 : firstColumns66.length = 98 := by rfl
theorem gramRowsLength66 : gramRows66.length = 98 := by rfl

theorem sourceDeltaRow67 (j : Basis) : sourceRows67[j.val]! =
    Witness.Upper.sourceRows67[j.val]! - (if j = (67 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[67]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow67 (j : Basis) : sourceRows67[j.val]! =
    (if j = (67 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (67 : Basis) j + 1000*Witness.vector[67]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow67, Upper.sourceRow67]
  split_ifs <;> ring

theorem firstColumn67 : firstColumns67 = sourceRows.map (fun row => Rows.dot row basisColumns67) := by rfl

theorem gramRow67 : gramRows67 = firstColumns.map (Rows.dot basisColumns67) := by rfl

theorem dominanceRow67 : 0 < Rows.margin gramRows67 (⟨67, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength67 : sourceRows67.length = 98 := by rfl
theorem basisColumnsLength67 : basisColumns67.length = 98 := by rfl
theorem firstColumnsLength67 : firstColumns67.length = 98 := by rfl
theorem gramRowsLength67 : gramRows67.length = 98 := by rfl

theorem sourceDeltaRow68 (j : Basis) : sourceRows68[j.val]! =
    Witness.Upper.sourceRows68[j.val]! - (if j = (68 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[68]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow68 (j : Basis) : sourceRows68[j.val]! =
    (if j = (68 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (68 : Basis) j + 1000*Witness.vector[68]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow68, Upper.sourceRow68]
  split_ifs <;> ring

theorem firstColumn68 : firstColumns68 = sourceRows.map (fun row => Rows.dot row basisColumns68) := by rfl

theorem gramRow68 : gramRows68 = firstColumns.map (Rows.dot basisColumns68) := by rfl

theorem dominanceRow68 : 0 < Rows.margin gramRows68 (⟨68, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength68 : sourceRows68.length = 98 := by rfl
theorem basisColumnsLength68 : basisColumns68.length = 98 := by rfl
theorem firstColumnsLength68 : firstColumns68.length = 98 := by rfl
theorem gramRowsLength68 : gramRows68.length = 98 := by rfl

theorem sourceDeltaRow69 (j : Basis) : sourceRows69[j.val]! =
    Witness.Upper.sourceRows69[j.val]! - (if j = (69 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[69]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow69 (j : Basis) : sourceRows69[j.val]! =
    (if j = (69 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (69 : Basis) j + 1000*Witness.vector[69]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow69, Upper.sourceRow69]
  split_ifs <;> ring

theorem firstColumn69 : firstColumns69 = sourceRows.map (fun row => Rows.dot row basisColumns69) := by rfl

theorem gramRow69 : gramRows69 = firstColumns.map (Rows.dot basisColumns69) := by rfl

theorem dominanceRow69 : 0 < Rows.margin gramRows69 (⟨69, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength69 : sourceRows69.length = 98 := by rfl
theorem basisColumnsLength69 : basisColumns69.length = 98 := by rfl
theorem firstColumnsLength69 : firstColumns69.length = 98 := by rfl
theorem gramRowsLength69 : gramRows69.length = 98 := by rfl

end Second
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
