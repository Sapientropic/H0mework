import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Second
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Vector
import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.B13

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
namespace Second
open Propagation.Interface
open Witness.Second

theorem sourceDeltaRow91 (j : Basis) : sourceRows91[j.val]! =
    Witness.Upper.sourceRows91[j.val]! - (if j = (91 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[91]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow91 (j : Basis) : sourceRows91[j.val]! =
    (if j = (91 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (91 : Basis) j + 1000*Witness.vector[91]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow91, Upper.sourceRow91]
  split_ifs <;> ring

theorem firstColumn91 : firstColumns91 = sourceRows.map (fun row => Rows.dot row basisColumns91) := by rfl

theorem gramRow91 : gramRows91 = firstColumns.map (Rows.dot basisColumns91) := by rfl

theorem dominanceRow91 : 0 < Rows.margin gramRows91 (⟨91, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength91 : sourceRows91.length = 98 := by rfl
theorem basisColumnsLength91 : basisColumns91.length = 98 := by rfl
theorem firstColumnsLength91 : firstColumns91.length = 98 := by rfl
theorem gramRowsLength91 : gramRows91.length = 98 := by rfl

theorem sourceDeltaRow92 (j : Basis) : sourceRows92[j.val]! =
    Witness.Upper.sourceRows92[j.val]! - (if j = (92 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[92]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow92 (j : Basis) : sourceRows92[j.val]! =
    (if j = (92 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (92 : Basis) j + 1000*Witness.vector[92]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow92, Upper.sourceRow92]
  split_ifs <;> ring

theorem firstColumn92 : firstColumns92 = sourceRows.map (fun row => Rows.dot row basisColumns92) := by rfl

theorem gramRow92 : gramRows92 = firstColumns.map (Rows.dot basisColumns92) := by rfl

theorem dominanceRow92 : 0 < Rows.margin gramRows92 (⟨92, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength92 : sourceRows92.length = 98 := by rfl
theorem basisColumnsLength92 : basisColumns92.length = 98 := by rfl
theorem firstColumnsLength92 : firstColumns92.length = 98 := by rfl
theorem gramRowsLength92 : gramRows92.length = 98 := by rfl

theorem sourceDeltaRow93 (j : Basis) : sourceRows93[j.val]! =
    Witness.Upper.sourceRows93[j.val]! - (if j = (93 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[93]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow93 (j : Basis) : sourceRows93[j.val]! =
    (if j = (93 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (93 : Basis) j + 1000*Witness.vector[93]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow93, Upper.sourceRow93]
  split_ifs <;> ring

theorem firstColumn93 : firstColumns93 = sourceRows.map (fun row => Rows.dot row basisColumns93) := by rfl

theorem gramRow93 : gramRows93 = firstColumns.map (Rows.dot basisColumns93) := by rfl

theorem dominanceRow93 : 0 < Rows.margin gramRows93 (⟨93, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength93 : sourceRows93.length = 98 := by rfl
theorem basisColumnsLength93 : basisColumns93.length = 98 := by rfl
theorem firstColumnsLength93 : firstColumns93.length = 98 := by rfl
theorem gramRowsLength93 : gramRows93.length = 98 := by rfl

theorem sourceDeltaRow94 (j : Basis) : sourceRows94[j.val]! =
    Witness.Upper.sourceRows94[j.val]! - (if j = (94 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[94]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow94 (j : Basis) : sourceRows94[j.val]! =
    (if j = (94 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (94 : Basis) j + 1000*Witness.vector[94]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow94, Upper.sourceRow94]
  split_ifs <;> ring

theorem firstColumn94 : firstColumns94 = sourceRows.map (fun row => Rows.dot row basisColumns94) := by rfl

theorem gramRow94 : gramRows94 = firstColumns.map (Rows.dot basisColumns94) := by rfl

theorem dominanceRow94 : 0 < Rows.margin gramRows94 (⟨94, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength94 : sourceRows94.length = 98 := by rfl
theorem basisColumnsLength94 : basisColumns94.length = 98 := by rfl
theorem firstColumnsLength94 : firstColumns94.length = 98 := by rfl
theorem gramRowsLength94 : gramRows94.length = 98 := by rfl

theorem sourceDeltaRow95 (j : Basis) : sourceRows95[j.val]! =
    Witness.Upper.sourceRows95[j.val]! - (if j = (95 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[95]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow95 (j : Basis) : sourceRows95[j.val]! =
    (if j = (95 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (95 : Basis) j + 1000*Witness.vector[95]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow95, Upper.sourceRow95]
  split_ifs <;> ring

theorem firstColumn95 : firstColumns95 = sourceRows.map (fun row => Rows.dot row basisColumns95) := by rfl

theorem gramRow95 : gramRows95 = firstColumns.map (Rows.dot basisColumns95) := by rfl

theorem dominanceRow95 : 0 < Rows.margin gramRows95 (⟨95, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength95 : sourceRows95.length = 98 := by rfl
theorem basisColumnsLength95 : basisColumns95.length = 98 := by rfl
theorem firstColumnsLength95 : firstColumns95.length = 98 := by rfl
theorem gramRowsLength95 : gramRows95.length = 98 := by rfl

theorem sourceDeltaRow96 (j : Basis) : sourceRows96[j.val]! =
    Witness.Upper.sourceRows96[j.val]! - (if j = (96 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[96]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow96 (j : Basis) : sourceRows96[j.val]! =
    (if j = (96 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (96 : Basis) j + 1000*Witness.vector[96]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow96, Upper.sourceRow96]
  split_ifs <;> ring

theorem firstColumn96 : firstColumns96 = sourceRows.map (fun row => Rows.dot row basisColumns96) := by rfl

theorem gramRow96 : gramRows96 = firstColumns.map (Rows.dot basisColumns96) := by rfl

theorem dominanceRow96 : 0 < Rows.margin gramRows96 (⟨96, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength96 : sourceRows96.length = 98 := by rfl
theorem basisColumnsLength96 : basisColumns96.length = 98 := by rfl
theorem firstColumnsLength96 : firstColumns96.length = 98 := by rfl
theorem gramRowsLength96 : gramRows96.length = 98 := by rfl

theorem sourceDeltaRow97 (j : Basis) : sourceRows97[j.val]! =
    Witness.Upper.sourceRows97[j.val]! - (if j = (97 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[97]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow97 (j : Basis) : sourceRows97[j.val]! =
    (if j = (97 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (97 : Basis) j + 1000*Witness.vector[97]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow97, Upper.sourceRow97]
  split_ifs <;> ring

theorem firstColumn97 : firstColumns97 = sourceRows.map (fun row => Rows.dot row basisColumns97) := by rfl

theorem gramRow97 : gramRows97 = firstColumns.map (Rows.dot basisColumns97) := by rfl

theorem dominanceRow97 : 0 < Rows.margin gramRows97 (⟨97, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength97 : sourceRows97.length = 98 := by rfl
theorem basisColumnsLength97 : basisColumns97.length = 98 := by rfl
theorem firstColumnsLength97 : firstColumns97.length = 98 := by rfl
theorem gramRowsLength97 : gramRows97.length = 98 := by rfl

end Second
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
