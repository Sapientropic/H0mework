import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Second
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Vector
import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.B01

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
namespace Second
open Propagation.Interface
open Witness.Second

theorem sourceDeltaRow7 (j : Basis) : sourceRows7[j.val]! =
    Witness.Upper.sourceRows7[j.val]! - (if j = (7 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[7]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow7 (j : Basis) : sourceRows7[j.val]! =
    (if j = (7 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (7 : Basis) j + 1000*Witness.vector[7]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow7, Upper.sourceRow7]
  split_ifs <;> ring

theorem firstColumn7 : firstColumns7 = sourceRows.map (fun row => Rows.dot row basisColumns7) := by rfl

theorem gramRow7 : gramRows7 = firstColumns.map (Rows.dot basisColumns7) := by rfl

theorem dominanceRow7 : 0 < Rows.margin gramRows7 (⟨7, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength7 : sourceRows7.length = 98 := by rfl
theorem basisColumnsLength7 : basisColumns7.length = 98 := by rfl
theorem firstColumnsLength7 : firstColumns7.length = 98 := by rfl
theorem gramRowsLength7 : gramRows7.length = 98 := by rfl

theorem sourceDeltaRow8 (j : Basis) : sourceRows8[j.val]! =
    Witness.Upper.sourceRows8[j.val]! - (if j = (8 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[8]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow8 (j : Basis) : sourceRows8[j.val]! =
    (if j = (8 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (8 : Basis) j + 1000*Witness.vector[8]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow8, Upper.sourceRow8]
  split_ifs <;> ring

theorem firstColumn8 : firstColumns8 = sourceRows.map (fun row => Rows.dot row basisColumns8) := by rfl

theorem gramRow8 : gramRows8 = firstColumns.map (Rows.dot basisColumns8) := by rfl

theorem dominanceRow8 : 0 < Rows.margin gramRows8 (⟨8, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength8 : sourceRows8.length = 98 := by rfl
theorem basisColumnsLength8 : basisColumns8.length = 98 := by rfl
theorem firstColumnsLength8 : firstColumns8.length = 98 := by rfl
theorem gramRowsLength8 : gramRows8.length = 98 := by rfl

theorem sourceDeltaRow9 (j : Basis) : sourceRows9[j.val]! =
    Witness.Upper.sourceRows9[j.val]! - (if j = (9 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[9]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow9 (j : Basis) : sourceRows9[j.val]! =
    (if j = (9 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (9 : Basis) j + 1000*Witness.vector[9]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow9, Upper.sourceRow9]
  split_ifs <;> ring

theorem firstColumn9 : firstColumns9 = sourceRows.map (fun row => Rows.dot row basisColumns9) := by rfl

theorem gramRow9 : gramRows9 = firstColumns.map (Rows.dot basisColumns9) := by rfl

theorem dominanceRow9 : 0 < Rows.margin gramRows9 (⟨9, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength9 : sourceRows9.length = 98 := by rfl
theorem basisColumnsLength9 : basisColumns9.length = 98 := by rfl
theorem firstColumnsLength9 : firstColumns9.length = 98 := by rfl
theorem gramRowsLength9 : gramRows9.length = 98 := by rfl

theorem sourceDeltaRow10 (j : Basis) : sourceRows10[j.val]! =
    Witness.Upper.sourceRows10[j.val]! - (if j = (10 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[10]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow10 (j : Basis) : sourceRows10[j.val]! =
    (if j = (10 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (10 : Basis) j + 1000*Witness.vector[10]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow10, Upper.sourceRow10]
  split_ifs <;> ring

theorem firstColumn10 : firstColumns10 = sourceRows.map (fun row => Rows.dot row basisColumns10) := by rfl

theorem gramRow10 : gramRows10 = firstColumns.map (Rows.dot basisColumns10) := by rfl

theorem dominanceRow10 : 0 < Rows.margin gramRows10 (⟨10, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength10 : sourceRows10.length = 98 := by rfl
theorem basisColumnsLength10 : basisColumns10.length = 98 := by rfl
theorem firstColumnsLength10 : firstColumns10.length = 98 := by rfl
theorem gramRowsLength10 : gramRows10.length = 98 := by rfl

theorem sourceDeltaRow11 (j : Basis) : sourceRows11[j.val]! =
    Witness.Upper.sourceRows11[j.val]! - (if j = (11 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[11]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow11 (j : Basis) : sourceRows11[j.val]! =
    (if j = (11 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (11 : Basis) j + 1000*Witness.vector[11]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow11, Upper.sourceRow11]
  split_ifs <;> ring

theorem firstColumn11 : firstColumns11 = sourceRows.map (fun row => Rows.dot row basisColumns11) := by rfl

theorem gramRow11 : gramRows11 = firstColumns.map (Rows.dot basisColumns11) := by rfl

theorem dominanceRow11 : 0 < Rows.margin gramRows11 (⟨11, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength11 : sourceRows11.length = 98 := by rfl
theorem basisColumnsLength11 : basisColumns11.length = 98 := by rfl
theorem firstColumnsLength11 : firstColumns11.length = 98 := by rfl
theorem gramRowsLength11 : gramRows11.length = 98 := by rfl

theorem sourceDeltaRow12 (j : Basis) : sourceRows12[j.val]! =
    Witness.Upper.sourceRows12[j.val]! - (if j = (12 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[12]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow12 (j : Basis) : sourceRows12[j.val]! =
    (if j = (12 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (12 : Basis) j + 1000*Witness.vector[12]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow12, Upper.sourceRow12]
  split_ifs <;> ring

theorem firstColumn12 : firstColumns12 = sourceRows.map (fun row => Rows.dot row basisColumns12) := by rfl

theorem gramRow12 : gramRows12 = firstColumns.map (Rows.dot basisColumns12) := by rfl

theorem dominanceRow12 : 0 < Rows.margin gramRows12 (⟨12, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength12 : sourceRows12.length = 98 := by rfl
theorem basisColumnsLength12 : basisColumns12.length = 98 := by rfl
theorem firstColumnsLength12 : firstColumns12.length = 98 := by rfl
theorem gramRowsLength12 : gramRows12.length = 98 := by rfl

theorem sourceDeltaRow13 (j : Basis) : sourceRows13[j.val]! =
    Witness.Upper.sourceRows13[j.val]! - (if j = (13 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[13]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow13 (j : Basis) : sourceRows13[j.val]! =
    (if j = (13 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (13 : Basis) j + 1000*Witness.vector[13]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow13, Upper.sourceRow13]
  split_ifs <;> ring

theorem firstColumn13 : firstColumns13 = sourceRows.map (fun row => Rows.dot row basisColumns13) := by rfl

theorem gramRow13 : gramRows13 = firstColumns.map (Rows.dot basisColumns13) := by rfl

theorem dominanceRow13 : 0 < Rows.margin gramRows13 (⟨13, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength13 : sourceRows13.length = 98 := by rfl
theorem basisColumnsLength13 : basisColumns13.length = 98 := by rfl
theorem firstColumnsLength13 : firstColumns13.length = 98 := by rfl
theorem gramRowsLength13 : gramRows13.length = 98 := by rfl

end Second
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
