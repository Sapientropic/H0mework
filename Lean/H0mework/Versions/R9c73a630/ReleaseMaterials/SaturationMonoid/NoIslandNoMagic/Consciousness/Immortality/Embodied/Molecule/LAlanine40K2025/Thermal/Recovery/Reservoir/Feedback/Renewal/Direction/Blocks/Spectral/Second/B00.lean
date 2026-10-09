import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Second
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Vector
import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.B00

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
namespace Second
open Propagation.Interface
open Witness.Second

theorem sourceDeltaRow0 (j : Basis) : sourceRows0[j.val]! =
    Witness.Upper.sourceRows0[j.val]! - (if j = (0 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[0]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow0 (j : Basis) : sourceRows0[j.val]! =
    (if j = (0 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (0 : Basis) j + 1000*Witness.vector[0]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow0, Upper.sourceRow0]
  split_ifs <;> ring

theorem firstColumn0 : firstColumns0 = sourceRows.map (fun row => Rows.dot row basisColumns0) := by rfl

theorem gramRow0 : gramRows0 = firstColumns.map (Rows.dot basisColumns0) := by rfl

theorem dominanceRow0 : 0 < Rows.margin gramRows0 (⟨0, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength0 : sourceRows0.length = 98 := by rfl
theorem basisColumnsLength0 : basisColumns0.length = 98 := by rfl
theorem firstColumnsLength0 : firstColumns0.length = 98 := by rfl
theorem gramRowsLength0 : gramRows0.length = 98 := by rfl

theorem sourceDeltaRow1 (j : Basis) : sourceRows1[j.val]! =
    Witness.Upper.sourceRows1[j.val]! - (if j = (1 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[1]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow1 (j : Basis) : sourceRows1[j.val]! =
    (if j = (1 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (1 : Basis) j + 1000*Witness.vector[1]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow1, Upper.sourceRow1]
  split_ifs <;> ring

theorem firstColumn1 : firstColumns1 = sourceRows.map (fun row => Rows.dot row basisColumns1) := by rfl

theorem gramRow1 : gramRows1 = firstColumns.map (Rows.dot basisColumns1) := by rfl

theorem dominanceRow1 : 0 < Rows.margin gramRows1 (⟨1, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength1 : sourceRows1.length = 98 := by rfl
theorem basisColumnsLength1 : basisColumns1.length = 98 := by rfl
theorem firstColumnsLength1 : firstColumns1.length = 98 := by rfl
theorem gramRowsLength1 : gramRows1.length = 98 := by rfl

theorem sourceDeltaRow2 (j : Basis) : sourceRows2[j.val]! =
    Witness.Upper.sourceRows2[j.val]! - (if j = (2 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[2]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow2 (j : Basis) : sourceRows2[j.val]! =
    (if j = (2 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (2 : Basis) j + 1000*Witness.vector[2]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow2, Upper.sourceRow2]
  split_ifs <;> ring

theorem firstColumn2 : firstColumns2 = sourceRows.map (fun row => Rows.dot row basisColumns2) := by rfl

theorem gramRow2 : gramRows2 = firstColumns.map (Rows.dot basisColumns2) := by rfl

theorem dominanceRow2 : 0 < Rows.margin gramRows2 (⟨2, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength2 : sourceRows2.length = 98 := by rfl
theorem basisColumnsLength2 : basisColumns2.length = 98 := by rfl
theorem firstColumnsLength2 : firstColumns2.length = 98 := by rfl
theorem gramRowsLength2 : gramRows2.length = 98 := by rfl

theorem sourceDeltaRow3 (j : Basis) : sourceRows3[j.val]! =
    Witness.Upper.sourceRows3[j.val]! - (if j = (3 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[3]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow3 (j : Basis) : sourceRows3[j.val]! =
    (if j = (3 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (3 : Basis) j + 1000*Witness.vector[3]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow3, Upper.sourceRow3]
  split_ifs <;> ring

theorem firstColumn3 : firstColumns3 = sourceRows.map (fun row => Rows.dot row basisColumns3) := by rfl

theorem gramRow3 : gramRows3 = firstColumns.map (Rows.dot basisColumns3) := by rfl

theorem dominanceRow3 : 0 < Rows.margin gramRows3 (⟨3, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength3 : sourceRows3.length = 98 := by rfl
theorem basisColumnsLength3 : basisColumns3.length = 98 := by rfl
theorem firstColumnsLength3 : firstColumns3.length = 98 := by rfl
theorem gramRowsLength3 : gramRows3.length = 98 := by rfl

theorem sourceDeltaRow4 (j : Basis) : sourceRows4[j.val]! =
    Witness.Upper.sourceRows4[j.val]! - (if j = (4 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[4]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow4 (j : Basis) : sourceRows4[j.val]! =
    (if j = (4 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (4 : Basis) j + 1000*Witness.vector[4]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow4, Upper.sourceRow4]
  split_ifs <;> ring

theorem firstColumn4 : firstColumns4 = sourceRows.map (fun row => Rows.dot row basisColumns4) := by rfl

theorem gramRow4 : gramRows4 = firstColumns.map (Rows.dot basisColumns4) := by rfl

theorem dominanceRow4 : 0 < Rows.margin gramRows4 (⟨4, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength4 : sourceRows4.length = 98 := by rfl
theorem basisColumnsLength4 : basisColumns4.length = 98 := by rfl
theorem firstColumnsLength4 : firstColumns4.length = 98 := by rfl
theorem gramRowsLength4 : gramRows4.length = 98 := by rfl

theorem sourceDeltaRow5 (j : Basis) : sourceRows5[j.val]! =
    Witness.Upper.sourceRows5[j.val]! - (if j = (5 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[5]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow5 (j : Basis) : sourceRows5[j.val]! =
    (if j = (5 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (5 : Basis) j + 1000*Witness.vector[5]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow5, Upper.sourceRow5]
  split_ifs <;> ring

theorem firstColumn5 : firstColumns5 = sourceRows.map (fun row => Rows.dot row basisColumns5) := by rfl

theorem gramRow5 : gramRows5 = firstColumns.map (Rows.dot basisColumns5) := by rfl

theorem dominanceRow5 : 0 < Rows.margin gramRows5 (⟨5, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength5 : sourceRows5.length = 98 := by rfl
theorem basisColumnsLength5 : basisColumns5.length = 98 := by rfl
theorem firstColumnsLength5 : firstColumns5.length = 98 := by rfl
theorem gramRowsLength5 : gramRows5.length = 98 := by rfl

theorem sourceDeltaRow6 (j : Basis) : sourceRows6[j.val]! =
    Witness.Upper.sourceRows6[j.val]! - (if j = (6 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[6]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow6 (j : Basis) : sourceRows6[j.val]! =
    (if j = (6 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (6 : Basis) j + 1000*Witness.vector[6]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow6, Upper.sourceRow6]
  split_ifs <;> ring

theorem firstColumn6 : firstColumns6 = sourceRows.map (fun row => Rows.dot row basisColumns6) := by rfl

theorem gramRow6 : gramRows6 = firstColumns.map (Rows.dot basisColumns6) := by rfl

theorem dominanceRow6 : 0 < Rows.margin gramRows6 (⟨6, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength6 : sourceRows6.length = 98 := by rfl
theorem basisColumnsLength6 : basisColumns6.length = 98 := by rfl
theorem firstColumnsLength6 : firstColumns6.length = 98 := by rfl
theorem gramRowsLength6 : gramRows6.length = 98 := by rfl

end Second
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
