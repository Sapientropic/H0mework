import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Second
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Witness.Vector
import H0mework.Chemistry.LAlaninePropagation.BoundElectronicPropagation

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.B02

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
namespace Second
open Propagation.Interface
open Witness.Second

theorem sourceDeltaRow14 (j : Basis) : sourceRows14[j.val]! =
    Witness.Upper.sourceRows14[j.val]! - (if j = (14 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[14]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow14 (j : Basis) : sourceRows14[j.val]! =
    (if j = (14 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (14 : Basis) j + 1000*Witness.vector[14]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow14, Upper.sourceRow14]
  split_ifs <;> ring

theorem firstColumn14 : firstColumns14 = sourceRows.map (fun row => Rows.dot row basisColumns14) := by rfl

theorem gramRow14 : gramRows14 = firstColumns.map (Rows.dot basisColumns14) := by rfl

theorem dominanceRow14 : 0 < Rows.margin gramRows14 (⟨14, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength14 : sourceRows14.length = 98 := by rfl
theorem basisColumnsLength14 : basisColumns14.length = 98 := by rfl
theorem firstColumnsLength14 : firstColumns14.length = 98 := by rfl
theorem gramRowsLength14 : gramRows14.length = 98 := by rfl

theorem sourceDeltaRow15 (j : Basis) : sourceRows15[j.val]! =
    Witness.Upper.sourceRows15[j.val]! - (if j = (15 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[15]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow15 (j : Basis) : sourceRows15[j.val]! =
    (if j = (15 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (15 : Basis) j + 1000*Witness.vector[15]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow15, Upper.sourceRow15]
  split_ifs <;> ring

theorem firstColumn15 : firstColumns15 = sourceRows.map (fun row => Rows.dot row basisColumns15) := by rfl

theorem gramRow15 : gramRows15 = firstColumns.map (Rows.dot basisColumns15) := by rfl

theorem dominanceRow15 : 0 < Rows.margin gramRows15 (⟨15, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength15 : sourceRows15.length = 98 := by rfl
theorem basisColumnsLength15 : basisColumns15.length = 98 := by rfl
theorem firstColumnsLength15 : firstColumns15.length = 98 := by rfl
theorem gramRowsLength15 : gramRows15.length = 98 := by rfl

theorem sourceDeltaRow16 (j : Basis) : sourceRows16[j.val]! =
    Witness.Upper.sourceRows16[j.val]! - (if j = (16 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[16]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow16 (j : Basis) : sourceRows16[j.val]! =
    (if j = (16 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (16 : Basis) j + 1000*Witness.vector[16]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow16, Upper.sourceRow16]
  split_ifs <;> ring

theorem firstColumn16 : firstColumns16 = sourceRows.map (fun row => Rows.dot row basisColumns16) := by rfl

theorem gramRow16 : gramRows16 = firstColumns.map (Rows.dot basisColumns16) := by rfl

theorem dominanceRow16 : 0 < Rows.margin gramRows16 (⟨16, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength16 : sourceRows16.length = 98 := by rfl
theorem basisColumnsLength16 : basisColumns16.length = 98 := by rfl
theorem firstColumnsLength16 : firstColumns16.length = 98 := by rfl
theorem gramRowsLength16 : gramRows16.length = 98 := by rfl

theorem sourceDeltaRow17 (j : Basis) : sourceRows17[j.val]! =
    Witness.Upper.sourceRows17[j.val]! - (if j = (17 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[17]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow17 (j : Basis) : sourceRows17[j.val]! =
    (if j = (17 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (17 : Basis) j + 1000*Witness.vector[17]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow17, Upper.sourceRow17]
  split_ifs <;> ring

theorem firstColumn17 : firstColumns17 = sourceRows.map (fun row => Rows.dot row basisColumns17) := by rfl

theorem gramRow17 : gramRows17 = firstColumns.map (Rows.dot basisColumns17) := by rfl

theorem dominanceRow17 : 0 < Rows.margin gramRows17 (⟨17, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength17 : sourceRows17.length = 98 := by rfl
theorem basisColumnsLength17 : basisColumns17.length = 98 := by rfl
theorem firstColumnsLength17 : firstColumns17.length = 98 := by rfl
theorem gramRowsLength17 : gramRows17.length = 98 := by rfl

theorem sourceDeltaRow18 (j : Basis) : sourceRows18[j.val]! =
    Witness.Upper.sourceRows18[j.val]! - (if j = (18 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[18]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow18 (j : Basis) : sourceRows18[j.val]! =
    (if j = (18 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (18 : Basis) j + 1000*Witness.vector[18]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow18, Upper.sourceRow18]
  split_ifs <;> ring

theorem firstColumn18 : firstColumns18 = sourceRows.map (fun row => Rows.dot row basisColumns18) := by rfl

theorem gramRow18 : gramRows18 = firstColumns.map (Rows.dot basisColumns18) := by rfl

theorem dominanceRow18 : 0 < Rows.margin gramRows18 (⟨18, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength18 : sourceRows18.length = 98 := by rfl
theorem basisColumnsLength18 : basisColumns18.length = 98 := by rfl
theorem firstColumnsLength18 : firstColumns18.length = 98 := by rfl
theorem gramRowsLength18 : gramRows18.length = 98 := by rfl

theorem sourceDeltaRow19 (j : Basis) : sourceRows19[j.val]! =
    Witness.Upper.sourceRows19[j.val]! - (if j = (19 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[19]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow19 (j : Basis) : sourceRows19[j.val]! =
    (if j = (19 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (19 : Basis) j + 1000*Witness.vector[19]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow19, Upper.sourceRow19]
  split_ifs <;> ring

theorem firstColumn19 : firstColumns19 = sourceRows.map (fun row => Rows.dot row basisColumns19) := by rfl

theorem gramRow19 : gramRows19 = firstColumns.map (Rows.dot basisColumns19) := by rfl

theorem dominanceRow19 : 0 < Rows.margin gramRows19 (⟨19, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength19 : sourceRows19.length = 98 := by rfl
theorem basisColumnsLength19 : basisColumns19.length = 98 := by rfl
theorem firstColumnsLength19 : firstColumns19.length = 98 := by rfl
theorem gramRowsLength19 : gramRows19.length = 98 := by rfl

theorem sourceDeltaRow20 (j : Basis) : sourceRows20[j.val]! =
    Witness.Upper.sourceRows20[j.val]! - (if j = (20 : Basis) then 150000000000000 else 0) +
      1000*Witness.vector[20]!*Witness.vector[j.val]! := by
  fin_cases j <;> rfl

theorem sourceRow20 (j : Basis) : sourceRows20[j.val]! =
    (if j = (20 : Basis) then 3000000000000000 else 0) -
      Propagation.Interface.activeNumerator Propagation.Source.electronicSource (20 : Basis) j + 1000*Witness.vector[20]!*Witness.vector[j.val]! := by
  rw [sourceDeltaRow20, Upper.sourceRow20]
  split_ifs <;> ring

theorem firstColumn20 : firstColumns20 = sourceRows.map (fun row => Rows.dot row basisColumns20) := by rfl

theorem gramRow20 : gramRows20 = firstColumns.map (Rows.dot basisColumns20) := by rfl

theorem dominanceRow20 : 0 < Rows.margin gramRows20 (⟨20, by decide +kernel⟩ : Fin 98) := by decide +kernel

theorem sourceRowsLength20 : sourceRows20.length = 98 := by rfl
theorem basisColumnsLength20 : basisColumns20.length = 98 := by rfl
theorem firstColumnsLength20 : firstColumns20.length = 98 := by rfl
theorem gramRowsLength20 : gramRows20.length = 98 := by rfl

end Second
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
