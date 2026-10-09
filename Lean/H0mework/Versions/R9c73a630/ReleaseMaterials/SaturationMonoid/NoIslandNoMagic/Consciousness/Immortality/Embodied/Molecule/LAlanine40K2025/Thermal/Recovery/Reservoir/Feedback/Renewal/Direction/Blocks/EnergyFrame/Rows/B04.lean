import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Data
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Spectral.Upper.Assembly

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Spectral Propagation.Interface

theorem original_row_28 : frameRows28 = originalRows[28]! := by rfl

theorem original_column_28 : frameColumns28 = originalRows.map (fun row => row[28]!) := by rfl

theorem original_hamiltonian_28 (j : Basis) : hamiltonianRows28[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (28 : Basis) j := by
  have previous := Upper.source_entries (28 : Basis) j
  have restore : hamiltonianRows28[j.val]! = (if j=(28 : Basis) then 3150000000000000 else 0)-Upper.numerator (28 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_28 : appliedColumns28 = hamiltonianRows.map (fun row => Rows.dot row frameColumns28) := by rfl

theorem gram_row_28 : gramRows28 = frameColumns.map (Rows.dot frameColumns28) := by rfl

theorem eigen_residual_28 : residualColumns28 = (appliedColumns28.zip frameColumns28).map (fun pair => pair.1-pair.2*energies[28]!) := by rfl

theorem gram_error_28 : ((gramRows28.zip (List.ofFn (fun j : Fin 98 => if j=(28 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_28 : (residualColumns28.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_28 : hamiltonianRows28.length = 98 := by rfl
theorem frameRows_length_28 : frameRows28.length = 98 := by rfl
theorem frameColumns_length_28 : frameColumns28.length = 98 := by rfl
theorem appliedColumns_length_28 : appliedColumns28.length = 98 := by rfl
theorem gramRows_length_28 : gramRows28.length = 98 := by rfl
theorem residualColumns_length_28 : residualColumns28.length = 98 := by rfl

theorem original_row_29 : frameRows29 = originalRows[29]! := by rfl

theorem original_column_29 : frameColumns29 = originalRows.map (fun row => row[29]!) := by rfl

theorem original_hamiltonian_29 (j : Basis) : hamiltonianRows29[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (29 : Basis) j := by
  have previous := Upper.source_entries (29 : Basis) j
  have restore : hamiltonianRows29[j.val]! = (if j=(29 : Basis) then 3150000000000000 else 0)-Upper.numerator (29 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_29 : appliedColumns29 = hamiltonianRows.map (fun row => Rows.dot row frameColumns29) := by rfl

theorem gram_row_29 : gramRows29 = frameColumns.map (Rows.dot frameColumns29) := by rfl

theorem eigen_residual_29 : residualColumns29 = (appliedColumns29.zip frameColumns29).map (fun pair => pair.1-pair.2*energies[29]!) := by rfl

theorem gram_error_29 : ((gramRows29.zip (List.ofFn (fun j : Fin 98 => if j=(29 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_29 : (residualColumns29.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_29 : hamiltonianRows29.length = 98 := by rfl
theorem frameRows_length_29 : frameRows29.length = 98 := by rfl
theorem frameColumns_length_29 : frameColumns29.length = 98 := by rfl
theorem appliedColumns_length_29 : appliedColumns29.length = 98 := by rfl
theorem gramRows_length_29 : gramRows29.length = 98 := by rfl
theorem residualColumns_length_29 : residualColumns29.length = 98 := by rfl

theorem original_row_30 : frameRows30 = originalRows[30]! := by rfl

theorem original_column_30 : frameColumns30 = originalRows.map (fun row => row[30]!) := by rfl

theorem original_hamiltonian_30 (j : Basis) : hamiltonianRows30[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (30 : Basis) j := by
  have previous := Upper.source_entries (30 : Basis) j
  have restore : hamiltonianRows30[j.val]! = (if j=(30 : Basis) then 3150000000000000 else 0)-Upper.numerator (30 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_30 : appliedColumns30 = hamiltonianRows.map (fun row => Rows.dot row frameColumns30) := by rfl

theorem gram_row_30 : gramRows30 = frameColumns.map (Rows.dot frameColumns30) := by rfl

theorem eigen_residual_30 : residualColumns30 = (appliedColumns30.zip frameColumns30).map (fun pair => pair.1-pair.2*energies[30]!) := by rfl

theorem gram_error_30 : ((gramRows30.zip (List.ofFn (fun j : Fin 98 => if j=(30 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_30 : (residualColumns30.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_30 : hamiltonianRows30.length = 98 := by rfl
theorem frameRows_length_30 : frameRows30.length = 98 := by rfl
theorem frameColumns_length_30 : frameColumns30.length = 98 := by rfl
theorem appliedColumns_length_30 : appliedColumns30.length = 98 := by rfl
theorem gramRows_length_30 : gramRows30.length = 98 := by rfl
theorem residualColumns_length_30 : residualColumns30.length = 98 := by rfl

theorem original_row_31 : frameRows31 = originalRows[31]! := by rfl

theorem original_column_31 : frameColumns31 = originalRows.map (fun row => row[31]!) := by rfl

theorem original_hamiltonian_31 (j : Basis) : hamiltonianRows31[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (31 : Basis) j := by
  have previous := Upper.source_entries (31 : Basis) j
  have restore : hamiltonianRows31[j.val]! = (if j=(31 : Basis) then 3150000000000000 else 0)-Upper.numerator (31 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_31 : appliedColumns31 = hamiltonianRows.map (fun row => Rows.dot row frameColumns31) := by rfl

theorem gram_row_31 : gramRows31 = frameColumns.map (Rows.dot frameColumns31) := by rfl

theorem eigen_residual_31 : residualColumns31 = (appliedColumns31.zip frameColumns31).map (fun pair => pair.1-pair.2*energies[31]!) := by rfl

theorem gram_error_31 : ((gramRows31.zip (List.ofFn (fun j : Fin 98 => if j=(31 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_31 : (residualColumns31.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_31 : hamiltonianRows31.length = 98 := by rfl
theorem frameRows_length_31 : frameRows31.length = 98 := by rfl
theorem frameColumns_length_31 : frameColumns31.length = 98 := by rfl
theorem appliedColumns_length_31 : appliedColumns31.length = 98 := by rfl
theorem gramRows_length_31 : gramRows31.length = 98 := by rfl
theorem residualColumns_length_31 : residualColumns31.length = 98 := by rfl

theorem original_row_32 : frameRows32 = originalRows[32]! := by rfl

theorem original_column_32 : frameColumns32 = originalRows.map (fun row => row[32]!) := by rfl

theorem original_hamiltonian_32 (j : Basis) : hamiltonianRows32[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (32 : Basis) j := by
  have previous := Upper.source_entries (32 : Basis) j
  have restore : hamiltonianRows32[j.val]! = (if j=(32 : Basis) then 3150000000000000 else 0)-Upper.numerator (32 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_32 : appliedColumns32 = hamiltonianRows.map (fun row => Rows.dot row frameColumns32) := by rfl

theorem gram_row_32 : gramRows32 = frameColumns.map (Rows.dot frameColumns32) := by rfl

theorem eigen_residual_32 : residualColumns32 = (appliedColumns32.zip frameColumns32).map (fun pair => pair.1-pair.2*energies[32]!) := by rfl

theorem gram_error_32 : ((gramRows32.zip (List.ofFn (fun j : Fin 98 => if j=(32 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_32 : (residualColumns32.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_32 : hamiltonianRows32.length = 98 := by rfl
theorem frameRows_length_32 : frameRows32.length = 98 := by rfl
theorem frameColumns_length_32 : frameColumns32.length = 98 := by rfl
theorem appliedColumns_length_32 : appliedColumns32.length = 98 := by rfl
theorem gramRows_length_32 : gramRows32.length = 98 := by rfl
theorem residualColumns_length_32 : residualColumns32.length = 98 := by rfl

theorem original_row_33 : frameRows33 = originalRows[33]! := by rfl

theorem original_column_33 : frameColumns33 = originalRows.map (fun row => row[33]!) := by rfl

theorem original_hamiltonian_33 (j : Basis) : hamiltonianRows33[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (33 : Basis) j := by
  have previous := Upper.source_entries (33 : Basis) j
  have restore : hamiltonianRows33[j.val]! = (if j=(33 : Basis) then 3150000000000000 else 0)-Upper.numerator (33 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_33 : appliedColumns33 = hamiltonianRows.map (fun row => Rows.dot row frameColumns33) := by rfl

theorem gram_row_33 : gramRows33 = frameColumns.map (Rows.dot frameColumns33) := by rfl

theorem eigen_residual_33 : residualColumns33 = (appliedColumns33.zip frameColumns33).map (fun pair => pair.1-pair.2*energies[33]!) := by rfl

theorem gram_error_33 : ((gramRows33.zip (List.ofFn (fun j : Fin 98 => if j=(33 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_33 : (residualColumns33.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_33 : hamiltonianRows33.length = 98 := by rfl
theorem frameRows_length_33 : frameRows33.length = 98 := by rfl
theorem frameColumns_length_33 : frameColumns33.length = 98 := by rfl
theorem appliedColumns_length_33 : appliedColumns33.length = 98 := by rfl
theorem gramRows_length_33 : gramRows33.length = 98 := by rfl
theorem residualColumns_length_33 : residualColumns33.length = 98 := by rfl

theorem original_row_34 : frameRows34 = originalRows[34]! := by rfl

theorem original_column_34 : frameColumns34 = originalRows.map (fun row => row[34]!) := by rfl

theorem original_hamiltonian_34 (j : Basis) : hamiltonianRows34[j.val]! =
    Propagation.Interface.activeNumerator Propagation.Source.electronicSource (34 : Basis) j := by
  have previous := Upper.source_entries (34 : Basis) j
  have restore : hamiltonianRows34[j.val]! = (if j=(34 : Basis) then 3150000000000000 else 0)-Upper.numerator (34 : Basis) j := by
    fin_cases j <;> rfl
  rw [restore,previous]
  omega

theorem applied_column_34 : appliedColumns34 = hamiltonianRows.map (fun row => Rows.dot row frameColumns34) := by rfl

theorem gram_row_34 : gramRows34 = frameColumns.map (Rows.dot frameColumns34) := by rfl

theorem eigen_residual_34 : residualColumns34 = (appliedColumns34.zip frameColumns34).map (fun pair => pair.1-pair.2*energies[34]!) := by rfl

theorem gram_error_34 : ((gramRows34.zip (List.ofFn (fun j : Fin 98 => if j=(34 : Fin 98) then (10^30 : Int) else 0))).map (fun pair => |pair.1-pair.2|)).all (· ≤ 3*10^15) = true := by decide +kernel

theorem eigen_error_34 : (residualColumns34.map abs).all (· ≤ 3*10^16) = true := by decide +kernel

theorem hamiltonianRows_length_34 : hamiltonianRows34.length = 98 := by rfl
theorem frameRows_length_34 : frameRows34.length = 98 := by rfl
theorem frameColumns_length_34 : frameColumns34.length = 98 := by rfl
theorem appliedColumns_length_34 : appliedColumns34.length = 98 := by rfl
theorem gramRows_length_34 : gramRows34.length = 98 := by rfl
theorem residualColumns_length_34 : residualColumns34.length = 98 := by rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
